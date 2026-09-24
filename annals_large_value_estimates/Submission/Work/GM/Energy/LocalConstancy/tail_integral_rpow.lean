import Mathlib

namespace Work.GM.Energy.LocalConstancy

open MeasureTheory
set_option autoImplicit false

/-- The tail integral of `|ξ|^{-(m+1)}` outside `[-K,K]`, for `K ≥ 1` and `m ≥ 1`, is at most
`2 K^{-m}` (the exact value is `2 K^{-m}/m`).

Route: `(Set.Icc (-K) K)ᶜ` is the disjoint union (up to null sets) of `Set.Ioi K` and
`Set.Iic (-K)`.  On `Set.Ioi K` use `MeasureTheory.integral_Ioi_rpow_of_lt` with `a = -(m:ℝ)-1 < -1`
and `c = K`, giving `-K^{-m}/(-m) = K^{-m}/m`; on the left half use the change of variables
`ξ ↦ -ξ` (`MeasureTheory.integral_comp_neg_Iic`) where `|ξ| = -ξ`.  Then add the two halves
(e.g. `MeasureTheory.integral_add_compl` / `MeasureTheory.setIntegral_union`) and use `m ≥ 1`,
`K ≥ 1`.  Note `Real.rpow_neg`, `Real.rpow_natCast` convert between `|ξ| ^ (-(m:ℝ) - 1)` and the
powers Mathlib's rpow lemmas produce. -/
theorem tail_integral_rpow (m : ℕ) (hm : 1 ≤ m) {K : ℝ} (hK : 1 ≤ K) :
    (∫ ξ in (Set.Icc (-K) K)ᶜ, |ξ| ^ (-(m : ℝ) - 1)) ≤ 2 * K ^ (-(m : ℝ)) := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hm)
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have ha : -(m : ℝ) - 1 < -1 := by linarith
  -- Integrability and value of the integral on the right half `Ioi K`.
  have hint1 : IntegrableOn (fun x : ℝ => |x| ^ (-(m : ℝ) - 1)) (Set.Ioi K) volume :=
    (integrableOn_Ioi_rpow_of_lt ha hK0).congr_fun
      (fun x hx => by rw [abs_of_pos (lt_trans hK0 hx)]) measurableSet_Ioi
  have hright : ∫ x in Set.Ioi K, |x| ^ (-(m : ℝ) - 1) = K ^ (-(m : ℝ)) / (m : ℝ) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => by
      rw [abs_of_pos (lt_trans hK0 hx)])]
    rw [integral_Ioi_rpow_of_lt ha hK0]
    rw [show -(m : ℝ) - 1 + 1 = -(m : ℝ) from by ring, neg_div_neg_eq]
  -- The substitution `x ↦ -x` identifies the left half with the right half.
  have hleftaux : ∫ x in Set.Iic (-K), |x| ^ (-(m : ℝ) - 1)
      = ∫ x in Set.Ioi K, |x| ^ (-(m : ℝ) - 1) := by
    simpa using integral_comp_neg_Iic (-K) (fun x : ℝ => |x| ^ (-(m : ℝ) - 1))
  have hint2 : IntegrableOn (fun x : ℝ => |x| ^ (-(m : ℝ) - 1)) (Set.Iio (-K)) volume := by
    have hA : MeasurableEmbedding (fun x : ℝ => -x) := (Homeomorph.neg ℝ).measurableEmbedding
    rw [← MeasureTheory.Measure.map_neg_eq_self (volume : Measure ℝ)]
    rw [hA.integrableOn_map_iff]
    have hpre : (fun x : ℝ => -x) ⁻¹' Set.Iio (-K) = Set.Ioi K := by
      ext x; simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_Ioi]
      constructor <;> intro hx <;> linarith
    rw [hpre]
    exact (integrableOn_Ioi_rpow_of_lt ha hK0).congr_fun (fun x hx => by
      rw [Function.comp_apply, abs_neg, abs_of_pos (lt_trans hK0 hx)]) measurableSet_Ioi
  have hleft : ∫ x in Set.Iio (-K), |x| ^ (-(m : ℝ) - 1) = K ^ (-(m : ℝ)) / (m : ℝ) := by
    rw [← integral_Iic_eq_integral_Iio, hleftaux, hright]
  -- `Ioi K ∪ Iio (-K)` is exactly the complement of `Icc (-K) K`.
  have hunion : Set.Ioi K ∪ Set.Iio (-K) = (Set.Icc (-K) K)ᶜ := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioi, Set.mem_Iio, Set.mem_compl_iff, Set.mem_Icc]
    constructor
    · rintro (h | h) ⟨h1, h2⟩ <;> linarith
    · intro h
      by_cases hx : -K ≤ x
      · left; by_contra hc; exact h ⟨hx, le_of_not_gt hc⟩
      · right; exact lt_of_not_ge hx
  have hdisj : Disjoint (Set.Ioi K) (Set.Iio (-K)) := by
    rw [Set.disjoint_left]
    intro x hx hy
    simp only [Set.mem_Ioi] at hx
    simp only [Set.mem_Iio] at hy
    linarith
  rw [← hunion, setIntegral_union hdisj measurableSet_Iio hint1 hint2, hright, hleft]
  -- Both halves are `K^{-m}/m ≤ K^{-m}`, and there are two of them.
  have hKpow_nonneg : 0 ≤ K ^ (-(m : ℝ)) := Real.rpow_nonneg hK0.le _
  have hinv : (1 : ℝ) / (m : ℝ) ≤ 1 := by
    rw [div_le_one hm0]; exact hm1
  have hdiv : K ^ (-(m : ℝ)) / (m : ℝ) ≤ K ^ (-(m : ℝ)) := by
    rw [div_eq_mul_inv, ← one_div]
    calc K ^ (-(m : ℝ)) * (1 / (m : ℝ)) ≤ K ^ (-(m : ℝ)) * 1 :=
          mul_le_mul_of_nonneg_left hinv hKpow_nonneg
      _ = K ^ (-(m : ℝ)) := by ring
  linarith [hdiv, hKpow_nonneg]

end Work.GM.Energy.LocalConstancy
