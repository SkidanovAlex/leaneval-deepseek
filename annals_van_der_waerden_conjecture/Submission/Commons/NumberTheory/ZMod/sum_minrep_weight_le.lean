import Mathlib.Algebra.Order.Ring.Star
import Submission.Commons.Analysis.ExpLog.harmonic_le_one_add_log

/-!
# A weighted sum over `ZMod M`

For `M ≥ 1` and `H ≥ 0`, we bound
`∑_{b : ZMod M} min (2H+1) (M / (2·d(b)))`, where `d(b) = min b.val (M - b.val)`
is the distance of `b` to `0` in `ZMod M`, by `O((M + (2H+1))·log M)`.

The proof uses the elementary inequality `1 / min x y ≤ 1/x + 1/y` together with
the involution `b ↦ -b` of `ZMod M` and the harmonic-sum bound
`∑_{j=1}^{M-1} 1/j ≤ 1 + log M`.
-/

open scoped BigOperators

namespace Commons.NumberTheory.ZMod

/-- Reindex a sum over `ZMod M` that only depends on `b.val` as a sum over
`Finset.range M`. -/
lemma sum_zmod_val_eq_sum_range (M : ℕ) [NeZero M] (Ψ : ℕ → ℝ) :
    (∑ b : ZMod M, Ψ b.val) = ∑ j ∈ Finset.range M, Ψ j := by
  refine Finset.sum_bij' (fun b _ => b.val) (fun j _ => (j : ZMod M)) ?_ ?_ ?_ ?_ ?_
  · intro b hb; exact Finset.mem_range.mpr (ZMod.val_lt b)
  · intro j hj; exact Finset.mem_univ _
  · intro b hb; exact ZMod.natCast_zmod_val b
  · intro j hj; exact ZMod.val_cast_of_lt (Finset.mem_range.mp hj)
  · intro b hb; rfl

/-- Elementary inequality: `1 / min x y ≤ 1/x + 1/y` for nonnegative reals. -/
lemma one_div_min_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    1 / min x y ≤ 1/x + 1/y := by
  rcases le_total x y with h | h
  · rw [min_eq_left h]
    exact le_add_of_nonneg_right (div_nonneg zero_le_one hy)
  · rw [min_eq_right h]
    exact le_add_of_nonneg_left (div_nonneg zero_le_one hx)

lemma mul_div_two_eq (m D : ℝ) : m / (2 * D) = (m/2) * (1/D) := by
  rw [one_div]; ring

/-- Pointwise bound for the weight `min t (M / (2·d b))` in terms of the
reciprocal of `b.val` and that of `(-b).val`. -/
lemma sum_minrep_weight_pointwise (M : ℕ) [NeZero M] (t : ℝ) (ht : 0 ≤ t) (b : ZMod M) :
    min t ((M : ℝ) / (2 * ((min b.val (M - b.val) : ℕ) : ℝ)))
      ≤ ((M : ℝ)/2) * (1/(b.val:ℝ) + 1/(((-b).val : ℕ) : ℝ)) := by
  by_cases hb : b = 0
  · subst hb
    have hzero : (min (0:ZMod M).val (M - (0:ZMod M).val) : ℕ) = 0 := by
      simp [ZMod.val_zero]
    rw [hzero]
    simp only [Nat.cast_zero, mul_zero, div_zero, neg_zero, ZMod.val_zero]
    rw [min_eq_right ht]
    simp
  · have hneg : ((-b).val : ℝ) = ((M - b.val : ℕ) : ℝ) := by
      rw [ZMod.neg_val b, if_neg hb]
    have hd : ((min b.val (M - b.val) : ℕ) : ℝ) = min ((b.val:ℝ)) ((((-b).val : ℕ):ℝ)) := by
      rw [Nat.cast_min, ← hneg]
    have h1 : (1:ℝ)/((min b.val (M-b.val):ℕ):ℝ) ≤ 1/(b.val:ℝ) + 1/(((-b).val:ℕ):ℝ) := by
      rw [hd]; exact one_div_min_le (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hX : (M:ℝ)/(2*((min b.val (M-b.val):ℕ):ℝ)) = ((M:ℝ)/2)*(1/((min b.val (M-b.val):ℕ):ℝ)) :=
      mul_div_two_eq _ _
    calc min t ((M:ℝ)/(2*((min b.val (M-b.val):ℕ):ℝ)))
        ≤ (M:ℝ)/(2*((min b.val (M-b.val):ℕ):ℝ)) := min_le_right _ _
      _ = ((M:ℝ)/2)*(1/((min b.val (M-b.val):ℕ):ℝ)) := hX
      _ ≤ ((M:ℝ)/2)*(1/(b.val:ℝ) + 1/(((-b).val:ℕ):ℝ)) := by
            apply mul_le_mul_of_nonneg_left h1; positivity

/-- The weighted sum (without the special `b = 0` term) is bounded by
`M · (1 + log M)`. -/
lemma sum_minrep_weight_bound (M : ℕ) [NeZero M] (t : ℝ) (ht : 0 ≤ t) :
    (∑ b : ZMod M, (if b = 0 then t
        else min t ((M : ℝ) / (2 * ((min b.val (M - b.val) : ℕ) : ℝ)))))
      ≤ t + (M : ℝ) * (1 + Real.log M) := by
  have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr (NeZero.ne M)
  have hm : (0:ℝ) ≤ (M:ℝ) := by positivity
  have hdecomp : ∀ b : ZMod M,
      (if b = 0 then t else min t ((M:ℝ)/(2*((min b.val (M-b.val):ℕ):ℝ))))
        = min t ((M:ℝ)/(2*((min b.val (M-b.val):ℕ):ℝ))) + (if b = 0 then t else (0:ℝ)) := by
    intro b
    by_cases hb : b = 0
    · subst hb
      have hzero : (min (0:ZMod M).val (M - (0:ZMod M).val) : ℕ) = 0 := by simp [ZMod.val_zero]
      rw [hzero]
      simp only [Nat.cast_zero, mul_zero, div_zero, if_true]
      rw [min_eq_right ht]; simp
    · simp [hb]
  rw [Finset.sum_congr rfl (fun b _ => hdecomp b)]
  rw [Finset.sum_add_distrib]
  have hind : (∑ b : ZMod M, (if b = 0 then t else (0:ℝ))) = t := by
    rw [Finset.sum_ite_eq']
    simp
  rw [hind]
  have hg : (∑ b : ZMod M, min t ((M:ℝ)/(2*((min b.val (M-b.val):ℕ):ℝ))))
      ≤ ((M:ℝ)/2) * (∑ b : ZMod M, (1/(b.val:ℝ) + 1/(((-b).val:ℕ):ℝ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b _
    exact sum_minrep_weight_pointwise M t ht b
  have hSS : (∑ b : ZMod M, (1/(b.val:ℝ) + 1/(((-b).val:ℕ):ℝ)))
      = 2 * (∑ b : ZMod M, 1/(b.val:ℝ)) := by
    rw [Finset.sum_add_distrib]
    have hneg : (∑ b : ZMod M, 1/(((-b).val:ℕ):ℝ)) = (∑ b : ZMod M, 1/(b.val:ℝ)) := by
      have h := Equiv.sum_comp (Equiv.neg (ZMod M)) (fun b : ZMod M => (1:ℝ)/(b.val:ℝ))
      simpa using h
    rw [hneg]; ring
  have hS : (∑ b : ZMod M, 1/(b.val:ℝ)) ≤ 1 + Real.log (M:ℝ) := by
    rw [sum_zmod_val_eq_sum_range M (fun j => (1:ℝ)/(j:ℝ))]
    calc ∑ j ∈ Finset.range M, (1:ℝ)/(j:ℝ)
        ≤ ∑ j ∈ Finset.Icc 0 M, (1:ℝ)/(j:ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro j hj; simp only [Finset.mem_range] at hj; simp only [Finset.mem_Icc]; omega
          · intro j hj hnj; positivity
      _ = ∑ j ∈ Finset.Icc 1 M, (1:ℝ)/(j:ℝ) := by
          rw [← Finset.insert_Icc_succ_left_eq_Icc (show 0 ≤ M by omega)]
          rw [Finset.sum_insert (by simp [Finset.mem_Icc])]
          simp
      _ ≤ 1 + Real.log (M:ℝ) := Commons.Analysis.ExpLog.harmonic_le_one_add_log M hM1
  have hg_bound : (∑ b : ZMod M, min t ((M:ℝ)/(2*((min b.val (M-b.val):ℕ):ℝ))))
      ≤ (M:ℝ) * (1 + Real.log (M:ℝ)) := by
    calc (∑ b : ZMod M, min t ((M:ℝ)/(2*((min b.val (M-b.val):ℕ):ℝ))))
        ≤ ((M:ℝ)/2) * (∑ b : ZMod M, (1/(b.val:ℝ) + 1/(((-b).val:ℕ):ℝ))) := hg
      _ = ((M:ℝ)/2) * (2 * (∑ b : ZMod M, 1/(b.val:ℝ))) := by rw [hSS]
      _ = (M:ℝ) * (∑ b : ZMod M, 1/(b.val:ℝ)) := by ring
      _ ≤ (M:ℝ) * (1 + Real.log (M:ℝ)) := mul_le_mul_of_nonneg_left hS hm
  linarith [hg_bound]

theorem sum_minrep_weight_le (M : ℕ) [NeZero M] (H : ℕ) :
    (∑ b : ZMod M, (if b = 0 then (((2 * H + 1 : ℕ)) : ℝ)
        else min (((2 * H + 1 : ℕ)) : ℝ)
          ((M : ℝ) / (2 * ((min b.val (M - b.val) : ℕ) : ℝ)))))
      ≤ 5 * ((M : ℝ) + (((2 * H + 1 : ℕ)) : ℝ)) * (1 + Real.log M) := by
  have ht : (0:ℝ) ≤ ((2*H+1 : ℕ) : ℝ) := by positivity
  have hmain := sum_minrep_weight_bound M ((2*H+1:ℕ):ℝ) ht
  refine hmain.trans ?_
  have hm : (0:ℝ) ≤ (M:ℝ) := by positivity
  have hlog : 0 ≤ Real.log (M:ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne M)
  nlinarith [ht, hm, hlog, mul_nonneg hm hlog, mul_nonneg ht hlog]

end Commons.NumberTheory.ZMod