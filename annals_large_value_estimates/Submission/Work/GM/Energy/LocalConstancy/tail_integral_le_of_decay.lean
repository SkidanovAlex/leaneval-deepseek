import Mathlib

namespace Work.GM.Energy.LocalConstancy

open MeasureTheory Set

set_option linter.unusedVariables false

/-!
# Tail integral of a function with power decay

For `g : ℝ → ℂ` satisfying `‖g ξ‖ ≤ C / |ξ|^j` for `ξ ≠ 0`, `j ≥ 2`, `K ≥ 1`:

  `∫_{|ξ| > K} ‖g ξ‖ dξ ≤ (2 C / (j - 1)) K ^ (1 - j)`.

The proof splits the domain into the two half lines `(K, ∞)` and `(-∞, -K)`, computes
`∫_K^∞ C x ^ (-j) dx = C K ^ (1-j) / (j-1)` on each, and uses that the comparison function
`x ↦ C / |x|^j` is integrable there.
-/

/-- Value of the tail integral `∫_{x > K} C / |x|^j`. -/
private lemma integral_Ioi_div_abs_pow (C : ℝ) {K : ℝ} {j : ℕ} (hK : 0 < K)
    (hj : 1 < (j : ℝ)) :
    ∫ x in Ioi K, C / |x| ^ j = C * (K ^ (1 - (j : ℝ)) / ((j : ℝ) - 1)) := by
  have hcongr : ∫ x in Ioi K, C / |x| ^ j = ∫ x in Ioi K, C * x ^ (-(j : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    rw [Set.mem_Ioi] at hx
    have hxpos : 0 < x := hK.trans hx
    rw [abs_of_pos hxpos, Real.rpow_neg (le_of_lt hxpos), Real.rpow_natCast, div_eq_mul_inv]
  rw [hcongr, integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hK]
  have hkey : -K ^ (-(j : ℝ) + 1) / (-(j : ℝ) + 1)
      = K ^ (1 - (j : ℝ)) / ((j : ℝ) - 1) := by
    have e1 : -(j : ℝ) + 1 = 1 - (j : ℝ) := by ring
    rw [e1]
    rw [div_eq_div_iff (by linarith : (1 : ℝ) - (j : ℝ) ≠ 0) (by linarith : (j : ℝ) - 1 ≠ 0)]
    ring
  rw [hkey]

/-- Value of the tail integral `∫_{x < -K} C / |x|^j`, by symmetry `x ↦ -x`. -/
private lemma integral_Iio_neg_div_abs_pow (C K : ℝ) {j : ℕ}
    (hIoi : ∫ x in Ioi K, C / |x| ^ j = C * (K ^ (1 - (j : ℝ)) / ((j : ℝ) - 1))) :
    ∫ x in Iio (-K), C / |x| ^ j = C * (K ^ (1 - (j : ℝ)) / ((j : ℝ) - 1)) := by
  have hae : Iio (-K) =ᵐ[volume] Iic (-K) := by
    rw [ae_eq_set]
    constructor
    · rw [show Iio (-K) \ Iic (-K) = ∅ by ext x; simp]
      exact measure_empty
    · have hset : Iic (-K) \ Iio (-K) = {-K} := by
        ext x
        simp only [Set.mem_sdiff, Set.mem_Iic, Set.mem_Iio, Set.mem_singleton_iff]
        constructor
        · rintro ⟨h1, h2⟩; exact le_antisymm h1 (not_lt.mp h2)
        · rintro rfl; exact ⟨le_refl _, lt_irrefl _⟩
      rw [hset, measure_singleton]
  rw [setIntegral_congr_set hae]
  rw [setIntegral_congr_fun (f := fun x : ℝ => C / |x| ^ j)
        (g := fun x : ℝ => (fun y : ℝ => C / |y| ^ j) (-x)) measurableSet_Iic
        (fun x _ => by simp)]
  rw [integral_comp_neg_Iic (-K) (fun y : ℝ => C / |y| ^ j), neg_neg]
  exact hIoi

/-- Integrability of `x ↦ C / |x|^j` on `(K, ∞)`. -/
private lemma integrableOn_Ioi_div_abs_pow (C : ℝ) {K : ℝ} {j : ℕ} (hK : 0 < K)
    (hj : 1 < (j : ℝ)) : IntegrableOn (fun x : ℝ => C / |x| ^ j) (Ioi K) := by
  have h1 : IntegrableOn (fun x : ℝ => C * x ^ (-(j : ℝ))) (Ioi K) :=
    (integrableOn_Ioi_rpow_of_lt (a := -(j : ℝ)) (by linarith) hK).const_mul C
  refine h1.congr_fun (fun x hx => ?_) measurableSet_Ioi
  simp only [Set.mem_Ioi] at hx
  have hxpos : 0 < x := hK.trans hx
  change C * x ^ (-(j : ℝ)) = C / |x| ^ j
  rw [abs_of_pos hxpos, Real.rpow_neg (le_of_lt hxpos), Real.rpow_natCast, div_eq_mul_inv]

/-- Integrability of `x ↦ C / |x|^j` on `(-∞, -K)`, by the substitution `x ↦ -x`. -/
private lemma integrableOn_Iio_neg_div_abs_pow (C K : ℝ) {j : ℕ}
    (hIoi : IntegrableOn (fun x : ℝ => C / |x| ^ j) (Ioi K)) :
    IntegrableOn (fun x : ℝ => C / |x| ^ j) (Iio (-K)) := by
  let A : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
  rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
  rw [A.integrableOn_map_iff]
  simp only [Function.comp_def]
  rw [show (fun x : ℝ => C / |(-x)| ^ j) = (fun x : ℝ => C / |x| ^ j) by
        funext x; rw [abs_neg]]
  rw [show ((fun x : ℝ => -x) ⁻¹' Iio (-K)) = Ioi K by
        ext x; simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_Ioi, neg_lt_neg_iff]]
  exact hIoi

theorem tail_integral_le_of_decay {g : ℝ → ℂ} {C K : ℝ} {j : ℕ}
    (hC : 0 ≤ C) (hj : 2 ≤ j) (hK : 1 ≤ K)
    (hg : ∀ ξ : ℝ, ξ ≠ 0 → ‖g ξ‖ ≤ C / |ξ| ^ j) :
    ∫ ξ in {ξ : ℝ | K < |ξ|}, ‖g ξ‖ ≤ (2 * C / ((j : ℝ) - 1)) * K ^ (1 - (j : ℝ)) := by
  have hKpos : 0 < K := by linarith
  have hj1 : (1 : ℝ) < (j : ℝ) := by
    have : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    linarith
  have hD : (j : ℝ) - 1 ≠ 0 := by linarith
  -- the domain is the union of the two half lines
  have hset : {ξ : ℝ | K < |ξ|} = Ioi K ∪ Iio (-K) := by
    ext x
    have hiff : K < -x ↔ x < -K := by constructor <;> intro h <;> linarith
    show K < |x| ↔ (K < x ∨ x < -K)
    rw [lt_abs, hiff]
  have hdisj : Disjoint (Ioi K) (Iio (-K)) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    simp only [Set.mem_Ioi] at hx1
    simp only [Set.mem_Iio] at hx2
    linarith
  -- integrability of the comparison function
  have hintIoi : IntegrableOn (fun ξ : ℝ => C / |ξ| ^ j) (Ioi K) :=
    integrableOn_Ioi_div_abs_pow C hKpos hj1
  have hintIio : IntegrableOn (fun ξ : ℝ => C / |ξ| ^ j) (Iio (-K)) :=
    integrableOn_Iio_neg_div_abs_pow C K hintIoi
  have hint : IntegrableOn (fun ξ : ℝ => C / |ξ| ^ j) {ξ : ℝ | K < |ξ|} := by
    rw [hset]
    exact hintIoi.union hintIio
  -- comparison of `‖g‖` with the comparison function
  have hmono : ∫ ξ in {ξ : ℝ | K < |ξ|}, ‖g ξ‖ ≤ ∫ ξ in {ξ : ℝ | K < |ξ|}, C / |ξ| ^ j := by
    refine integral_mono_of_nonneg (μ := volume.restrict {ξ : ℝ | K < |ξ|}) ?_ hint ?_
    · exact Filter.Eventually.of_forall (fun x => norm_nonneg _)
    · filter_upwards [MeasureTheory.ae_restrict_mem
        (measurableSet_lt measurable_const continuous_abs.measurable)] with x hx
      exact hg x (abs_pos.mp (lt_trans (lt_of_lt_of_le zero_lt_one hK) hx))
  -- the value of the integral of the comparison function
  have hv1 : ∫ x in Ioi K, C / |x| ^ j = C * (K ^ (1 - (j : ℝ)) / ((j : ℝ) - 1)) :=
    integral_Ioi_div_abs_pow C hKpos hj1
  have hv2 : ∫ x in Iio (-K), C / |x| ^ j = C * (K ^ (1 - (j : ℝ)) / ((j : ℝ) - 1)) :=
    integral_Iio_neg_div_abs_pow C K hv1
  have hval : ∫ ξ in {ξ : ℝ | K < |ξ|}, C / |ξ| ^ j
      = (2 * C / ((j : ℝ) - 1)) * K ^ (1 - (j : ℝ)) := by
    rw [hset, setIntegral_union hdisj measurableSet_Iio hintIoi hintIio, hv1, hv2]
    field_simp
    ring
  rw [hval] at hmono
  exact hmono

end Work.GM.Energy.LocalConstancy
