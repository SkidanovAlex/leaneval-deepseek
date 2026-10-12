import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.summable_one_add_norm_latVec_pow_inv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.summable_shift_latVec`

The *shifted* lattice series of a polynomially decaying function converges:

    `Σ_{d ∈ ℤ³} Φ (z + a • latVec d)  < ∞`

whenever `‖Φ q‖ ≤ C (1 + ‖q‖)^{-4}`, `a > 0` and `z ∈ ℝ³` is arbitrary.

This is the three-dimensional `L⁴`-type p-series statement: on the lattice `ℤ³` a decay
`(1 + ‖·‖)^{-4}` is summable because the number of lattice points at distance `≍ r` grows like
`r²`, while the weight decays like `r^{-4}`.

## Route

The whole content is the *pointwise* comparison of the shifted weight with the unshifted one
`(1 + ‖latVec d‖)^{-4}`, which satisfies the already proved summability
`Work.BoseBoxFock.summable_one_add_norm_latVec_pow_inv` (`N = 4`).

Writing `m = min 1 (a/2) > 0` and `R = 2‖z‖/a`:

* in the *far* region `R ≤ ‖latVec d‖` the reverse triangle inequality gives
  `‖z + a • latVec d‖ ≥ (a/2)‖latVec d‖`, whence (with the elementary identity
  `1 + (a/2)t ≥ m(1 + t)`, valid because `m ≤ 1` and `m ≤ a/2`)
  `1 + ‖z + a • latVec d‖ ≥ m (1 + ‖latVec d‖)`;
* in the *near* region `‖latVec d‖ < R` one crudely has
  `(1 + ‖z + a • latVec d‖)^{-4} ≤ 1` while `(1 + ‖latVec d‖)^{-4} ≥ (1 + R)^{-4}`.

In both cases

    `(1 + ‖z + a • latVec d‖)^{-4} ≤ K (1 + ‖latVec d‖)^{-4}`,

with the *constant* `K = max (m^{-4}) ((1 + R)^4)`; the transferred series is then summable.
-/

namespace Work.BoseBoxFock

open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The negative fourth power rewrites as the inverse of the fourth power, for every real `x`. -/
private lemma zpow_neg_four_eq_inv (x : ℝ) : x ^ (-(4 : ℤ)) = (x ^ 4)⁻¹ := by
  rw [zpow_neg]; norm_num

theorem summable_shift_latVec {Φ : EuclideanSpace ℝ (Fin 3) → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hΦ : ∀ q : EuclideanSpace ℝ (Fin 3), ‖Φ q‖ ≤ C * (1 + ‖q‖) ^ (-(4 : ℤ)))
    {a : ℝ} (ha : 0 < a) (z : EuclideanSpace ℝ (Fin 3)) :
    Summable (fun d : Fin 3 → ℤ => Φ (z + a • Work.BoseBoxFock.latVec d)) := by
  classical
  -- the constant `m = min 1 (a/2)`, the threshold `R = 2‖z‖/a` and the comparison constant `K`
  set m : ℝ := min 1 (a / 2) with hm
  have hmpos : 0 < m := by rw [hm]; exact lt_min one_pos (by linarith)
  have hmle1 : m ≤ 1 := by rw [hm]; exact min_le_left _ _
  have hmlea : m ≤ a / 2 := by rw [hm]; exact min_le_right _ _
  set R : ℝ := 2 * ‖z‖ / a with hR
  have hRnn : 0 ≤ R := by rw [hR]; positivity
  set K : ℝ := max ((m ^ 4)⁻¹) ((1 + R) ^ 4) with hK
  have hKleft : (m ^ 4)⁻¹ ≤ K := le_max_left _ _
  have hKright : (1 + R) ^ 4 ≤ K := le_max_right _ _
  -- the unshifted lattice weight is summable
  have hsum : Summable (fun d : Fin 3 → ℤ => ((1 + ‖latVec d‖) ^ 4)⁻¹) :=
    summable_one_add_norm_latVec_pow_inv (N := 4) le_rfl
  refine Summable.of_norm_bounded
    (g := fun d : Fin 3 → ℤ => C * K * ((1 + ‖latVec d‖) ^ 4)⁻¹)
    (hsum.mul_left (C * K)) (fun d => ?_)
  -- the pointwise comparison of the shifted and unshifted weights
  have hweight : (1 + ‖z + a • latVec d‖) ^ (-(4 : ℤ)) ≤ K * ((1 + ‖latVec d‖) ^ 4)⁻¹ := by
    rw [zpow_neg_four_eq_inv]
    have hu4pos : (0 : ℝ) < (1 + ‖latVec d‖) ^ 4 := by positivity
    have hvpos : (0 : ℝ) < 1 + ‖z + a • latVec d‖ := by positivity
    have hu1 : (0 : ℝ) ≤ 1 + ‖latVec d‖ := by positivity
    have hv1 : (1 : ℝ) ≤ 1 + ‖z + a • latVec d‖ := by
      have := norm_nonneg (z + a • latVec d); linarith
    rcases le_or_gt R ‖latVec d‖ with hcase | hcase
    · -- far region: `‖z + a • latVec d‖ ≥ (a/2)‖latVec d‖`
      have hz2 : ‖z‖ ≤ a * ‖latVec d‖ / 2 := by
        rw [hR] at hcase
        rw [div_le_iff₀ ha] at hcase
        linarith
      have htri : a * ‖latVec d‖ - ‖z‖ ≤ ‖z + a • latVec d‖ := by
        have h := norm_sub_norm_le (a • latVec d) (-z)
        rw [norm_neg] at h
        have heq : a • latVec d - (-z) = z + a • latVec d := by rw [sub_neg_eq_add, add_comm]
        rwa [heq, norm_smul, Real.norm_of_nonneg ha.le] at h
      have hvge : (a / 2) * ‖latVec d‖ ≤ ‖z + a • latVec d‖ := by linarith
      have hmu : m * (1 + ‖latVec d‖) ≤ 1 + ‖z + a • latVec d‖ := by
        have h1 : m * (1 + ‖latVec d‖) ≤ 1 + (a / 2) * ‖latVec d‖ := by
          nlinarith [hmle1, hmlea, norm_nonneg (latVec d)]
        linarith
      have hmupos : 0 < m * (1 + ‖latVec d‖) := by positivity
      have h1 : ((1 + ‖z + a • latVec d‖) ^ 4)⁻¹ ≤ ((m * (1 + ‖latVec d‖)) ^ 4)⁻¹ :=
        (inv_le_inv₀ (pow_pos hvpos 4) (pow_pos hmupos 4)).mpr
          (pow_le_pow_left₀ hmupos.le hmu 4)
      calc ((1 + ‖z + a • latVec d‖) ^ 4)⁻¹
          ≤ ((m * (1 + ‖latVec d‖)) ^ 4)⁻¹ := h1
        _ = (m ^ 4)⁻¹ * ((1 + ‖latVec d‖) ^ 4)⁻¹ := by rw [mul_pow, mul_inv]
        _ ≤ K * ((1 + ‖latVec d‖) ^ 4)⁻¹ :=
            mul_le_mul_of_nonneg_right hKleft (inv_nonneg.mpr hu4pos.le)
    · -- near region: the shifted weight is bounded by `1`
      have hR1 : (0 : ℝ) < 1 + R := by linarith
      have huR : 1 + ‖latVec d‖ ≤ 1 + R := by linarith
      have hvle1 : ((1 + ‖z + a • latVec d‖) ^ 4)⁻¹ ≤ 1 := by
        refine inv_le_one_of_one_le₀ ?_
        exact one_le_pow₀ hv1
      have h2 : (1 : ℝ) ≤ (1 + R) ^ 4 * ((1 + ‖latVec d‖) ^ 4)⁻¹ := by
        have hpow : (1 + ‖latVec d‖) ^ 4 ≤ (1 + R) ^ 4 := pow_le_pow_left₀ hu1 huR 4
        have hle := (inv_le_inv₀ (pow_pos hR1 4) hu4pos).mpr hpow
        have hmul := mul_le_mul_of_nonneg_left hle (pow_nonneg hR1.le 4)
        rwa [mul_inv_cancel₀ (pow_ne_zero 4 (by linarith : (1 : ℝ) + R ≠ 0))] at hmul
      calc ((1 + ‖z + a • latVec d‖) ^ 4)⁻¹ ≤ 1 := hvle1
        _ ≤ (1 + R) ^ 4 * ((1 + ‖latVec d‖) ^ 4)⁻¹ := h2
        _ ≤ K * ((1 + ‖latVec d‖) ^ 4)⁻¹ :=
            mul_le_mul_of_nonneg_right hKright (inv_nonneg.mpr hu4pos.le)
  -- assemble: the decay hypothesis, the weight comparison, and the summation of the majorant
  calc ‖Φ (z + a • latVec d)‖
      ≤ C * (1 + ‖z + a • latVec d‖) ^ (-(4 : ℤ)) := hΦ _
    _ ≤ C * (K * ((1 + ‖latVec d‖) ^ 4)⁻¹) := mul_le_mul_of_nonneg_left hweight hC
    _ = C * K * ((1 + ‖latVec d‖) ^ 4)⁻¹ := by ring

end Work.BoseBoxFock
