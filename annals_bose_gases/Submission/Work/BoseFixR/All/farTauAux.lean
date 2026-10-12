import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/All/farTauAux.lean` — pointwise lower bounds for the honest `τ`

Auxiliary lemmas for `Submission/Work/BoseFixR/All/farTauRow.lean` (the `τ'`-weighted sharp
lattice row of the `All`-vocabulary far leg).

Everything here is about the *smoothed kinetic symbol*
`tauSm eT s d ℓ k = (1−eT)·c₁²·tauProf (‖k‖/c₁) + eT·c₂²·tauProf (‖k‖/c₂)`,
`c₁ = (2sℓ)⁻¹`, `c₂ = (2dsℓ)⁻¹`, and its *lower* bound by the shifted kinks
`(max 0 (‖k‖ − 2c))²`, which is what the pointwise comparison of `τ` with `‖k‖²` needs
(`tauProf` satisfies (P6): `(max 0 (r−2))² ≤ tauProf r`).
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixR.All

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox
open Work.BoseBoxFix Work.BoseBoxFock Work.BoseB7 Work.BoseB7A

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **(P6) of the chosen kinetic profile**: `(max 0 (r − 2))² ≤ tauProf r`. -/
lemma tauProf_ge_max_two_sq (r : ℝ) : (max 0 (r - 2)) ^ 2 ≤ tauProf r :=
  tauProf_spec.2.2.1 r

/-- **The rescaled kink**: for `c > 0`, `(max 0 (‖k‖ − 2c))² ≤ c²·tauProf (‖k‖/c)`. -/
lemma max_kink_le_smul_tauProf {c : ℝ} (hc : 0 < c) (k : E3) :
    (max 0 (‖k‖ - 2 * c)) ^ 2 ≤ c ^ 2 * tauProf (‖k‖ / c) := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have h := tauProf_ge_max_two_sq (‖k‖ / c)
  have e : (max 0 (‖k‖ - 2 * c)) ^ 2 = c ^ 2 * (max 0 (‖k‖ / c - 2)) ^ 2 := by
    have hdiv : (max 0 (‖k‖ - 2 * c)) / c = max 0 ((‖k‖ - 2 * c) / c) := by
      by_cases h : 0 ≤ ‖k‖ - 2 * c
      · rw [max_eq_right h, max_eq_right (div_nonneg h (le_of_lt hc))]
      · push_neg at h
        rw [max_eq_left (le_of_lt h),
          max_eq_left (le_of_lt (div_neg_of_neg_of_pos h hc))]
        simp
    have h1 : max 0 (‖k‖ / c - 2) = (max 0 (‖k‖ - 2 * c)) / c := by
      have h2 : ‖k‖ / c - 2 = (‖k‖ - 2 * c) / c := by field_simp
      rw [h2, hdiv]
    rw [h1]
    field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left h (sq_nonneg c)

/-- **The pointwise lower bound for the smoothed symbol**: for `0 < s`, `0 < d`, `0 < ℓ`,

  `tauSm eT s d ℓ k ≥ (1−eT)·(max 0 (‖k‖ − 2c₁))² + eT·(max 0 (‖k‖ − 2c₂))²`,
  `c₁ = (2sℓ)⁻¹`, `c₂ = (2dsℓ)⁻¹`. -/
lemma tauSm_ge_shifted {eT s d ℓ : ℝ} (hs : 0 < s) (hd : 0 < d) (hℓ : 0 < ℓ)
    (heT0 : 0 ≤ eT) (heT1 : eT ≤ 1) (k : E3) :
    (1 - eT) * (max 0 (‖k‖ - 2 * (2 * s * ℓ)⁻¹)) ^ 2
        + eT * (max 0 (‖k‖ - 2 * (2 * d * s * ℓ)⁻¹)) ^ 2
      ≤ tauSm eT s d ℓ k := by
  have hc1 : 0 < (2 * s * ℓ)⁻¹ := by positivity
  have hc2 : 0 < (2 * d * s * ℓ)⁻¹ := by positivity
  have h1 := max_kink_le_smul_tauProf hc1 k
  have h2 := max_kink_le_smul_tauProf hc2 k
  simp only [tauSm]
  refine add_le_add ?_ ?_
  · calc (1 - eT) * (max 0 (‖k‖ - 2 * (2 * s * ℓ)⁻¹)) ^ 2
        ≤ (1 - eT) * ((2 * s * ℓ)⁻¹ ^ 2 * tauProf (‖k‖ / (2 * s * ℓ)⁻¹)) :=
          mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = (1 - eT) * (2 * s * ℓ)⁻¹ ^ 2 * tauProf (‖k‖ / (2 * s * ℓ)⁻¹) := by ring
  · calc eT * (max 0 (‖k‖ - 2 * (2 * d * s * ℓ)⁻¹)) ^ 2
        ≤ eT * ((2 * d * s * ℓ)⁻¹ ^ 2 * tauProf (‖k‖ / (2 * d * s * ℓ)⁻¹)) :=
          mul_le_mul_of_nonneg_left h2 heT0
      _ = eT * (2 * d * s * ℓ)⁻¹ ^ 2 * tauProf (‖k‖ / (2 * d * s * ℓ)⁻¹) := by ring

end Work.BoseFixR.All
