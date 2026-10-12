import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1S.conv3chi_dev_quadratic
import Submission.Work.BoseFixR.massDeficit_taylor
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.All.massDeficitFar` — the mass deficit with the *named* `χ⋆χ` constant

`Work.BoseFixR.massDeficit_taylor` (`Submission/Work/BoseFixR/massDeficit_taylor.lean`) proves the
sharp mass identity of the far leg with a *free* constant `S` in the hypothesis

    `hconv : ∀ x, ‖x‖ ≤ R → (1 − convScale ℓ x)/convScale ℓ x ≤ S·(‖x‖/ℓ)²`.

That is inconvenient for a consumer: the natural value of `S` is the one read off the *proved*
global quadratic deviation of `χ⋆χ`, `Work.BoseFixB1S.conv3chi_dev_quadratic`, namely `S = 2·C`
with `C` the chosen deviation constant.  `convScale_taylor` (`All/convScale_taylor.lean`) gives
the same row with an *existential* `S`; this module fixes the constant once and for all, so that
every consumer can cite `massDeficitFar` without re-deriving `hconv`.

The mathematical content is the same two-line sandwich: `χ⋆χ` is maximal at `0` with value `1`, so
`0 ≤ 1 − (χ⋆χ) ≤ C‖t‖²`, and `χ⋆χ ≥ 1/2` on `‖t‖ ≤ chiR0` (the proved `chiR0_half`), whence
`1/(χ⋆χ) ≤ 2` there; the restriction `R ≤ ℓ·chiR0` puts `t = ℓ⁻¹x` inside that ball.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixR.All

open _root_.BoseGases Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The quantitative `χ⋆χ` Taylor row for a *given* deviation constant `C`.**

If `|(χ⋆χ)(t) − 1| ≤ C‖t‖²` for all `t` (which the proved `conv3chi_dev_quadratic` supplies for
`C = Classical.choose conv3chi_dev_quadratic`), then on `ball 0 R ⊆ ball 0 (ℓ·chiR0)`

    `(1 − convScale ℓ x)/convScale ℓ x ≤ (2C)·(‖x‖/ℓ)²`.

This is the proof body of `convScale_taylor` with the constant kept explicit. -/
private lemma convScale_le_two_mul_dev {C : ℝ} (hC : 0 ≤ C)
    (hdev : ∀ t : E3,
      |Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi t - 1|
        ≤ C * ‖t‖ ^ 2)
    {R ℓ : ℝ} (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) :
    ∀ x : E3, ‖x‖ ≤ R →
      (1 - Submission.BoseGases.convScale ℓ x) / Submission.BoseGases.convScale ℓ x
        ≤ (2 * C) * (‖x‖ / ℓ) ^ 2 := by
  intro x hx
  -- `ℓ⁻¹ x` lies in the ball where `χ⋆χ ≥ 1/2`
  have hxn : ‖(ℓ⁻¹) • x‖ ≤ chiR0 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hℓ.le)]
    calc ℓ⁻¹ * ‖x‖ ≤ ℓ⁻¹ * R :=
          mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hℓ.le)
      _ ≤ chiR0 := by
          rw [inv_mul_le_iff₀ hℓ]
          simpa [mul_comm] using hRℓ
  have hhalf : (1 : ℝ) / 2 ≤ conv3 chi chi ((ℓ⁻¹) • x) := chiR0_half _ hxn
  have hdev' : |conv3 chi chi ((ℓ⁻¹) • x) - 1| ≤ C * ‖(ℓ⁻¹) • x‖ ^ 2 := hdev _
  have hnorm : ‖(ℓ⁻¹) • x‖ ^ 2 = (‖x‖ / ℓ) ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hℓ.le), div_eq_mul_inv]
    ring
  have hconvpos : 0 < conv3 chi chi ((ℓ⁻¹) • x) := lt_of_lt_of_le (by norm_num) hhalf
  have hkey : 1 - conv3 chi chi ((ℓ⁻¹) • x) ≤ C * (‖x‖ / ℓ) ^ 2 := by
    have := (abs_le.mp hdev').1
    rw [hnorm] at this
    linarith
  rw [Submission.BoseGases.convScale]
  by_cases hcase : 1 - conv3 chi chi ((ℓ⁻¹) • x) ≤ 0
  · have h2 : (1 - conv3 chi chi ((ℓ⁻¹) • x)) / conv3 chi chi ((ℓ⁻¹) • x) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hcase hconvpos.le
    have h3 : 0 ≤ 2 * C * (‖x‖ / ℓ) ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    linarith
  · push_neg at hcase
    have h2 : (1 - conv3 chi chi ((ℓ⁻¹) • x)) / conv3 chi chi ((ℓ⁻¹) • x)
        ≤ 2 * (1 - conv3 chi chi ((ℓ⁻¹) • x)) := by
      rw [div_le_iff₀ hconvpos]
      nlinarith [hcase, hhalf]
    calc (1 - conv3 chi chi ((ℓ⁻¹) • x)) / conv3 chi chi ((ℓ⁻¹) • x)
        ≤ 2 * (1 - conv3 chi chi ((ℓ⁻¹) • x)) := h2
      _ ≤ 2 * (C * (‖x‖ / ℓ) ^ 2) := by linarith
      _ = 2 * C * (‖x‖ / ℓ) ^ 2 := by ring

theorem massDeficitFar {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : BoseGases.IsRadial v) {R ℓ : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (hW : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h ℓ)) :
    ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : EuclideanSpace ℝ (Fin 3),
        (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q) ^ 2 / (2 * ‖q‖ ^ 2)
      ≤ (1 + (2 * Classical.choose Work.BoseFixB1S.conv3chi_dev_quadratic) * (R / ℓ) ^ 2)
        * ∫ x : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1omegaFun v h ℓ x := by
  have hspec := Classical.choose_spec Work.BoseFixB1S.conv3chi_dev_quadratic
  exact Work.BoseFixR.massDeficit_taylor h hv hvrad hR hℓ hv_supp hRℓ
    (by linarith [hspec.1])
    (convScale_le_two_mul_dev hspec.1 hspec.2 hℓ hRℓ) hW

end Work.BoseFixR.All
