import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.BoseBoxFock.PCFU.ChWordChains
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.lowKer_abs_integral_le`

**The `L¹`-norm of the low-momentum kernel is bounded uniformly in the cut-off `κ`.**

    ∃ C ≥ 0, ∀ κ > 0, ∫_z |lowKer fc κ z| dz ≤ C .

## Why it is true (and why it is not just `lowKer_decay`)

`lowKer fc κ z = (2π)^{-3}∫_p f(‖p‖/κ)·cos⟪p,z⟫ dp` is the inverse Fourier transform of the
symbol `p ↦ f(‖p‖/κ)`.  The decay bounds already on disk (`lowKer_decay`) are *not* uniform in `κ`:
there the constant carries the `L¹`-norms of the derivatives of `f(‖·‖/κ)`, which grow like `κ³`.

The uniform statement is true because `lowKer fc κ` is the **`κ`-dilate** of `lowKer fc 1`:

    lowKer fc κ z = κ³ · lowKer fc 1 (κ • z)        (κ > 0),

and the substitution `y = κ z` in `∫ |κ³ h(κ z)| dz` is exactly measure-preserving on `ℝ³`,
so the `L¹`-norm is *independent* of `κ`:

    ∫_z |lowKer fc κ z| dz = ∫_y |lowKer fc 1 y| dy .

Both steps are unconditional identities of the Bochner integral (`Measure.integral_comp_smul` is
valid even for non-integrable functions), so the witnessing constant is
`C = ∫_y |lowKer fc 1 y|` — no integrability input is needed, only `C ≥ 0` (`integral_nonneg`).

The scaling identity (`lowKer_smul_scale`, `private` here) is the same computation as the one used
by the tied-cutoff chapter (`PCFU/chiScale_lowKer_image_le.lean`, where it is private as well).
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

namespace Work.BoseBoxFock.PCFU

/-- **The exact scaling of the low-momentum kernel**: `Κ_κ(z) = κ³·Κ₁(κz)`
(the symbol `f(‖p‖/κ)` is the `κ`-dilate of `f(‖p‖)`). -/
private lemma lowKer_smul_scale (fc : Work.BoseBoxFix.LowCut) {κ : ℝ} (hκ : 0 < κ) (z : E3) :
    lowKer fc κ z = κ ^ 3 * lowKer fc 1 (κ • z) := by
  have hG : ∀ q : E3, fc.f (‖κ • q‖ / κ) * Real.cos (inner ℝ (κ • q) z)
      = fc.f (‖q‖ / 1) * Real.cos (inner ℝ q (κ • z)) := by
    intro q
    have h1 : ‖κ • q‖ / κ = ‖q‖ / 1 := by
      rw [norm_smul, Real.norm_of_nonneg hκ.le, div_one]
      field_simp
    have h2 : inner ℝ (κ • q) z = inner ℝ q (κ • z) := by
      rw [real_inner_smul_left, real_inner_smul_right]
    rw [h1, h2]
  have hsub := Measure.integral_comp_smul_of_nonneg (μ := (volume : Measure E3))
    (f := fun p : E3 => fc.f (‖p‖ / κ) * Real.cos (inner ℝ p z)) κ (hR := hκ.le)
  have hfin : Module.finrank ℝ E3 = 3 := by simp [EuclideanSpace]
  rw [hfin] at hsub
  rw [lowKer_apply, lowKer_apply]
  have hkey : (∫ p : E3, fc.f (‖p‖ / κ) * Real.cos (inner ℝ p z))
      = κ ^ 3 * ∫ q : E3, fc.f (‖κ • q‖ / κ) * Real.cos (inner ℝ (κ • q) z) := by
    rw [hsub, smul_eq_mul]
    have hne : κ ^ 3 ≠ 0 := pow_ne_zero _ (ne_of_gt hκ)
    field_simp
  rw [hkey, integral_congr_ae (Filter.Eventually.of_forall hG)]
  ring

/-- **The `L¹`-norm of `lowKer fc κ` is independent of `κ > 0`.** -/
theorem lowKer_abs_integral_eq (fc : Work.BoseBoxFix.LowCut) {κ : ℝ} (hκ : 0 < κ) :
    (∫ z : E3, |lowKer fc κ z|) = ∫ y : E3, |lowKer fc 1 y| := by
  have hpt : ∀ z : E3, |lowKer fc κ z| = κ ^ 3 * |lowKer fc 1 (κ • z)| := by
    intro z
    rw [lowKer_smul_scale fc hκ z, abs_mul, abs_of_nonneg (pow_nonneg hκ.le 3)]
  -- the substitution `y = κ z`: `∫ |h(κ z)| dz = (κ³)⁻¹ ∫ |h|`
  have hscale : (∫ z : E3, |lowKer fc 1 (κ • z)|)
      = (κ ^ 3)⁻¹ * ∫ y : E3, |lowKer fc 1 y| := by
    have hsub := Measure.integral_comp_smul (μ := (volume : Measure E3))
      (f := fun y : E3 => |lowKer fc 1 y|) κ
    have hfin : Module.finrank ℝ E3 = 3 := by simp [EuclideanSpace]
    rw [hfin, smul_eq_mul, abs_of_nonneg (by positivity)] at hsub
    exact hsub
  have hne : κ ^ 3 ≠ 0 := pow_ne_zero _ (ne_of_gt hκ)
  calc (∫ z : E3, |lowKer fc κ z|)
      = ∫ z : E3, κ ^ 3 * |lowKer fc 1 (κ • z)| := by
        exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = κ ^ 3 * ∫ z : E3, |lowKer fc 1 (κ • z)| := integral_const_mul _ _
    _ = κ ^ 3 * ((κ ^ 3)⁻¹ * ∫ y : E3, |lowKer fc 1 y|) := by rw [hscale]
    _ = ∫ y : E3, |lowKer fc 1 y| := by
        rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]

theorem lowKer_abs_integral_le (fc : Work.BoseBoxFix.LowCut) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {κ : ℝ}, 0 < κ →
      (∫ z : EuclideanSpace ℝ (Fin 3), |Work.BoseBoxFock.PCFU.lowKer fc κ z|) ≤ C := by
  refine ⟨∫ y : E3, |lowKer fc 1 y|, integral_nonneg (fun y => abs_nonneg _), ?_⟩
  intro κ hκ
  rw [lowKer_abs_integral_eq fc hκ]

end Work.BoseBoxFock.PCFU
