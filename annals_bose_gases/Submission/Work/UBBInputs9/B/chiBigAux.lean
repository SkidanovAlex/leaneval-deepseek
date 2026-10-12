import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.UBBInputs9.B.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs9.B.chiBigAux` — the two calculus inputs of the big-box Dirichlet identity

The big-box window of FS's `lem:LocKinEn` is `chiBig ℓ u x = chiScale ℓ (x − ℓ • u)`
(`Work.UBBInputs9.chiBig`), i.e. on the one-particle space `X 1` the window applied to a state is

    `y ↦ chiBig ℓ u (y 0) * Φ y = (fun y => chiScale ℓ (y 0 − ℓ•u)) y * Φ y`.

This module provides the two ingredients that the pointwise `u`-integral identity
(`B/integral_fderiv_chiBigPhi_sq_eq`) and the joint integrability of the big-box Dirichlet
integrand (`B/integrable_fderiv_chiBigPhi_sq`) both use:

* `fderiv_chiBigPhi_eq` — the Leibniz (product) formula for the derivative of the big-box
  windowed state in the kinetic direction `kcDir 1 0 k`.  Both `u`-dependent factors are the
  *same* single scaled bump `chiScale ℓ` evaluated at the sliding point `x 0 − ℓ•u` (unlike the
  sliding small-box window `chiB`, which is a product `χ(x/ℓ)·χ(x/(ℓd) − u)`).
* `integral_fderiv_chiScale_sq` — the dilation rule for the `L²`-norm of the gradient of the
  scaled bump: `∫_z (∂_e chiScale ℓ z)² = ℓ · ∫_z (∂_e χ z)²`.  This is what converts the
  small-`u`-window constant `∫_z (∂_k χ)²/ℓ²` into the big-box constant
  `(∫_z (∂_k chiScale ℓ)²)/ℓ³` appearing in `B/integral_dirichlet_chiBig_eq`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.UBBInputs9.B

open Submission.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "X1" => Submission.BoseGases.X 1

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **The Leibniz formula for the big-box window.**  With `chiBig ℓ u (y 0) = chiScale ℓ (y 0 − ℓ•u)`
the derivative of the windowed state along the kinetic direction `kcDir 1 0 k` is

    ∂_k (chiBig ℓ u (· 0)·Φ)(x)
      = Φ(x) · (∂_k chiScale ℓ)(x 0 − ℓ•u) + chiScale ℓ (x 0 − ℓ•u) · ∂_k Φ(x).

Both sliding factors are the *same* bump `chiScale ℓ`, and they are the only `u`-dependent
quantities. -/
lemma fderiv_chiBigPhi_eq {ℓ : ℝ} {Φ : X1 → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (u : ℝ³) (x : X1) (k : Fin 3) :
    fderiv ℝ (fun y : X1 => chiBig ℓ u (y 0) * Φ y) x (kcDir 1 0 k)
      = Φ x * fderiv ℝ (chiScale ℓ) (x 0 - ℓ • u) (kcStdBasis k)
        + chiScale ℓ (x 0 - ℓ • u) * fderiv ℝ Φ x (kcDir 1 0 k) := by
  have hchi : Differentiable ℝ (chiScale ℓ) :=
    (ChiDeriv.chiScale_contDiff_any ℓ).differentiable (by norm_num)
  have hAdiff : DifferentiableAt ℝ (fun y : X1 => chiScale ℓ (y 0 - ℓ • u)) x :=
    hchi.differentiableAt.comp x ((differentiableAt_projX1 x).sub_const _)
  have hΦdiff : DifferentiableAt ℝ Φ x := hΦ.differentiable (by norm_num) x
  have hfun : (fun y : X1 => chiBig ℓ u (y 0) * Φ y)
      = (fun y : X1 => chiScale ℓ (y 0 - ℓ • u)) * Φ := by
    funext y; rfl
  rw [hfun, fderiv_mul hAdiff hΦdiff, add_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul,
    fderiv_liftX_sub_const_apply (chiScale ℓ) (ℓ • u) x hchi.differentiableAt k]
  ring

/-- **The dilation rule for the gradient's `L²`-norm.**  For `0 < ℓ` and any direction `e`,

    `∫_z (∂_e chiScale ℓ)(z)² dz = ℓ · ∫_z (∂_e χ)(z)² dz`.

`chiScale ℓ = χ(ℓ⁻¹ • ·)`, so the chain rule gives a factor `ℓ⁻¹` on the gradient and the
substitution `z = ℓ • s` gives a factor `ℓ³` on the measure: `ℓ³·ℓ⁻² = ℓ`. -/
lemma integral_fderiv_chiScale_sq (ℓ : ℝ) (hℓ : 0 < ℓ) (e : ℝ³) :
    (∫ z : ℝ³, (fderiv ℝ (chiScale ℓ) z e) ^ 2)
      = ℓ * (∫ z : ℝ³, (fderiv ℝ chi z e) ^ 2) := by
  have hne : ℓ ≠ 0 := ne_of_gt hℓ
  have hstep : (∫ z : ℝ³, (fderiv ℝ (chiScale ℓ) z e) ^ 2)
      = ℓ ^ 3 * (∫ s : ℝ³, (fderiv ℝ (chiScale ℓ) (ℓ • s) e) ^ 2) :=
    integral_comp_smul_right (g := fun z : ℝ³ => (fderiv ℝ (chiScale ℓ) z e) ^ 2) hℓ
  have hpt : ∀ s : ℝ³, (fderiv ℝ (chiScale ℓ) (ℓ • s) e) ^ 2
      = (ℓ⁻¹) ^ 2 * (fderiv ℝ chi s e) ^ 2 := by
    intro s
    rw [ChiDeriv.fderiv_chiScale_apply ℓ (ℓ • s) e]
    have harg : ℓ⁻¹ • (ℓ • s) = s := by rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [harg]
    ring
  rw [hstep, integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul]
  field_simp

end Work.UBBInputs9.B
