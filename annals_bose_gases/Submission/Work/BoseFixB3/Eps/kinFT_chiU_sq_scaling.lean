import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixB3.Eps.Defs
import Submission.Work.BoseFixB3.Scaling.kinFT_scaled_phi
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Eps.kinFT_chiU_sq_scaling` — the scaling of `kinFT` on the localisation window

The window `χ_Λ` of the box `Λ = acube ℓ` is the `ℓ`-scaling of the fixed bump
`χ`: `chiU ℓ 0 y = χ(ℓ⁻¹ • y)` (`Submission.BoseGases.chiU`).  Hence the
complexified square window `(χ_Λ)²` is the `ℓ`-scaling of `bumpSq`, and the
`p`-convention Fourier transform `kinFT` (FS's `𝓕`) scales as

`kinFT ((χ_Λ)²) p = ℓ³ · kinFT (bumpSqC) (ℓ • p)`

— the Haar measure of `ℝ³` picks up the factor `ℓ³ = ℓ^{finrank ℝ ℝ³}` and the
oscillatory factor `e^{-i⟪p,z⟫}` becomes `e^{-i⟪ℓp,ℓ⁻¹z⟫}`.

This is `Work.BoseFixB3.Scaling.kinFT_scaled_phi` (`φ = χ² = bumpSq`) together
with the identification `chiU ℓ 0 · = φ(ℓ⁻¹ • ·)` and `(ℓ³ : ℝ) • c = (ℓ : ℂ)³ * c`.
-/

namespace Work.BoseFixB3.Eps

open Submission.BoseGases Work.BoseFixB3.Scaling

/-- The window `χ_Λ` at scale `ℓ` is the fixed bump scaled by `ℓ⁻¹`:
`chiU ℓ 0 y = χ(ℓ⁻¹ • y)`. -/
lemma chiU_zero_eq (ℓ : ℝ) (y : EuclideanSpace ℝ (Fin 3)) :
    chiU ℓ 0 y = chi (ℓ⁻¹ • y) := by
  simp [Submission.BoseGases.chiU]

/-- The complexified square window is the `ℓ`-scaling of `bumpSqC`. -/
lemma chiU_sq_eq_scaling (ℓ : ℝ) :
    (fun y : EuclideanSpace ℝ (Fin 3) => (((chiU ℓ 0 y) ^ 2 : ℝ) : ℂ))
      = fun z => (phi (ℓ⁻¹ • z) : ℂ) := by
  funext z
  simp [chiU_zero_eq, Work.BoseFixB3.Scaling.phi]

theorem kinFT_chiU_sq_scaling (ℓ : ℝ) (hℓ : 0 < ℓ) (p : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.kinFT
        (fun y => (((Submission.BoseGases.chiU ℓ 0 y) ^ 2 : ℝ) : ℂ)) p
      = (ℓ : ℂ) ^ 3 *
        Submission.BoseGases.kinFT Work.BoseFixB3.Eps.bumpSqC (ℓ • p) := by
  have hC : Work.BoseFixB3.Eps.bumpSqC = Work.BoseFixB3.Scaling.phiC := rfl
  rw [chiU_sq_eq_scaling ℓ, Work.BoseFixB3.Scaling.kinFT_scaled_phi ℓ hℓ p, hC]
  -- `(ℓ ^ 3 : ℝ) • c = (ℓ : ℂ) ^ 3 * c`
  rw [← Complex.ofReal_pow, Algebra.smul_def]
  simp

end Work.BoseFixB3.Eps
