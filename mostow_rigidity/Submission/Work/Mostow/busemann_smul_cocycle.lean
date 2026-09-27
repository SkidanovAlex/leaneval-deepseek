import Mathlib
import Submission.Work.Mostow.busemannCocycle

/-!
# The Busemann cocycle in the form used by the geometrically finite argument

`busemann_smul_cocycle` is the cocycle identity for the Busemann function normalised at `0`,
written with `γ⁻¹` acting on the boundary point:

  `β_ζ (γ • z) = β_{bd γ⁻¹ ζ} z + β_ζ (γ • 0)`.

It is the cocycle identity `busemannCocycle` (proved in `busemannCocycle.lean`) applied with
`g = γ` and `ξ = bd γ⁻¹ ζ`, using `bd γ (bd γ⁻¹ ζ) = ζ` and `γ⁻¹ • (γ • z) = z`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

theorem busemann_smul_cocycle (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (γ : LeanEval.Geometry.MostowRigidity.PO n 1) (ζ z : Submission.Mostow.E n)
    (hζ : ζ ∈ Submission.Mostow.Sph n) :
    Submission.Mostow.busemann ζ (γ • z) = Submission.Mostow.busemann (Submission.Mostow.bd γ⁻¹ ζ) z
      + Submission.Mostow.busemann ζ (γ • 0) := by
  -- `bd γ⁻¹ ζ` is again on the sphere
  have hbdmem : bd γ⁻¹ ζ ∈ Sph n := hA.2.2.2.2.2.2.2.1 γ⁻¹ ζ hζ
  -- `bd γ (bd γ⁻¹ ζ) = ζ`
  have hcomp : bd γ (bd γ⁻¹ ζ) = ζ := by
    have h1 : bd (γ * γ⁻¹) ζ = bd γ (bd γ⁻¹ ζ) :=
      hA.2.2.2.2.2.2.2.2.2.1 γ γ⁻¹ ζ hζ
    have h2 : bd (γ * γ⁻¹) ζ = ζ := by
      rw [mul_inv_cancel γ]
      exact hA.2.2.2.2.2.2.2.2.1 ζ hζ
    rw [h2] at h1
    exact h1.symm
  -- action laws
  have hact1 : γ⁻¹ • (γ • z) = z := by
    rw [← hA.2.2.2.2.1 γ⁻¹ γ z, inv_mul_cancel γ, hA.2.2.2.1 z]
  have hact2 : γ • (γ⁻¹ • (γ • z)) = γ • z := by
    rw [← hA.2.2.2.2.1 γ γ⁻¹ (γ • z), mul_inv_cancel γ, hA.2.2.2.1 (γ • z)]
  have h := busemannCocycle n hA γ (bd γ⁻¹ ζ) (γ⁻¹ • (γ • z)) hbdmem
  rw [hact2, hact1, hcomp] at h
  exact h

end Work.Mostow
