import Submission.Work.PL.Subdiv
import Submission.Work.Cells.Connell.Defs

/-!
# `Work.Final.Forms`: two interface fields of `Work.Cells.Connell.Assumptions` that no other
area had packaged yet

`Work.Cells.Connell.Assumptions` asks for `CubeTriangulationForm` (`A2`/`G7`) and
`DomDimAffineForm` (`A2`/`G10`).  Both contents are delivered in `Submission/Work/PL/Subdiv`
(`exists_cube_triangulation`, `domDim_affine_image`), but not in the `Form` shape; this file does
the packaging so that `Work.Final.assumptionsOfInputs` needs no further inputs.
-/

open Set Metric

namespace Work.Final

/-- `A2`/`G7` in the `Form` shape of area `A8`: a triangulation of the closed `β`-cube with
mesh `< δ`, from `Work.PL.Subdiv.Cube.exists_cube_triangulation`. -/
theorem cubeTriangulationForm (n : ℕ) : Work.Cells.Connell.CubeTriangulationForm n :=
  fun β δ hβ hδ => Work.PL.Subdiv.Cube.exists_cube_triangulation n β δ hβ hδ

/-- `A2`/`G10` in the `Form` shape of area `A8`: affine rescalings preserve `PL.DomDim`
(`z ↦ y₀ + r • z` is the preimage of the affine isomorphism `w ↦ r⁻¹ • (w - y₀)`). -/
theorem domDimAffineForm (n : ℕ) : Work.Cells.Connell.DomDimAffineForm n := by
  intro y₀ r hr A d hA
  let φ : PL.E n →ᵃ[ℝ] PL.E n :=
    r⁻¹ • (AffineMap.id ℝ (PL.E n) - AffineMap.const ℝ (PL.E n) y₀)
  have hφ : ∀ w : PL.E n, φ w = r⁻¹ • (w - y₀) := by
    intro w
    simp [φ]
  have hinj : Function.Injective φ := by
    intro a b hab
    rw [hφ a, hφ b] at hab
    have h := congrArg (fun z : PL.E n => r • z) hab
    simp only [smul_smul, mul_inv_cancel₀ hr, one_smul] at h
    simpa using congrArg (fun z : PL.E n => z + y₀) h
  have himg : φ '' A = {z : PL.E n | y₀ + r • z ∈ A} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      show y₀ + r • φ w ∈ A
      rw [hφ w]
      have h1 : y₀ + r • (r⁻¹ • (w - y₀)) = w := by
        rw [smul_smul, mul_inv_cancel₀ hr, one_smul]
        abel
      rwa [h1]
    · intro hz
      refine ⟨y₀ + r • z, hz, ?_⟩
      rw [hφ]
      have h1 : y₀ + r • z - y₀ = r • z := by abel
      rw [h1, smul_smul, inv_mul_cancel₀ hr, one_smul]
  rw [← himg]
  exact Work.PL.Subdiv.DomDim.domDim_affine_image φ hinj hA

end Work.Final
