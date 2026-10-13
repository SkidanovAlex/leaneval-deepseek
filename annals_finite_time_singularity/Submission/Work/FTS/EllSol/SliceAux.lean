/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `θ`-slices of the mixed derivatives of an open-quadrant smooth datum

For `G` which is `C^∞` on the open quadrant `Q0 = (0,∞) × (0,π/2)` (`SmoothOpen G`), the
`θ`-slice `θ ↦ D_zG(z,θ)` is smooth and its derivatives are the mixed derivatives:

* `deriv_slice_Dz` : `deriv (fun θ' => D_zG z θ') θ = D_z(∂_θG) z θ`,
* `deriv_deriv_slice_Dz` : `deriv (deriv (fun θ' => D_zG z θ')) θ = D_z(∂_θ²G) z θ`,

for `z > 0` and `θ ∈ (0,π/2)`.  Both are consequences of Clairaut's theorem
`Work.Spaces.pz_pth_comm` on the open quadrant.  These are the identifications which turn the
one-dimensional angular integration by parts for the slice `θ ↦ D_zG(z,θ)` into the identity
with `D_z∂_θG` and `D_z∂_θ²G` used by the box pairing identity.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.mixed_comm
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol

set_option autoImplicit false

/-- **The `θ`-derivative of the slice of `D_zG`.**  For `G` smooth on the open quadrant, `z > 0`
and `θ ∈ (0,π/2)`, the derivative of `θ' ↦ D_zG z θ'` at `θ` is `D_z(∂_θG) z θ`. -/
theorem deriv_slice_Dz {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun θ' => Work.Spaces.Dz G z θ') θ = Work.Spaces.Dz (Work.Spaces.pth G) z θ := by
  have hcd : ContDiffAt ℝ 2 (Function.uncurry G) (z, θ) :=
    (hG.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ⟩))).of_le (by norm_num)
  have h1 : Work.Spaces.pth (Work.Spaces.pz G) z θ = Work.Spaces.pz (Work.Spaces.pth G) z θ :=
    (Work.Spaces.pz_pth_comm (f := G) hcd).symm
  calc deriv (fun θ' => Work.Spaces.Dz G z θ') θ
      = deriv (fun θ' => z * Work.Spaces.pz G z θ') θ := rfl
    _ = z * deriv (fun θ' => Work.Spaces.pz G z θ') θ := by rw [deriv_const_mul_field]
    _ = z * Work.Spaces.pth (Work.Spaces.pz G) z θ := rfl
    _ = z * Work.Spaces.pz (Work.Spaces.pth G) z θ := by rw [h1]
    _ = Work.Spaces.Dz (Work.Spaces.pth G) z θ := rfl

/-- **The second `θ`-derivative of the slice of `D_zG`.**  For `G` smooth on the open quadrant,
`z > 0` and `θ ∈ (0,π/2)`, the second derivative of `θ' ↦ D_zG z θ'` at `θ` is `D_z(∂_θ²G) z θ`. -/
theorem deriv_deriv_slice_Dz {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (deriv (fun θ' => Work.Spaces.Dz G z θ')) θ
      = Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ := by
  have hmem : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
  have hev : (fun θ'' => deriv (fun θ' => Work.Spaces.Dz G z θ') θ'')
      =ᶠ[𝓝 θ] (fun θ'' => Work.Spaces.Dz (Work.Spaces.pth G) z θ'') := by
    filter_upwards [hmem] with θ'' hθ''
    exact deriv_slice_Dz hG hz hθ''
  have hcd : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pth G)) (z, θ) :=
    ((hG.pth).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ⟩))).of_le (by norm_num)
  have h2 : Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth G)) z θ
      = Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth G)) z θ :=
    (Work.Spaces.pz_pth_comm (f := Work.Spaces.pth G) hcd).symm
  calc deriv (deriv (fun θ' => Work.Spaces.Dz G z θ')) θ
      = deriv (fun θ'' => Work.Spaces.Dz (Work.Spaces.pth G) z θ'') θ := hev.deriv_eq
    _ = deriv (fun θ'' => z * Work.Spaces.pz (Work.Spaces.pth G) z θ'') θ := rfl
    _ = z * deriv (fun θ'' => Work.Spaces.pz (Work.Spaces.pth G) z θ'') θ := by
        rw [deriv_const_mul_field]
    _ = z * Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth G)) z θ := rfl
    _ = z * Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth G)) z θ := by rw [h2]
    _ = Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ := rfl

/-- The `z`-derivative of the `z`-slice of `∂_θ²G` is `∂_z∂_θ²G` (definitional). -/
theorem deriv_slice_pthpth {G : ℝ → ℝ → ℝ} {z θ : ℝ} :
    deriv (fun z' => Work.Spaces.pth (Work.Spaces.pth G) z' θ) z
      = Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth G)) z θ := rfl

end Work.FTS.EllSol
