import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Symmetry of the second directional derivatives (`C²` version)

For a `C²` function `f` on an open set and any two directions `u v`, the two
iterated directional derivatives commute:

`fderiv (fun y => fderiv f y u) x v = fderiv (fun y => fderiv f y v) x u`.

Mathlib's machinery: `ContDiffAt.isSymmSndFDerivAt` (in
`Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`) proves
`IsSymmSndFDerivAt f x` for `ContDiffAt ℝ n f x` with
`minSmoothness ℝ 2 ≤ n`; combine that with the chain rule connecting
`fderiv (fun y => fderiv f y u) x v` to the full second derivative
`(fderiv (fderiv f) x v) u` (evaluation of the derivative of a
`fderiv`-valued function at a fixed vector).  A companion result with the
stronger analytic (`ω`) hypothesis already exists in the commons as
`Commons.Analysis.Calculus.FDeriv.secondDirectional_commute`, which may be
used for the conversion step.

IMPORTANT: the hypothesis here is `ContDiffOn ℝ 2` (twice continuously
differentiable), NOT analyticity.
-/

open scoped ContDiff
open Topology

noncomputable section
namespace Commons.Analysis.Calculus.FDeriv

/-- Mixed second partial derivatives commute for a `C²` function on an open
set. -/
theorem secondDirectional_commute_two {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {s : Set E} {f : E → F} {x : E}
    (hs : IsOpen s) (hx : x ∈ s) (hf : ContDiffOn ℝ 2 f s) (u v : E) :
    fderiv ℝ (fun y : E => fderiv ℝ f y u) x v =
      fderiv ℝ (fun y : E => fderiv ℝ f y v) x u := by
  have hcontAt : ContDiffAt ℝ 2 f x := hf.contDiffAt (hs.mem_nhds hx)
  have hsymm : IsSymmSndFDerivAt ℝ f x := hcontAt.isSymmSndFDerivAt (by simp)
  have hfdiff : DifferentiableAt ℝ (fun y : E => fderiv ℝ f y) x := by
    exact (hcontAt.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  let H : E →L[ℝ] (E →L[ℝ] F) := fderiv ℝ (fun y : E => fderiv ℝ f y) x
  have hdecomp : ∀ w : E, fderiv ℝ (fun y : E => fderiv ℝ f y w) x = H.flip w := by
    intro w
    have hu : DifferentiableAt ℝ (fun _ : E => w) x := differentiableAt_const w
    have hm := fderiv_clm_apply (𝕜 := ℝ) (c := fun y : E => fderiv ℝ f y)
      (u := fun _ : E => w) hfdiff hu
    simp at hm
    exact hm
  calc
    fderiv ℝ (fun y : E => fderiv ℝ f y u) x v
        = (H.flip u) v := congrArg (fun L : E →L[ℝ] F => L v) (hdecomp u)
    _ = H v u := by
      rw [ContinuousLinearMap.flip_apply]
    _ = H u v := hsymm v u
    _ = (H.flip v) u := by
      rw [← ContinuousLinearMap.flip_apply]
    _ = fderiv ℝ (fun y : E => fderiv ℝ f y v) x u :=
      (congrArg (fun L : E →L[ℝ] F => L u) (hdecomp v)).symm

end Commons.Analysis.Calculus.FDeriv
