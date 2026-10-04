import Mathlib
import Submission.Work.Diff.EXT.splice_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead

open Filter

/-- **The spatial `2`-jet `Work.Diff.EXT.jet2` is additive in the function.**

`jet2 u p = (u p, ∂_y u, ∂_y² u)` is built from the value and from the first and second spatial
Fréchet derivatives, and `fderiv` is linear *at the points where the functions are differentiable*.
Smoothness of `u` and `v` at `p` gives all the required differentiability: `u` is `C^n` at `p` for
every `n`, hence so is the slice `y ↦ u (p.1, y)` (compose with the affine map `y ↦ (p.1, y)`);
`C^1` of the slice gives differentiability of the slice everywhere near `p.2` (used to identify
`∂_y (u - v)` with `∂_y u - ∂_y v` on a neighbourhood), and `C^2` of the slice gives
differentiability of its derivative at `p.2` (used for the outer `fderiv_sub`). -/
theorem jet2_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u v : ℝ × E → F) (p : ℝ × E) (hu : ContDiffAt ℝ (⊤ : ℕ∞) u p)
    (hv : ContDiffAt ℝ (⊤ : ℕ∞) v p) :
    Work.Diff.EXT.jet2 (E := E) (fun q => u q - v q) p
      = Work.Diff.EXT.jet2 (E := E) u p - Work.Diff.EXT.jet2 (E := E) v p := by
  -- Smoothness of the two spatial slices at `p.2`.
  have hsu : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : E => u (p.1, y)) p.2 :=
    hu.comp p.2 (ContDiffAt.prodMk contDiffAt_const contDiffAt_id)
  have hsv : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : E => v (p.1, y)) p.2 :=
    hv.comp p.2 (ContDiffAt.prodMk contDiffAt_const contDiffAt_id)
  have h1u : ContDiffAt ℝ (1 : ℕ) (fun y : E => u (p.1, y)) p.2 := (contDiffAt_infty.mp hsu) 1
  have h1v : ContDiffAt ℝ (1 : ℕ) (fun y : E => v (p.1, y)) p.2 := (contDiffAt_infty.mp hsv) 1
  have h2u : ContDiffAt ℝ (2 : ℕ) (fun y : E => u (p.1, y)) p.2 := (contDiffAt_infty.mp hsu) 2
  have h2v : ContDiffAt ℝ (2 : ℕ) (fun y : E => v (p.1, y)) p.2 := (contDiffAt_infty.mp hsv) 2
  -- Differentiability of the slices, and of the slices of the first derivatives.
  have hdu : DifferentiableAt ℝ (fun y : E => u (p.1, y)) p.2 := h1u.differentiableAt_one
  have hdv : DifferentiableAt ℝ (fun y : E => v (p.1, y)) p.2 := h1v.differentiableAt_one
  have hduA : DifferentiableAt ℝ (fderiv ℝ (fun y : E => u (p.1, y))) p.2 :=
    (h2u.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hdvA : DifferentiableAt ℝ (fderiv ℝ (fun y : E => v (p.1, y))) p.2 :=
    (h2v.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  -- The two slices of `(u - v)` are the differences of the slices of `u` and `v`, near `p.2`.
  have hevu : ∀ᶠ y in nhds p.2, DifferentiableAt ℝ (fun y' : E => u (p.1, y')) y := by
    filter_upwards [h1u.eventually (by norm_num)] with y hy
    exact hy.differentiableAt_one
  have hevv : ∀ᶠ y in nhds p.2, DifferentiableAt ℝ (fun y' : E => v (p.1, y')) y := by
    filter_upwards [h1v.eventually (by norm_num)] with y hy
    exact hy.differentiableAt_one
  have hEq : (fun y : E => fderiv ℝ (fun y' : E => u (p.1, y') - v (p.1, y')) y)
      =ᶠ[nhds p.2] (fun y : E => fderiv ℝ (fun y' : E => u (p.1, y')) y
        - fderiv ℝ (fun y' : E => v (p.1, y')) y) := by
    filter_upwards [hevu, hevv] with y h1 h2
    exact fderiv_sub h1 h2
  simp only [Work.Diff.EXT.jet2, Prod.mk_sub_mk]
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · exact fderiv_sub hdu hdv
  · rw [Filter.EventuallyEq.fderiv_eq hEq]
    exact fderiv_sub hduA hdvA

end Work.Diff.STE.Lead
