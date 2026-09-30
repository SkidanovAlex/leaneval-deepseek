import Mathlib
import Submission.Work.Curvature.Basic
import Submission.Work.Curvature.Deriv
import Submission.Work.Curvature.warpedMetric_chrWarped_koszul
import Submission.Work.Curvature.warpedMetric_dBmodel

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The sectional curvature numerator of the warped model

This file proves the explicit formula for the sectional curvature numerator
`⟨R(u,v)v, u⟩ = warpedMetric f h q (modelCurv (warpedMetric f h) q u v v) u` of the
multiply warped product metric `warpedMetric f h = diag(1, f(r)², h(r)², h(r)²)`,
`r = q 0`, namely

`⟨R(u,v)v,u⟩ = - ( f f'' (u₀v₁-u₁v₀)² + h h'' [(u₀v₂-u₂v₀)² + (u₀v₃-u₃v₀)²]
                  + f h f' h' [(u₁v₂-u₂v₁)² + (u₁v₃-u₃v₁)²] + h² h'² (u₂v₃-u₃v₂)² )`,

which is the coordinatewise expansion of `Σ_{i<j} K_{ij} g_ii g_jj (u_i v_j - u_j v_i)²`
with the orthonormal-frame sectional curvatures `K₀₁ = -f''/f`, `K₀₂ = K₀₃ = -h''/h`,
`K₁₂ = K₁₃ = -f'h'/(fh)`, `K₂₃ = -(h'/h)²`.

The proof combines the two model identities proved in the companion files
(`Work.Curvature.warpedMetric_chrWarped_koszul` and
`Work.Curvature.warpedMetric_dBmodel`), which identify the Christoffel symbol of
`warpedMetric f h` with `chrWarped f h` and its derivative with `chrWarpedDeriv`,
with the explicit coordinate computation.
-/

open scoped RealInnerProductSpace
open Filter Topology
open Classical

namespace Work.Curvature

noncomputable section

/-- **The Christoffel symbol of the warped metric.**  The explicit vector
`chrWarped f h q a b` satisfies the Koszul formula against `warpedMetric f h`, and
`koszulChr` is characterized by that property (`koszulChr_eq_of_forall`), so the two
agree. -/
theorem koszulChr_warped_eq (f h : ℝ → ℝ) (q a b : E4)
    (hfd : DifferentiableAt ℝ f (q 0)) (hhd : DifferentiableAt ℝ h (q 0))
    (hf0 : 0 < f (q 0)) (hh0 : 0 < h (q 0)) :
    koszulChr (warpedMetric f h) q a b = chrWarped f h q a b :=
  koszulChr_eq_of_forall (fun x y c => warpedMetric_sub_fst f h q x y c)
    (warpedMetric_pos' f h q (ne_of_gt hf0) (ne_of_gt hh0))
    (fun c =>
      warpedMetric_chrWarped_koszul f h q a b c hfd hhd (ne_of_gt hf0) (ne_of_gt hh0))

/-- **Derivative of the warped Christoffel symbol.**  Since `chrWarped f h · a b`
depends on `q` only through `q 0`, its derivative is `(d 0) • chrWarpedDeriv f h (q 0) a b`,
where `chrWarpedDeriv` is the `r`-derivative of the explicit expression. -/
theorem dBmodel_warped_eq (f h : ℝ → ℝ) (q : E4) (d a b : E4)
    (hf : ContDiff ℝ 2 f) (hh : ContDiff ℝ 2 h)
    (hf0 : 0 < f (q 0)) (hh0 : 0 < h (q 0)) :
    dBmodel (warpedMetric f h) q d a b = (d 0) • chrWarpedDeriv f h (q 0) a b := by
  refine warpedMetric_dBmodel f h q d a b hf hh (ne_of_gt hf0) (ne_of_gt hh0) ?_
  have hcf : Continuous fun q' : E4 => f (q' 0) := hf.continuous.comp (coord 0).continuous
  have hch : Continuous fun q' : E4 => h (q' 0) := hh.continuous.comp (coord 0).continuous
  filter_upwards [(isOpen_Ioi.preimage hcf).mem_nhds hf0,
    (isOpen_Ioi.preimage hch).mem_nhds hh0] with q' hf' hh'
  exact koszulChr_warped_eq f h q' a b ((hf.differentiable (by norm_num)).differentiableAt)
    ((hh.differentiable (by norm_num)).differentiableAt) hf' hh'

/-- **The sectional curvature numerator of the warped model.** -/
theorem warped_sec_eq (f h : ℝ → ℝ) (q : E4) (u v : E4)
    (hf : ContDiff ℝ 2 f) (hh : ContDiff ℝ 2 h)
    (hf0 : 0 < f (q 0)) (hh0 : 0 < h (q 0)) :
    warpedMetric f h q (modelCurv (warpedMetric f h) q u v v) u
      = -( f (q 0) * deriv^[2] f (q 0) * (u 0 * v 1 - u 1 * v 0) ^ 2
         + h (q 0) * deriv^[2] h (q 0)
             * ((u 0 * v 2 - u 2 * v 0) ^ 2 + (u 0 * v 3 - u 3 * v 0) ^ 2)
         + (f (q 0) * h (q 0) * deriv f (q 0) * deriv h (q 0))
             * ((u 1 * v 2 - u 2 * v 1) ^ 2 + (u 1 * v 3 - u 3 * v 1) ^ 2)
         + h (q 0) ^ 2 * deriv h (q 0) ^ 2 * (u 2 * v 3 - u 3 * v 2) ^ 2 ) := by
  have hdiff_f : DifferentiableAt ℝ f (q 0) := (hf.differentiable (by norm_num)).differentiableAt
  have hdiff_h : DifferentiableAt ℝ h (q 0) := (hh.differentiable (by norm_num)).differentiableAt
  have hchr : ∀ a b, koszulChr (warpedMetric f h) q a b = chrWarped f h q a b :=
    fun a b => koszulChr_warped_eq f h q a b hdiff_f hdiff_h hf0 hh0
  have hdB : ∀ d a b,
      dBmodel (warpedMetric f h) q d a b = (d 0) • chrWarpedDeriv f h (q 0) a b :=
    fun d a b => dBmodel_warped_eq f h q d a b hf hh hf0 hh0
  have hf0' : f (q 0) ≠ 0 := ne_of_gt hf0
  have hh0' : h (q 0) ≠ 0 := ne_of_gt hh0
  rw [modelCurv, hdB, hdB, hchr, hchr, hchr, hchr]
  simp [chrWarped, chrWarpedDeriv, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
    Matrix.cons_val_two, Matrix.cons_val_three]
  field_simp
  ring

end

end Work.Curvature
