import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_EllLimOK.BoxRegAux.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.jet_fderiv_partial_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH.H2.Support

set_option autoImplicit false

/-- **The second Fréchet derivative of a `C²` curried function, in terms of the four second
partials.**

For `f : ℝ → ℝ → ℝ` of class `C²` at `(z,θ)`, the second Fréchet derivative of
`F = Function.uncurry f` at `(z,θ)` is the curried bilinear form whose four entries are the
second partials `∂_z∂_z f`, `∂_θ∂_z f`, `∂_z∂_θ f`, `∂_θ∂_θ f`, i.e.
`D²F(v,w) = v.1 w.1 ∂_z∂_zf + v.1 w.2 ∂_θ∂_zf + v.2 w.1 ∂_z∂_θf + v.2 w.2 ∂_θ∂_θf`.

The two first partials of `F` are `A := pz f` and `B := pth f`; `fderiv ℝ (uncurry f)` agrees
near `(z,θ)` with `q ↦ copBilin (A q, B q) = ellCop (A q) (B q)`, so its derivative is the
composition of `copBilin` with the derivative of the pair `(A,B)`, which by the first-order
formula is `(ellCop ∂_zA ∂_θA).prod (ellCop ∂_zB ∂_θB)`. -/
theorem fderiv_fderiv_uncurry_eq
    {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ)) :
    fderiv ℝ (fderiv ℝ (Function.uncurry f)) (z, θ)
      = Work.FTS_EllLimOK.copBilin.comp
        ((Work.FTS_EllLimOK.ellCop (Work.Spaces.pz (Work.Spaces.pz f) z θ)
            (Work.Spaces.pth (Work.Spaces.pz f) z θ)).prod
          (Work.FTS_EllLimOK.ellCop (Work.Spaces.pz (Work.Spaces.pth f) z θ)
            (Work.Spaces.pth (Work.Spaces.pth f) z θ))) := by
  -- an open neighbourhood of `(z,θ)` on which `Function.uncurry f` is `C²`
  have hsmU : ContDiffWithinAt ℝ 2 (Function.uncurry f) Set.univ (z, θ) := h
  obtain ⟨u, hu_open, hu_mem, hu_cd⟩ :=
    hsmU.contDiffOn' (le_refl (2 : WithTop ℕ∞)) (by intro hc; simp at hc)
  have hu_eq : insert (z, θ) Set.univ ∩ u = u := by ext x; simp
  rw [hu_eq] at hu_cd
  have hdiff_u : ∀ q ∈ u, DifferentiableAt ℝ (Function.uncurry f) q := fun q hq =>
    (hu_cd.contDiffAt (hu_open.mem_nhds hq)).differentiableAt (by norm_num)
  have h_ev_pz : Function.uncurry (Work.Spaces.pz f) =ᶠ[𝓝 (z, θ)]
      fun q : ℝ × ℝ => fderiv ℝ (Function.uncurry f) q (1, 0) := by
    filter_upwards [hu_open.mem_nhds hu_mem] with q hq
    exact Work.Spaces.pz_eq_fderiv (hdiff_u q hq)
  have h_ev_pth : Function.uncurry (Work.Spaces.pth f) =ᶠ[𝓝 (z, θ)]
      fun q : ℝ × ℝ => fderiv ℝ (Function.uncurry f) q (0, 1) := by
    filter_upwards [hu_open.mem_nhds hu_mem] with q hq
    exact Work.Spaces.pth_eq_fderiv (hdiff_u q hq)
  have hdF1 : ContDiffAt ℝ 1 (fderiv ℝ (Function.uncurry f)) (z, θ) :=
    h.fderiv_right (m := 1) (by norm_num)
  have hdiffF1 : DifferentiableAt ℝ (fderiv ℝ (Function.uncurry f)) (z, θ) :=
    hdF1.differentiableAt (by norm_num)
  have hdA : DifferentiableAt ℝ (Function.uncurry (Work.Spaces.pz f)) (z, θ) :=
    (hdiffF1.clm_apply (differentiableAt_const ((1 : ℝ), (0 : ℝ)))).congr_of_eventuallyEq
      h_ev_pz
  have hdB : DifferentiableAt ℝ (Function.uncurry (Work.Spaces.pth f)) (z, θ) :=
    (hdiffF1.clm_apply (differentiableAt_const ((0 : ℝ), (1 : ℝ)))).congr_of_eventuallyEq
      h_ev_pth
  have hA : HasFDerivAt (fun q : ℝ × ℝ => Work.Spaces.pz f q.1 q.2)
      (Work.FTS_EllLimOK.ellCop (Work.Spaces.pz (Work.Spaces.pz f) z θ)
        (Work.Spaces.pth (Work.Spaces.pz f) z θ)) (z, θ) :=
    hdA.hasFDerivAt.congr_fderiv
      (Work.FTS_EllLimOK.ProducerH.BoxAux.fderiv_uncurry_eq_ellCop (g := Work.Spaces.pz f) hdA)
  have hB : HasFDerivAt (fun q : ℝ × ℝ => Work.Spaces.pth f q.1 q.2)
      (Work.FTS_EllLimOK.ellCop (Work.Spaces.pz (Work.Spaces.pth f) z θ)
        (Work.Spaces.pth (Work.Spaces.pth f) z θ)) (z, θ) :=
    hdB.hasFDerivAt.congr_fderiv
      (Work.FTS_EllLimOK.ProducerH.BoxAux.fderiv_uncurry_eq_ellCop (g := Work.Spaces.pth f) hdB)
  have hg_ev : fderiv ℝ (Function.uncurry f) =ᶠ[𝓝 (z, θ)]
      fun q : ℝ × ℝ => Work.FTS_EllLimOK.copBilin
        (Work.Spaces.pz f q.1 q.2, Work.Spaces.pth f q.1 q.2) := by
    filter_upwards [hu_open.mem_nhds hu_mem] with q hq
    rw [Work.FTS_EllLimOK.ProducerH.BoxAux.fderiv_uncurry_eq_ellCop (g := f) (hdiff_u q hq),
      Work.FTS_EllLimOK.copBilin_apply]
  have hpair : HasFDerivAt
      (fun q : ℝ × ℝ => (Work.Spaces.pz f q.1 q.2, Work.Spaces.pth f q.1 q.2))
      ((Work.FTS_EllLimOK.ellCop (Work.Spaces.pz (Work.Spaces.pz f) z θ)
          (Work.Spaces.pth (Work.Spaces.pz f) z θ)).prod
        (Work.FTS_EllLimOK.ellCop (Work.Spaces.pz (Work.Spaces.pth f) z θ)
          (Work.Spaces.pth (Work.Spaces.pth f) z θ))) (z, θ) := hA.prodMk hB
  have hcomp : HasFDerivAt (fun q : ℝ × ℝ => Work.FTS_EllLimOK.copBilin
      (Work.Spaces.pz f q.1 q.2, Work.Spaces.pth f q.1 q.2))
      (Work.FTS_EllLimOK.copBilin.comp
        ((Work.FTS_EllLimOK.ellCop (Work.Spaces.pz (Work.Spaces.pz f) z θ)
            (Work.Spaces.pth (Work.Spaces.pz f) z θ)).prod
          (Work.FTS_EllLimOK.ellCop (Work.Spaces.pz (Work.Spaces.pth f) z θ)
            (Work.Spaces.pth (Work.Spaces.pth f) z θ)))) (z, θ) :=
    (ContinuousLinearMap.hasFDerivAt Work.FTS_EllLimOK.copBilin).comp (z, θ) hpair
  exact hg_ev.fderiv_eq.trans hcomp.fderiv

end Work.FTS_EllLimOK.ProducerH.H2.Support
