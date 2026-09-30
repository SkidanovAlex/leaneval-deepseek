import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.Complex

/-!
# Real-part of the logarithmic derivative along a real line

For a complex-differentiable `g` with `g a ≠ 0`, the real curve
`t ↦ Real.log ‖g (a + t)‖` has derivative `Re (g'(a) / g(a))` at `t = 0`.

The proof uses the complex logarithm on the slit plane: either `g a` or
`-g a` lies in `Complex.slitPlane` (`Complex.mem_slitPlane_or_neg_mem_slitPlane`),
and on the slit plane `Complex.log` is complex-differentiable with derivative
`z ↦ z⁻¹` (`Complex.hasDerivAt_log`, `HasDerivAt.clog_real`).  Taking real parts
(`hasDerivAt_re` below) and using `Complex.log_re : (Complex.log z).re = Real.log ‖z‖`
gives the result; in the rotated branch `‖-z‖ = ‖z‖` supplies the last step.
-/

/-- The real part of a real-differentiable complex curve is real-differentiable, with
derivative the real part of the complex derivative. -/
private lemma hasDerivAt_re {F : ℝ → ℂ} {f' : ℂ} {x : ℝ} (hF : HasDerivAt F f' x) :
    HasDerivAt (fun t : ℝ => (F t).re) (Complex.re f') x := by
  have hFd : HasFDerivAt F (ContinuousLinearMap.toSpanSingleton ℝ f') x := hF.hasFDerivAt
  have hc : HasFDerivAt (fun t : ℝ => Complex.re (F t))
      ((Complex.reCLM : ℂ →L[ℝ] ℝ).comp (ContinuousLinearMap.toSpanSingleton ℝ f')) x := by
    exact (ContinuousLinearMap.hasFDerivAt (Complex.reCLM : ℂ →L[ℝ] ℝ)).comp x hFd
  simpa [Complex.reCLM_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul] using hc.hasDerivAt

/-- For a real curve `h : ℝ → ℂ` with `h x` in the slit plane, `t ↦ Real.log ‖h t‖`
has derivative `Re (h' / h x)` at `x`. -/
private lemma hasDerivAt_log_norm_of_hasDerivAt {h : ℝ → ℂ} {x : ℝ} {h' : ℂ}
    (hh : HasDerivAt h h' x) (hx : h x ∈ Complex.slitPlane) :
    HasDerivAt (fun t : ℝ => Real.log ‖h t‖) (Complex.re (h' / h x)) x := by
  have hlog : HasDerivAt (fun t : ℝ => Complex.log (h t)) (h' / h x) x := hh.clog_real hx
  have hre : HasDerivAt (fun t : ℝ => ((Complex.log (h t)).re))
      (Complex.re (h' / h x)) x := hasDerivAt_re hlog
  convert hre using 1
  ext t
  rw [Complex.log_re]

/-- The derivative at `0` of the real curve `t ↦ g (a + t)` equals the complex
derivative `deriv g a`. -/
private lemma hasDerivAt_translate {g : ℂ → ℂ} {a : ℂ} (hg : DifferentiableAt ℂ g a) :
    HasDerivAt (fun t : ℝ => g (a + (t : ℂ))) (deriv g a) 0 := by
  have htrans : HasDerivAt (fun z : ℂ => a + z) (1 : ℂ) (0 : ℂ) := by
    simpa using (hasDerivAt_id (x := (0 : ℂ))).const_add a
  have hg' : HasDerivAt g (deriv g a) a := hg.hasDerivAt
  have hcomp : HasDerivAt (fun z : ℂ => g (a + z)) ((1 : ℂ) • deriv g a) (0 : ℂ) := by
    exact HasDerivAt.scomp_of_eq (x := (0 : ℂ)) (y := a) hg' htrans (by simp : a = a + 0)
  simpa using hcomp.comp_ofReal

/-- If `g` is complex-differentiable at `a` and `g a ≠ 0`, then
`t ↦ Real.log ‖g (a + t)‖` has derivative `Re (deriv g a / g a)` at `t = 0`. -/
theorem partialX_log_norm {g : ℂ → ℂ} {a : ℂ} (hg : DifferentiableAt ℂ g a)
    (hga : g a ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.log ‖g (a + (t : ℂ))‖) (Complex.re (deriv g a / g a)) 0 := by
  have hF : HasDerivAt (fun t : ℝ => g (a + (t : ℂ))) (deriv g a) 0 := hasDerivAt_translate hg
  by_cases h₁ : g a ∈ Complex.slitPlane
  · have h₁' : g (a + (0 : ℂ)) ∈ Complex.slitPlane := by simpa using h₁
    simpa using hasDerivAt_log_norm_of_hasDerivAt hF h₁'
  · have h₂ : -g a ∈ Complex.slitPlane :=
      (Complex.mem_slitPlane_or_neg_mem_slitPlane hga).resolve_left h₁
    have hFneg : HasDerivAt (fun t : ℝ => -g (a + (t : ℂ))) (-deriv g a) 0 := hF.neg
    have h₂' : -g (a + (0 : ℂ)) ∈ Complex.slitPlane := by simpa using h₂
    have hres := hasDerivAt_log_norm_of_hasDerivAt hFneg h₂'
    have hFunext : (fun t : ℝ => Real.log ‖g (a + (t : ℂ))‖) =
        fun t : ℝ => Real.log ‖-g (a + (t : ℂ))‖ := by
      funext t
      simp [norm_neg]
    have hdiv : (-deriv g a) / (-g a) = deriv g a / g a := by
      field_simp [hga]
    simpa [hFunext.symm, hdiv] using hres

end Commons.Analysis.Complex