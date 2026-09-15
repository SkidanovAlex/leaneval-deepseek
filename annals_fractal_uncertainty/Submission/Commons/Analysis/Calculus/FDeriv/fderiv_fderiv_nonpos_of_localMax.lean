import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Commons.Analysis.Calculus.Deriv.deriv_deriv_nonpos_of_localMax
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv

open Filter
open scoped Topology

namespace Commons.Analysis.Calculus.FDeriv

theorem fderiv_fderiv_nonpos_of_localMax {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (hmax : IsLocalMax f x) (v : E) :
    (fderiv ℝ (fderiv ℝ f) x) v v ≤ 0 := by
  -- the restriction of `f` to the line through `x` in direction `v`
  have hmaxg : IsLocalMax (fun t : ℝ => f (x + t • v)) 0 := by
    have hφ : ContinuousAt (fun t : ℝ => x + t • v) 0 := by fun_prop
    have htend : Tendsto (fun t : ℝ => x + t • v) (𝓝 0) (𝓝 x) := by simpa using hφ.tendsto
    have h : ∀ᶠ t in 𝓝 (0:ℝ), f (x + t • v) ≤ f x := htend.eventually hmax
    simpa only [IsLocalMax, IsMaxFilter, zero_smul, add_zero] using h
  have hg : ContDiffAt ℝ 2 (fun t : ℝ => f (x + t • v)) 0 := by
    have hφ : ContDiffAt ℝ 2 (fun t : ℝ => x + t • v) 0 := by fun_prop
    exact ContDiffAt.fun_comp (x := (0 : ℝ)) (f := fun t : ℝ => x + t • v) (g := f)
      (by simpa using hf) hφ
  -- first derivative along the line
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) x := by
    have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) x := hf.fderiv_right (m := 1) (by norm_num)
    exact h1.differentiableAt_one
  have hA : HasDerivAt (fun t : ℝ => fderiv ℝ f (x + t • v))
      ((fderiv ℝ (fderiv ℝ f) x) v) 0 :=
    fderiv_along_axis_eq_deriv (H := fderiv ℝ f) (p := x) (e := v) hfd
  -- evaluation at `v`
  have hB : HasDerivAt (fun t : ℝ => (fderiv ℝ f (x + t • v)) v)
      ((fderiv ℝ (fderiv ℝ f) x) v v) 0 := by
    have hev : HasFDerivAt (ContinuousLinearMap.apply ℝ ℝ v)
        (ContinuousLinearMap.apply ℝ ℝ v) ((fun t : ℝ => fderiv ℝ f (x + t • v)) 0) :=
      (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt
    have h := HasFDerivAt.comp_hasDerivAt
      (l := ContinuousLinearMap.apply ℝ ℝ v) (l' := ContinuousLinearMap.apply ℝ ℝ v)
      (f := fun t : ℝ => fderiv ℝ f (x + t • v))
      (f' := (fderiv ℝ (fderiv ℝ f) x) v) (x := (0:ℝ)) hev hA
    rw [show (⇑(ContinuousLinearMap.apply ℝ ℝ v) ∘ fun t : ℝ => fderiv ℝ f (x + t • v))
        = (fun t : ℝ => (fderiv ℝ f (x + t • v)) v) from by
      ext t; simp] at h
    simpa using h
  -- identify `deriv` of the restriction with the above function
  have hderivg : deriv (fun t : ℝ => f (x + t • v)) =ᶠ[𝓝 (0:ℝ)]
      fun t : ℝ => (fderiv ℝ f (x + t • v)) v := by
    have hf_near : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y :=
      (hf.eventually (by norm_num)).mono fun y hy => hy.differentiableAt (by norm_num)
    have hφ : ContinuousAt (fun t : ℝ => x + t • v) 0 := by fun_prop
    have htend : Tendsto (fun t : ℝ => x + t • v) (𝓝 0) (𝓝 x) := by simpa using hφ.tendsto
    have hnear : ∀ᶠ t in 𝓝 (0:ℝ), DifferentiableAt ℝ f (x + t • v) := htend.eventually hf_near
    filter_upwards [hnear] with t ht
    have hlin : HasDerivAt (fun s : ℝ => x + s • v) v t := by
      simpa using (((hasDerivAt_id t).smul_const v).const_add x)
    have hcomp : HasDerivAt (fun s : ℝ => f (x + s • v))
        ((fderiv ℝ f (x + t • v)) v) t :=
      HasFDerivAt.comp_hasDerivAt (l := f) (l' := fderiv ℝ f (x + t • v))
        (f := fun s : ℝ => x + s • v) (f' := v) (x := t) ht.hasFDerivAt hlin
    exact hcomp.deriv
  -- second derivative along the line
  have hderiv2 : deriv (deriv (fun t : ℝ => f (x + t • v))) 0 =
      (fderiv ℝ (fderiv ℝ f) x) v v := by
    rw [hderivg.deriv_eq, hB.deriv]
  have h := Commons.Analysis.Calculus.Deriv.deriv_deriv_nonpos_of_localMax hg hmaxg
  rw [hderiv2] at h
  exact h

end Commons.Analysis.Calculus.FDeriv