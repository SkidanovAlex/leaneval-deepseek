import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology

namespace Commons.Analysis.Convex

open Set

/-- **Second derivative test for convexity (higher-dimensional version).**
If `f : E → ℝ` is convex and `C²` on a real normed space `E`, then its second derivative is
positive semidefinite everywhere: `0 ≤ D²f(x)(v,v)` for all `x` and `v`.

Suggested proof: fix `x v : E` and consider the one-dimensional function
`g s = f (x + s • v)`, which is convex (`ConvexOn.comp_affineMap` or `AffineMap`-composition
lemmas) and `C²` (chain rule, `ContDiff.comp`).  By `ConvexOn.monotoneOn_deriv` the derivative
`deriv g` is monotone, hence `0 ≤ deriv (deriv g) 0` (`Monotone.deriv_nonneg`).  Finally compute
`deriv (deriv g) 0 = fderiv ℝ (fderiv ℝ f) x v v` by the chain rule twice
(`fderiv` of `s ↦ x + s • v` is `1 • v`). -/
theorem fderiv2_nonneg_of_convexOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (hf : ContDiff ℝ 2 f) (hconv : ConvexOn ℝ Set.univ f) :
    ∀ x v : E, 0 ≤ fderiv ℝ (fderiv ℝ f) x v v := by
  intro x v
  -- The restriction of `f` to the affine line `s ↦ x + s • v`.
  let phi : ℝ → E := fun s => x + s • v
  let G : ℝ → ℝ := fun s => f (phi s)
  -- The function `z ↦ fderiv ℝ f z v` (evaluation of the derivative in direction `v`).
  let hh : E → ℝ := fun z => fderiv ℝ f z v
  -- `G` is convex, being the composition of a convex function with an affine map.
  have hGconv : ConvexOn ℝ Set.univ G := by
    have h := hconv.comp_affineMap (AffineMap.lineMap x (x + v))
    have heq : (f ∘ ⇑(AffineMap.lineMap x (x + v))) = G := by
      funext s; simp [G, phi, AffineMap.lineMap_apply, add_comm]
    rwa [Set.preimage_univ, heq] at h
  -- `G` is `C²`.
  have hGcont : ContDiff ℝ 2 G := by
    have hphi : ContDiff ℝ 2 phi := by
      change ContDiff ℝ 2 (fun s : ℝ => x + s • v)
      exact ContDiff.add contDiff_const (ContinuousLinearMap.toSpanSingleton ℝ v).contDiff
    exact hf.comp hphi
  have hGdiff : Differentiable ℝ G := hGcont.differentiable (by norm_num)
  -- For a convex differentiable function, `deriv G` is monotone, hence `deriv (deriv G) ≥ 0`.
  have hmonoOn : MonotoneOn (deriv G) Set.univ :=
    hGconv.monotoneOn_deriv (fun s _ => hGdiff s)
  have hmono : Monotone (deriv G) := monotoneOn_univ.mp hmonoOn
  have hnonneg : 0 ≤ deriv (deriv G) 0 := hmono.deriv_nonneg
  -- The chain rule for `s ↦ x + s • v`.
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hφfd : ∀ s : ℝ, HasFDerivAt phi (ContinuousLinearMap.toSpanSingleton ℝ v) s := by
    intro s
    have h'' : HasFDerivAt (fun t : ℝ => t • v + x)
        (ContinuousLinearMap.toSpanSingleton ℝ v) s :=
      (ContinuousLinearMap.toSpanSingleton ℝ v).hasFDerivAt.add_const x
    change HasFDerivAt (fun t : ℝ => x + t • v) (ContinuousLinearMap.toSpanSingleton ℝ v) s
    simpa [add_comm] using h''
  -- First computation: `deriv G = hh ∘ phi`.
  have hderivG : deriv G = hh ∘ phi := by
    funext s
    have hcomp : HasFDerivAt G
        ((fderiv ℝ f (phi s)) ∘SL (ContinuousLinearMap.toSpanSingleton ℝ v)) s :=
      ((hfd (phi s)).hasFDerivAt).comp s (hφfd s)
    rw [hcomp.hasDerivAt.deriv]
    simp [hh, phi]
  -- Differentiability of `hh` and its derivative.
  have hfH : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (m := 1) (by norm_num)
  have hHd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hfH.differentiable (by norm_num)).differentiableAt
  have hhd : DifferentiableAt ℝ hh x := by
    have hev : hh = (ContinuousLinearMap.apply ℝ ℝ v) ∘ (fderiv ℝ f) := by
      funext z; rfl
    rw [hev]
    exact DifferentiableAt.comp x (ContinuousLinearMap.differentiableAt _) hHd
  -- Second computation: `deriv (deriv G) 0 = fderiv ℝ hh x v`.
  have hhd' : HasFDerivAt hh (fderiv ℝ hh x) (x + (0 : ℝ) • v) := by
    simpa using hhd.hasFDerivAt
  have hcomp2 : HasFDerivAt (hh ∘ phi)
      ((fderiv ℝ hh x) ∘SL (ContinuousLinearMap.toSpanSingleton ℝ v)) 0 :=
    hhd'.comp 0 (hφfd 0)
  have hderiv2 : deriv (hh ∘ phi) 0 = fderiv ℝ hh x v := by
    rw [hcomp2.hasDerivAt.deriv]
    simp
  -- Third computation: `fderiv ℝ hh x v = fderiv ℝ (fderiv ℝ f) x v v`.
  have hev2 : hh = (ContinuousLinearMap.apply ℝ ℝ v) ∘ (fderiv ℝ f) := by
    funext z; rfl
  have hcomp3 : HasFDerivAt hh
      ((ContinuousLinearMap.apply ℝ ℝ v) ∘SL (fderiv ℝ (fderiv ℝ f) x)) x := by
    rw [hev2]
    exact (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.apply ℝ ℝ v)).comp x
      hHd.hasFDerivAt
  have hderiv3 : fderiv ℝ hh x v = fderiv ℝ (fderiv ℝ f) x v v := by
    rw [hcomp3.fderiv]
    simp
  have hident : deriv (deriv G) 0 = fderiv ℝ (fderiv ℝ f) x v v := by
    rw [hderivG, hderiv2, hderiv3]
  rw [hident] at hnonneg
  exact hnonneg

end Commons.Analysis.Convex