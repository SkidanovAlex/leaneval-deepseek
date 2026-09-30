import Mathlib
import Submission.Work.Curvature.Basic
import Submission.Work.Curvature.Deriv

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The derivative of the warped Christoffel symbol

`Warped.ChrWarped` (see `Work.Curvature.Basic`) records the explicit Christoffel
symbol `chrWarped f h q a b` of the warped metric `warpedMetric f h`.  This file
computes its derivative `dBmodel (warpedMetric f h) q d a b`, i.e. the directional
derivative of `q' ↦ koszulChr (warpedMetric f h) q' a b`.

Because `chrWarped f h · a b` depends on `q'` only through the coordinate
`q' 0 =: r`, this derivative is `(d 0) • chrWarpedDeriv f h (q 0) a b`, where
`chrWarpedDeriv` is the `r`-derivative of the explicit expression, recorded in
`Work.Curvature.Basic`.

The proof splits in three parts:

* `chrWarped_eq_chrWarpedFun`: `chrWarped f h q a b = chrWarpedFun f h a b (q 0)`,
  where `chrWarpedFun f h a b` is the same explicit expression with `q 0` replaced
  by the variable `r`; the equality is componentwise.
* `hasDerivAt_chrWarpedFun`: the one-dimensional statement
  `HasDerivAt (chrWarpedFun f h a b) (chrWarpedDeriv f h (q 0) a b) (q 0)`, obtained
  componentwise from `ContDiff ℝ 2` hypotheses (which give `HasDerivAt (deriv f)`),
  the product and quotient rules, and the `Fin 4`-product rule `hasDerivAt_pi`.
* the chain rule `HasFDerivAt.comp` with the coordinate projection `coord 0`, plus
  `Filter.EventuallyEq.fderiv_eq` to replace `koszulChr` by `chrWarped` in the
  definition of `dBmodel`.
-/

open scoped RealInnerProductSpace
open Filter Topology

namespace Work.Curvature

noncomputable section

/-- The linear isometry `(Fin 4 → ℝ) ≃L[ℝ] E4` underlying the `!₂[·,·,·,·]`
notation. -/
private noncomputable def e4Lift : (Fin 4 → ℝ) →L[ℝ] E4 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm

/-- The explicit Christoffel symbol of the warped metric, as a function of the
radial variable `r = q 0` alone. -/
private noncomputable def chrWarpedFun (f h : ℝ → ℝ) (a b : E4) (r : ℝ) : E4 :=
  !₂[-(deriv f r * f r) * (a 1 * b 1) - (deriv h r * h r) * (a 2 * b 2 + a 3 * b 3),
      (deriv f r / f r) * (a 0 * b 1 + a 1 * b 0),
      (deriv h r / h r) * (a 0 * b 2 + a 2 * b 0),
      (deriv h r / h r) * (a 0 * b 3 + a 3 * b 0)]

/-- `chrWarped f h · a b` depends on the point only through its `0`-th coordinate. -/
private theorem chrWarped_eq_chrWarpedFun (f h : ℝ → ℝ) (q a b : E4) :
    chrWarped f h q a b = chrWarpedFun f h a b (q 0) := by
  ext i
  fin_cases i <;> simp [chrWarped, chrWarpedFun]

/-- The one-dimensional derivative of the explicit warped Christoffel symbol. -/
private theorem hasDerivAt_chrWarpedFun (f h : ℝ → ℝ) (a b : E4) (r0 : ℝ)
    (hf : ContDiff ℝ 2 f) (hh : ContDiff ℝ 2 h) (hf0 : f r0 ≠ 0) (hh0 : h r0 ≠ 0) :
    HasDerivAt (chrWarpedFun f h a b) (chrWarpedDeriv f h r0 a b) r0 := by
  have hdf : HasDerivAt (deriv f) (deriv^[2] f r0) r0 := by
    have h : Differentiable ℝ (deriv f) := ContDiff.differentiable_deriv_two hf
    exact (h r0).hasDerivAt
  have hdh : HasDerivAt (deriv h) (deriv^[2] h r0) r0 := by
    have h : Differentiable ℝ (deriv h) := ContDiff.differentiable_deriv_two hh
    exact (h r0).hasDerivAt
  have hf' : HasDerivAt f (deriv f r0) r0 := by
    have h : Differentiable ℝ f := hf.differentiable (by norm_num)
    exact (h r0).hasDerivAt
  have hh' : HasDerivAt h (deriv h r0) r0 := by
    have h : Differentiable ℝ h := hh.differentiable (by norm_num)
    exact (h r0).hasDerivAt
  have hφf : HasDerivAt (fun r => deriv f r * f r)
      (deriv^[2] f r0 * f r0 + deriv f r0 ^ 2) r0 := by
    have hm := hdf.mul hf'
    rwa [show deriv f r0 * deriv f r0 = deriv f r0 ^ 2 from by ring] at hm
  have hφh : HasDerivAt (fun r => deriv h r * h r)
      (deriv^[2] h r0 * h r0 + deriv h r0 ^ 2) r0 := by
    have hm := hdh.mul hh'
    rwa [show deriv h r0 * deriv h r0 = deriv h r0 ^ 2 from by ring] at hm
  have hψf : HasDerivAt (fun r => deriv f r / f r)
      ((deriv^[2] f r0 * f r0 - deriv f r0 ^ 2) / f r0 ^ 2) r0 := by
    have hm := hdf.div hf' hf0
    rwa [show deriv f r0 * deriv f r0 = deriv f r0 ^ 2 from by ring] at hm
  have hψh : HasDerivAt (fun r => deriv h r / h r)
      ((deriv^[2] h r0 * h r0 - deriv h r0 ^ 2) / h r0 ^ 2) r0 := by
    have hm := hdh.div hh' hh0
    rwa [show deriv h r0 * deriv h r0 = deriv h r0 ^ 2 from by ring] at hm
  have hg0 : HasDerivAt (fun r => -(deriv f r * f r) * (a 1 * b 1)
        - (deriv h r * h r) * (a 2 * b 2 + a 3 * b 3))
      (-((deriv^[2] f r0 * f r0 + deriv f r0 ^ 2) * (a 1 * b 1)
        + (deriv^[2] h r0 * h r0 + deriv h r0 ^ 2) * (a 2 * b 2 + a 3 * b 3))) r0 := by
    have h3 := ((hφf.const_mul (a 1 * b 1)).neg).sub (hφh.const_mul (a 2 * b 2 + a 3 * b 3))
    convert h3 using 1
    · funext r
      simp only [Pi.neg_apply, Pi.sub_apply]
      ring
    · ring
  have hg1 : HasDerivAt (fun r => (deriv f r / f r) * (a 0 * b 1 + a 1 * b 0))
      (((deriv^[2] f r0 * f r0 - deriv f r0 ^ 2) / f r0 ^ 2) * (a 0 * b 1 + a 1 * b 0)) r0 :=
    hψf.mul_const _
  have hg2 : HasDerivAt (fun r => (deriv h r / h r) * (a 0 * b 2 + a 2 * b 0))
      (((deriv^[2] h r0 * h r0 - deriv h r0 ^ 2) / h r0 ^ 2) * (a 0 * b 2 + a 2 * b 0)) r0 :=
    hψh.mul_const _
  have hg3 : HasDerivAt (fun r => (deriv h r / h r) * (a 0 * b 3 + a 3 * b 0))
      (((deriv^[2] h r0 * h r0 - deriv h r0 ^ 2) / h r0 ^ 2) * (a 0 * b 3 + a 3 * b 0)) r0 :=
    hψh.mul_const _
  have hF : HasDerivAt (fun r : ℝ => (![-(deriv f r * f r) * (a 1 * b 1)
          - (deriv h r * h r) * (a 2 * b 2 + a 3 * b 3),
        (deriv f r / f r) * (a 0 * b 1 + a 1 * b 0),
        (deriv h r / h r) * (a 0 * b 2 + a 2 * b 0),
        (deriv h r / h r) * (a 0 * b 3 + a 3 * b 0)] : Fin 4 → ℝ))
      (![-((deriv^[2] f r0 * f r0 + deriv f r0 ^ 2) * (a 1 * b 1)
          + (deriv^[2] h r0 * h r0 + deriv h r0 ^ 2) * (a 2 * b 2 + a 3 * b 3)),
        ((deriv^[2] f r0 * f r0 - deriv f r0 ^ 2) / f r0 ^ 2) * (a 0 * b 1 + a 1 * b 0),
        ((deriv^[2] h r0 * h r0 - deriv h r0 ^ 2) / h r0 ^ 2) * (a 0 * b 2 + a 2 * b 0),
        ((deriv^[2] h r0 * h r0 - deriv h r0 ^ 2) / h r0 ^ 2) * (a 0 * b 3 + a 3 * b 0)] :
          Fin 4 → ℝ) r0 := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · simpa using hg0
    · simpa using hg1
    · simpa using hg2
    · simpa using hg3
  have hd := ((ContinuousLinearMap.hasFDerivAt e4Lift).comp r0 hF.hasFDerivAt).hasDerivAt
  convert hd using 1
  · funext r
    rfl
  · simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      one_smul]
    rfl

theorem warpedMetric_dBmodel (f h : ℝ → ℝ) (q : E4) (d a b : E4)
    (hf : ContDiff ℝ 2 f) (hh : ContDiff ℝ 2 h) (hf0 : f (q 0) ≠ 0) (hh0 : h (q 0) ≠ 0)
    (hchr : ∀ᶠ q' in nhds q,
      koszulChr (warpedMetric f h) q' a b = chrWarped f h q' a b) :
    dBmodel (warpedMetric f h) q d a b = (d 0) • chrWarpedDeriv f h (q 0) a b := by
  have hG : HasDerivAt (chrWarpedFun f h a b) (chrWarpedDeriv f h (q 0) a b) (q 0) :=
    hasDerivAt_chrWarpedFun f h a b (q 0) hf hh hf0 hh0
  have hcomp := hG.hasFDerivAt.comp q (hasFDerivAt_coord 0 q)
  have hval : fderiv ℝ (fun q' : E4 => chrWarped f h q' a b) q d
      = (d 0) • chrWarpedDeriv f h (q 0) a b := by
    have hfun : (fun q' : E4 => chrWarped f h q' a b)
        = (chrWarpedFun f h a b ∘ fun q' : E4 => q' 0) := by
      funext q'
      rw [Function.comp_apply, chrWarped_eq_chrWarpedFun]
    rw [hfun, hcomp.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      coord_apply]
  show fderiv ℝ (fun q' : E4 => koszulChr (warpedMetric f h) q' a b) q d
      = (d 0) • chrWarpedDeriv f h (q 0) a b
  rw [Filter.EventuallyEq.fderiv_eq hchr]
  exact hval

end

end Work.Curvature
