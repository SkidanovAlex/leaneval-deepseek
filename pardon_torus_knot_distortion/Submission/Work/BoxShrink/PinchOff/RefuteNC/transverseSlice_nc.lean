import Mathlib
import Submission.Work.BoxShrink.PinchOff.RefuteNC.Config

/-!
# The cutting plane of the `nc` configuration is transverse

The configuration `RefuteNC/Config.lean` (the standard torus `ψ = idDiffeo`, the box
`PBox ncRad ncCtr ncCyc3` and the cutting plane `{x = 1/2}`, i.e. `u = ncU = -1/2`) was designed so
that the residual of the pinch fails at it *while the general-position hypothesis `TransverseSlice`
is in force*.  This module supplies that hypothesis.

In the parameter plane of the standard torus the plane coordinate is

  `planeG idDiffeo ncCtr ncCyc3 ncU (θ, φ) = (2 + cos φ) cos θ - 1/2`  (`planeG_nc`),

so on the slice `{G = 0}` one has `(2 + cos φ) cos θ = 1/2`, hence `cos θ = 1 / (2 (2 + cos φ))`
which lies in `(0, 1/2]` because `2 + cos φ ∈ [1, 3]`.  In particular `cos θ ≠ ±1`, so `sin θ ≠ 0`,
and the directional derivative in the `θ`-direction,

  `∂G/∂θ = -(2 + cos φ) sin θ ≠ 0`,

never vanishes.  Hence `∇G ≠ 0` on the whole slice and `TransverseSlice` holds — in fact without
any use of the box condition `boxB < ncRad`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Work.BoxShrink.PinchOff

namespace Work.BoxShrink.PinchOff.RefuteNC

noncomputable section

/-- **The derivative of the explicit plane coordinate** `(θ, φ) ↦ (2 + cos φ) cos θ - 1/2`. -/
private theorem fderiv_nc_explicit (p : ℝ × ℝ) :
    fderiv ℝ (fun p : ℝ × ℝ => (2 + Real.cos p.2) * Real.cos p.1 - 1/2) p
      = (2 + Real.cos p.2) • ((-Real.sin p.1) • (ContinuousLinearMap.fst ℝ ℝ ℝ))
        + Real.cos p.1 • ((-Real.sin p.2) • (ContinuousLinearMap.snd ℝ ℝ ℝ)) := by
  have hA : HasFDerivAt (fun x : ℝ × ℝ => 2 + Real.cos x.2)
      ((-Real.sin p.2) • (ContinuousLinearMap.snd ℝ ℝ ℝ)) p :=
    ((ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.snd ℝ ℝ ℝ)).cos).const_add 2
  have hB : HasFDerivAt (fun x : ℝ × ℝ => Real.cos x.1)
      ((-Real.sin p.1) • (ContinuousLinearMap.fst ℝ ℝ ℝ)) p :=
    (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.fst ℝ ℝ ℝ)).cos
  exact ((hA.mul hB).sub_const (1/2)).fderiv

/-- **The derivative of the explicit plane coordinate is nonzero on its zero level.**  At a point
`p` with `(2 + cos p.2) cos p.1 = 1/2` the `θ`-derivative `-(2 + cos p.2) sin p.1` is nonzero,
because `2 + cos p.2 ≥ 1` forces `cos p.1 = 1 / (2 (2 + cos p.2)) ∈ (0, 1/2]`, whence
`sin p.1 ≠ 0`. -/
private theorem fderiv_nc_ne (p : ℝ × ℝ)
    (hG : (2 + Real.cos p.2) * Real.cos p.1 - 1/2 = 0) :
    fderiv ℝ (fun p : ℝ × ℝ => (2 + Real.cos p.2) * Real.cos p.1 - 1/2) p ≠ 0 := by
  have hprod : (2 + Real.cos p.2) * Real.cos p.1 = 1/2 := by linarith
  have hpos : (0:ℝ) < 2 + Real.cos p.2 := by nlinarith [Real.neg_one_le_cos p.2]
  have hcos_eq : Real.cos p.1 = 1 / (2 * (2 + Real.cos p.2)) := by
    field_simp at hprod ⊢
    linarith
  have hval : (fderiv ℝ (fun p : ℝ × ℝ => (2 + Real.cos p.2) * Real.cos p.1 - 1/2) p) (1, 0)
      = -(2 + Real.cos p.2) * Real.sin p.1 := by
    rw [fderiv_nc_explicit]; simp; ring
  have hsin : Real.sin p.1 ≠ 0 := by
    intro hs
    have hsq : Real.cos p.1 ^ 2 < 1 := by
      rw [hcos_eq]; rw [div_pow, one_pow, div_lt_one (by positivity)]
      nlinarith [Real.neg_one_le_cos p.2]
    have h := Real.sin_sq_add_cos_sq p.1
    rw [hs] at h
    nlinarith
  intro hzero
  have hz : (fderiv ℝ (fun p : ℝ × ℝ => (2 + Real.cos p.2) * Real.cos p.1 - 1/2) p) (1, 0) = 0 := by
    rw [hzero]; rfl
  rw [hval] at hz
  exact (mul_ne_zero (neg_ne_zero.mpr (ne_of_gt hpos)) hsin) hz

/-- **The cutting plane of the `nc` configuration is transverse along the slice.**  The derivative
of the plane coordinate never vanishes on `{G = 0}` (a fortiori on `{G = 0} ∩ {boxB < ncRad}`),
because its `θ`-derivative is `-(2 + cos p.2) sin p.1 ≠ 0` there. -/
theorem transverseSlice_nc :
    Work.BoxShrink.Pinch.TransverseSlice Work.BoxShrink.PinchOff.idDiffeo
      Work.BoxShrink.PinchOff.ncRad Work.BoxShrink.PinchOff.ncCtr
      Work.BoxShrink.PinchOff.ncCyc3 Work.BoxShrink.PinchOff.ncU := by
  intro p _ hG
  have hfun : Work.BoxShrink.Pinch.planeG idDiffeo ncCtr ncCyc3 ncU
      = fun p : ℝ × ℝ => (2 + Real.cos p.2) * Real.cos p.1 - 1/2 :=
    funext (fun p => Work.BoxShrink.PinchOff.planeG_nc p)
  rw [hfun] at hG ⊢
  exact fderiv_nc_ne p hG

end

end Work.BoxShrink.PinchOff.RefuteNC
