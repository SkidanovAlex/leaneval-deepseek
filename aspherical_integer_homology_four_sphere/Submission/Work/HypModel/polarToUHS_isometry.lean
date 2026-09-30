import Mathlib
import Submission.Work.HypModel.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `polarToUHS` is an isometry from the warped metric to the upper half space metric

The map `polarToUHS C D (r,θ,w₁,w₂) = ((C/D)θ, w₁, w₂, (1/D)e^{−r})` identifies the warped metric
`dr² + (C e^r)² dθ² + (D e^r)²(|dw₁|² + |dw₂|²)` with the upper half space metric
`(|dx|² + ds²)/s²`.  Concretely, we prove that for every `p` and every pair of tangent vectors
`v, w`,

`polarToUHS` is differentiable everywhere, with explicit derivative `dPolarToUHS C D p`; the
pullback of the upper half space metric along it is exactly the warped metric with `f r = C e^r`
and `h r = D e^r`.

The computation is purely coordinatewise: `uhsMetric` is `(q 3)⁻²⟪·,·⟫`, the derivative of
`polarToUHS` is read off coordinate by coordinate (`C/D·v₁`, `v₂`, `v₃`, `−D⁻¹e^{−p₀}v₀`), and the
identity reduces to a rational identity after clearing the denominators `D` and `e^{p₀}`.
-/

noncomputable section

namespace Work.HypModel

open scoped Matrix InnerProductSpace

/-- The `i`-th coordinate projection of `E4`, as a continuous linear map. -/
abbrev coordE4 (i : Fin 4) : E4 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 4 => ℝ) i

/-- The explicit derivative of `polarToUHS C D` at `p`: it kills the vector in the angle direction
(component `0`) and scales the height direction (component `3`) by `−D⁻¹e^{−p₀}`. -/
def dPolarToUHS (C D : ℝ) (p : E4) : E4 →L[ℝ] E4 :=
  LinearMap.toContinuousLinearMap
  { toFun v := !₂[C / D * v 1, v 2, v 3, -(D⁻¹ * Real.exp (-(p 0))) * v 0]
    map_add' v w := by ext i; fin_cases i <;> simp <;> ring
    map_smul' c v := by ext i; fin_cases i <;> simp <;> ring }

@[simp] theorem dPolarToUHS_apply_zero (C D : ℝ) (p v : E4) :
    dPolarToUHS C D p v 0 = C / D * v 1 := by simp [dPolarToUHS]

@[simp] theorem dPolarToUHS_apply_one (C D : ℝ) (p v : E4) :
    dPolarToUHS C D p v 1 = v 2 := by simp [dPolarToUHS]

@[simp] theorem dPolarToUHS_apply_two (C D : ℝ) (p v : E4) :
    dPolarToUHS C D p v 2 = v 3 := by simp [dPolarToUHS]

@[simp] theorem dPolarToUHS_apply_three (C D : ℝ) (p v : E4) :
    dPolarToUHS C D p v 3 = -(D⁻¹ * Real.exp (-(p 0))) * v 0 := by simp [dPolarToUHS]

@[simp] theorem polarToUHS_apply_zero (C D : ℝ) (p : E4) :
    polarToUHS C D p 0 = C / D * p 1 := by simp [polarToUHS]

@[simp] theorem polarToUHS_apply_one (C D : ℝ) (p : E4) :
    polarToUHS C D p 1 = p 2 := by simp [polarToUHS]

@[simp] theorem polarToUHS_apply_two (C D : ℝ) (p : E4) :
    polarToUHS C D p 2 = p 3 := by simp [polarToUHS]

@[simp] theorem polarToUHS_apply_three (C D : ℝ) (p : E4) :
    polarToUHS C D p 3 = D⁻¹ * Real.exp (-(p 0)) := by simp [polarToUHS]

/-- `polarToUHS C D` is differentiable everywhere, with the explicit derivative `dPolarToUHS C D p`.

The proof goes through `hasFDerivWithinAt_euclidean`: a function into `EuclideanSpace ℝ (Fin 4)` is
differentiable iff each of its coordinates is, and the four coordinate functions
`x ↦ C/D·x₁`, `x ↦ x₂`, `x ↦ x₃`, `x ↦ D⁻¹e^{−x₀}` have derivatives
`(C/D)·∂₁`, `∂₂`, `∂₃`, `−(D⁻¹e^{−p₀})·∂₀`. -/
theorem hasFDerivAt_polarToUHS (C D : ℝ) (p : E4) :
    HasFDerivAt (polarToUHS C D) (dPolarToUHS C D p) p := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_euclidean]
  intro i
  fin_cases i
  · have h0 : HasFDerivAt (fun x : E4 => C / D * x.ofLp 1) ((C / D) • (coordE4 1)) p := by
      have h : HasFDerivAt (fun x : E4 => (C / D) • (coordE4 1) x) ((C / D) • (coordE4 1)) p :=
        (ContinuousLinearMap.hasFDerivAt (coordE4 1)).const_smul (C / D)
      simpa [coordE4, smul_eq_mul, PiLp.proj_apply] using h
    convert h0.hasFDerivWithinAt using 1
    · funext x; simp [polarToUHS]
    · ext v; simp [dPolarToUHS, coordE4, PiLp.proj_apply]
  · have h1 : HasFDerivAt (fun x : E4 => x.ofLp 2) (coordE4 2) p := by
      simpa [coordE4, PiLp.proj_apply] using
        (ContinuousLinearMap.hasFDerivAt (coordE4 2) (x := p))
    convert h1.hasFDerivWithinAt using 1
    · funext x; simp [polarToUHS]
    · ext v; simp [dPolarToUHS, coordE4, PiLp.proj_apply]
  · have h2 : HasFDerivAt (fun x : E4 => x.ofLp 3) (coordE4 3) p := by
      simpa [coordE4, PiLp.proj_apply] using
        (ContinuousLinearMap.hasFDerivAt (coordE4 3) (x := p))
    convert h2.hasFDerivWithinAt using 1
    · funext x; simp [polarToUHS]
    · ext v; simp [dPolarToUHS, coordE4, PiLp.proj_apply]
  · have hneg : HasFDerivAt (fun x : E4 => -(x.ofLp 0)) (-(coordE4 0)) p :=
      (ContinuousLinearMap.hasFDerivAt (coordE4 0)).neg
    have hexp : HasFDerivAt (fun x : E4 => Real.exp (-(x.ofLp 0)))
        (Real.exp (-(p.ofLp 0)) • (-(coordE4 0))) p := hneg.exp
    have h : HasFDerivAt (fun x : E4 => D⁻¹ * Real.exp (-(x.ofLp 0)))
        (D⁻¹ • (Real.exp (-(p.ofLp 0)) • (-(coordE4 0)))) p := hexp.const_smul (D⁻¹)
    have h3 : HasFDerivAt (fun x : E4 => D⁻¹ * Real.exp (-(x.ofLp 0)))
        (-(D⁻¹ * Real.exp (-(p.ofLp 0))) • (coordE4 0)) p := by
      convert h using 1
      ext v
      simp only [smul_apply, neg_apply, coordE4, PiLp.proj_apply]
      ring
    convert h3.hasFDerivWithinAt using 1
    · funext x; simp [polarToUHS]
    · ext v; simp [dPolarToUHS, coordE4, PiLp.proj_apply]

set_option linter.unusedVariables false in
/-- **The pullback of the upper half space metric along `polarToUHS` is the warped metric.**

For every `p` and tangent vectors `v, w`,
`uhsMetric (polarToUHS C D p) (d(polarToUHS)ₚ v) (d(polarToUHS)ₚ w) = dr² + (C eʳ)² dθ² +
(D eʳ)²(|dw₁|² + |dw₂|²)` evaluated at `p`. -/
theorem polarToUHS_isometry {C D : ℝ} (hC : 0 < C) (hD : 0 < D) (p v w : E4) :
    uhsMetric (polarToUHS C D p) (fderiv ℝ (polarToUHS C D) p v)
        (fderiv ℝ (polarToUHS C D) p w) =
      warpedMetric (fun r => C * Real.exp r) (fun r => D * Real.exp r) p v w := by
  rw [show fderiv ℝ (polarToUHS C D) p = dPolarToUHS C D p from
    (hasFDerivAt_polarToUHS C D p).fderiv]
  simp only [uhsMetric_apply, warpedMetric, PiLp.inner_apply, Fin.sum_univ_four,
    polarToUHS_apply_three, dPolarToUHS_apply_zero, dPolarToUHS_apply_one,
    dPolarToUHS_apply_two, dPolarToUHS_apply_three,
    Real.exp_neg, RCLike.inner_apply, Real.ringHom_apply]
  field_simp [hC.ne', hD.ne', Real.exp_ne_zero]
  ring

end Work.HypModel
