import Mathlib
import Submission.Work.HypModel.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `polarToCartesian` is an isometry from the warped metric to the flat metric

The polar-to-Cartesian map of the flat core

`polarToCartesian (r,θ,w₁,w₂) = (r cos θ, r sin θ, w₁, w₂)`

identifies the warped metric `dr² + r² dθ² + h₀²(|dw₁|² + |dw₂|²)` with the flat metric
`da² + db² + h₀²(|dw₁|² + |dw₂|²)` in the Cartesian coordinates `(a,b,w₁,w₂)`.  Concretely, for
every `p` and every pair of tangent vectors `v, w`,

`flatMetric h₀ (polarToCartesian p) (d(polarToCartesian)ₚ v) (d(polarToCartesian)ₚ w)
  = dr² + r² dθ² + h₀²(|dw₁|² + |dw₂|²)`

evaluated at `p`.

The computation is purely coordinatewise.  We compute the explicit derivative
`dPolarToCartesian p`, whose coordinates are the linear forms

`v ↦ v₀ cos p₁ − p₀ sin p₁ · v₁`,  `v ↦ v₀ sin p₁ + p₀ cos p₁ · v₁`,  `v ↦ v₂`,  `v ↦ v₃`,

and then the identity reduces to the trigonometric identity `cos² + sin² = 1`:

`(v₀ cos p₁ − p₀ sin p₁ v₁)(w₀ cos p₁ − p₀ sin p₁ w₁)
 + (v₀ sin p₁ + p₀ cos p₁ v₁)(w₀ sin p₁ + p₀ cos p₁ w₁)
 = v₀ w₀ + p₀² v₁ w₁`.
-/

noncomputable section

namespace Work.HypModel

open scoped Matrix InnerProductSpace

/-- The `i`-th coordinate projection of `E4`, as a continuous linear map. -/
abbrev pcCoord (i : Fin 4) : E4 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 4 => ℝ) i

/-- The explicit derivative of `polarToCartesian` at `p`:
`v ↦ (v₀ cos p₁ − p₀ sin p₁ v₁, v₀ sin p₁ + p₀ cos p₁ v₁, v₂, v₃)`. -/
def dPolarToCartesian (p : E4) : E4 →L[ℝ] E4 :=
  LinearMap.toContinuousLinearMap
  { toFun v := !₂[v 0 * Real.cos (p 1) - p 0 * Real.sin (p 1) * v 1,
                 v 0 * Real.sin (p 1) + p 0 * Real.cos (p 1) * v 1,
                 v 2, v 3]
    map_add' v w := by ext i; fin_cases i <;> simp <;> ring
    map_smul' c v := by ext i; fin_cases i <;> simp <;> ring }

@[simp] theorem dPolarToCartesian_apply_zero (p v : E4) :
    dPolarToCartesian p v 0 = v 0 * Real.cos (p 1) - p 0 * Real.sin (p 1) * v 1 := by
  simp [dPolarToCartesian]

@[simp] theorem dPolarToCartesian_apply_one (p v : E4) :
    dPolarToCartesian p v 1 = v 0 * Real.sin (p 1) + p 0 * Real.cos (p 1) * v 1 := by
  simp [dPolarToCartesian]

@[simp] theorem dPolarToCartesian_apply_two (p v : E4) :
    dPolarToCartesian p v 2 = v 2 := by simp [dPolarToCartesian]

@[simp] theorem dPolarToCartesian_apply_three (p v : E4) :
    dPolarToCartesian p v 3 = v 3 := by simp [dPolarToCartesian]

/-- `polarToCartesian` is differentiable everywhere, with the explicit derivative
`dPolarToCartesian p`.  Each of the four coordinate functions
`x ↦ x₀ cos x₁`, `x ↦ x₀ sin x₁`, `x ↦ x₂`, `x ↦ x₃` is differentiated with the product rule,
and the four coordinate derivatives are glued with `hasFDerivWithinAt_euclidean`. -/
theorem hasFDerivAt_polarToCartesian (p : E4) :
    HasFDerivAt polarToCartesian (dPolarToCartesian p) p := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_euclidean]
  intro i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by fin_cases i <;> simp
  rcases hi with h | h | h | h
  · subst h
    have hcos : HasFDerivAt (fun x : E4 => Real.cos (x.ofLp 1))
        (-(Real.sin (p.ofLp 1) • pcCoord 1)) p := by
      have hf : HasFDerivAt (fun x : E4 => x.ofLp 1) (pcCoord 1) p := by
        simpa [pcCoord, PiLp.proj_apply] using
          (ContinuousLinearMap.hasFDerivAt (pcCoord 1) (x := p))
      simpa [Function.comp_def] using
        (Real.hasDerivAt_cos (p.ofLp 1)).comp_hasFDerivAt p hf
    have hx0 : HasFDerivAt (fun x : E4 => x.ofLp 0) (pcCoord 0) p := by
      simpa [pcCoord, PiLp.proj_apply] using
        (ContinuousLinearMap.hasFDerivAt (pcCoord 0) (x := p))
    have h0 : HasFDerivAt (fun x : E4 => x.ofLp 0 * Real.cos (x.ofLp 1))
        (p.ofLp 0 • (-(Real.sin (p.ofLp 1) • pcCoord 1)) + Real.cos (p.ofLp 1) • pcCoord 0) p :=
      hx0.mul hcos
    convert h0.hasFDerivWithinAt using 1
    · funext x; simp [polarToCartesian]
    · ext v
      simp only [ContinuousLinearMap.comp_apply, add_apply, smul_apply, neg_apply, pcCoord,
        PiLp.proj_apply, dPolarToCartesian_apply_zero, smul_eq_mul]
      ring
  · subst h
    have hsin : HasFDerivAt (fun x : E4 => Real.sin (x.ofLp 1))
        (Real.cos (p.ofLp 1) • pcCoord 1) p := by
      have hf : HasFDerivAt (fun x : E4 => x.ofLp 1) (pcCoord 1) p := by
        simpa [pcCoord, PiLp.proj_apply] using
          (ContinuousLinearMap.hasFDerivAt (pcCoord 1) (x := p))
      simpa [Function.comp_def] using
        (Real.hasDerivAt_sin (p.ofLp 1)).comp_hasFDerivAt p hf
    have hx0 : HasFDerivAt (fun x : E4 => x.ofLp 0) (pcCoord 0) p := by
      simpa [pcCoord, PiLp.proj_apply] using
        (ContinuousLinearMap.hasFDerivAt (pcCoord 0) (x := p))
    have h1 : HasFDerivAt (fun x : E4 => x.ofLp 0 * Real.sin (x.ofLp 1))
        (p.ofLp 0 • (Real.cos (p.ofLp 1) • pcCoord 1) + Real.sin (p.ofLp 1) • pcCoord 0) p :=
      hx0.mul hsin
    convert h1.hasFDerivWithinAt using 1
    · funext x; simp [polarToCartesian]
    · ext v
      simp only [ContinuousLinearMap.comp_apply, add_apply, smul_apply, pcCoord,
        PiLp.proj_apply, dPolarToCartesian_apply_one, smul_eq_mul]
      ring
  · subst h
    have hx2 : HasFDerivAt (fun x : E4 => x.ofLp 2) (pcCoord 2) p := by
      simpa [pcCoord, PiLp.proj_apply] using
        (ContinuousLinearMap.hasFDerivAt (pcCoord 2) (x := p))
    convert hx2.hasFDerivWithinAt using 1
    · funext x; simp [polarToCartesian]
    · ext v
      simp only [ContinuousLinearMap.comp_apply, pcCoord, PiLp.proj_apply,
        dPolarToCartesian_apply_two]
  · subst h
    have hx3 : HasFDerivAt (fun x : E4 => x.ofLp 3) (pcCoord 3) p := by
      simpa [pcCoord, PiLp.proj_apply] using
        (ContinuousLinearMap.hasFDerivAt (pcCoord 3) (x := p))
    convert hx3.hasFDerivWithinAt using 1
    · funext x; simp [polarToCartesian]
    · ext v
      simp only [ContinuousLinearMap.comp_apply, pcCoord, PiLp.proj_apply,
        dPolarToCartesian_apply_three]

set_option linter.unusedVariables false in
/-- **The pullback of the flat metric along `polarToCartesian` is the warped metric with `f r = r`
and `h ≡ h₀`.**

For every `p` and tangent vectors `v, w`,
`flatMetric h₀ (polarToCartesian p) (d(polarToCartesian)ₚ v) (d(polarToCartesian)ₚ w)
 = dr² + r² dθ² + h₀²(|dw₁|² + |dw₂|²)` evaluated at `p`. -/
theorem polarToCartesian_isometry {h₀ : ℝ} (hh₀ : 0 < h₀) (p v w : E4) :
    flatMetric h₀ (polarToCartesian p) (fderiv ℝ polarToCartesian p v)
        (fderiv ℝ polarToCartesian p w) =
      warpedMetric (fun r => r) (fun _ => h₀) p v w := by
  rw [show fderiv ℝ polarToCartesian p = dPolarToCartesian p from
    (hasFDerivAt_polarToCartesian p).fderiv]
  simp only [flatMetric, warpedMetric, dPolarToCartesian_apply_zero, dPolarToCartesian_apply_one,
    dPolarToCartesian_apply_two, dPolarToCartesian_apply_three]
  linear_combination (v.ofLp 0 * w.ofLp 0 + p.ofLp 0 ^ 2 * v.ofLp 1 * w.ofLp 1)
    * Real.cos_sq_add_sin_sq (p.ofLp 1)

end Work.HypModel
