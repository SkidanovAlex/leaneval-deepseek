/-
# The polar change of the flat model (v3)

The polar map `polarMap q = (q₀ cos q₁, q₀ sin q₁, q₂, q₃)` of `E4 = ℝ⁴` (the standard polar
coordinates of the filling, blueprint §1) is an isometry between the *flat* metric
`diag(1, q₀², h₀², h₀²)` of the polar chart and the flat Cartesian metric
`diag(1, 1, h₀², h₀²)` of the core chart: pulling back `flatModel h₀` along `polarMap` gives the
quadratic form `diagQuad ![1, q₀², h₀², h₀²]`.

This is the coordinate computation behind the fact that the polar charts of the filling carry the
pullback of the flat metric — the two middle coordinates transform by `(dx)² + (dy)² =
dr² + r²dθ²`, while the `w`-coordinates are unchanged.

The derivative of `polarMap` is computed explicitly (`polarDeriv`, with the chain rule,
`hasFDerivAt_pi` and the commutation of `hasFDerivAt` with the linear isometry
`PiLp p β ≃L (∀ i, β i)`), and the trigonometric identity
`(c a - r s b)(c d - r s e) + (s a + r c b)(s d + r c e) = a d + r² b e` (for `c² + s² = 1`)
finishes the computation.
-/
import Mathlib
import Submission.Work.RTInstance.Models

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOWed

noncomputable section

open Work.RTInstance

/-- The chart space `ℝ⁴` of the project. -/
private abbrev E4 := Work.Cusp.E4

/-- **The polar map** `(r, θ, w₁, w₂) ↦ (r cos θ, r sin θ, w₁, w₂)`. -/
private def polarMap : E4 → E4 :=
  fun q => !₂[q 0 * Real.cos (q 1), q 0 * Real.sin (q 1), q 2, q 3]

/-- **The derivative of `polarMap`**: in coordinates,
`(u₀, u₁, u₂, u₃) ↦ (cos q₁ · u₀ - q₀ sin q₁ · u₁, sin q₁ · u₀ + q₀ cos q₁ · u₁, u₂, u₃)`. -/
private noncomputable def polarDeriv (q : E4) : E4 →L[ℝ] E4 :=
  ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm : (Fin 4 → ℝ) →L[ℝ] E4).comp
    (ContinuousLinearMap.pi ![
      Real.cos (q 1) • coord4 0 + (-(q 0 * Real.sin (q 1))) • coord4 1,
      Real.sin (q 1) • coord4 0 + (q 0 * Real.cos (q 1)) • coord4 1,
      coord4 2, coord4 3])

private lemma polarDeriv_ofLp_0 (q u : E4) :
    (polarDeriv q u).ofLp 0 = Real.cos (q 1) * u 0 - q 0 * Real.sin (q 1) * u 1 := by
  simp [polarDeriv]
  ring

private lemma polarDeriv_ofLp_1 (q u : E4) :
    (polarDeriv q u).ofLp 1 = Real.sin (q 1) * u 0 + q 0 * Real.cos (q 1) * u 1 := by
  simp [polarDeriv]

private lemma polarDeriv_ofLp_2 (q u : E4) : (polarDeriv q u).ofLp 2 = u 2 := by
  simp [polarDeriv]

private lemma polarDeriv_ofLp_3 (q u : E4) : (polarDeriv q u).ofLp 3 = u 3 := by
  simp [polarDeriv]

/-- The coordinate functions are differentiable. -/
private lemma hasFDerivAt_coord4 (i : Fin 4) (q : E4) :
    HasFDerivAt (fun q : E4 => q i) (coord4 i) q := by
  have h : (fun q : E4 => q i) = ⇑(coord4 i) := by funext q; rw [coord4_apply]
  rw [h]
  exact (coord4 i).hasFDerivAt

/-- The product rule at the first coordinate `q₀ cos q₁` of `polarMap`. -/
private lemma hasFDerivAt_polarMap_c0 (q : E4) :
    HasFDerivAt (fun q : E4 => q 0 * Real.cos (q 1))
      (Real.cos (q 1) • coord4 0 + (-(q 0 * Real.sin (q 1))) • coord4 1) q := by
  have h1 : HasFDerivAt (fun q : E4 => q 0) (coord4 0) q := hasFDerivAt_coord4 0 q
  have h2 : HasFDerivAt (fun q : E4 => Real.cos (q 1)) (-(Real.sin (q 1)) • coord4 1) q := by
    have hc : HasDerivAt Real.cos (-Real.sin (q 1)) (q 1) := Real.hasDerivAt_cos (q 1)
    exact hc.comp_hasFDerivAt q (hasFDerivAt_coord4 1 q)
  have hm := h1.mul h2
  have hD : ((q 0) • (-(Real.sin (q 1)) • coord4 1) + Real.cos (q 1) • coord4 0)
      = (Real.cos (q 1) • coord4 0 + (-(q 0 * Real.sin (q 1))) • coord4 1) := by
    ext w; simp [coord4_apply]; ring
  rw [hD] at hm
  exact hm

/-- The product rule at the second coordinate `q₀ sin q₁` of `polarMap`. -/
private lemma hasFDerivAt_polarMap_c1 (q : E4) :
    HasFDerivAt (fun q : E4 => q 0 * Real.sin (q 1))
      (Real.sin (q 1) • coord4 0 + (q 0 * Real.cos (q 1)) • coord4 1) q := by
  have h1 : HasFDerivAt (fun q : E4 => q 0) (coord4 0) q := hasFDerivAt_coord4 0 q
  have h2 : HasFDerivAt (fun q : E4 => Real.sin (q 1)) (Real.cos (q 1) • coord4 1) q := by
    have hc : HasDerivAt Real.sin (Real.cos (q 1)) (q 1) := Real.hasDerivAt_sin (q 1)
    exact hc.comp_hasFDerivAt q (hasFDerivAt_coord4 1 q)
  have hm := h1.mul h2
  have hD : ((q 0) • (Real.cos (q 1) • coord4 1) + Real.sin (q 1) • coord4 0)
      = (Real.sin (q 1) • coord4 0 + (q 0 * Real.cos (q 1)) • coord4 1) := by
    ext w; simp [coord4_apply]; ring
  rw [hD] at hm
  exact hm

/-- The derivative of the four-component tuple `![q₀ cos q₁, q₀ sin q₁, q₂, q₃]`, assembled from
the coordinate derivatives by `hasFDerivAt_pi`. -/
private lemma hasFDerivAt_polarMap_pi (q : E4) :
    HasFDerivAt (fun q : E4 => (![q 0 * Real.cos (q 1), q 0 * Real.sin (q 1), q 2, q 3] : Fin 4 → ℝ))
      (ContinuousLinearMap.pi ![
        Real.cos (q 1) • coord4 0 + (-(q 0 * Real.sin (q 1))) • coord4 1,
        Real.sin (q 1) • coord4 0 + (q 0 * Real.cos (q 1)) • coord4 1,
        coord4 2, coord4 3]) q := by
  rw [hasFDerivAt_pi]
  intro i
  fin_cases i
  · exact hasFDerivAt_polarMap_c0 q
  · exact hasFDerivAt_polarMap_c1 q
  · exact hasFDerivAt_coord4 2 q
  · exact hasFDerivAt_coord4 3 q

/-- **`polarMap` is differentiable at every point, with derivative `polarDeriv q`.** -/
private lemma hasFDerivAt_polarMap (q : E4) : HasFDerivAt polarMap (polarDeriv q) q := by
  have hcomp := (ContinuousLinearEquiv.hasFDerivAt
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm).comp q (hasFDerivAt_polarMap_pi q)
  exact hcomp

/-- **The trigonometric identity of the polar change**: if `c² + s² = 1`, then
`(ca - rsb)(cd - rse) + (sa + rcb)(sd + rce) = ad + r²be`.  This is `(dx)² + (dy)² = dr² + r²dθ²`
read in the four coordinates `a, b, d, e`. -/
private lemma trig_id (r c s a b d e : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    (c * a - r * s * b) * (c * d - r * s * e) + (s * a + r * c * b) * (s * d + r * c * e)
      = a * d + r ^ 2 * b * e := by
  have hc : c ^ 2 = 1 - s ^ 2 := by linarith
  ring_nf
  rw [hc]
  ring

private lemma consQ_0 (q : E4) (h₀ : ℝ) : (![1, q 0 ^ 2, h₀ ^ 2, h₀ ^ 2] : Fin 4 → ℝ) 0 = 1 := by simp

private lemma consQ_1 (q : E4) (h₀ : ℝ) :
    (![1, q 0 ^ 2, h₀ ^ 2, h₀ ^ 2] : Fin 4 → ℝ) 1 = q 0 ^ 2 := by simp

private lemma consQ_2 (q : E4) (h₀ : ℝ) :
    (![1, q 0 ^ 2, h₀ ^ 2, h₀ ^ 2] : Fin 4 → ℝ) 2 = h₀ ^ 2 := by simp

private lemma consQ_3 (q : E4) (h₀ : ℝ) :
    (![1, q 0 ^ 2, h₀ ^ 2, h₀ ^ 2] : Fin 4 → ℝ) 3 = h₀ ^ 2 := by simp

/-- **The flat model in polar coordinates**: pulling `flatModel h₀` back along the polar map
gives the flat model in the Cartesian core coordinates. -/
theorem flatModel_polar_change (h₀ : ℝ) (q u v : Work.Cusp.E4) :
    Work.RTInstance.flatModel h₀ (!₂[q 0 * Real.cos (q 1), q 0 * Real.sin (q 1), q 2, q 3])
        (fderiv ℝ (fun q : Work.Cusp.E4 => !₂[q 0 * Real.cos (q 1), q 0 * Real.sin (q 1), q 2, q 3]) q u)
        (fderiv ℝ (fun q : Work.Cusp.E4 => !₂[q 0 * Real.cos (q 1), q 0 * Real.sin (q 1), q 2, q 3]) q v)
      = Work.RTInstance.diagQuad ![1, q 0 ^ 2, h₀ ^ 2, h₀ ^ 2] u v := by
  change flatModel h₀ (polarMap q) (fderiv ℝ polarMap q u) (fderiv ℝ polarMap q v)
      = diagQuad ![1, q 0 ^ 2, h₀ ^ 2, h₀ ^ 2] u v
  rw [(hasFDerivAt_polarMap q).fderiv]
  simp only [flatModel_apply, diagQuad_apply, polarDeriv_ofLp_0, polarDeriv_ofLp_1,
    polarDeriv_ofLp_2, polarDeriv_ofLp_3, consQ_0, consQ_1, consQ_2, consQ_3]
  rw [trig_id (q 0) (Real.cos (q 1)) (Real.sin (q 1)) (u 0) (u 1) (v 0) (v 1)
    (Real.cos_sq_add_sin_sq (q 1))]
  ring

end

end Work.RTOWed

/-! ### The same lemma under the path-derived namespace

The module of this file is `Submission.Work.RTOwed.flatModel_polar_change` (the file lives in the
directory `RTOwed`), so the path-derived namespace of the declaration is `Work.RTOwed`.  The
requested statement uses the namespace `Work.RTOWed` (and is declared above, unchanged); for
convenience both names are provided, the second being a one-line restatement of the first. -/
namespace Work.RTOwed

theorem flatModel_polar_change (h₀ : ℝ) (q u v : Work.Cusp.E4) :
    Work.RTInstance.flatModel h₀ (!₂[q 0 * Real.cos (q 1), q 0 * Real.sin (q 1), q 2, q 3])
        (fderiv ℝ (fun q : Work.Cusp.E4 => !₂[q 0 * Real.cos (q 1), q 0 * Real.sin (q 1), q 2, q 3]) q u)
        (fderiv ℝ (fun q : Work.Cusp.E4 => !₂[q 0 * Real.cos (q 1), q 0 * Real.sin (q 1), q 2, q 3]) q v)
      = Work.RTInstance.diagQuad ![1, q 0 ^ 2, h₀ ^ 2, h₀ ^ 2] u v :=
  Work.RTOWed.flatModel_polar_change h₀ q u v

end Work.RTOwed
