import Mathlib
import Submission.Work.Drive.Mono.Geom2Defs
import Submission.Work.Smooth.Morse.Immersion
import Submission.Work.Smooth.BoxGeneric.Vertex.fderiv_torusLevel
import Submission.Work.Smooth.BoxGeneric.Vertex.torus_combination_of_tangential

/-!
# A critical point of the swept height on the knot's trace

`Work.Drive.Mono.knotCritLevels_null` shows that for a.e. half-width `h` of the tilted slab the knot
has no critical point of its tilted height at the two faces.  This file supplies the *analytic* input
of the complementary statement (`offK` of `Work.Drive.Mono.Geom2Data`): **if the knot's trace passes
through a parameter point `p₀` where the swept height `sweepHeight ψ ℓ` is critical, then the height
`ℓ` is critical along the knot at that time.**

The mathematical content is the tangency of a smooth curve lying on the surface:
`K.curve` is a `C^∞` curve whose range is contained in the carrier of the parametrised torus
`F = ψ(standard torus)`, hence its velocity at `t₀` is a **tangent vector of `F`**; and a critical
point of `ℓ|_F` in the parameter plane is a point where `ℓ` annihilates the whole tangent plane
`d(param ψ)_{p₀}(ℝ²)`.

The tangency is proved without any manifold theory, as in
`Work.Smooth.BoxGeneric.Vertex.vertexDir_mem_fderiv_range_of_not_isolated`: the surface is the zero
set of the explicit polynomial

`surfLevel y = (‖y‖² + 3)² - 16 (y₀² + y₁²)`

(the `torusLevel` of that file, reproved here since it is `private` there), so after transporting by
`ψ⁻¹` the curve `t ↦ surfLevel (ψ⁻¹ (K.curve t))` vanishes identically; its derivative at `t₀` is
zero, and the chain rule identifies that derivative with `d(surfLevel)_{y₀} (d(ψ⁻¹)_{x₀} v)`, where
`v = deriv K.curve t₀` and `y₀ = torusMap p₀`.  The explicit derivative
`Work.Smooth.BoxGeneric.Vertex.fderiv_torusLevel` turns this into the single scalar (normal) equation
solved by `Work.Smooth.BoxGeneric.Vertex.torus_combination_of_tangential`, which exhibits `v` as
`d(param ψ)_{p₀}` of an explicit parameter direction.

## Contents

* `surfLevel_torusMap_eq_zero` — the standard torus lies in the zero set of `surfLevel`;
* `surfLevel_invFun_eq_zero` — so does the carrier, after `ψ⁻¹`;
* `exists_tangentDir_eq_deriv_of_mem_carrier` — **the velocity of a smooth curve on the surface is a
  tangent vector**;
* `knot_deriv_of_sweepHeight_crit` — the target lemma.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Drive.Mono

noncomputable section

/-- The level function of the standard torus of revolution of major radius `2` and minor radius `1`:
the polynomial `(‖y‖² + 3)² - 16 (y₀² + y₁²)`, whose zero set is that torus.  Unlike
`(√(y₀² + y₁²) - 2)² + y₂² - 1` it is smooth on all of `ℝ³`. -/
private abbrev surfLevel : R3 → ℝ :=
  fun y => (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 + 3) ^ 2 - 16 * (y 0 ^ 2 + y 1 ^ 2)

private theorem surfLevel_contDiff : ContDiff ℝ (⊤ : ℕ∞) surfLevel := by
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun y : R3 => (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 + 3) ^ 2 - 16 * (y 0 ^ 2 + y 1 ^ 2))
  fun_prop

/-- **The standard torus of revolution lies in the zero set of `surfLevel`**: along the
parametrisation `torusMap u v` the level function vanishes, because `‖torusMap u v‖² + 3` takes the
value `4 (2 + cos v)`. -/
private theorem surfLevel_torusMap_eq_zero (u v : ℝ) : surfLevel (Work.Core.torusMap u v) = 0 := by
  rw [surfLevel, Work.Core.torusMap_apply_zero, Work.Core.torusMap_apply_one,
    Work.Core.torusMap_apply_two]
  have h1 : ((2 + Real.cos v) * Real.cos u) ^ 2 + ((2 + Real.cos v) * Real.sin u) ^ 2
      = (2 + Real.cos v) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq u]
  have h2 : (2 + Real.cos v) ^ 2 + Real.sin v ^ 2 + 3 = 4 * (2 + Real.cos v) := by
    nlinarith [Real.sin_sq_add_cos_sq v]
  rw [h1, h2]
  ring

/-- **The carrier of the torus of the challenge lies in the zero set of `surfLevel ∘ ψ⁻¹`.** -/
private theorem surfLevel_invFun_eq_zero {ψ : Submission.Diffeo} {x : R3}
    (hx : x ∈ (Work.Smooth.Morse.torus ψ).carrier) : surfLevel (ψ.invFun x) = 0 := by
  rw [Work.Smooth.Morse.torus_carrier] at hx
  obtain ⟨p, hp⟩ := Set.mem_range.mp hx
  have hpx : ψ.invFun x = Work.Core.torusMap p.1 p.2 := by
    rw [← hp]; exact ψ.left_inv _
  rw [hpx]
  exact surfLevel_torusMap_eq_zero p.1 p.2

/-- **The velocity of a smooth curve lying on the surface `F = ψ(standard torus)` is a tangent
vector of `F`.**  If `γ` is `C^∞`, its range is contained in the carrier of `torus ψ`, and it passes
through the point parametrised by `p₀` at time `t₀`, then `deriv γ t₀` is the image under
`fderiv ℝ (param ψ) p₀` of some parameter direction.

The proof is the one of
`Work.Smooth.BoxGeneric.Vertex.vertexDir_mem_fderiv_range_of_not_isolated`: `surfLevel ∘ ψ⁻¹`
vanishes on the surface, so the derivative of `t ↦ surfLevel (ψ⁻¹ (γ t))` at `t₀` vanishes; the
explicit derivative of `surfLevel` makes this the equation of the tangent plane of the standard
torus, solved by `torus_combination_of_tangential`. -/
theorem exists_tangentDir_eq_deriv_of_mem_carrier (ψ : Submission.Diffeo) (γ : ℝ → R3)
    (hγ : ContDiff ℝ (⊤ : ℕ∞) γ)
    (hsub : ∀ t : ℝ, γ t ∈ (Work.Smooth.Morse.torus ψ).carrier)
    (t₀ : ℝ) {p₀ : ℝ × ℝ} (hp : γ t₀ = Work.Smooth.Morse.param ψ p₀) :
    ∃ r : ℝ × ℝ, fderiv ℝ (Work.Smooth.Morse.param ψ) p₀ r = deriv γ t₀ := by
  classical
  have hx₀ : γ t₀ = ψ (Work.Core.torusMap p₀.1 p₀.2) := by rw [hp]; rfl
  have hinv : ψ.invFun (γ t₀) = Work.Core.torusMap p₀.1 p₀.2 := by rw [hx₀, ψ.left_inv]
  have hγd : HasDerivAt γ (deriv γ t₀) t₀ :=
    ((hγ.differentiable (by simp)).differentiableAt).hasDerivAt
  have hψinv : HasFDerivAt ψ.invFun (fderiv ℝ ψ.invFun (γ t₀)) (γ t₀) :=
    (ψ.smooth_invFun.hasStrictFDerivAt (by simp)).hasFDerivAt
  have hcomp1 : HasDerivAt (fun t => ψ.invFun (γ t))
      ((fderiv ℝ ψ.invFun (γ t₀)) (deriv γ t₀)) t₀ := hψinv.comp_hasDerivAt t₀ hγd
  have hL : HasFDerivAt surfLevel (fderiv ℝ surfLevel (ψ.invFun (γ t₀))) (ψ.invFun (γ t₀)) :=
    (surfLevel_contDiff.hasStrictFDerivAt (by simp)).hasFDerivAt
  have hcomp2 : HasDerivAt (fun t => surfLevel (ψ.invFun (γ t)))
      ((fderiv ℝ surfLevel (ψ.invFun (γ t₀)))
        ((fderiv ℝ ψ.invFun (γ t₀)) (deriv γ t₀))) t₀ :=
    hL.comp_hasDerivAt (l := surfLevel) t₀ hcomp1
  have hzero : ∀ t : ℝ, surfLevel (ψ.invFun (γ t)) = 0 :=
    fun t => surfLevel_invFun_eq_zero (hsub t)
  -- the derivative of the identically vanishing composite is zero
  have hval : (fderiv ℝ surfLevel (ψ.invFun (γ t₀)))
      ((fderiv ℝ ψ.invFun (γ t₀)) (deriv γ t₀)) = 0 := by
    have h1 := hcomp2.deriv
    have h2 : deriv (fun t => surfLevel (ψ.invFun (γ t))) t₀ = 0 := by
      have : (fun t => surfLevel (ψ.invFun (γ t))) = fun _ => (0 : ℝ) := funext hzero
      rw [this, deriv_const]
    rw [← h1, h2]
  rw [hinv] at hval
  set w : R3 := (fderiv ℝ ψ.invFun (γ t₀)) (deriv γ t₀) with hw
  have hker : fderiv ℝ surfLevel (Work.Core.torusMap p₀.1 p₀.2) w = 0 := hval
  -- the explicit derivative of `surfLevel` at a point of the torus
  have hformula : fderiv ℝ surfLevel (Work.Core.torusMap p₀.1 p₀.2) w =
      16 * (2 + Real.cos p₀.2) *
        (Real.cos p₀.2 * (w 0 * Real.cos p₀.1 + w 1 * Real.sin p₀.1)
          + Real.sin p₀.2 * w 2) := by
    change fderiv ℝ (fun y : R3 => (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 + 3) ^ 2
        - 16 * (y 0 ^ 2 + y 1 ^ 2)) (Work.Core.torusMap p₀.1 p₀.2) w = _
    rw [Work.Smooth.BoxGeneric.Vertex.fderiv_torusLevel]
    have hD : (Work.Core.torusMap p₀.1 p₀.2) 0 ^ 2 + (Work.Core.torusMap p₀.1 p₀.2) 1 ^ 2
        + (Work.Core.torusMap p₀.1 p₀.2) 2 ^ 2 + 3 = 4 * (2 + Real.cos p₀.2) := by
      rw [Work.Core.torusMap_apply_zero, Work.Core.torusMap_apply_one, Work.Core.torusMap_apply_two]
      nlinarith [Real.sin_sq_add_cos_sq p₀.1, Real.sin_sq_add_cos_sq p₀.2]
    rw [hD, Work.Core.torusMap_apply_zero, Work.Core.torusMap_apply_one,
      Work.Core.torusMap_apply_two]
    ring
  -- the scalar (normal) equation of the tangent plane
  have hbracket : Real.cos p₀.2 * (w 0 * Real.cos p₀.1 + w 1 * Real.sin p₀.1)
      + Real.sin p₀.2 * w 2 = 0 := by
    have hpos : (0 : ℝ) < 16 * (2 + Real.cos p₀.2) := by
      have h := Real.neg_one_le_cos p₀.2; linarith
    have h0 : 16 * (2 + Real.cos p₀.2) *
        (Real.cos p₀.2 * (w 0 * Real.cos p₀.1 + w 1 * Real.sin p₀.1)
          + Real.sin p₀.2 * w 2) = 0 := by
      rw [← hformula, hker]
    exact (mul_eq_zero.mp h0).resolve_left (ne_of_gt hpos)
  have hz : (2 + Real.cos p₀.2 - 2) ^ 2 + Real.sin p₀.2 ^ 2 = 1 := by
    have h := Real.sin_sq_add_cos_sq p₀.2
    nlinarith [h]
  have hbracket' : (2 + Real.cos p₀.2 - 2) * (w 0 * Real.cos p₀.1 + w 1 * Real.sin p₀.1)
      + Real.sin p₀.2 * w 2 = 0 := by
    rw [show (2 : ℝ) + Real.cos p₀.2 - 2 = Real.cos p₀.2 by ring]
    exact hbracket
  have hρpos : (0 : ℝ) < 2 + Real.cos p₀.2 := by
    have h := Real.neg_one_le_cos p₀.2; linarith
  obtain ⟨r₁, r₂, hr1, hr2, hr3⟩ := Work.Smooth.BoxGeneric.Vertex.torus_combination_of_tangential
    (ρ := 2 + Real.cos p₀.2) (z := Real.sin p₀.2) (u := p₀.1)
    (w0 := w 0) (w1 := w 1) (w2 := w 2) hρpos hz hbracket'
  -- `w` is the image of the parameter direction `(r₁, r₂)` under the differential of the
  -- parametrisation of the standard torus
  have htd : Work.Smooth.Morse.torusDeriv p₀ (r₁, r₂) = w := by
    rw [Work.Smooth.Morse.torusDeriv_apply, WithLp.ext_iff]
    funext i
    fin_cases i
    · simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Work.Smooth.Morse.dtheta, Work.Smooth.Morse.dphi, ↓reduceIte, neg_mul]
      exact hr1
    · simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Work.Smooth.Morse.dtheta, Work.Smooth.Morse.dphi, ↓reduceIte, neg_mul]
      exact hr2
    · simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Work.Smooth.Morse.dtheta, Work.Smooth.Morse.dphi, ↓reduceIte, reduceCtorEq, neg_mul]
      split_ifs with h
      · exact absurd h (by decide)
      · have h3' : r₂ * Real.cos p₀.2 = w 2 := by
          have h3 := hr3
          rw [show (2 : ℝ) + Real.cos p₀.2 - 2 = Real.cos p₀.2 by ring] at h3
          exact h3
        rw [h3']
        simp
  -- the derivative of `ψ` inverts the derivative of `ψ⁻¹`
  have hright : (fderiv ℝ (ψ : R3 → R3) (Work.Core.torusMap p₀.1 p₀.2)).comp
      (fderiv ℝ ψ.invFun (γ t₀)) = ContinuousLinearMap.id ℝ R3 := by
    have hmain : HasFDerivAt (fun y : R3 => ψ (ψ.invFun y))
        ((fderiv ℝ (ψ : R3 → R3) (Work.Core.torusMap p₀.1 p₀.2)).comp
          (fderiv ℝ ψ.invFun (γ t₀))) (γ t₀) := by
      have hψ2 : HasFDerivAt (fun y : R3 => ψ y)
          (fderiv ℝ (ψ : R3 → R3) (ψ.invFun (γ t₀))) (ψ.invFun (γ t₀)) :=
        (ψ.smooth_toFun.hasStrictFDerivAt (by simp)).hasFDerivAt
      have hcomp := hψ2.comp (γ t₀) hψinv
      rw [hinv] at hcomp
      exact hcomp
    have hid : (fun y : R3 => ψ (ψ.invFun y)) = id := funext fun y => ψ.right_inv y
    rw [hid] at hmain
    exact hmain.unique (hasFDerivAt_id (γ t₀))
  have hw_eq : fderiv ℝ (ψ : R3 → R3) (Work.Core.torusMap p₀.1 p₀.2) w = deriv γ t₀ := by
    have h := congrArg (fun (L : R3 →L[ℝ] R3) => L (deriv γ t₀)) hright
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, ← hw] using h
  -- assemble
  refine ⟨(r₁, r₂), ?_⟩
  rw [Work.Smooth.Morse.fderiv_param ψ p₀, ContinuousLinearMap.comp_apply, htd]
  exact hw_eq

/-- **A critical point of the swept height on the trace of the knot is a critical point of the knot's
height.**

If the smooth knot `K` has its trace on the surface `F = ψ(standard torus)` and passes through the
point parametrised by `p₀` at time `t₀`, and if `p₀` is a critical point of the swept height
`p ↦ ℓ (param ψ p)`, then the height `t ↦ ℓ (K.curve t)` has vanishing derivative at `t₀`.

Indeed, by `exists_tangentDir_eq_deriv_of_mem_carrier` the velocity `deriv K.curve t₀` is a tangent
vector `fderiv ℝ (param ψ) p₀ r`, and the criticality says that `ℓ` annihilates the whole tangent
plane at `p₀`; the chain rule finishes. -/
theorem knot_deriv_of_sweepHeight_crit
    (ψ : Submission.Diffeo) (K : LeanEval.KnotTheory.PardonDistortion.Knot)
    (ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ)
    (hsub : Set.range K.curve ⊆ (Work.Drive.EpsSphere.torusOf ψ).carrier)
    {t₀ : ℝ} {p₀ : ℝ × ℝ}
    (hp : K.curve t₀ = Work.BoxShrink.Pinch.par ψ p₀)
    (hcrit : fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p₀ = 0) :
    deriv (fun t : ℝ => ℓ (K.curve t)) t₀ = 0 := by
  classical
  have hp' : K.curve t₀ = Work.Smooth.Morse.param ψ p₀ := hp
  -- the tangency of the knot at `t₀`
  obtain ⟨r, hr⟩ := exists_tangentDir_eq_deriv_of_mem_carrier ψ K.curve K.smooth
    (fun t => hsub ⟨t, rfl⟩) t₀ hp'
  -- the chain rule for `ℓ ∘ K.curve`
  have hKd : HasDerivAt K.curve (deriv K.curve t₀) t₀ :=
    ((K.smooth.differentiable (by simp)).differentiableAt).hasDerivAt
  have hcc : HasDerivAt (fun t : ℝ => ℓ (K.curve t)) (ℓ (deriv K.curve t₀)) t₀ :=
    (ContinuousLinearMap.hasFDerivAt ℓ).comp_hasDerivAt (l := ℓ) t₀ hKd
  -- the derivative of the swept height
  have hpard : HasFDerivAt (Work.Smooth.Morse.param ψ)
      (fderiv ℝ (Work.Smooth.Morse.param ψ) p₀) p₀ :=
    ((Work.Smooth.Morse.param_contDiff ψ).differentiable (by simp)).differentiableAt.hasFDerivAt
  have hd : HasFDerivAt (fun p : ℝ × ℝ => ℓ (Work.Smooth.Morse.param ψ p))
      (ℓ.comp (fderiv ℝ (Work.Smooth.Morse.param ψ) p₀)) p₀ :=
    (ContinuousLinearMap.hasFDerivAt ℓ).comp p₀ hpard
  have hfd : fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p₀ =
      ℓ.comp (fderiv ℝ (Work.Smooth.Morse.param ψ) p₀) := hd.fderiv
  -- `ℓ` vanishes in the tangent direction
  have h0 : (fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p₀) r = 0 := by rw [hcrit]; rfl
  rw [hfd, ContinuousLinearMap.comp_apply] at h0
  have hℓ0 : ℓ (deriv K.curve t₀) = 0 := by
    rw [← hr]
    exact h0
  rw [hcc.deriv, hℓ0]

end

end Work.Drive.Mono
