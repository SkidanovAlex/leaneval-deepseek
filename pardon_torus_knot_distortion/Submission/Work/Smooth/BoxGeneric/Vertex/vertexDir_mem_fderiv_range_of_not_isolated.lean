import Mathlib
import Submission.Work.Smooth.BoxGeneric.Defs
import Submission.Work.Smooth.BoxGeneric.Vertex.aeNoVertex_of_ae_centre
import Submission.Work.Smooth.Morse.All
import Submission.Work.Core.torusMap_eq_iff
import Submission.Work.Smooth.BoxGeneric.Vertex.torus_combination_of_tangential
import Submission.Work.Smooth.BoxGeneric.Vertex.fderiv_torusLevel
import Submission.Work.Analysis.Deriv.hasDerivAt_eq_zero_of_tendsto

/-!
# The vertex ray is tangent to the surface at an accumulation point of intersections

The vertex of Pardon's box `PBox s c σ` with sign pattern `ε` is the point
`Work.Smooth.BoxGeneric.boxVertex c σ ε s = c + s • vertexDir σ ε` of the vertex ray
`t ↦ c + t • vertexDir σ ε`.  This file proves that if such a ray meets the surface
`F = ψ(standard torus)` at the level `s`, and meets it again at levels `t` arbitrarily close to `s`
with `t ≠ s`, then the direction `vertexDir σ ε` of the ray is a **tangent direction** of `F` at
that point: there is a parameter `p` with `param ψ p = boxVertex c σ ε s` and a parameter
increment `r` with `fderiv ℝ (param ψ) p r = vertexDir σ ε`.

## The argument

The surface is described as a level set of the explicit smooth function

`G y = (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 + 3) ^ 2 - 16 * (y 0 ^ 2 + y 1 ^ 2)`,

which vanishes exactly on the standard torus of revolution
(`torusLevel_torusMap_eq_zero`) — the point of the polynomial form is that it is smooth on all of
`ℝ³`, so no localisation away from the `z`-axis is needed.  Writing `y₀ = ψ⁻¹(boxVertex c σ ε s)`
and `γ t = boxVertex c σ ε t`, the curve `t ↦ G (ψ⁻¹ (γ t))` vanishes at `s` and at the sequence
`t n → s` supplied by the accumulation hypothesis; by
`Work.Analysis.Deriv.hasDerivAt_eq_zero_of_tendsto` its derivative at `s` vanishes, and the chain
rule identifies that derivative as `dG_{y₀} (dψ⁻¹_{p₀} (vertexDir σ ε))`.

The explicit derivative `fderiv_torusLevel` turns this into the single scalar equation

`cos v * (w 0 * cos u + w 1 * sin u) + sin v * w 2 = 0`

at `(u, v) = q` with `y₀ = torusMap u v` and `w = dψ⁻¹_{p₀}(vertexDir σ ε)`, which is exactly the
linear-algebra hypothesis of `torus_combination_of_tangential`: it says that `w` is orthogonal to
the normal vector `(ρ - 2) (cos u, sin u, 0) + sin v · e₃` of the standard torus, and that lemma
produces `r₁, r₂` with `r₁ • dtheta q + r₂ • dphi q = w`.  Hence `w = torusDeriv q (r₁, r₂)` is in
the range of the derivative of the torus parametrisation, and transporting back along the chain
rule for `param ψ = ψ ∘ torusMap` gives the claim.

## Contents

* `torusLevel_torusMap_eq_zero` (private): the standard torus lies in the zero set of `G`;
* `vertexDir_mem_fderiv_range_of_not_isolated`: the statement of the file.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.BoxGeneric.Vertex

noncomputable section

/-- The level function of the standard torus of revolution: the polynomial
`(‖y‖² + 3)² - 16 (y₀² + y₁²)`, whose zero set is the torus of revolution of major radius `2` and
minor radius `1`.  Unlike `(√(y₀² + y₁²) - 2)² + y₂² - 1` it is smooth on all of `ℝ³`. -/
private abbrev torusLevel : R3 → ℝ :=
  fun y => (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 + 3) ^ 2 - 16 * (y 0 ^ 2 + y 1 ^ 2)

/-- **The standard torus of revolution lies in the zero set of `torusLevel`.**  Along the
parametrisation `torusMap u v` the level function takes the value `0`, because its value
`(2 + cos v)² + sin²v + 3` of `‖y‖² + 3` is `4 (2 + cos v)`. -/
private theorem torusLevel_torusMap_eq_zero (u v : ℝ) :
    torusLevel (Work.Core.torusMap u v) = 0 := by
  rw [torusLevel, Work.Core.torusMap_apply_zero, Work.Core.torusMap_apply_one,
    Work.Core.torusMap_apply_two]
  have h1 : ((2 + Real.cos v) * Real.cos u) ^ 2 + ((2 + Real.cos v) * Real.sin u) ^ 2
      = (2 + Real.cos v) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq u]
  have h2 : (2 + Real.cos v) ^ 2 + Real.sin v ^ 2 + 3 = 4 * (2 + Real.cos v) := by
    nlinarith [Real.sin_sq_add_cos_sq v]
  rw [h1, h2]
  ring

/-- **The direction of a vertex ray which meets the surface at an accumulation point of
intersections is a tangent direction.**  If the vertex `boxVertex c σ ε s` of the box lies on
`F = ψ(standard torus)` and the vertex ray meets `F` again at levels `t → s`, `t ≠ s`, then there
are a parameter `p` over the vertex point and a direction `r` in the parameter plane whose image
under `fderiv ℝ (param ψ) p` is `vertexDir σ ε`. -/
theorem vertexDir_mem_fderiv_range_of_not_isolated {ψ : Submission.Diffeo} {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)} {ε : Fin 3 → ℝ} {s : ℝ} (hy : Work.Smooth.BoxGeneric.boxVertex c σ ε s ∈ (Work.Smooth.Morse.torus ψ).carrier) (hacc : ∀ δ : ℝ, 0 < δ → ∃ t : ℝ, t ≠ s ∧ |t - s| < δ ∧ Work.Smooth.BoxGeneric.boxVertex c σ ε t ∈ (Work.Smooth.Morse.torus ψ).carrier) : ∃ p : ℝ × ℝ, Work.Smooth.Morse.param ψ p = Work.Smooth.BoxGeneric.boxVertex c σ ε s ∧ ∃ r : ℝ × ℝ, fderiv ℝ (Work.Smooth.Morse.param ψ) p r = Work.Smooth.BoxGeneric.Vertex.vertexDir σ ε := by
  classical
  -- a parameter over the vertex point
  obtain ⟨q, hq⟩ := hy
  refine ⟨q, hq, ?_⟩
  by_cases hv : vertexDir σ ε = 0
  · -- the trivial case: the vertex ray is constant
    exact ⟨0, by rw [hv, map_zero]⟩
  -- the curve `t ↦ boxVertex c σ ε t` has derivative `vertexDir σ ε` at `s`
  have hcurve : HasDerivAt (fun t : ℝ => boxVertex c σ ε t) (vertexDir σ ε) s := by
    have h : HasDerivAt (fun t : ℝ => c + t • vertexDir σ ε) (vertexDir σ ε) s := by
      simpa using ((hasDerivAt_id s).smul_const (vertexDir σ ε)).const_add c
    rwa [← funext fun t => boxVertex_eq_add_smul c σ ε t] at h
  -- a sequence of intersection levels tending to `s`
  have hseq : ∀ n : ℕ, ∃ t : ℝ, t ≠ s ∧ |t - s| < 1 / ((n : ℝ) + 1) ∧
      boxVertex c σ ε t ∈ (Work.Smooth.Morse.torus ψ).carrier := fun n => hacc _ (by positivity)
  choose ts hts_ne hts_lt hts_mem using hseq
  have hts_tend : Filter.Tendsto ts Filter.atTop (nhds s) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => abs_nonneg _) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [Real.norm_eq_abs]
    exact le_of_lt (hts_lt n)
  -- the point of the standard torus corresponding to the vertex
  set y₀ : R3 := Work.Core.torusMap q.1 q.2 with hy₀
  have hy₀eq : ψ.invFun (boxVertex c σ ε s) = y₀ := by
    rw [hy₀, ← hq]
    show ψ.invFun (ψ (Work.Core.torusMap q.1 q.2)) = Work.Core.torusMap q.1 q.2
    exact ψ.left_inv _
  -- the two derivatives
  have hψderiv : HasFDerivAt (fun y : R3 => ψ.invFun y)
      (fderiv ℝ ψ.invFun (boxVertex c σ ε s)) (boxVertex c σ ε s) :=
    (ψ.smooth_invFun.hasStrictFDerivAt (by simp)).hasFDerivAt
  have hGsmooth : ContDiff ℝ (⊤ : ℕ∞) torusLevel := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun y : R3 => (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 + 3) ^ 2 - 16 * (y 0 ^ 2 + y 1 ^ 2))
    fun_prop
  have hGderiv : HasFDerivAt torusLevel (fderiv ℝ torusLevel (ψ.invFun (boxVertex c σ ε s)))
      (ψ.invFun (boxVertex c σ ε s)) :=
    (hGsmooth.hasStrictFDerivAt (by simp)).hasFDerivAt
  -- the composite curve has derivative zero, by the difference quotient argument
  have hcomp1 : HasDerivAt (fun t : ℝ => ψ.invFun (boxVertex c σ ε t))
      ((fderiv ℝ ψ.invFun (boxVertex c σ ε s)) (vertexDir σ ε)) s :=
    hψderiv.comp_hasDerivAt s hcurve
  have hcomp2 : HasDerivAt (fun t : ℝ => torusLevel (ψ.invFun (boxVertex c σ ε t)))
      ((fderiv ℝ torusLevel (ψ.invFun (boxVertex c σ ε s)))
        ((fderiv ℝ ψ.invFun (boxVertex c σ ε s)) (vertexDir σ ε))) s :=
    hGderiv.comp_hasDerivAt (l := fun y : R3 => torusLevel y) s hcomp1
  have hval : ∀ t : ℝ, boxVertex c σ ε t ∈ (Work.Smooth.Morse.torus ψ).carrier →
      torusLevel (ψ.invFun (boxVertex c σ ε t)) = 0 := by
    intro t ht
    rw [Work.Smooth.Morse.torus_carrier] at ht
    obtain ⟨p, hp⟩ := Set.mem_range.mp ht
    have hz : boxVertex c σ ε t = ψ (Work.Core.torusMap p.1 p.2) := by
      rw [← hp]; rfl
    rw [hz, ψ.left_inv]
    exact torusLevel_torusMap_eq_zero p.1 p.2
  have hvalS : torusLevel (ψ.invFun (boxVertex c σ ε s)) = 0 := by
    rw [hy₀eq, hy₀]
    exact torusLevel_torusMap_eq_zero q.1 q.2
  have heq0 : ∀ n : ℕ, torusLevel (ψ.invFun (boxVertex c σ ε (ts n))) =
      torusLevel (ψ.invFun (boxVertex c σ ε s)) :=
    fun n => by rw [hval (ts n) (hts_mem n), hvalS]
  have hderiv0 : (fderiv ℝ torusLevel (ψ.invFun (boxVertex c σ ε s)))
      ((fderiv ℝ ψ.invFun (boxVertex c σ ε s)) (vertexDir σ ε)) = 0 :=
    Work.Analysis.Deriv.hasDerivAt_eq_zero_of_tendsto hcomp2 hts_tend hts_ne heq0
  -- the vector `w = d(ψ⁻¹)(vertexDir)`
  set w : R3 := (fderiv ℝ ψ.invFun (boxVertex c σ ε s)) (vertexDir σ ε) with hw
  have hw_ker : fderiv ℝ torusLevel y₀ w = 0 := by
    rw [hy₀eq] at hderiv0
    exact hderiv0
  -- the explicit form of that derivative at a point of the torus
  have hformula : fderiv ℝ torusLevel y₀ w = 16 * (2 + Real.cos q.2) *
      (Real.cos q.2 * (w 0 * Real.cos q.1 + w 1 * Real.sin q.1) + Real.sin q.2 * w 2) := by
    rw [hy₀]
    change fderiv ℝ (fun y : R3 => (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 + 3) ^ 2 - 16 * (y 0 ^ 2 + y 1 ^ 2))
        (Work.Core.torusMap q.1 q.2) w = 16 * (2 + Real.cos q.2) *
          (Real.cos q.2 * (w 0 * Real.cos q.1 + w 1 * Real.sin q.1) + Real.sin q.2 * w 2)
    rw [fderiv_torusLevel]
    have hD : (Work.Core.torusMap q.1 q.2) 0 ^ 2 + (Work.Core.torusMap q.1 q.2) 1 ^ 2
        + (Work.Core.torusMap q.1 q.2) 2 ^ 2 + 3 = 4 * (2 + Real.cos q.2) := by
      rw [Work.Core.torusMap_apply_zero, Work.Core.torusMap_apply_one,
        Work.Core.torusMap_apply_two]
      nlinarith [Real.sin_sq_add_cos_sq q.1, Real.sin_sq_add_cos_sq q.2]
    rw [hD, Work.Core.torusMap_apply_zero, Work.Core.torusMap_apply_one,
      Work.Core.torusMap_apply_two]
    ring
  -- the resulting scalar equation
  have hbracket : Real.cos q.2 * (w 0 * Real.cos q.1 + w 1 * Real.sin q.1)
      + Real.sin q.2 * w 2 = 0 := by
    have hpos : (0 : ℝ) < 16 * (2 + Real.cos q.2) := by
      have h := Real.neg_one_le_cos q.2
      linarith
    have h0 : 16 * (2 + Real.cos q.2) *
        (Real.cos q.2 * (w 0 * Real.cos q.1 + w 1 * Real.sin q.1) + Real.sin q.2 * w 2) = 0 := by
      rw [← hformula, hw_ker]
    exact (mul_eq_zero.mp h0).resolve_left (ne_of_gt hpos)
  -- solve for the parameter direction
  have hz : (2 + Real.cos q.2 - 2) ^ 2 + Real.sin q.2 ^ 2 = 1 := by
    have h := Real.sin_sq_add_cos_sq q.2
    nlinarith [h]
  have hbracket' : (2 + Real.cos q.2 - 2) * (w 0 * Real.cos q.1 + w 1 * Real.sin q.1)
      + Real.sin q.2 * w 2 = 0 := by
    rw [show (2 : ℝ) + Real.cos q.2 - 2 = Real.cos q.2 by ring]
    exact hbracket
  have hρpos : (0 : ℝ) < 2 + Real.cos q.2 := by
    have h := Real.neg_one_le_cos q.2; linarith
  obtain ⟨r₁, r₂, hr1, hr2, hr3⟩ := torus_combination_of_tangential (ρ := 2 + Real.cos q.2)
    (z := Real.sin q.2) (u := q.1) (w0 := w 0) (w1 := w 1) (w2 := w 2) hρpos hz hbracket'
  have htd : Work.Smooth.Morse.torusDeriv q (r₁, r₂) = w := by
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
      · have h3' : r₂ * Real.cos q.2 = w 2 := by
          have h3 := hr3
          rw [show (2 : ℝ) + Real.cos q.2 - 2 = Real.cos q.2 by ring] at h3
          exact h3
        rw [h3']
        simp
  -- the derivative of `ψ` at `y₀` inverts the derivative of `ψ⁻¹` at the vertex point
  have hright : (fderiv ℝ (ψ : R3 → R3) y₀).comp (fderiv ℝ ψ.invFun (boxVertex c σ ε s)) =
      ContinuousLinearMap.id ℝ R3 := by
    have hmain : HasFDerivAt (fun y : R3 => ψ (ψ.invFun y))
        ((fderiv ℝ (ψ : R3 → R3) y₀).comp (fderiv ℝ ψ.invFun (boxVertex c σ ε s)))
        (boxVertex c σ ε s) := by
      have hψ2 : HasFDerivAt (fun y : R3 => ψ y)
          (fderiv ℝ (ψ : R3 → R3) (ψ.invFun (boxVertex c σ ε s)))
          (ψ.invFun (boxVertex c σ ε s)) :=
        (ψ.smooth_toFun.hasStrictFDerivAt (by simp)).hasFDerivAt
      have hcomp := hψ2.comp (boxVertex c σ ε s) hψderiv
      rw [hy₀eq] at hcomp
      exact hcomp
    have hid : (fun y : R3 => ψ (ψ.invFun y)) = id := funext fun y => ψ.right_inv y
    rw [hid] at hmain
    exact hmain.unique (hasFDerivAt_id (boxVertex c σ ε s))
  have hv_eq : fderiv ℝ (ψ : R3 → R3) y₀ w = vertexDir σ ε := by
    have h := congrArg (fun (L : R3 →L[ℝ] R3) => L (vertexDir σ ε)) hright
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, ← hw] using h
  -- the chain rule for the parametrisation of the surface
  refine ⟨(r₁, r₂), ?_⟩
  rw [Work.Smooth.Morse.fderiv_param ψ q, ContinuousLinearMap.comp_apply, htd]
  exact hv_eq

end

end Work.Smooth.BoxGeneric.Vertex
