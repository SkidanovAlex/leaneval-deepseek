import Mathlib

/-!
# The plane ray ("slit") barrier

`Work.SimplyConnected.ABS.plane_sector_barrier_continuous` produces the classical *sector* barrier: if
`L₁, L₂` span a non-degenerate sector, then `φ z = Re √(-z/p)` (with `p` in the open sector) is
continuous, vanishes at the origin, and is harmonic and strictly positive off the closed sector.

This module supplies the **degenerate** companion needed when the local complement of a region is a
*ray* rather than a sector — the case arising at a point where two boundary circles are tangent:

`plane_ray_barrier d hd`: if `d ≠ 0`, there is `φ : ℂ → ℝ`, continuous, `φ 0 = 0`, harmonic off the
ray `{t • d : t ≥ 0}` of apex `0` through `d`, and strictly positive on the complement of that ray.

The construction is again `φ z = Re √(-(d⁻¹ z))`; the branch cut of the principal square root is the
ray through `d`, so the argument of `plane_sector_barrier_continuous` applies verbatim.

## Why this is the right degeneration

Let `Ω = ⋃_i int(B_i)` be a finite union of chart balls and `p ∈ frontier Ω`.  In a chart at `p` each
`int(B_i)` with `p ∈ ∂B_i` is locally the interior of a disc through `p`, hence contains the tangent
half-plane `{L_i < 0}` (`L_i` = outward normal), while `X ∖ B_i` locally contains `{L_i > 0}`.  If,
among the balls through `p`, some direction `e ≠ 0` satisfies `⟪e, u_i⟫ ≥ 0` for all of them (`u_i`
the unit vector from `p` towards the centre of `B_i`), then the ray `{t e : t > 0}` lies in the local
complement of `Ω` (for `x = p + t e`: `⟪x - p, φ p - c_i⟫ = t ρ_i ⟪e, u_i⟫ ≥ 0` while membership of
`B_i` forces `⟪x - p, φ p - c_i⟫ < -‖x - p‖²/2 < 0`), and the ray barrier here is a barrier at `p`.

**This is *not* automatic** — the "surrounding" (pinch/pinwheel) configurations have a complement
whose closure meets `p` in the single point `{p}`, and then no ray at all avoids `Ω`: for three unit
discs centred at `1, e^{2πi/3}, e^{4πi/3}` the union contains the punctured disc `ball(0,1) ∖ {0}` and
`0 ∈ frontier Ω` is irregular (its complement is the polar set `{0}`), so no barrier exists there.
A hypothesis preventing this — e.g. **at most two of the balls meet at each point** — is needed; with
it the local picture is the single-ball or two-ball one, handled by
`Work.SimplyConnected.ABS.barrier_of_sector` and `Work.SimplyConnected.ABS.barrier_of_ray` (via
`Work.SimplyConnected.ABS.hasSectorBoundary_or_hasRayBoundary_of_two_chartBall`).
-/

open Set

namespace Work.SimplyConnected.ABS

set_option linter.unusedVariables false

/-- The real part of `Complex.sqrt w` as an explicit continuous expression. -/
private lemma sqrt_re_eq (w : ℂ) : (Complex.sqrt w).re = Real.sqrt ((‖w‖ + w.re)/2) := by
  rw [Complex.sqrt_eq_real_add_ite]
  simp only [Complex.add_re, Complex.ofReal_re]
  rw [Complex.mul_I_re]
  split_ifs <;> simp

/-- If `-(d⁻¹ * z)` is a non-positive real number then `z` lies on the ray through `d`. -/
private lemma exists_smul_of_im_eq_zero {d z : ℂ} (hd : d ≠ 0)
    (him : (-(d⁻¹ * z)).im = 0) (hre : (-(d⁻¹ * z)).re ≤ 0) :
    ∃ t : ℝ, 0 ≤ t ∧ z = t • d := by
  have hw : -(d⁻¹ * z) = (((-(d⁻¹ * z)).re : ℝ) : ℂ) := by
    have h := Complex.re_add_im (-(d⁻¹ * z))
    rw [him] at h
    simpa using h.symm
  set t : ℝ := -(-(d⁻¹ * z)).re with ht
  have ht0 : 0 ≤ t := by rw [ht]; linarith
  have h1 : d⁻¹ * z = (t : ℂ) := by
    have := congrArg Neg.neg hw
    simp only [neg_neg] at this
    rw [this]
    push_cast [ht]
    ring
  refine ⟨t, ht0, ?_⟩
  calc z = d * (d⁻¹ * z) := by rw [← mul_assoc, mul_inv_cancel₀ hd, one_mul]
    _ = d * (t : ℂ) := by rw [h1]
    _ = t • d := by rw [mul_comm]; rfl

/-- **The plane ray ("slit") barrier, continuous form.**  For `d ≠ 0` there is `φ : ℂ → ℝ`,
continuous on all of `ℂ`, vanishing at the origin, and strictly positive and harmonic off the ray
`{t • d : t ≥ 0}`. -/
theorem plane_ray_barrier (d : ℂ) (hd : d ≠ 0) :
    ∃ φ : ℂ → ℝ, Continuous φ ∧ φ 0 = 0 ∧
      (∀ z : ℂ, (∀ t : ℝ, 0 ≤ t → z ≠ t • d) → 0 < φ z) ∧
      (∀ z : ℂ, (∀ t : ℝ, 0 ≤ t → z ≠ t • d) → InnerProductSpace.HarmonicAt φ z) := by
  refine ⟨fun z => (Complex.sqrt (-(d⁻¹ * z))).re, ?_, ?_, ?_, ?_⟩
  · have hfun : (fun z : ℂ => (Complex.sqrt (-(d⁻¹ * z))).re)
        = fun z : ℂ => Real.sqrt ((‖-(d⁻¹ * z)‖ + (-(d⁻¹ * z)).re)/2) := by
      funext z; exact sqrt_re_eq _
    rw [hfun]; fun_prop
  · simp
  · intro z hz
    have hw : -(d⁻¹ * z) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      by_contra hc
      push Not at hc
      obtain ⟨hre, him⟩ := hc
      obtain ⟨t, ht, hzt⟩ := exists_smul_of_im_eq_zero hd him hre
      exact hz t ht hzt
    have hpos : 0 < (Complex.sqrt (-(d⁻¹ * z))).re := by
      rw [sqrt_re_eq]
      refine Real.sqrt_pos.2 ?_
      have hsplit := Complex.mem_slitPlane_iff.mp hw
      rcases hsplit with hre | him
      · linarith [norm_nonneg (-(d⁻¹ * z))]
      · have h1 := (Complex.abs_re_lt_norm (z := -(d⁻¹ * z))).2 him
        have h2 : -(-(d⁻¹ * z)).re ≤ |(-(d⁻¹ * z)).re| := neg_le_abs _
        linarith
    exact hpos
  · intro z hz
    have hw : -(d⁻¹ * z) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      by_contra hc
      push Not at hc
      obtain ⟨hre, him⟩ := hc
      obtain ⟨t, ht, hzt⟩ := exists_smul_of_im_eq_zero hd him hre
      exact hz t ht hzt
    have hpoint : ((-(d⁻¹)) • (1 : ℂ →L[ℂ] ℂ)) z ∈ Complex.slitPlane := by
      have hz_eq : ((-(d⁻¹)) • (1 : ℂ →L[ℂ] ℂ)) z = -(d⁻¹ * z) := by
        simp [smul_eq_mul, neg_mul]
      rw [hz_eq]; exact hw
    have hana : AnalyticAt ℂ Complex.sqrt (((-(d⁻¹)) • (1 : ℂ →L[ℂ] ℂ)) z) :=
      Complex.differentiableOn_sqrt.analyticAt (Complex.isOpen_slitPlane.mem_nhds hpoint)
    have hcomp : AnalyticAt ℂ (Complex.sqrt ∘ (⇑((-d⁻¹) • (1 : ℂ →L[ℂ] ℂ)))) z :=
      hana.compContinuousLinearMap
    have hh := hcomp.harmonicAt_re
    simpa only [Function.comp_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
      smul_eq_mul, neg_mul] using hh

end Work.SimplyConnected.ABS
