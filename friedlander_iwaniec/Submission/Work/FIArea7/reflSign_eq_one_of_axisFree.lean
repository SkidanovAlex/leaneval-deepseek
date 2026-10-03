/-
# `Submission.Work.FIArea7.reflSign_eq_one_of_axisFree`

The mixed-sign correction `reflSign z₁ z₂` of *FI* Lemma 17.1 (see
`Submission.Work.FIArea7.reflection_pair_betaPrime`) is `-1` exactly on the pairs of the polar box
(5.14) for which `r₁r₂ < 0` and `r₁` and `Δ(z₁,z₂)` have opposite signs.  This file proves that
**such pairs cannot occur on an axis-free polar box**.

The two inputs are

* `9θ ≤ ϑ` (`hθϑ`) and `Pa.θ ≤ 1/8` (`Work.FIArea4.theta_le_eighth`, a consequence of
  `θ = (log x)^{-A'}`, `A' ≥ 2^{20}`, `log x ≥ log 3 > 1.09`);

* the hypothesis `hfar` that every point of the box (5.14) is axis-free,
  `ϑ√N < |Re z|` and `ϑ√N < |Im z|`.

**The crossing argument.**  Write `α(z) = arg z` and let `W = (φ, φ + 2πθ]` be the angular window
of the box, of length `2πθ ≤ π/4`.  If the box contained a point `u` with `Re u < 0` *below* a point
`w` with `Re w > 0`, that is `α(u) < α(w)`, then (as the box is a sector of width `< π/2` in which
the sign of `Re` changes at most once) the window would contain the angle `-π/2` of the negative
imaginary axis, and then *every* box point would satisfy `|cos α(z)| < 2πθ`.

But `|Re z| = |z|·|cos α(z)|` and `|z| ≤ √((1+θ)N)` for a box point, so
`|Re z| < 2πθ√((1+θ)N)`, while axis-freeness together with `9θ ≤ ϑ` gives
`|Re z| > ϑ√N ≥ 9θ√N`.  Hence `9θ√N < 2πθ√(1+θ)√N`, i.e. `9 < 2π√(1+θ)`, which is false for
`θ ≤ 1/8` (`2π√(9/8) < 9`).  So the box never straddles the imaginary axis: with `Re u > 0` and
`Re v < 0` always `α(u) < α(v)`, and the two cases of the definition of `reflSign` both return `1`.
-/
import Mathlib
import Submission.Work.FIArea7.reflSign_separable
import Submission.Work.FITop4.Defs6
import Submission.Work.FIArea4.arg_sub_bounds

set_option autoImplicit false

namespace Work.FIArea7

attribute [local instance] Classical.propDecidable

variable {Pa : Work.FITop.Params} {φ : ℝ}

/-! ## 1. The numerical comparison `9 > 2π√(1+θ)` -/

/-- For `0 < θ ≤ 1/8` the constant `9` of `9θ ≤ ϑ` beats `2π√(1+θ)`; indeed
`2π√(9/8) < 2·3.15·(17/16) < 9`. -/
lemma two_pi_sqrt_lt_nine {θ : ℝ} (hθ0 : 0 < θ) (hθ8 : θ ≤ 1 / 8) :
    2 * Real.pi * Real.sqrt (1 + θ) < 9 := by
  have hsq : Real.sqrt (1 + θ) ≤ 17 / 16 := by
    rw [Real.sqrt_le_iff]
    constructor <;> nlinarith
  nlinarith [hsq, Real.pi_lt_d2, Real.sqrt_nonneg (1 + θ)]

/-! ## 2. The two bounds on `|Re z|` for a box point -/

/-- Axis-freeness plus `9θ ≤ ϑ` give the lower bound `9θ√N < |Re z|`. -/
lemma nine_theta_sqrtN_lt_abs_re {z : GaussianInt} (haf : Work.FITop4.IsAxisFree Pa z)
    (hθϑ : 9 * Pa.θ ≤ Pa.ϑ) :
    9 * Pa.θ * Real.sqrt Pa.N < |(z.re : ℝ)| := by
  have hs : (0 : ℝ) ≤ Real.sqrt Pa.N := Real.sqrt_nonneg _
  calc 9 * Pa.θ * Real.sqrt Pa.N ≤ Pa.ϑ * Real.sqrt Pa.N :=
        mul_le_mul_of_nonneg_right hθϑ hs
    _ < |(z.re : ℝ)| := haf.1

/-- If the angular window of the box contains the angle `-π/2` of the negative imaginary axis,
then every point of the box is at angular distance `< 2πθ` from it, hence
`|cos α(z)| < 2πθ` (`|cos α| = |sin (α + π/2)| ≤ |α + π/2|`). -/
lemma abs_cos_arg_lt_of_window {z : GaussianInt} (hz : Work.FITop3.InPolarBox Pa φ z)
    (hlo : φ < -(Real.pi / 2)) (hhi : -(Real.pi / 2) < φ + 2 * Real.pi * Pa.θ) :
    |Real.cos (z : ℂ).arg| < 2 * Real.pi * Pa.θ := by
  obtain ⟨ha, hb⟩ := box_arg_bounds hz
  have h1 : (z : ℂ).arg + Real.pi / 2 < 2 * Real.pi * Pa.θ := by linarith
  have h2 : -(2 * Real.pi * Pa.θ) < (z : ℂ).arg + Real.pi / 2 := by linarith
  calc |Real.cos (z : ℂ).arg| = |Real.sin ((z : ℂ).arg + Real.pi / 2)| := by
        rw [Real.sin_add_pi_div_two]
    _ ≤ |(z : ℂ).arg + Real.pi / 2| := Real.abs_sin_le_abs
    _ < 2 * Real.pi * Pa.θ := abs_lt.mpr ⟨h2, h1⟩

/-- `|Re z| = |z|·|cos α(z)| ≤ √((1+θ)N)·|cos α(z)|` on the box, so a bound on `|cos α(z)|`
transfers to `|Re z|`. -/
lemma abs_re_lt_of_cos_bound {z : GaussianInt} (hz : Work.FITop3.InPolarBox Pa φ z)
    (hcos : |Real.cos (z : ℂ).arg| < 2 * Real.pi * Pa.θ) :
    |(z.re : ℝ)| < 2 * Real.pi * Pa.θ * Real.sqrt ((1 + Pa.θ) * Pa.N) := by
  have hre : |(z.re : ℝ)| = ‖(z : ℂ)‖ * |Real.cos (z : ℂ).arg| := by
    rw [GaussianInt.intCast_re z, ← Complex.norm_mul_cos_arg (z : ℂ), abs_mul,
      abs_of_nonneg (norm_nonneg _)]
  have hnorm : ‖(z : ℂ)‖ = Real.sqrt ((Work.FIPlan.gnorm z : ℕ) : ℝ) :=
    (Work.FIArea4.sqrt_gnorm z).symm
  have hle : Real.sqrt ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ Real.sqrt ((1 + Pa.θ) * Pa.N) :=
    Real.sqrt_le_sqrt hz.2.2.1
  have hpos : 0 < Real.sqrt ((1 + Pa.θ) * Pa.N) := by
    apply Real.sqrt_pos.mpr
    have hN : (0 : ℝ) < Pa.N := lt_of_lt_of_le zero_lt_one Pa.hN1
    nlinarith [Pa.hθ0]
  rw [hre, hnorm]
  calc Real.sqrt ((Work.FIPlan.gnorm z : ℕ) : ℝ) * |Real.cos (z : ℂ).arg|
      ≤ Real.sqrt ((1 + Pa.θ) * Pa.N) * |Real.cos (z : ℂ).arg| :=
        mul_le_mul_of_nonneg_right hle (abs_nonneg _)
    _ < Real.sqrt ((1 + Pa.θ) * Pa.N) * (2 * Real.pi * Pa.θ) :=
        mul_lt_mul_of_pos_left hcos hpos
    _ = 2 * Real.pi * Pa.θ * Real.sqrt ((1 + Pa.θ) * Pa.N) := by ring

/-! ## 3. The box never straddles the negative imaginary axis -/

/-- **The crossing lemma.**  If every point of the polar box (5.14) is axis-free and `9θ ≤ ϑ`, then
no two box points can straddle the angle `-π/2` (the negative imaginary axis): a point below it and
a point above it cannot both lie on the box.

Indeed, if `α(u) < -π/2 < α(w)` then the window `(φ, φ + 2πθ] ⊇ [α(u), α(w)]` contains `-π/2`, so
every box point is at angular distance `< 2πθ` from `-π/2`, whence `|Re z| < 2πθ√((1+θ)N)`; but
axis-freeness gives `|Re z| > 9θ√N`, and `9 > 2π√(1+θ)` for `θ ≤ 1/8`. -/
lemma no_straddle_of_axisFree (hfar : ∀ z, Work.FITop4.InPolarBox Pa φ z → Work.FITop4.IsAxisFree Pa z)
    (hθϑ : 9 * Pa.θ ≤ Pa.ϑ) :
    ∀ u w : GaussianInt, Work.FITop3.InPolarBox Pa φ u → Work.FITop3.InPolarBox Pa φ w →
      (u : ℂ).arg < -(Real.pi / 2) → -(Real.pi / 2) < (w : ℂ).arg → False := by
  intro u w hu hw hul hwr
  have hθ0 : 0 < Pa.θ := Pa.hθ0
  have hθ8 : Pa.θ ≤ 1 / 8 := Work.FIArea4.theta_le_eighth Pa
  have hπ : 2 * Real.pi * Real.sqrt (1 + Pa.θ) < 9 := two_pi_sqrt_lt_nine hθ0 hθ8
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hlo : φ < -(Real.pi / 2) := lt_trans (box_arg_bounds hu).1 hul
  have hhi : -(Real.pi / 2) < φ + 2 * Real.pi * Pa.θ :=
    lt_of_lt_of_le hwr (box_arg_bounds hw).2
  have hcos : |Real.cos (u : ℂ).arg| < 2 * Real.pi * Pa.θ :=
    abs_cos_arg_lt_of_window hu hlo hhi
  have hlow : 9 * Pa.θ * Real.sqrt Pa.N < |(u.re : ℝ)| :=
    nine_theta_sqrtN_lt_abs_re (hfar u hu) hθϑ
  have hup : |(u.re : ℝ)| < 2 * Real.pi * Pa.θ * Real.sqrt ((1 + Pa.θ) * Pa.N) :=
    abs_re_lt_of_cos_bound hu hcos
  have hNpos : (0 : ℝ) < Pa.N := lt_of_lt_of_le zero_lt_one hN1
  have hsN : (0 : ℝ) < Real.sqrt Pa.N := Real.sqrt_pos.mpr hNpos
  have hs1 : (0 : ℝ) ≤ 1 + Pa.θ := by linarith
  rw [Real.sqrt_mul hs1] at hup
  have hx : (0 : ℝ) < Pa.θ * Real.sqrt Pa.N := mul_pos hθ0 hsN
  have key : 9 * (Pa.θ * Real.sqrt Pa.N)
      < (2 * Real.pi * Real.sqrt (1 + Pa.θ)) * (Pa.θ * Real.sqrt Pa.N) := by
    nlinarith [hlow, hup]
  have hlt : 9 < 2 * Real.pi * Real.sqrt (1 + Pa.θ) := by
    by_contra hcon
    push_neg at hcon
    nlinarith [key, hx]
  linarith [hπ, hlt]

/-! ## 4. The reflection sign is trivial on an axis-free box -/

theorem reflSign_eq_one_of_axisFree {Pa : Work.FITop.Params} {φ : ℝ}
    (hfar : ∀ z, Work.FITop4.InPolarBox Pa φ z → Work.FITop4.IsAxisFree Pa z)
    (hθϑ : 9 * Pa.θ ≤ Pa.ϑ) :
    ∀ z1 z2 : GaussianInt, Work.FITop3.InPolarBox Pa φ z1 →
        Work.FITop3.InPolarBox Pa φ z2 → Work.FIArea7.reflSign z1 z2 = 1 := by
  intro z1 z2 h1 h2
  have hθ0 : 0 < Pa.θ := Pa.hθ0
  have hθ8 : Pa.θ ≤ 1 / 8 := Work.FIArea4.theta_le_eighth Pa
  have h4θ : 4 * Pa.θ < 1 := by linarith
  have hπ : 2 * Real.pi * Real.sqrt (1 + Pa.θ) < 9 := two_pi_sqrt_lt_nine hθ0 hθ8
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  -- **no box point lies below the negative imaginary axis while another lies above it**
  have hnoStraddle := no_straddle_of_axisFree (Pa := Pa) (φ := φ) hfar hθϑ
  -- **on the box, positive real parts come before negative ones**
  have horder : ∀ u w : GaussianInt, Work.FITop3.InPolarBox Pa φ u →
      Work.FITop3.InPolarBox Pa φ w → 0 < u.re → w.re < 0 →
      (u : ℂ).arg < (w : ℂ).arg := by
    intro u w hu hw hu_pos hw_neg
    by_contra hcon
    push_neg at hcon
    have huabs : |(u : ℂ).arg| < Real.pi / 2 := abs_arg_lt_of_re_pos (re_pos_toComplex hu_pos)
    have hwabs : Real.pi / 2 < |(w : ℂ).arg| := abs_arg_gt_of_re_neg (re_neg_toComplex hw_neg)
    have hwlt : (w : ℂ).arg < -(Real.pi / 2) := by
      rcases lt_abs.mp hwabs with h' | h'
      · linarith [(abs_lt.mp huabs).2]
      · linarith
    have hult : -(Real.pi / 2) < (u : ℂ).arg := (abs_lt.mp huabs).1
    exact hnoStraddle w u hw hu hwlt hult
  have hr1 : z1.re ≠ 0 := box_re_ne_zero h1
  have hr2 : z2.re ≠ 0 := box_re_ne_zero h2
  rw [reflSign]
  by_cases hprod : 0 < z1.re * z2.re
  · rw [if_pos hprod]
  · rw [if_neg hprod]
    have hcond : (0 < z1.re ∧ 0 < Work.FIPlan.Delta z1 z2) ∨
        (z1.re < 0 ∧ Work.FIPlan.Delta z1 z2 < 0) := by
      rcases lt_trichotomy z1.re 0 with h | h | h
      · have h2pos : 0 < z2.re := by
          rcases lt_trichotomy z2.re 0 with h2 | h2 | h2
          · exfalso; nlinarith
          · exact absurd h2 hr2
          · exact h2
        refine Or.inr ⟨h, ?_⟩
        exact Delta_neg_of_arg_gt h4θ h1 h2 (horder z2 z1 h2 h1 h2pos h)
      · exact absurd h hr1
      · have h2neg : z2.re < 0 := by
          rcases lt_trichotomy z2.re 0 with h2 | h2 | h2
          · exact h2
          · exact absurd h2 hr2
          · exfalso; nlinarith
        refine Or.inl ⟨h, ?_⟩
        exact Delta_pos_of_arg_lt h4θ h1 h2 (horder z1 z2 h1 h2 h h2neg)
    rw [if_pos hcond]

end Work.FIArea7
