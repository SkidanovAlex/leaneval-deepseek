import Mathlib
import Submission.Work.Interfaces.Parabolic

/-!
# `Work.PertU.geom` — the discs `Dsm (±η)` are, with an `η/10`-ball, inside the sector `QLeft ξ`

Shishikura's repelling sector is `MandelDim.QLeft ξ = {w | π/3 < |arg (w + ξ)|}`; by
`QLeft_iff` below it is the elementary set `{w | 2 * (w + ξ).re < ‖w + ξ‖}`.  The gate sets are
the discs `MandelDim.Dsm η = closedBall (I * η) (|η| / 4)` and their reflections `Dsm (-η)`.

We prove that for `η` large (how large depends only on `ξ`) the whole `η/10`-ball around any
point of `Dsm η ∪ Dsm (-η)` lies in the sector `QLeft ξ`, and that on those balls the norm is
`Θ(η)` (`η/2 ≤ ‖z‖ ≤ 2η`).

The geometric content: `Dsm η` sits at arguments close to `π/2`, while the boundary of the
sector is at argument `±π/3`; the angular gap `(13 - 7√3)/20 · η` beats `√3 |ξ|` once
`η ≳ 40 |ξ|`.  The elementary criterion used is `√3 · Re w < |Im w| ⟹ 2 Re w < ‖w‖`.
-/

namespace Work.PertU

open Complex Metric Set

noncomputable section

/-! ## The sector in elementary form -/

/-- `|cos|` of the argument of a nonzero complex number. -/
lemma cos_abs_arg {z : ℂ} (hz : z ≠ 0) : Real.cos |z.arg| = z.re / ‖z‖ := by
  rw [Real.cos_abs, Complex.cos_arg hz]

/-- The elementary reformulation of `π/3 < |arg z|` in terms of `cos`. -/
lemma pi_div_three_lt_abs_arg_iff {z : ℂ} :
    Real.pi / 3 < |z.arg| ↔ Real.cos |z.arg| < Real.cos (Real.pi / 3) := by
  constructor
  · intro h
    exact Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) (Complex.abs_arg_le_pi z) h
  · intro h
    by_contra hc
    push Not at hc
    exact absurd h (not_lt.mpr
      (Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hc))

/-- Shishikura's sector `QLeft ξ = {π/3 < |arg (w + ξ)|}` is the elementary set
`{w | 2 * (w + ξ).re < ‖w + ξ‖}`. -/
theorem QLeft_iff (ξ : ℝ) (w : ℂ) :
    w ∈ MandelDim.QLeft ξ ↔ 2 * (w + ξ).re < ‖w + ξ‖ := by
  change Real.pi / 3 < |(w + ξ).arg| ↔ 2 * (w + ξ).re < ‖w + ξ‖
  rcases eq_or_ne (w + ξ) 0 with hz | hz
  · rw [hz, Complex.arg_zero, abs_zero]
    simp only [Complex.zero_re, mul_zero, norm_zero]
    constructor <;> intro h <;> linarith [Real.pi_pos]
  · rw [pi_div_three_lt_abs_arg_iff, Real.cos_pi_div_three, cos_abs_arg hz,
      div_lt_iff₀ (norm_pos_iff.mpr hz)]
    constructor <;> intro h <;> linarith

/-! ## The elementary complex inequality -/

/-- Pure complex inequality: `√3 · Re w < |Im w|` forces `2 Re w < ‖w‖`. -/
lemma two_mul_re_lt_norm_of_sqrt3_mul_re_lt_abs_im {w : ℂ}
    (h : Real.sqrt 3 * w.re < |w.im|) : 2 * w.re < ‖w‖ := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rcases lt_or_ge 0 w.re with ha | ha
  · have hpos : 0 < Real.sqrt 3 * w.re := by positivity
    have habs : |Real.sqrt 3 * w.re| < |w.im| := by
      rwa [abs_of_nonneg hpos.le]
    have hsq : (Real.sqrt 3 * w.re) ^ 2 < w.im ^ 2 := sq_lt_sq.mpr habs
    have hmul : (Real.sqrt 3 * w.re) ^ 2 = 3 * w.re ^ 2 := by rw [mul_pow, h3]
    have hsq3 : 3 * w.re ^ 2 < w.im ^ 2 := by rw [← hmul]; exact hsq
    have hnorm : (2 * w.re) ^ 2 < ‖w‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith
    have := sq_lt_sq.mp hnorm
    rwa [abs_of_nonneg (by linarith), abs_of_nonneg (norm_nonneg w)] at this
  · have hnorm : 0 < ‖w‖ := by
      rcases eq_or_lt_of_le (norm_nonneg w) with h0 | h0
      · exfalso
        have hw0 : w = 0 := norm_eq_zero.mp h0.symm
        rw [hw0] at h
        simp at h
      · exact h0
    linarith

/-- Conjugation does not change membership in the sector. -/
lemma conj_mem_QLeft_iff (ξ : ℝ) (z : ℂ) :
    (starRingEnd ℂ) z ∈ MandelDim.QLeft ξ ↔ z ∈ MandelDim.QLeft ξ := by
  rw [QLeft_iff, QLeft_iff]
  have e : (starRingEnd ℂ) z + (ξ : ℂ) = (starRingEnd ℂ) (z + (ξ : ℂ)) := by
    rw [map_add, Complex.conj_ofReal]
  rw [e, Complex.conj_re, Complex.norm_conj]

/-! ## Norm bounds on the discs -/

/-- A point of the radius-`η/4` disc around a centre of norm `η` has norm between `3η/4`
and `5η/4`. -/
lemma norm_bounds_of_norm_sub_le {η : ℝ} {c w : ℂ} (hc : ‖c‖ = η)
    (h : ‖w - c‖ ≤ η / 4) : 3 * η / 4 ≤ ‖w‖ ∧ ‖w‖ ≤ 5 * η / 4 := by
  constructor
  · have h1 : ‖c‖ - ‖w‖ ≤ ‖c - w‖ := le_trans (le_abs_self _) (abs_norm_sub_norm_le c w)
    rw [norm_sub_rev] at h1
    linarith
  · have h1 := norm_add_le (w - c) c
    have e : (w - c) + c = w := by ring
    rw [e, hc] at h1
    linarith

/-- Norm bounds on `Dsm η ∪ Dsm (-η)`. -/
lemma Dsm_norm_bounds {η : ℝ} (hη : 0 < η) {w : ℂ}
    (hw : w ∈ MandelDim.Dsm η ∪ MandelDim.Dsm (-η)) :
    3 * η / 4 ≤ ‖w‖ ∧ ‖w‖ ≤ 5 * η / 4 := by
  have hc1 : ‖Complex.I * (η : ℂ)‖ = η := by
    rw [Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hη]
  rcases hw with hw | hw
  · have h : ‖w - Complex.I * (η : ℂ)‖ ≤ η / 4 := by
      rw [MandelDim.Dsm, Metric.mem_closedBall, dist_eq_norm] at hw
      rwa [abs_of_pos hη] at hw
    exact norm_bounds_of_norm_sub_le hc1 h
  · have h : ‖w - Complex.I * ((-η : ℝ) : ℂ)‖ ≤ η / 4 := by
      rw [MandelDim.Dsm, Metric.mem_closedBall, dist_eq_norm] at hw
      rwa [abs_neg, abs_of_pos hη] at hw
    have e : w - Complex.I * ((-η : ℝ) : ℂ) = w - (-(Complex.I * (η : ℂ))) := by
      push_cast; ring
    rw [e] at h
    have hc2 : ‖-(Complex.I * (η : ℂ))‖ = η := by rw [norm_neg, hc1]
    exact norm_bounds_of_norm_sub_le hc2 h

/-! ## The gate: the balls lie in the sector -/

/-- If `z` has real part `≤ 7η/20` and `|Im z| ≥ 13η/20`, and the angular margin
`√3(7η/20 + |ξ|) < 13η/20` holds, then `z ∈ QLeft ξ`. -/
lemma mem_QLeft_of_bounds {ξ η : ℝ} {z : ℂ}
    (hbig : Real.sqrt 3 * (7 * η / 20 + |ξ|) < 13 * η / 20)
    (hRe : z.re ≤ 7 * η / 20) (hIm : 13 * η / 20 ≤ |z.im|) :
    z ∈ MandelDim.QLeft ξ := by
  rw [QLeft_iff]
  apply two_mul_re_lt_norm_of_sqrt3_mul_re_lt_abs_im
  rw [Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im]
  have hzre : z.re + ξ ≤ 7 * η / 20 + |ξ| := by linarith [le_abs_self ξ]
  have ha : Real.sqrt 3 * (z.re + ξ) ≤ Real.sqrt 3 * (7 * η / 20 + |ξ|) :=
    mul_le_mul_of_nonneg_left hzre (Real.sqrt_nonneg 3)
  simp only [add_zero] at ha ⊢
  linarith

/-- **Upper gate.**  A point of the `η/10`-ball around a point of the disc `Dsm η` lies in
the sector, provided the angular margin holds. -/
lemma mem_QLeft_of_mem_Dsm {ξ η : ℝ} (hη : 0 < η)
    (hbig : Real.sqrt 3 * (7 * η / 20 + |ξ|) < 13 * η / 20)
    {w z : ℂ} (hw : w ∈ MandelDim.Dsm η) (hz : z ∈ Metric.closedBall w (η / 10)) :
    z ∈ MandelDim.QLeft ξ := by
  have hwη : ‖w - Complex.I * (η : ℂ)‖ ≤ η / 4 := by
    rw [MandelDim.Dsm, Metric.mem_closedBall, dist_eq_norm] at hw
    rwa [abs_of_pos hη] at hw
  have hzw : ‖z - w‖ ≤ η / 10 := by
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    exact hz
  have hzI : ‖z - Complex.I * (η : ℂ)‖ ≤ 7 * η / 20 := by
    have h := norm_add_le (z - w) (w - Complex.I * (η : ℂ))
    have e : (z - w) + (w - Complex.I * (η : ℂ)) = z - Complex.I * (η : ℂ) := by ring
    rw [e] at h
    linarith
  have hRe : z.re ≤ 7 * η / 20 := by
    have h := Complex.abs_re_le_norm (z - Complex.I * (η : ℂ))
    have e : (z - Complex.I * (η : ℂ)).re = z.re := by
      simp [Complex.sub_re, Complex.mul_re]
    rw [e] at h
    linarith [(abs_le.mp h).2]
  have hIm : 13 * η / 20 ≤ |z.im| := by
    have h := Complex.abs_im_le_norm (z - Complex.I * (η : ℂ))
    have e : (z - Complex.I * (η : ℂ)).im = z.im - η := by
      simp [Complex.sub_im, Complex.mul_im]
    rw [e] at h
    have h2 : η - 7 * η / 20 ≤ z.im := by linarith [(abs_le.mp h).1]
    rw [abs_of_nonneg (by linarith : 0 ≤ z.im)]
    linarith
  exact mem_QLeft_of_bounds hbig hRe hIm

/-- **Lower gate.**  A point of the `η/10`-ball around a point of the disc `Dsm (-η)` lies in
the sector, provided the angular margin holds. -/
lemma mem_QLeft_of_mem_Dsm_neg {ξ η : ℝ} (hη : 0 < η)
    (hbig : Real.sqrt 3 * (7 * η / 20 + |ξ|) < 13 * η / 20)
    {w z : ℂ} (hw : w ∈ MandelDim.Dsm (-η)) (hz : z ∈ Metric.closedBall w (η / 10)) :
    z ∈ MandelDim.QLeft ξ := by
  have hwη : ‖w + Complex.I * (η : ℂ)‖ ≤ η / 4 := by
    rw [MandelDim.Dsm, Metric.mem_closedBall, dist_eq_norm] at hw
    rw [abs_neg, abs_of_pos hη] at hw
    have e : w - Complex.I * ((-η : ℝ) : ℂ) = w + Complex.I * (η : ℂ) := by
      push_cast; ring
    rwa [e] at hw
  have hzw : ‖z - w‖ ≤ η / 10 := by
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    exact hz
  have hzI : ‖z + Complex.I * (η : ℂ)‖ ≤ 7 * η / 20 := by
    have h := norm_add_le (z - w) (w + Complex.I * (η : ℂ))
    have e : (z - w) + (w + Complex.I * (η : ℂ)) = z + Complex.I * (η : ℂ) := by ring
    rw [e] at h
    linarith
  have hRe : z.re ≤ 7 * η / 20 := by
    have h := Complex.abs_re_le_norm (z + Complex.I * (η : ℂ))
    have e : (z + Complex.I * (η : ℂ)).re = z.re := by
      simp [Complex.add_re, Complex.mul_re]
    rw [e] at h
    linarith [(abs_le.mp h).2]
  have hIm : 13 * η / 20 ≤ |z.im| := by
    have h := Complex.abs_im_le_norm (z + Complex.I * (η : ℂ))
    have e : (z + Complex.I * (η : ℂ)).im = z.im + η := by
      simp [Complex.add_im, Complex.mul_im]
    rw [e] at h
    have h2 : z.im ≤ -(13 * η / 20) := by linarith [(abs_le.mp h).2]
    rw [abs_of_nonpos (by linarith : z.im ≤ 0)]
    linarith
  exact mem_QLeft_of_bounds hbig hRe hIm

/-! ## The main lemma -/

theorem geom (ξ : ℝ) : ∃ η₁ : ℝ, 0 < η₁ ∧ ∀ η : ℝ, η₁ ≤ η →
    MandelDim.Dsm η ∪ MandelDim.Dsm (-η) ⊆ MandelDim.QLeft ξ ∧
    (∀ w ∈ MandelDim.Dsm η ∪ MandelDim.Dsm (-η),
      Metric.closedBall w (η / 10) ⊆ MandelDim.QLeft ξ) ∧
    (∀ w ∈ MandelDim.Dsm η ∪ MandelDim.Dsm (-η), ∀ z ∈ Metric.closedBall w (η / 10),
      η / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ 2 * η) := by
  refine ⟨100 * |ξ| + 1, by positivity, fun η hη => ?_⟩
  have hηpos : 0 < η := by
    have h0 : (0 : ℝ) < 100 * |ξ| + 1 := by positivity
    linarith
  -- the angular margin
  have hbig : Real.sqrt 3 * (7 * η / 20 + |ξ|) < 13 * η / 20 := by
    have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
    have h36 : Real.sqrt 3 * 36 < 65 := by nlinarith [h3, Real.sqrt_nonneg 3]
    have h13 : 0 < 13 - 7 * Real.sqrt 3 := by nlinarith [h3, Real.sqrt_nonneg 3]
    have hηgt : 100 * |ξ| < η := by linarith
    have hA : (13 - 7 * Real.sqrt 3) * (100 * |ξ|) / 20
        < (13 - 7 * Real.sqrt 3) * η / 20 := by
      have h := mul_lt_mul_of_pos_left hηgt h13
      linarith [h]
    have hB : Real.sqrt 3 * |ξ| ≤ (13 - 7 * Real.sqrt 3) * (100 * |ξ|) / 20 := by
      have hpos : 0 ≤ 65 - 36 * Real.sqrt 3 := by linarith [h36]
      have h := mul_nonneg hpos (abs_nonneg ξ)
      nlinarith [h]
    have hstep : Real.sqrt 3 * |ξ| < (13 - 7 * Real.sqrt 3) * η / 20 := lt_of_le_of_lt hB hA
    nlinarith [hstep]
  have hQ : ∀ w ∈ MandelDim.Dsm η ∪ MandelDim.Dsm (-η),
      Metric.closedBall w (η / 10) ⊆ MandelDim.QLeft ξ := by
    intro w hw z hz
    rcases hw with hw | hw
    · exact mem_QLeft_of_mem_Dsm hηpos hbig hw hz
    · exact mem_QLeft_of_mem_Dsm_neg hηpos hbig hw hz
  refine ⟨fun w hw => hQ w hw ?_, hQ, ?_⟩
  · rw [Metric.mem_closedBall, dist_self]
    positivity
  · intro w hw z hz
    have hzw : ‖z - w‖ ≤ η / 10 := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      exact hz
    obtain ⟨hge, hle⟩ := Dsm_norm_bounds hηpos hw
    constructor
    · have h : ‖w‖ - ‖z‖ ≤ ‖z - w‖ := by
        have := abs_norm_sub_norm_le w z
        rw [norm_sub_rev] at this
        exact le_trans (le_abs_self _) this
      linarith
    · have h := norm_add_le w (z - w)
      have e : w + (z - w) = z := by ring
      rw [e] at h
      linarith

end

end Work.PertU
