import ChallengeDeps
import Submission.Commons.Analysis.Complex.strip_map_mapsTo

open MeasureTheory Metric Set Complex Filter
open scoped ENNReal BigOperators Topology

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# The elementary conformal "lens" used for the single-scale localisation

See `Submission/FUP/ROADMAP.md`, Session 56 §0 (S2).

`Ψ_q(w) = (2q/π)·log((1+w)/(1-w))` is the elementary conformal map of the open unit disk onto the
strip `{|Im z| < q}` (commons: `Commons.Analysis.Complex.strip_map_mapsTo`,
`…strip_map_real_bijOn`, `…strip_map_hasDerivAt`).  For `0 < ε < 1` we set
`lensMap q ε w = Ψ_q ((1-ε)·w)`, mapping `𝔻` conformally onto the bounded lens
`Ω_ε = Ψ_q((1-ε)𝔻) ⊆ {|Im z| < q}`, whose closure is compact and contains `[-L,L]` with
`L = Ψ_q(1-ε) ≈ 1`.

The point (ROADMAP Session 56 §0): the lens replaces Han–Schlag's `Rect(q)` without any
Schwarz–Christoffel map, and because `Ω_ε` is *bounded*, `g ∘ lensMap` is holomorphic on a
neighbourhood of the closed disk for every entire `g`, so the abstract Cartan estimate
`Commons.Analysis.Complex.riesz_cartan_disk` applies directly.
-/

namespace Submission.FUP

/-- The elementary conformal map `Ψ_q(w) = (2q/π)·log((1+w)/(1-w))` of the open unit disk onto
the strip `{|Im z| < q}`. -/
noncomputable def stripMap (q : ℝ) (w : ℂ) : ℂ :=
  ((2 * q / Real.pi : ℝ) : ℂ) * Complex.log ((1 + w) / (1 - w))

/-- The conformal map `𝔻 → Ω_ε = Ψ_q((1-ε)𝔻)` onto the lens. -/
noncomputable def lensMap (q ε : ℝ) (w : ℂ) : ℂ :=
  stripMap q (((1 - ε : ℝ) : ℂ) * w)

lemma norm_ofReal_eq_abs (x : ℝ) : ‖(x : ℂ)‖ = |x| := by
  rw [← Real.sqrt_sq (norm_nonneg (x : ℂ)), ← Complex.normSq_eq_norm_sq,
    Complex.normSq_ofReal, Real.sqrt_mul_self_eq_abs]

/-- The image of the disk under the lens map lies in the open strip. -/
lemma lensMap_mapsTo {q ε : ℝ} (hq : 0 < q) (hε0 : 0 < ε) (hε1 : ε < 1) :
    MapsTo (lensMap q ε) (ball (0 : ℂ) 1) {z : ℂ | |z.im| < q} := by
  intro w hw
  rw [mem_ball, dist_zero_right] at hw
  have hpm : (0:ℝ) < 1 - ε := by linarith
  have hco : ((1 - ε : ℝ) : ℂ) = (1 : ℂ) - (ε : ℂ) := by push_cast; ring
  have hnorm : ‖((1 - ε : ℝ) : ℂ) * w‖ < 1 := by
    rw [norm_mul, norm_ofReal_eq_abs, abs_of_pos hpm]
    have h1 : (1 - ε) * ‖w‖ < (1 - ε) * 1 := mul_lt_mul_of_pos_left hw hpm
    have h2 : (1 - ε) ≤ 1 := by linarith
    linarith
  have hmem : ((1 - ε : ℝ) : ℂ) * w ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball, dist_zero_right]; exact hnorm
  have hstrip : (2 * q / Real.pi) * Complex.log
      ((1 + ((1 - ε : ℝ) : ℂ) * w) / (1 - ((1 - ε : ℝ) : ℂ) * w)) ∈ {z : ℂ | |z.im| < q} :=
    Commons.Analysis.Complex.strip_map_mapsTo q hq hmem
  have e1 : ((2 * q / Real.pi : ℝ) : ℂ) = (2 * q / Real.pi : ℂ) := by push_cast; ring
  simpa only [stripMap, lensMap, e1] using hstrip

/-- The auxiliary Möbius map `u(w) = (1+w)/(1-w)` takes the disk into the right half plane. -/
lemma one_add_div_one_sub_re_pos {w : ℂ} (hw : ‖w‖ < 1) :
    0 < ((1 + w) / (1 - w)).re := by
  have hne : (1 : ℂ) - w ≠ 0 := by
    intro h
    have hw1 : w = 1 := (sub_eq_zero.mp h).symm
    rw [hw1] at hw
    simp at hw
  have hre : ((1 + w) / (1 - w)).re = (1 - ‖w‖^2) / Complex.normSq (1 - w) := by
    rw [Complex.div_re]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re, Complex.sub_re,
      Complex.sub_im, Complex.one_im, Complex.add_im]
    have hsq : ‖w‖^2 = w.re*w.re + w.im*w.im := by
      rw [Complex.sq_norm, Complex.normSq_apply]
    rw [hsq]
    ring
  rw [hre]
  exact div_pos (by nlinarith [norm_nonneg w]) (Complex.normSq_pos.mpr hne)

/-- The derivative of `Ψ_q` on the disk. -/
lemma stripMap_hasDerivAt' (q : ℝ) {w : ℂ} (hw : ‖w‖ < 1) :
    HasDerivAt (stripMap q) (((2 * q / Real.pi : ℝ) : ℂ) * (2 / (1 - w ^ 2))) w := by
  have hw1 : w ≠ 1 := by intro h; rw [h] at hw; simp at hw
  have hwm1 : w ≠ -1 := by intro h; rw [h] at hw; simp at hw
  have hne : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
  have hne2 : (1 : ℂ) + w ≠ 0 := fun h => hwm1 (by linear_combination h)
  have hne3 : (1 : ℂ) - w ^ 2 ≠ 0 := by
    rw [show (1:ℂ) - w^2 = (1-w)*(1+w) by ring]
    exact mul_ne_zero hne hne2
  have hmem : (1 + w) / (1 - w) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    exact Or.inl (one_add_div_one_sub_re_pos hw)
  have hu : HasDerivAt (fun w : ℂ => (1 + w) / (1 - w)) (2 / (1 - w) ^ 2) w := by
    have hnum : HasDerivAt (fun w : ℂ => 1 + w) 1 w := (hasDerivAt_id w).const_add 1
    have hden : HasDerivAt (fun w : ℂ => 1 - w) (-1) w := (hasDerivAt_id w).const_sub 1
    have h := hnum.div hden hne
    have heq : (1 * (1 - w) - (1 + w) * (-1)) / (1 - w) ^ 2 = 2 / (1 - w) ^ 2 := by
      ring
    rw [heq] at h
    exact h
  have hlog : HasDerivAt (fun w : ℂ => Complex.log ((1 + w) / (1 - w)))
      ((2 / (1 - w) ^ 2) / ((1 + w) / (1 - w))) w := hu.clog hmem
  have hderiv : (2 / (1 - w) ^ 2) / ((1 + w) / (1 - w)) = 2 / (1 - w ^ 2) := by
    field_simp
    ring
  rw [hderiv] at hlog
  have hfin := hlog.const_mul (c := ((2 * q / Real.pi : ℝ) : ℂ))
  have hfun : (fun y : ℂ => ((2 * q / Real.pi : ℝ) : ℂ) * Complex.log ((1 + y) / (1 - y)))
      = stripMap q := rfl
  rw [← hfun]
  exact hfin

/-- The derivative of the lens map. -/
lemma lensMap_hasDerivAt {q ε : ℝ} {w : ℂ} (hε0 : 0 ≤ ε) (hε : ε < 1) (hw : ‖w‖ < 1) :
    HasDerivAt (lensMap q ε)
      (((1 - ε : ℝ) : ℂ) * (((2 * q / Real.pi : ℝ) : ℂ) *
        (2 / (1 - (((1 - ε : ℝ) : ℂ) * w) ^ 2)))) w := by
  have hpm : (0:ℝ) < 1 - ε := by linarith
  have hnorm : ‖((1 - ε : ℝ) : ℂ) * w‖ < 1 := by
    rw [norm_mul, norm_ofReal_eq_abs, abs_of_pos hpm]
    have h1 : (1 - ε) * ‖w‖ < (1 - ε) * 1 := mul_lt_mul_of_pos_left hw hpm
    have h2 : (1 - ε) ≤ 1 := by linarith
    linarith
  have hlin : HasDerivAt (fun w : ℂ => ((1 - ε : ℝ) : ℂ) * w) ((1 - ε : ℝ) : ℂ) w := by
    simpa using (hasDerivAt_id w).const_mul ((1 - ε : ℝ) : ℂ)
  have h := (stripMap_hasDerivAt' q hnorm).comp w hlin
  simp only [Function.comp_def] at h
  have hfun : (fun x : ℂ => stripMap q (((1 - ε : ℝ) : ℂ) * x)) = lensMap q ε := rfl
  rw [hfun] at h
  have hcomm : (((1 - ε : ℝ) : ℂ) * (((2 * q / Real.pi : ℝ) : ℂ) *
      (2 / (1 - (((1 - ε : ℝ) : ℂ) * w) ^ 2))))
      = ((2 * q / Real.pi : ℝ) : ℂ) *
        (2 / (1 - (((1 - ε : ℝ) : ℂ) * w) ^ 2)) * ((1 - ε : ℝ) : ℂ) := by ring
  rw [hcomm]
  exact h

/-- **Distortion bound (upper)** for the lens map: on the open unit disk the derivative is at
most `4q/(πε)`. -/
lemma lensMap_deriv_le {q ε : ℝ} (hq : 0 < q) (hε0 : 0 < ε) (hε1 : ε < 1) {w : ℂ} (hw : ‖w‖ < 1) :
    ‖((1 - ε : ℝ) : ℂ) * (((2 * q / Real.pi : ℝ) : ℂ) *
        (2 / (1 - (((1 - ε : ℝ) : ℂ) * w) ^ 2)))‖ ≤ 4 * q / (Real.pi * ε) := by
  have hpm : (0:ℝ) < 1 - ε := by linarith
  have h1 : ‖(2 : ℂ) / (1 - (((1-ε:ℝ):ℂ) * w) ^ 2)‖ ≤ 2 / ε := by
    have h6 : ε ≤ ‖(1 : ℂ) - (((1-ε:ℝ):ℂ) * w) ^ 2‖ := by
      have h3 := abs_norm_sub_norm_le (1 : ℂ) ((((1-ε:ℝ):ℂ) * w) ^ 2)
      have h4 : ‖(1:ℂ)‖ = 1 := by simp
      have h5 : ‖((((1-ε:ℝ):ℂ) * w)) ^ 2‖ = ((1-ε) * ‖w‖)^2 := by
        rw [norm_pow, norm_mul, norm_ofReal_eq_abs, abs_of_pos hpm]
      have hle' : (1 - ε) * ‖w‖ ≤ 1 - ε :=
        mul_le_of_le_one_right hpm.le (le_of_lt hw)
      have h7 : 1 - ((1-ε) * ‖w‖)^2 ≥ ε := by
        have h8 : ((1-ε) * ‖w‖)^2 ≤ (1-ε)^2 := pow_le_pow_left₀ (by positivity) hle' 2
        nlinarith [h8, hε0, hε1]
      have h9 : 0 ≤ 1 - ((1-ε) * ‖w‖)^2 := by linarith
      rw [h4, h5, abs_of_nonneg h9] at h3
      linarith
    rw [norm_div, show ‖(2:ℂ)‖ = 2 by norm_num,
      div_le_div_iff₀ (lt_of_lt_of_le hε0 h6) hε0]
    linarith
  have h5 : (1 - ε) * (2 * q / Real.pi) * (2 / ε) ≤ 4 * q / (Real.pi * ε) := by
    have h6 : (1 - ε) * (2 * q / Real.pi) * (2 / ε) ≤ 1 * (2 * q / Real.pi) * (2 / ε) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    refine h6.trans (le_of_eq ?_)
    field_simp
    ring
  rw [show ((1 - ε : ℝ) : ℂ) * (((2 * q / Real.pi : ℝ) : ℂ) *
      (2 / (1 - (((1 - ε : ℝ) : ℂ) * w) ^ 2)))
      = ((1 - ε : ℝ) : ℂ) * ((2 * q / Real.pi : ℝ) : ℂ) *
        (2 / (1 - (((1 - ε : ℝ) : ℂ) * w) ^ 2)) by ring]
  rw [norm_mul, norm_mul, norm_ofReal_eq_abs, norm_ofReal_eq_abs,
    abs_of_pos hpm, abs_of_pos (by positivity : (0:ℝ) < 2 * q / Real.pi)]
  calc (1 - ε) * (2 * q / Real.pi) * ‖(2 : ℂ) / (1 - (((1 - ε : ℝ) : ℂ) * w) ^ 2)‖
      ≤ (1 - ε) * (2 * q / Real.pi) * (2 / ε) := by
        apply mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ 4 * q / (Real.pi * ε) := h5

/-- **Distortion bound (lower)** for the lens map: on the open unit disk the derivative is at
least `(1-ε)q/π`. -/
lemma lensMap_deriv_ge {q ε : ℝ} (hq : 0 < q) (hε0 : 0 < ε) (hε1 : ε ≤ 1/2) {w : ℂ}
    (hw : ‖w‖ < 1) :
    (1 - ε) * q / Real.pi ≤ ‖((1 - ε : ℝ) : ℂ) * (((2 * q / Real.pi : ℝ) : ℂ) *
        (2 / (1 - (((1 - ε : ℝ) : ℂ) * w) ^ 2)))‖ := by
  have hpm : (0:ℝ) < 1 - ε := by linarith
  have h1 : (1 : ℝ) ≤ ‖(2 : ℂ) / (1 - (((1-ε:ℝ):ℂ) * w) ^ 2)‖ := by
    have h6 : ‖(1 : ℂ) - (((1-ε:ℝ):ℂ) * w) ^ 2‖ ≤ 2 := by
      have h3 := norm_sub_le (1 : ℂ) ((((1-ε:ℝ):ℂ) * w) ^ 2)
      have h4 : ‖(1:ℂ)‖ = 1 := by simp
      have h5 : ‖((((1-ε:ℝ):ℂ) * w)) ^ 2‖ ≤ 1 := by
        rw [norm_pow, norm_mul, norm_ofReal_eq_abs, abs_of_pos hpm]
        have hle' : (1 - ε) * ‖w‖ ≤ 1 - ε :=
          mul_le_of_le_one_right hpm.le (le_of_lt hw)
        have h7 : ((1-ε) * ‖w‖)^2 ≤ (1-ε)^2 := pow_le_pow_left₀ (by positivity) hle' 2
        nlinarith [h7, hε0, hε1]
      rw [h4] at h3
      linarith
    have hne : (1 : ℂ) - (((1-ε:ℝ):ℂ) * w) ^ 2 ≠ 0 := by
      intro hh
      have h2 : (((1-ε:ℝ):ℂ) * w) ^ 2 = 1 := (sub_eq_zero.mp hh).symm
      have h3 : ‖(((1-ε:ℝ):ℂ) * w) ^ 2‖ = 1 := by rw [h2]; simp
      have h4 : ‖(((1-ε:ℝ):ℂ) * w) ^ 2‖ = ((1-ε) * ‖w‖)^2 := by
        rw [norm_pow, norm_mul, norm_ofReal_eq_abs, abs_of_pos hpm]
      rw [h4] at h3
      have hle' : (1 - ε) * ‖w‖ ≤ 1 - ε := mul_le_of_le_one_right hpm.le (le_of_lt hw)
      have h5 : ((1-ε) * ‖w‖)^2 < 1 := by
        have h6 : ((1-ε) * ‖w‖)^2 ≤ (1-ε)^2 := pow_le_pow_left₀ (by positivity) hle' 2
        nlinarith [h6, hε0, hε1]
      linarith
    have hpos : 0 < ‖(1 : ℂ) - (((1-ε:ℝ):ℂ) * w) ^ 2‖ := norm_pos_iff.mpr hne
    rw [norm_div, show ‖(2:ℂ)‖ = 2 by norm_num, le_div_iff₀ hpos]
    linarith
  rw [show ((1 - ε : ℝ) : ℂ) * (((2 * q / Real.pi : ℝ) : ℂ) *
      (2 / (1 - (((1 - ε : ℝ) : ℂ) * w) ^ 2)))
      = ((1 - ε : ℝ) : ℂ) * ((2 * q / Real.pi : ℝ) : ℂ) *
        (2 / (1 - (((1 - ε : ℝ) : ℂ) * w) ^ 2)) by ring]
  rw [norm_mul, norm_mul, norm_ofReal_eq_abs, norm_ofReal_eq_abs,
    abs_of_pos hpm, abs_of_pos (by positivity : (0:ℝ) < 2 * q / Real.pi)]
  have h7 : (1 - ε) * q / Real.pi ≤ (1 - ε) * (2 * q / Real.pi) * 1 := by
    have : (1 - ε) * (2 * q / Real.pi) * 1 = 2 * ((1 - ε) * q / Real.pi) := by ring
    rw [this]
    linarith [show (1 - ε) * q / Real.pi ≥ 0 by positivity]
  calc (1 - ε) * q / Real.pi
      ≤ (1 - ε) * (2 * q / Real.pi) * 1 := h7
    _ ≤ (1 - ε) * (2 * q / Real.pi) * ‖(2 : ℂ) / (1 - (((1 - ε : ℝ) : ℂ) * w) ^ 2)‖ := by
        apply mul_le_mul_of_nonneg_left h1 (by positivity)

/-- `lensMap q ε` maps real points of the disk to real points. -/
lemma lensMap_ofReal {q ε : ℝ} (_hq : 0 < q) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {x : ℝ}
    (hx : |x| < 1) : ∃ y : ℝ, lensMap q ε (x : ℂ) = (y : ℂ) := by
  have hco : ((1 - ε : ℝ) : ℂ) * (x : ℂ) = (((1 - ε) * x : ℝ) : ℂ) := by push_cast; ring
  have hu : |(1 - ε) * x| < 1 := by
    rw [abs_mul]
    have h1 : |1 - ε| ≤ 1 := by rw [abs_of_nonneg (by linarith)]; linarith
    nlinarith [abs_nonneg x, hx, h1, abs_nonneg (1 - ε)]
  have hpos : 0 < (1 + (1 - ε) * x) / (1 - (1 - ε) * x) := by
    apply div_pos <;> linarith [abs_lt.mp hu]
  refine ⟨(2 * q / Real.pi) * Real.log ((1 + (1 - ε) * x) / (1 - (1 - ε) * x)), ?_⟩
  rw [lensMap, stripMap, hco]
  have hcast : (1 + ((((1 - ε) * x : ℝ)) : ℂ)) / (1 - ((((1 - ε) * x : ℝ)) : ℂ))
      = (((1 + (1 - ε) * x) / (1 - (1 - ε) * x) : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, ← Complex.ofReal_log hpos.le]
  push_cast
  ring





end Submission.FUP
