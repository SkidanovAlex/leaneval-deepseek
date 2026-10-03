import Mathlib
import Submission.Work.Pert.V5.exp_sin_lower
import Submission.Work.Pert.V5.two_pi_mul_div_le_four_mul_exp
import Submission.Work.Pert.V5.two_pi_mul_div_le_one_sub_exp

/-!
# `Work.Pert.V5.inv_one_sub_exp_le`

The pointwise bound behind the gate integral of Shishikura's §A.4 / (4.2.x): if the distance from
`z : ℂ` to the lattice `ℤ ⊆ ℂ` is at least `D > 0`, then

`1 / ‖1 - exp (-2 π i z)‖ ≤ 9 / (2 π D) + 1`.

The number `z` is reduced modulo `ℤ` to the fundamental strip `|Re w| ≤ 1/2` (the exponential is
`ℤ`-periodic: `exp (-2 π i k) = 1` for `k : ℤ`), and one uses

* `‖1 - exp (-2 π i w)‖ = 2 exp (π Im w) · ‖sin (π w)‖` together with `‖sin (π w)‖ ≥ 2 ‖w‖` on the
  strip (`Work.Pert.V5.exp_sin_lower`), giving `‖1 - exp (-2 π i w)‖ ≥ 4 D exp (π Im w)`, and
* the reverse triangle inequality `‖1 - exp (-2 π i w)‖ ≥ 1 - exp (2 π Im w)`.

Case analysis: for `Im w ≥ 0` the first bound gives `4 D`; for `Im w < 0` one sets `u = -Im w` and
splits at `u = 1/4` (`Work.Pert.V5.two_pi_mul_div_le_four_mul_exp` and
`Work.Pert.V5.two_pi_mul_div_le_one_sub_exp`).
-/

namespace Work.Pert.V5

/-- Rounding to the nearest integer: some `m : ℤ` is within `1/2` of `x`. -/
private lemma exists_int_abs_sub_le_half (x : ℝ) : ∃ m : ℤ, |x - (m : ℝ)| ≤ 1 / 2 := by
  refine ⟨⌊x + 1 / 2⌋, ?_⟩
  have h1 : ((⌊x + 1 / 2⌋ : ℤ) : ℝ) ≤ x + 1 / 2 := Int.floor_le _
  have h2 : x + 1 / 2 < ((⌊x + 1 / 2⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  rw [abs_le]; constructor <;> linarith

theorem inv_one_sub_exp_le {z : ℂ} {D : ℝ} (hD : 0 < D)
    (hDle : D ≤ ⨅ k : ℤ, ‖z - (k : ℂ)‖) :
    1 / ‖1 - Complex.exp (-(2 * Real.pi * Complex.I * z))‖ ≤ 9 / (2 * Real.pi * D) + 1 := by
  -- reduce `z` modulo `ℤ` to the strip `|Re w| ≤ 1/2`
  obtain ⟨m, hm⟩ := exists_int_abs_sub_le_half z.re
  set w : ℂ := z - (m : ℂ) with hwdef
  have hwre : w.re = z.re - (m : ℝ) := by simp [hwdef]
  have ha : |w.re| ≤ 1 / 2 := by rw [hwre]; exact hm
  -- periodicity of the exponential
  have hper : Complex.exp (-(2 * Real.pi * Complex.I * z))
      = Complex.exp (-(2 * Real.pi * Complex.I * w)) := by
    have he : -(2 * Real.pi * Complex.I * z)
        = -(2 * Real.pi * Complex.I * w) + ((-m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      rw [hwdef]; push_cast; ring
    rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  -- `D` is below `‖w‖`
  have hbb : BddBelow (Set.range (fun k : ℤ => ‖z - (k : ℂ)‖)) :=
    ⟨0, by rintro _ ⟨k, rfl⟩; exact norm_nonneg _⟩
  have hDw : D ≤ ‖w‖ := by
    rw [hwdef]; exact le_trans hDle (ciInf_le hbb m)
  -- first lower bound: `‖1 - exp (-2 π i w)‖ ≥ 4 D exp (π Im w)`
  have hI : 4 * D * Real.exp (Real.pi * w.im)
      ≤ ‖1 - Complex.exp (-(2 * Real.pi * Complex.I * w))‖ :=
    exp_sin_lower w ha hD hDw
  -- second lower bound: reverse triangle, valid for `Im w < 0`
  have hII : w.im < 0 → 1 - Real.exp (2 * Real.pi * w.im)
      ≤ ‖1 - Complex.exp (-(2 * Real.pi * Complex.I * w))‖ := by
    intro hb
    have h := abs_norm_sub_norm_le (1 : ℂ) (Complex.exp (-(2 * Real.pi * Complex.I * w)))
    have hnorm : ‖Complex.exp (-(2 * Real.pi * Complex.I * w))‖
        = Real.exp (2 * Real.pi * w.im) := by
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.mul_re, Complex.mul_im]
    rw [norm_one, hnorm] at h
    have h2 : 1 - Real.exp (2 * Real.pi * w.im) = |1 - Real.exp (2 * Real.pi * w.im)| := by
      rw [abs_of_nonneg]
      have : Real.exp (2 * Real.pi * w.im) ≤ 1 := by
        rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
      linarith
    rw [h2]; exact h
  -- geometry of the strip: `‖w‖ ≤ |Im w| + 1/2`
  have hwle : ‖w‖ ≤ |w.im| + 1 / 2 := by
    have h2 : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have h3 : w.re ^ 2 ≤ 1 / 4 := by
      nlinarith [ha, sq_abs w.re, abs_nonneg w.re]
    have h4 : ‖w‖ ^ 2 ≤ (|w.im| + 1 / 2) ^ 2 := by
      rw [h2]
      nlinarith [h3, sq_abs w.im, abs_nonneg w.im, sq_nonneg (|w.im| + 1 / 2)]
    have hs := Real.sqrt_le_sqrt h4
    rwa [Real.sqrt_sq (norm_nonneg w), Real.sqrt_sq (by positivity)] at hs
  -- the key lower bound
  have hkey : 2 * Real.pi * D / (2 * Real.pi * D + 9)
      ≤ ‖1 - Complex.exp (-(2 * Real.pi * Complex.I * w))‖ := by
    rcases lt_or_ge w.im 0 with hb | hb
    · -- `Im w < 0`; write `u = -Im w > 0`
      set u : ℝ := -w.im with hu
      have hu_pos : 0 < u := by rw [hu]; linarith
      have hwu : w.im = -u := by rw [hu]; ring
      have hI' : 4 * D * Real.exp (-(Real.pi * u))
          ≤ ‖1 - Complex.exp (-(2 * Real.pi * Complex.I * w))‖ := by
        have h := hI
        rw [hwu, show Real.pi * (-u) = -(Real.pi * u) by ring] at h
        exact h
      have hII' : 1 - Real.exp (-(2 * Real.pi * u))
          ≤ ‖1 - Complex.exp (-(2 * Real.pi * Complex.I * w))‖ := by
        have h := hII hb
        rw [hwu, show 2 * Real.pi * (-u) = -(2 * Real.pi * u) by ring] at h
        exact h
      have hDu : D ≤ u + 1 / 2 := by
        have h1 : ‖w‖ ≤ u + 1 / 2 := by
          have h2 : |w.im| = u := by rw [hwu, abs_neg, abs_of_pos hu_pos]
          rw [h2] at hwle; exact hwle
        exact le_trans hDw h1
      rcases le_or_gt u (1 / 4) with hu1 | hu1
      · exact le_trans (two_pi_mul_div_le_four_mul_exp (le_of_lt hu_pos) hu1 hD) hI'
      · exact le_trans (two_pi_mul_div_le_one_sub_exp (le_of_lt hu1) hD hDu) hII'
    · -- `Im w ≥ 0`: `exp (π Im w) ≥ 1`, so the first bound gives `4 D`
      have hexp : 1 ≤ Real.exp (Real.pi * w.im) := by
        rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by positivity)
      have hI' : 4 * D ≤ ‖1 - Complex.exp (-(2 * Real.pi * Complex.I * w))‖ := by
        nlinarith [hI, hD, Real.exp_pos (Real.pi * w.im), hexp]
      have hb1 : 2 * Real.pi * D / (2 * Real.pi * D + 9) ≤ 4 * D := by
        have hDn : (0 : ℝ) ≤ 2 * Real.pi * D := by positivity
        have h1 : 2 * Real.pi * D / (2 * Real.pi * D + 9) ≤ 2 * Real.pi * D / 9 :=
          div_le_div_of_nonneg_left hDn (by norm_num) (by nlinarith [Real.pi_pos, hD])
        have h2 : 2 * Real.pi * D / 9 ≤ 4 * D := by
          rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 9)]
          nlinarith [Real.pi_lt_four, hD]
        linarith
      exact le_trans hb1 hI'
  -- convert `1 / ‖·‖ ≤ 1 / δ` with `δ = 2πD/(2πD+9)`
  rw [hper]
  have hpos : 0 < 2 * Real.pi * D / (2 * Real.pi * D + 9) := by positivity
  have hstep := one_div_le_one_div_of_le hpos hkey
  have hval : 1 / (2 * Real.pi * D / (2 * Real.pi * D + 9)) = 9 / (2 * Real.pi * D) + 1 := by
    have hp : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  calc 1 / ‖1 - Complex.exp (-(2 * Real.pi * Complex.I * w))‖
      ≤ 1 / (2 * Real.pi * D / (2 * Real.pi * D + 9)) := hstep
    _ = 9 / (2 * Real.pi * D) + 1 := hval

end Work.Pert.V5
