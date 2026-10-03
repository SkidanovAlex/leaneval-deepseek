import Mathlib
import Submission.Work.Repel.V10.chain_v9_src

/-!
# `Work.Repel.SrcC_sub_Dflat`

The source region `V.SrcC j k n` of a §6 cell (`chain_v9_src`) is cut out of the raw preimage
`Raw j k` by the round box `Metric.ball (w_c + n) (1/2)`, where `w_c = V.wc j k` is the principal
lift of the fibre image `φ₁ '' (W j + k)`.

Because `w_c` is *principal* (`Re w_c ∈ (-1/2, 1/2]`) and its imaginary part sits within
`log 2 / (2π) < 1` of `η` (the `φ₁`-bounds on `Sm1` give `η₁ ‖φ₁ u‖ ∈ [40/51, 40/29] ⊂ (1/2, 2)`),
the whole box `ball (w_c + n) (1/2)` — and hence `SrcC j k n` — lies inside the level-0 counting
disc `Dflat η = closedBall (iη) (η/8)` as soon as `|n| ≤ η/10 + 1` (with `η ≥ 100`).

This is row 2 of the step/hypothesis table of `chain_returns_v9`: it is what allows the source
geometry (and the `φ_star_close` asymptotics on `Dsm η`) to be applied to the cell.
-/

set_option linter.style.haveILetI false

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology

noncomputable section

/-- `Re (log z / (2π i)) = z.arg / (2π)`: the principal argument normalised to `(-1/2, 1/2]`. -/
theorem log_div_two_pi_I_re (z : ℂ) :
    (Complex.log z / (2 * (Real.pi : ℂ) * Complex.I)).re = z.arg / (2 * Real.pi) := by
  have h : (2 * (Real.pi : ℂ) * Complex.I) = ((2 * Real.pi : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.div_re, Complex.log_re, Complex.log_im]
  have hn : Complex.normSq (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = (2 * Real.pi) ^ 2 := by
    rw [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have hmr : (((2 * Real.pi : ℝ) : ℂ) * Complex.I).re = 0 := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring
  have hmi : (((2 * Real.pi : ℝ) : ℂ) * Complex.I).im = 2 * Real.pi := by
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring
  rw [hn, hmr, hmi]
  field_simp
  ring

/-- `Im (log z / (2π i)) = -log ‖z‖ / (2π)`. -/
theorem log_div_two_pi_I_im (z : ℂ) :
    (Complex.log z / (2 * (Real.pi : ℂ) * Complex.I)).im = -Real.log ‖z‖ / (2 * Real.pi) := by
  have h : (2 * (Real.pi : ℂ) * Complex.I) = ((2 * Real.pi : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.div_im, Complex.log_re, Complex.log_im]
  have hn : Complex.normSq (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = (2 * Real.pi) ^ 2 := by
    rw [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have hmr : (((2 * Real.pi : ℝ) : ℂ) * Complex.I).re = 0 := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring
  have hmi : (((2 * Real.pi : ℝ) : ℂ) * Complex.I).im = 2 * Real.pi := by
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring
  rw [hn, hmr, hmi]
  field_simp
  ring

namespace V10

variable (V : V10)

/-- The reference point `w_c` is principal: `|Re w_c| ≤ 1/2`. -/
theorem abs_re_wc_le (j : ℕ) (k : ℤ) : |(V.wc j k).re| ≤ 1/2 := by
  rw [V10.wc, log_div_two_pi_I_re]
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
  have h : |(V.P₁.φ (V.uc j + ((k : ℤ) : ℂ)) / V.s).arg| ≤ Real.pi :=
    abs_le.mpr ⟨le_of_lt (Complex.neg_pi_lt_arg _), Complex.arg_le_pi _⟩
  linarith

/-- The imaginary part of `w_c` is within `1` of `η`: `η₁ ‖φ₁ (u_c + k)‖ ∈ [40/51, 40/29]`. -/
theorem abs_im_wc_sub_eta_le {j : ℕ} {k : ℤ} (hSm : V.fib j k ⊆ V.Sm1) :
    |(V.wc j k).im - V.η| ≤ 1 := by
  have hu : V.uc j + ((k : ℤ) : ℂ) ∈ V.fib j k := V.uc_fib j k
  obtain ⟨hlo, hhi⟩ := V.phi_bounds_of_mem_Sm1 (hSm hu)
  have hApos : 0 < ‖V.P₁.φ (V.uc j + ((k : ℤ) : ℂ))‖ :=
    lt_of_lt_of_le (div_pos (by norm_num) (mul_pos (by norm_num) V.hη₁pos)) hlo
  have hsnorm : ‖V.s‖ ≠ 0 := norm_ne_zero_iff.mpr V.hs
  rw [V10.wc, log_div_two_pi_I_im]
  have hlogz : Real.log ‖(V.P₁.φ (V.uc j + ((k : ℤ) : ℂ)) / V.s)‖
      = Real.log (V.η₁ * ‖V.P₁.φ (V.uc j + ((k : ℤ) : ℂ))‖) - 2 * Real.pi * V.η := by
    rw [norm_div, Real.log_div hApos.ne' hsnorm]
    have hlogs : Real.log ‖V.s‖ = 2 * Real.pi * V.η - Real.log V.η₁ := by
      have h1 : Real.log (V.η₁ * ‖V.s‖) = 2 * Real.pi * V.η := by rw [V.hη₁, Real.log_exp]
      rw [Real.log_mul V.hη₁pos.ne' hsnorm] at h1
      linarith
    rw [hlogs, Real.log_mul V.hη₁pos.ne' hApos.ne']
    ring
  have hre : -Real.log ‖(V.P₁.φ (V.uc j + ((k : ℤ) : ℂ)) / V.s)‖ / (2 * Real.pi) - V.η
      = -Real.log (V.η₁ * ‖V.P₁.φ (V.uc j + ((k : ℤ) : ℂ))‖) / (2 * Real.pi) := by
    rw [hlogz]; field_simp; ring
  rw [hre, abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
  have hone : V.η₁ * (40 / (51 * V.η₁)) = 40 / 51 := by field_simp [V.hη₁pos.ne']
  have htwo : V.η₁ * (40 / (29 * V.η₁)) = 40 / 29 := by field_simp [V.hη₁pos.ne']
  have hBlow : (1 : ℝ) / 2 ≤ V.η₁ * ‖V.P₁.φ (V.uc j + ((k : ℤ) : ℂ))‖ := by
    have h := mul_le_mul_of_nonneg_left hlo (le_of_lt V.hη₁pos)
    rw [hone] at h
    linarith
  have hBhigh : V.η₁ * ‖V.P₁.φ (V.uc j + ((k : ℤ) : ℂ))‖ ≤ 2 := by
    have h := mul_le_mul_of_nonneg_left hhi (le_of_lt V.hη₁pos)
    rw [htwo] at h
    linarith
  have hBpos : 0 < V.η₁ * ‖V.P₁.φ (V.uc j + ((k : ℤ) : ℂ))‖ :=
    mul_pos V.hη₁pos hApos
  have hpi : Real.log 2 ≤ 2 * Real.pi := by
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith [Real.pi_gt_three]
  rw [abs_le]
  constructor
  · have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hBlow
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0), Real.log_one,
      zero_sub] at h
    linarith
  · have h := Real.log_le_log hBpos hBhigh
    linarith

end V10

/-- **The source region of a §6 cell lies in the level-0 counting disc `Dflat η`.**
Row 2 of the step/hypothesis table of `chain_returns_v9`. -/
theorem SrcC_sub_Dflat (V : Work.Repel.V10) {j : ℕ} {k n : ℤ}
    (hSm : V.fib j k ⊆ V.Sm1) (hn : |((n : ℤ) : ℝ)| ≤ V.η / 10 + 1) :
    V.SrcC j k n ⊆ Work.Repel.Dflat V.η := by
  intro w hw
  obtain ⟨hwRaw, hwball⟩ := hw
  rw [Metric.mem_ball, dist_eq_norm] at hwball
  have hηpos := V.hηpos
  have hwc_re : |(V.wc j k).re| ≤ 1 / 2 := V.abs_re_wc_le j k
  have hwc_im : |(V.wc j k).im - V.η| ≤ 1 := V.abs_im_wc_sub_eta_le hSm
  have hre1 : |w.re - ((V.wc j k).re + (n : ℝ))| < 1 / 2 := by
    have h := Complex.abs_re_le_norm (w - (V.wc j k + ((n : ℤ) : ℂ)))
    have hre_eq : (w - (V.wc j k + ((n : ℤ) : ℂ))).re = w.re - ((V.wc j k).re + (n : ℝ)) := by
      simp [Complex.sub_re, Complex.add_re]
    rw [hre_eq] at h
    linarith
  have hre2 : |(V.wc j k).re + (n : ℝ)| ≤ 1 / 2 + (V.η / 10 + 1) := by
    calc |(V.wc j k).re + (n : ℝ)| ≤ |(V.wc j k).re| + |(n : ℝ)| := abs_add_le _ _
      _ ≤ 1 / 2 + (V.η / 10 + 1) := by linarith [hwc_re, hn]
  have hre : |w.re| ≤ V.η / 10 + 2 := by
    have hsplit : w.re = (w.re - ((V.wc j k).re + (n : ℝ))) + ((V.wc j k).re + (n : ℝ)) := by
      ring
    rw [hsplit]
    calc |(w.re - ((V.wc j k).re + (n : ℝ))) + ((V.wc j k).re + (n : ℝ))|
        ≤ |w.re - ((V.wc j k).re + (n : ℝ))| + |(V.wc j k).re + (n : ℝ)| := abs_add_le _ _
      _ ≤ V.η / 10 + 2 := by linarith
  have him1 : |w.im - (V.wc j k).im| < 1 / 2 := by
    have h := Complex.abs_im_le_norm (w - (V.wc j k + ((n : ℤ) : ℂ)))
    have him_eq : (w - (V.wc j k + ((n : ℤ) : ℂ))).im = w.im - (V.wc j k).im := by
      simp [Complex.sub_im, Complex.add_im]
    rw [him_eq] at h
    linarith
  have him : |w.im - V.η| ≤ 3 / 2 := by
    have hsplit : w.im - V.η = (w.im - (V.wc j k).im) + ((V.wc j k).im - V.η) := by ring
    rw [hsplit]
    calc |(w.im - (V.wc j k).im) + ((V.wc j k).im - V.η)|
        ≤ |w.im - (V.wc j k).im| + |(V.wc j k).im - V.η| := abs_add_le _ _
      _ ≤ 3 / 2 := by linarith
  rw [Dflat, Metric.mem_closedBall, dist_eq_norm, abs_of_pos hηpos]
  have hsqi : Complex.normSq (w - Complex.I * (V.η : ℂ)) = w.re ^ 2 + (w.im - V.η) ^ 2 := by
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hsq : ‖w - Complex.I * (V.η : ℂ)‖ ^ 2 ≤ (V.η / 8) ^ 2 := by
    rw [Complex.sq_norm, hsqi]
    have h1 := abs_le.mp hre
    have h2 := abs_le.mp him
    nlinarith [h1.1, h1.2, h2.1, h2.2, V.hη]
  have h := sq_le_sq.mp hsq
  simpa [abs_of_nonneg (norm_nonneg _),
    abs_of_nonneg (div_nonneg (le_of_lt hηpos) (by norm_num : (0 : ℝ) ≤ 8))] using h

end

end Work.Repel
