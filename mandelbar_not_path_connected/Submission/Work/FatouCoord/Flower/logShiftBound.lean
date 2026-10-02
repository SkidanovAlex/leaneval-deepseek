import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter

namespace Work.FatouCoord.Flower

/-- If `z` has positive real part and `z/w` has positive real part, then the principal
logarithm satisfies `log z - log w = log (z/w)` (the branch ambiguity is `2πiℤ`, and the
imaginary parts of the three principal logarithms force the integer to be `0`). -/
lemma log_sub_log_eq_log_div {z w : ℂ} (hw : w ≠ 0) (hz : z ≠ 0)
    (hzre : 0 < z.re) (hzwe : 0 < (z / w).re) :
    Complex.log z - Complex.log w = Complex.log (z / w) := by
  have hzw : z / w ≠ 0 := div_ne_zero hz hw
  have hexp : Complex.exp (Complex.log z)
      = Complex.exp (Complex.log w + Complex.log (z / w)) := by
    rw [Complex.exp_add, Complex.exp_log hz, Complex.exp_log hw, Complex.exp_log hzw,
      mul_div_cancel₀ z hw]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  have hn_im : ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)).im
      = (n : ℝ) * (2 * Real.pi) := by
    simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have hargz : |z.arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hzre)
  have hargw : |w.arg| ≤ Real.pi := Complex.abs_arg_le_pi w
  have hargzw : |(z / w).arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hzwe)
  have him : z.arg - w.arg - (z / w).arg = (n : ℝ) * (2 * Real.pi) := by
    have h := congrArg Complex.im hn
    simp only [Complex.add_im, Complex.log_im, hn_im] at h
    linarith
  have hlt : |(n : ℝ) * (2 * Real.pi)| < 2 * Real.pi := by
    rw [← him, abs_lt]
    constructor <;>
      linarith [hargz, hargw, hargzw, neg_abs_le z.arg, le_abs_self z.arg,
        neg_abs_le w.arg, le_abs_self w.arg, neg_abs_le (z / w).arg, le_abs_self (z / w).arg]
  have hn0 : n = 0 := by
    have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
    have h1 : |(n : ℝ)| < 1 := by
      have hc := hlt
      rw [abs_mul, abs_of_pos h2pi] at hc
      exact lt_of_mul_lt_mul_right (by simpa using hc) (le_of_lt h2pi)
    exact Int.abs_lt_one_iff.mp (by exact_mod_cast h1)
  rw [hn, hn0]
  simp

theorem logShiftBound (c : ℂ) : ∃ T : ℝ, 0 < T ∧ ∀ w : ℂ, T ≤ ‖w‖ →
    (w + c * (Complex.log w + (Real.pi : ℂ) * Complex.I)).re > 0 →
      ‖Complex.log (w + c * (Complex.log w + (Real.pi : ℂ) * Complex.I)) - Complex.log w‖
        ≤ 2 * ‖c‖ * (Real.log ‖w‖ + 2 * Real.pi) / ‖w‖ := by
  -- the ratio `(log x + 2π)/x` tends to `0`
  have hratio : Tendsto (fun x : ℝ => (Real.log x + 2 * Real.pi) / x) atTop (nhds 0) := by
    have h1 : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
      simpa using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero)
    have h2 : Tendsto (fun x : ℝ => (2 * Real.pi) / x) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h3 : Tendsto (fun x : ℝ => Real.log x / x + (2 * Real.pi) / x) atTop (nhds 0) := by
      simpa using h1.add h2
    exact h3.congr' (Eventually.of_forall fun x => by ring)
  have hg : Tendsto (fun x : ℝ => 2 * ‖c‖ * ((Real.log x + 2 * Real.pi) / x)) atTop (nhds 0) := by
    have hc := hratio.const_mul (2 * ‖c‖)
    simpa using hc
  have hev : ∀ᶠ x in atTop, 2 * ‖c‖ * ((Real.log x + 2 * Real.pi) / x) ≤ 1 :=
    hg.eventually_le_const (by norm_num)
  have hbig : ∀ᶠ x in atTop, (1 : ℝ) ≤ x := eventually_ge_atTop 1
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp (hev.and hbig)
  refine ⟨max T 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro w hwT hzre
  have hwT' : T ≤ ‖w‖ := le_trans (le_max_left T 1) hwT
  have hw1 : (1 : ℝ) ≤ ‖w‖ := le_trans (le_max_right T 1) hwT
  obtain ⟨hhr, -⟩ := hT ‖w‖ hwT'
  have hwnorm_pos : 0 < ‖w‖ := lt_of_lt_of_le one_pos hw1
  have hw : w ≠ 0 := norm_pos_iff.mp hwnorm_pos
  have hlog_nonneg : 0 ≤ Real.log ‖w‖ := Real.log_nonneg hw1
  let z : ℂ := w + c * (Complex.log w + (Real.pi : ℂ) * Complex.I)
  change ‖Complex.log z - Complex.log w‖ ≤ 2 * ‖c‖ * (Real.log ‖w‖ + 2 * Real.pi) / ‖w‖
  have hzre' : 0 < z.re := hzre
  have hz : z ≠ 0 := by
    intro h; rw [h] at hzre'; exact lt_irrefl 0 hzre'
  let s : ℂ := c * (Complex.log w + (Real.pi : ℂ) * Complex.I) / w
  have hzw_eq : z / w = 1 + s := by
    simp only [z, s]
    rw [add_div, div_self hw]
  have hs_bound : ‖s‖ ≤ ‖c‖ * ((Real.log ‖w‖ + 2 * Real.pi) / ‖w‖) := by
    have hlogw_bound : ‖Complex.log w + (Real.pi : ℂ) * Complex.I‖
        ≤ Real.log ‖w‖ + 2 * Real.pi := by
      have h1 : ‖Complex.log w + (Real.pi : ℂ) * Complex.I‖
          ≤ ‖Complex.log w‖ + ‖(Real.pi : ℂ) * Complex.I‖ := norm_add_le _ _
      have h2 : ‖(Real.pi : ℂ) * Complex.I‖ = Real.pi := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos Real.pi_pos]
      have h3 : ‖Complex.log w‖ ≤ Real.log ‖w‖ + Real.pi := by
        have h33 : ‖Complex.log w‖ ≤ |(Complex.log w).re| + |(Complex.log w).im| :=
          Complex.norm_le_abs_re_add_abs_im _
        rw [Complex.log_re, Complex.log_im] at h33
        have := Complex.abs_arg_le_pi w
        rw [abs_of_nonneg hlog_nonneg] at h33
        linarith
      linarith
    have hmul : ‖c * (Complex.log w + (Real.pi : ℂ) * Complex.I)‖
        ≤ ‖c‖ * (Real.log ‖w‖ + 2 * Real.pi) := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hlogw_bound (norm_nonneg c)
    simp only [s]
    rw [norm_div]
    calc ‖c * (Complex.log w + (Real.pi : ℂ) * Complex.I)‖ / ‖w‖
        ≤ ‖c‖ * (Real.log ‖w‖ + 2 * Real.pi) / ‖w‖ :=
          div_le_div_of_nonneg_right hmul (le_of_lt hwnorm_pos)
      _ = ‖c‖ * ((Real.log ‖w‖ + 2 * Real.pi) / ‖w‖) := by ring
  have hs_half : ‖s‖ ≤ 1 / 2 := by
    have h1 : ‖c‖ * ((Real.log ‖w‖ + 2 * Real.pi) / ‖w‖) ≤ 1 / 2 := by
      have h2 : 2 * ‖c‖ * ((Real.log ‖w‖ + 2 * Real.pi) / ‖w‖)
          = 2 * (‖c‖ * ((Real.log ‖w‖ + 2 * Real.pi) / ‖w‖)) := by ring
      rw [h2] at hhr
      linarith
    linarith [hs_bound]
  have hre1s : 0 < (1 + s).re := by
    have h1 : (1 + s).re = 1 + s.re := by simp
    have h2 : -(1 / 2 : ℝ) ≤ s.re := by
      have := Complex.abs_re_le_norm s
      linarith [hs_half, neg_abs_le s.re]
    rw [h1]; linarith
  have hzwnormre : 0 < (z / w).re := by rw [hzw_eq]; exact hre1s
  have hlogid : Complex.log z - Complex.log w = Complex.log (z / w) :=
    log_sub_log_eq_log_div hw hz hzre' hzwnormre
  calc ‖Complex.log z - Complex.log w‖
      = ‖Complex.log (1 + s)‖ := by rw [hlogid, hzw_eq]
    _ ≤ (3 / 2) * ‖s‖ := Complex.norm_log_one_add_half_le_self hs_half
    _ ≤ (3 / 2) * (‖c‖ * ((Real.log ‖w‖ + 2 * Real.pi) / ‖w‖)) :=
        mul_le_mul_of_nonneg_left hs_bound (by norm_num)
    _ ≤ 2 * ‖c‖ * (Real.log ‖w‖ + 2 * Real.pi) / ‖w‖ := by
        have hA : 0 ≤ ‖c‖ * ((Real.log ‖w‖ + 2 * Real.pi) / ‖w‖) :=
          mul_nonneg (norm_nonneg c)
            (div_nonneg (by linarith [hlog_nonneg, Real.pi_pos]) (le_of_lt hwnorm_pos))
        have heq : 2 * ‖c‖ * (Real.log ‖w‖ + 2 * Real.pi) / ‖w‖
            = 2 * (‖c‖ * ((Real.log ‖w‖ + 2 * Real.pi) / ‖w‖)) := by ring
        rw [heq]
        linarith

end Work.FatouCoord.Flower
