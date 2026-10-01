import Mathlib
import Submission.Work.ZeroFreeTables.P9.zetaDiffExplicit_gen

namespace Work.ZeroFreeTables.P9

open scoped BigOperators Topology

/-- `‖(1 / w) ^ 2‖ = 1 / ‖w‖ ^ 2` for `w : ℂ`. -/
private lemma norm_inv_sq (w : ℂ) : ‖(1 / w) ^ 2‖ = 1 / ‖w‖ ^ 2 := by
  rw [norm_pow, norm_div, norm_one, div_pow, one_pow]

/-- For `w : ℂ` the real part of `(1 / w) ^ 2` is at least `-1 / ‖w‖ ^ 2`. -/
private lemma inv_sq_re_ge (w : ℂ) : -1 / ‖w‖ ^ 2 ≤ ((1 / w) ^ 2).re := by
  have h : -(1 / ‖w‖ ^ 2) ≤ ((1 / w) ^ 2).re := by
    have h' : -‖(1 / w) ^ 2‖ ≤ ((1 / w) ^ 2).re := by
      have h'' := Complex.abs_re_le_norm ((1 / w) ^ 2)
      rw [abs_le] at h''
      exact h''.1
    rwa [norm_inv_sq w] at h'
  rwa [neg_div'] at h

/-- If `0 < δ` and `δ / 2 ≤ r` then `-(1 + 4 / δ²) / (1 + r²) ≤ -1 / r²`. -/
private lemma neg_div_le_neg_inv_sq {δ r : ℝ} (hδ : 0 < δ) (hr : δ / 2 ≤ r) :
    -(1 + 4 / δ ^ 2) / (1 + r ^ 2) ≤ -1 / r ^ 2 := by
  have hrpos : 0 < r := lt_of_lt_of_le (by positivity) hr
  have hpos : 1 / r ^ 2 ≤ (1 + 4 / δ ^ 2) / (1 + r ^ 2) := by
    rw [div_le_div_iff₀ (pow_pos hrpos 2) (by positivity : (0 : ℝ) < 1 + r ^ 2)]
    have hkey : (1 : ℝ) ≤ (4 / δ ^ 2) * r ^ 2 := by
      have hδ2 : (0 : ℝ) < δ ^ 2 := by positivity
      have h2r : δ ≤ 2 * r := by linarith
      have h4 : δ ^ 2 ≤ 4 * r ^ 2 := by
        have h := pow_le_pow_left₀ (le_of_lt hδ) h2r 2
        nlinarith [h]
      rw [div_mul_eq_mul_div]
      calc (1 : ℝ) = δ ^ 2 / δ ^ 2 := (div_self (ne_of_gt hδ2)).symm
        _ ≤ 4 * r ^ 2 / δ ^ 2 := div_le_div_of_nonneg_right h4 (le_of_lt hδ2)
    have hexp : (1 + 4 / δ ^ 2) * r ^ 2 = (4 / δ ^ 2) * r ^ 2 + r ^ 2 := by ring
    linarith [hkey, hexp]
  have h1 : -(1 + 4 / δ ^ 2) / (1 + r ^ 2) = -((1 + 4 / δ ^ 2) / (1 + r ^ 2)) := by
    rw [neg_div]
  have h2 : -1 / r ^ 2 = -(1 / r ^ 2) := by rw [neg_div]
  rw [h1, h2]
  linarith [hpos]

theorem zetaFarZeroSqBound {a δ L Cz : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hLt : 1 < L)
    (haδL : 2 * a ≤ δ * L) {s : ℂ} (hsre : s.re = 1 + a / L)
    (hnz : ∀ u : ℂ, riemannZeta u = 0 → δ < ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖)
    (hCz : (∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2))) ≤ Cz) :
    (∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℝ) * ((1 / (s - u)) ^ 2).re)
      ≥ -(1 + 4 / δ ^ 2) * Cz := by
  have hLpos : 0 < L := lt_trans zero_lt_one hLt
  have haLpos : 0 < a / L := div_pos ha hLpos
  have hsc : 1 < s.re := by rw [hsre]; linarith
  -- the point `1 + i·Im s` lies at distance `a / L` from `s`
  have hw0 : s - ((1 : ℂ) + (s.im : ℂ) * Complex.I) = ((a / L : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero,
        zero_mul, sub_zero, add_zero]
      linarith [hsre]
    · simp only [Complex.sub_im, Complex.add_im, Complex.one_im, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero,
        zero_mul, add_zero, zero_add, sub_self]
  have hsw0 : ‖s - ((1 : ℂ) + (s.im : ℂ) * Complex.I)‖ = a / L := by
    rw [hw0, Complex.norm_of_nonneg (le_of_lt haLpos)]
  -- any zero of `Λ = completedRiemannZeta` is a zero of `ζ`
  have hfar : ∀ u : ℂ, analyticOrderNatAt completedRiemannZeta u ≠ 0 → δ / 2 ≤ ‖s - u‖ := by
    intro u hord
    have hζ : riemannZeta u = 0 := by
      have hu0 : u ≠ 0 := by
        intro h
        rw [h] at hord
        exact hord
          (analyticOrderNatAt_of_not_analyticAt Work.LinnikAreas.not_analyticAt_completedZeta_zero)
      rw [riemannZeta_def_of_ne_zero hu0, apply_eq_zero_of_analyticOrderNatAt_ne_zero hord,
        zero_div]
    have hδu : δ < ‖((1 : ℂ) + (s.im : ℂ) * Complex.I) - u‖ := hnz u hζ
    have haLδ : a / L ≤ δ / 2 := by
      rw [div_le_div_iff₀ hLpos (by norm_num : (0 : ℝ) < 2)]
      linarith [haδL]
    have htri : ‖((1 : ℂ) + (s.im : ℂ) * Complex.I) - u‖
        ≤ ‖s - ((1 : ℂ) + (s.im : ℂ) * Complex.I)‖ + ‖s - u‖ := by
      have hsplit : ((1 : ℂ) + (s.im : ℂ) * Complex.I) - u
          = (s - u) - (s - ((1 : ℂ) + (s.im : ℂ) * Complex.I)) := by ring
      rw [hsplit]
      calc ‖(s - u) - (s - ((1 : ℂ) + (s.im : ℂ) * Complex.I))‖
          ≤ ‖s - u‖ + ‖s - ((1 : ℂ) + (s.im : ℂ) * Complex.I)‖ := norm_sub_le _ _
        _ = ‖s - ((1 : ℂ) + (s.im : ℂ) * Complex.I)‖ + ‖s - u‖ := add_comm _ _
    linarith [hδu, htri, hsw0, haLδ, hδ]
  -- summability of the complex zero sum
  have hsummC : Summable (fun u : ℂ =>
      (analyticOrderNatAt completedRiemannZeta u : ℂ) * (1 / (s - u)) ^ 2) :=
    zetaZeroSum_summable_gen 1 le_rfl hsc
  -- summability of the real part
  have hfsumm : Summable (fun u : ℂ =>
      (analyticOrderNatAt completedRiemannZeta u : ℝ) * ((1 / (s - u)) ^ 2).re) := by
    have h := Complex.reCLM.summable hsummC
    refine h.congr (fun u => ?_)
    simp only [Complex.reCLM_apply, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero]
  -- summability of the kernel sum
  have hksumm : Summable (fun u : ℂ =>
      (analyticOrderNatAt completedRiemannZeta u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2))) := by
    refine Summable.of_nonneg_of_le (fun u => ?_) (fun u => ?_) hsummC.norm
    · exact mul_nonneg (Nat.cast_nonneg _) (by positivity)
    · by_cases h0 : analyticOrderNatAt completedRiemannZeta u = 0
      · simp [h0]
      · have hr : δ / 2 ≤ ‖s - u‖ := hfar u h0
        have hrpos : 0 < ‖s - u‖ := lt_of_lt_of_le (by positivity) hr
        have hle1 : 1 / (1 + ‖s - u‖ ^ 2) ≤ 1 / ‖s - u‖ ^ 2 := by
          rw [div_le_div_iff₀ (by positivity) (pow_pos hrpos 2)]
          nlinarith [sq_nonneg ‖s - u‖]
        calc (analyticOrderNatAt completedRiemannZeta u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2))
            ≤ (analyticOrderNatAt completedRiemannZeta u : ℝ) * (1 / ‖s - u‖ ^ 2) :=
              mul_le_mul_of_nonneg_left hle1 (Nat.cast_nonneg _)
          _ = ‖(analyticOrderNatAt completedRiemannZeta u : ℂ) * (1 / (s - u)) ^ 2‖ := by
              rw [norm_mul, Complex.norm_natCast, norm_inv_sq]
  -- pointwise comparison
  have hpt : ∀ u : ℂ, (-(1 + 4 / δ ^ 2)) *
      ((analyticOrderNatAt completedRiemannZeta u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2)))
      ≤ (analyticOrderNatAt completedRiemannZeta u : ℝ) * ((1 / (s - u)) ^ 2).re := by
    intro u
    by_cases h0 : analyticOrderNatAt completedRiemannZeta u = 0
    · simp [h0]
    · have hr : δ / 2 ≤ ‖s - u‖ := hfar u h0
      have h₁ : -1 / ‖s - u‖ ^ 2 ≤ ((1 / (s - u)) ^ 2).re := inv_sq_re_ge (s - u)
      have h₂ : -(1 + 4 / δ ^ 2) / (1 + ‖s - u‖ ^ 2) ≤ -1 / ‖s - u‖ ^ 2 :=
        neg_div_le_neg_inv_sq hδ hr
      have hc : (0 : ℝ) ≤ (analyticOrderNatAt completedRiemannZeta u : ℝ) := Nat.cast_nonneg _
      have key : (-(1 + 4 / δ ^ 2)) *
            ((analyticOrderNatAt completedRiemannZeta u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2)))
          = (analyticOrderNatAt completedRiemannZeta u : ℝ) *
            (-(1 + 4 / δ ^ 2) / (1 + ‖s - u‖ ^ 2)) := by ring
      rw [key]
      exact le_trans (mul_le_mul_of_nonneg_left h₂ hc) (mul_le_mul_of_nonneg_left h₁ hc)
  -- assembly
  have hgsumm : Summable (fun u : ℂ => (-(1 + 4 / δ ^ 2)) *
      ((analyticOrderNatAt completedRiemannZeta u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2)))) :=
    Summable.mul_left (-(1 + 4 / δ ^ 2)) hksumm
  have hkey : (-(1 + 4 / δ ^ 2)) *
      (∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2)))
      ≤ ∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℝ) * ((1 / (s - u)) ^ 2).re := by
    have h := Summable.tsum_le_tsum hpt hgsumm hfsumm
    rwa [tsum_mul_left] at h
  have hneg : (-(1 + 4 / δ ^ 2)) ≤ 0 := by
    have : (0 : ℝ) < 1 + 4 / δ ^ 2 := by positivity
    linarith
  calc (-(1 + 4 / δ ^ 2)) * Cz
      ≤ (-(1 + 4 / δ ^ 2)) *
          (∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2))) :=
        mul_le_mul_of_nonpos_left hCz hneg
    _ ≤ ∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℝ) * ((1 / (s - u)) ^ 2).re := hkey

end Work.ZeroFreeTables.P9
