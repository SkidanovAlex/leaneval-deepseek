import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_strip_polyGrowth
import Submission.Commons.NumberTheory.Zeta.zeta_strip_polyGrowth_neg
import Submission.Commons.NumberTheory.Zeta.zeta_norm_le_const_of_three_le_re
import Submission.Commons.NumberTheory.Zeta.zeta_lower_re_two

open Complex Filter Metric Set
open scoped Real Topology BigOperators

noncomputable section

namespace Commons.NumberTheory.Zeta

/-- A point of the circle of radius 4 centred at `c = 2 + i·t` has real part in `[-2, 6]`,
imaginary part at least `1` in absolute value, and `|im| ≤ |t| + 4`. -/
private lemma sphere4_re_im {t : ℝ} (ht : 5 ≤ |t|) {z : ℂ}
    (hz : z ∈ Metric.sphere ((2 : ℂ) + Complex.I * (t : ℂ)) (4 : ℝ)) :
    -2 ≤ z.re ∧ z.re ≤ 6 ∧ 1 ≤ |z.im| ∧ |z.im| ≤ |t| + 4 := by
  let c : ℂ := (2 : ℂ) + Complex.I * (t : ℂ)
  change z ∈ Metric.sphere c 4 at hz
  have hd : dist z c = (4 : ℝ) := by simpa using (Metric.mem_sphere.mp hz)
  have hnorm : ‖z - c‖ = (4 : ℝ) := by simpa [dist_eq_norm] using hd
  have hre_abs : |z.re - 2| ≤ 4 := by
    calc
      |z.re - 2| = |(z - c).re| := by simp [c]
      _ ≤ ‖z - c‖ := Complex.abs_re_le_norm (z - c)
      _ = 4 := hnorm
  have him_abs : |z.im - t| ≤ 4 := by
    calc
      |z.im - t| = |(z - c).im| := by simp [c]
      _ ≤ ‖z - c‖ := Complex.abs_im_le_norm (z - c)
      _ = 4 := hnorm
  have habs := abs_le.mp hre_abs
  have him_bounds := abs_le.mp him_abs
  have hzge : t - 4 ≤ z.im := by linarith
  have hzle : z.im ≤ t + 4 := by linarith
  have ht_im_lo : 1 ≤ |z.im| := by
    by_cases ht0 : 0 ≤ t
    · have ht5 : 5 ≤ t := by
        have htn : |t| = t := abs_of_nonneg ht0
        rwa [htn] at ht
      have htz : 0 ≤ z.im := by linarith
      rw [abs_of_nonneg htz]
      linarith
    · have htneg : t < 0 := lt_of_not_ge ht0
      have htn : |t| = -t := abs_of_neg htneg
      have ht5 : t ≤ -5 := by
        rw [htn] at ht
        linarith
      have hzn : z.im ≤ 0 := by linarith
      rw [abs_of_nonpos hzn]
      linarith
  have ht_im_up : |z.im| ≤ |t| + 4 := by
    calc
      |z.im| = |(z.im - t) + t| := by congr 1; ring
      _ ≤ |z.im - t| + |t| := abs_add_le _ _
      _ ≤ |t| + 4 := by linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · exact ht_im_lo
  · exact ht_im_up

/-- Uniform growth of `ζ` on the circle of radius 4 centred at `2 + i·t` (`|t| ≥ 5`):
`‖ζ z‖ ≤ B · (|t| + 7)^12` for all `z` on the circle.  Obtained by splitting the circle into
the three regions `re ≤ -1` (use `zeta_strip_polyGrowth_neg`), `-1 ≤ re ≤ 3`
(`zeta_strip_polyGrowth`) and `re ≥ 3` (`zeta_norm_le_const_of_three_le_re`). -/
private lemma zeta_sphere4_bound :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (t : ℝ), 5 ≤ |t| → ∀ z : ℂ,
      z ∈ Metric.sphere ((2 : ℂ) + Complex.I * (t : ℂ)) (4 : ℝ) →
      ‖riemannZeta z‖ ≤ B * (|t| + 7) ^ 12 := by
  rcases zeta_strip_polyGrowth with ⟨Cpos, hCpos, hCposS⟩
  rcases zeta_strip_polyGrowth_neg with ⟨Cneg, hCneg, hCnegS⟩
  rcases zeta_norm_le_const_of_three_le_re with ⟨C3, hC3, hC3S⟩
  let C : ℝ := Cpos + Cneg + C3
  let B : ℝ := max C 1
  have hB1 : 1 ≤ B := le_max_right C 1
  have hCpos0 : 0 ≤ Cpos := le_of_lt hCpos
  have hCneg0 : 0 ≤ Cneg := le_of_lt hCneg
  have hC30 : 0 ≤ C3 := le_of_lt hC3
  have hCneg_le_B : Cneg ≤ B := by
    calc Cneg ≤ Cpos + Cneg + C3 := by nlinarith
    _ ≤ B := le_max_left C 1
  have hCpos_le_B : Cpos ≤ B := by
    calc Cpos ≤ Cpos + Cneg + C3 := by nlinarith
    _ ≤ B := le_max_left C 1
  have hC3_le_B : C3 ≤ B := by
    calc C3 ≤ Cpos + Cneg + C3 := by nlinarith
    _ ≤ B := le_max_left C 1
  refine ⟨B, hB1, ?_⟩
  intro t ht z hz
  obtain ⟨hσ_lo, _hσ_hi, htim1, htimup⟩ := sphere4_re_im (t := t) ht hz
  have hbase1 : 1 ≤ |z.im| + 3 := by linarith
  have hle7 : |z.im| + 3 ≤ |t| + 7 := by linarith
  have hpow12le : (|z.im| + 3) ^ 12 ≤ (|t| + 7) ^ 12 :=
    pow_le_pow_left₀ (by positivity : 0 ≤ |z.im| + 3) hle7 12
  have hpownn : 0 ≤ (|t| + 7) ^ 12 := by positivity
  have hzexp : ((z.re : ℂ) + Complex.I * (z.im : ℂ)) = z := by
    calc
      (z.re : ℂ) + Complex.I * (z.im : ℂ) = (z.re : ℂ) + (z.im : ℂ) * Complex.I := by ring
      _ = z := Complex.re_add_im z
  by_cases hneg : z.re ≤ -1
  · -- region re ∈ [-2, -1]
    have hb := hCnegS z.re z.im hσ_lo hneg htim1
    have hb0 : ‖riemannZeta z‖ ≤ Cneg * (|z.im| + 3) ^ 12 := by
      simpa [hzexp] using hb
    calc
      ‖riemannZeta z‖ ≤ Cneg * (|z.im| + 3) ^ 12 := hb0
      _ ≤ Cneg * (|t| + 7) ^ 12 := by
        exact mul_le_mul_of_nonneg_left hpow12le hCneg0
      _ ≤ B * (|t| + 7) ^ 12 := by
        exact mul_le_mul_of_nonneg_right hCneg_le_B hpownn
  · by_cases hle3 : z.re ≤ 3
    · -- region re ∈ (-1, 3]
      have hσ_ge : -1 ≤ z.re := by linarith
      have hb := hCposS z.re z.im hσ_ge hle3 htim1
      have hb0 : ‖riemannZeta z‖ ≤ Cpos * (|z.im| + 3) ^ 4 := by
        simpa [hzexp] using hb
      have hpow4 : (|z.im| + 3) ^ 4 ≤ (|z.im| + 3) ^ 12 :=
        pow_le_pow_right₀ hbase1 (by norm_num : (4 : ℕ) ≤ 12)
      calc
        ‖riemannZeta z‖ ≤ Cpos * (|z.im| + 3) ^ 4 := hb0
        _ ≤ Cpos * (|z.im| + 3) ^ 12 := by
          exact mul_le_mul_of_nonneg_left hpow4 hCpos0
        _ ≤ Cpos * (|t| + 7) ^ 12 := by
          exact mul_le_mul_of_nonneg_left hpow12le hCpos0
        _ ≤ B * (|t| + 7) ^ 12 := by
          exact mul_le_mul_of_nonneg_right hCpos_le_B hpownn
    · -- region re > 3
      have hσ3 : 3 ≤ z.re := by linarith
      have hb := hC3S z hσ3
      have hpow1 : 1 ≤ (|t| + 7) ^ 12 := by
        apply one_le_pow₀
        linarith
      calc
        ‖riemannZeta z‖ ≤ C3 := hb
        _ ≤ C3 * (|t| + 7) ^ 12 := by
          exact le_mul_of_one_le_right hC30 hpow1
        _ ≤ B * (|t| + 7) ^ 12 := by
          exact mul_le_mul_of_nonneg_right hC3_le_B hpownn

/-- **Lagarias–Jensen bound for the divisor of the Riemann zeta function on a disk of radius 3**
centred on the line `re s = 2` with `|t| ≥ 5`: the (integer, multiplicity-weighted) divisor sum
is `O(log |t|)`. -/
theorem zeta_ball3_divisor_le_log :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 5 ≤ |t| →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor riemannZeta
          (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ))) u : ℤ) : ℝ)) ≤
        K * (Real.log (|t| + 6) + 1) := by
  classical
  rcases zeta_sphere4_bound with ⟨B, hB1, hBspec⟩
  rcases zeta_lower_re_two with ⟨c0, hc0, hc0spec⟩
  let d : ℝ := Real.log ((4 : ℝ) / (3 : ℝ))
  have hd : 0 < d := by
    dsimp [d]
    exact Real.log_pos (by norm_num : (1 : ℝ) < (4 : ℝ) / (3 : ℝ))
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB1
  let A : ℝ := Real.log B + 12 * Real.log 2 - Real.log c0
  let K : ℝ := (12 + |A|) / d
  have hK : 0 < K := by
    dsimp [K, d]
    positivity
  refine ⟨K, hK, ?_⟩
  intro t ht
  let c : ℂ := (2 : ℂ) + Complex.I * (t : ℂ)
  let M : ℝ := B * (|t| + 7) ^ 12
  have hpow1 : 1 ≤ (|t| + 7) ^ 12 := by
    apply one_le_pow₀
    linarith
  have hM1 : 1 ≤ M := by
    dsimp [M]
    calc 1 ≤ B := hB1
    _ ≤ B * (|t| + 7) ^ 12 := le_mul_of_one_le_right (by positivity) hpow1
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  have hX1 : 1 ≤ |t| + 6 := by linarith
  have hlogX_nonneg : 0 ≤ Real.log (|t| + 6) := Real.log_nonneg hX1
  -- ζ is analytic on the closed ball of radius 4 (it avoids the pole at 1)
  have hdist1 : (4 : ℝ) < ‖(1 : ℂ) - c‖ := by
    have him := Complex.abs_im_le_norm ((1 : ℂ) - c)
    have hre : ((1 : ℂ) - c).im = -t := by simp [c]
    rw [hre] at him
    rw [abs_neg] at him
    linarith
  have hnot1 : (1 : ℂ) ∉ Metric.closedBall c (4 : ℝ) := by
    intro h1
    have hd' : ‖(1 : ℂ) - c‖ ≤ (4 : ℝ) := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using h1
    linarith
  have hζan : AnalyticOnNhd ℂ riemannZeta (Metric.closedBall c (4 : ℝ)) := by
    refine analyticOn_riemannZeta.mono ?_
    intro z hz hz1
    have hd' : ‖(1 : ℂ) - c‖ ≤ (4 : ℝ) := by
      rw [← hz1]
      simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    linarith
  have hζan4 : AnalyticOnNhd ℂ riemannZeta (Metric.closedBall c |(4 : ℝ)|) := by
    simpa using hζan
  -- ζ (2 + i t) ≠ 0, with the uniform lower bound
  have hfc : riemannZeta c ≠ 0 := by
    intro h0
    have hnorm0 : ‖riemannZeta c‖ = 0 := by simp [h0]
    have hlb : c0 ≤ ‖riemannZeta c‖ := by
      simpa [c] using hc0spec t
    linarith
  have hnormc : 0 < ‖riemannZeta c‖ := norm_pos_iff.mpr hfc
  have hlogc_lower : Real.log c0 ≤ Real.log ‖riemannZeta c‖ := by
    exact Real.log_le_log hc0 (by simpa [c] using hc0spec t)
  -- bound ζ on the circle of radius 4 by M
  have f_bound : ∀ z : ℂ, z ∈ Metric.sphere c |(4 : ℝ)| → ‖riemannZeta z‖ ≤ M := by
    intro z hz
    have hb := hBspec t ht z (by simpa [c] using hz)
    simpa [M] using hb
  -- Jensen inequality on the closed ball of radius 4, counting zeros in the ball of radius 3
  have hjs := AnalyticOnNhd.sum_divisor_le (c := c) (r := (3 : ℝ)) (R := (4 : ℝ))
      (M := M) (f := riemannZeta) (r_pos := by norm_num) (r_lt_R := by norm_num)
      (hM := hM1) (h₁f := hζan4) (h₂f := hfc) (f_bound := f_bound)
  have hEq3 : Metric.closedBall c (3 : ℝ) = Metric.closedBall c |(3 : ℝ)| := by
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
  have hfinZ3 : Function.HasFiniteSupport
      (fun u : ℂ => (MeromorphicOn.divisor riemannZeta (Metric.closedBall c |(3 : ℝ)|)) u) := by
    simpa [Function.HasFiniteSupport] using
      ((MeromorphicOn.divisor riemannZeta (Metric.closedBall c |(3 : ℝ)|)).finiteSupport
        (isCompact_closedBall c |(3 : ℝ)|))
  have hEqSum3 : ↑(∑ᶠ u : ℂ, ((MeromorphicOn.divisor riemannZeta (Metric.closedBall c |(3 : ℝ)|)) u : ℤ)) =
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor riemannZeta (Metric.closedBall c |(3 : ℝ)|)) u : ℤ) : ℝ)) := by
    simpa using ((Int.castRingHom ℝ).map_finsum hfinZ3)
  have hsumSet : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor riemannZeta (Metric.closedBall c (3 : ℝ))) u : ℤ) : ℝ)) =
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor riemannZeta (Metric.closedBall c |(3 : ℝ)|)) u : ℤ) : ℝ)) := by
    apply finsum_congr
    intro u
    rw [hEq3]
  have hsum : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor riemannZeta (Metric.closedBall c |(3 : ℝ)|)) u : ℤ) : ℝ)) ≤
      Real.log (M / ‖riemannZeta c‖) / d := by
    simpa [d] using (le_of_eq hEqSum3.symm).trans hjs
  -- arithmetic: log (M / ‖ζ c‖) ≤ (12 + |A|) * (log (|t|+6) + 1)
  have hlog7 : Real.log (|t| + 7) ≤ Real.log (|t| + 6) + Real.log 2 := by
    have hle : |t| + 7 ≤ 2 * (|t| + 6) := by nlinarith
    have hlog := Real.log_le_log (by positivity : 0 < |t| + 7)
      (le_trans hle (by nlinarith : 2 * (|t| + 6) ≤ 2 * (|t| + 6)))
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : |t| + 6 ≠ 0)] at hlog
    linarith
  have hlogM : Real.log M = Real.log B + 12 * Real.log (|t| + 7) := by
    dsimp [M]
    have hBne : B ≠ 0 := ne_of_gt hB0
    have hpne : (|t| + 7) ^ 12 ≠ 0 := by positivity
    rw [Real.log_mul hBne hpne, Real.log_pow]
    norm_num
  have hdivlog : Real.log (M / ‖riemannZeta c‖) = Real.log M - Real.log ‖riemannZeta c‖ := by
    exact Real.log_div (ne_of_gt hM0) (ne_of_gt hnormc)
  have hmain_upper : Real.log (M / ‖riemannZeta c‖) ≤ 12 * Real.log (|t| + 6) + A := by
    have hstep : Real.log M - Real.log c0 ≤ 12 * Real.log (|t| + 6) + A := by
      dsimp [A]
      rw [hlogM]
      have hlt : 12 * Real.log (|t| + 7) ≤ 12 * (Real.log (|t| + 6) + Real.log 2) :=
        mul_le_mul_of_nonneg_left hlog7 (by norm_num : (0 : ℝ) ≤ 12)
      linarith
    calc
      Real.log (M / ‖riemannZeta c‖) = Real.log M - Real.log ‖riemannZeta c‖ := hdivlog
      _ ≤ Real.log M - Real.log c0 := by linarith
      _ ≤ 12 * Real.log (|t| + 6) + A := hstep
  let X : ℝ := Real.log (|t| + 6) + 1
  have hXge1 : 1 ≤ X := by dsimp [X]; linarith
  have hA1 : |A| ≤ |A| * X := le_mul_of_one_le_right (abs_nonneg A) hXge1
  have hA2 : A ≤ |A| := le_abs_self A
  have hXlog : 12 * Real.log (|t| + 6) ≤ 12 * X := by
    dsimp [X]
    nlinarith
  have hfinal_upper : Real.log (M / ‖riemannZeta c‖) ≤ (12 + |A|) * X := by
    calc
      Real.log (M / ‖riemannZeta c‖) ≤ 12 * Real.log (|t| + 6) + A := hmain_upper
      _ ≤ (12 + |A|) * X := by nlinarith
  have hratio : Real.log (M / ‖riemannZeta c‖) / d ≤ K * X := by
    calc
      Real.log (M / ‖riemannZeta c‖) / d ≤ ((12 + |A|) * X) / d :=
        div_le_div_of_nonneg_right hfinal_upper (le_of_lt hd)
      _ = K * X := by
        dsimp [K]
        ring
  calc
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor riemannZeta
        (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ))) u : ℤ) : ℝ))
        = (∑ᶠ u : ℂ, (((MeromorphicOn.divisor riemannZeta (Metric.closedBall c (3 : ℝ))) u : ℤ) : ℝ)) := by
            dsimp [c]
    _ = (∑ᶠ u : ℂ, (((MeromorphicOn.divisor riemannZeta (Metric.closedBall c |(3 : ℝ)|)) u : ℤ) : ℝ)) := hsumSet
    _ ≤ Real.log (M / ‖riemannZeta c‖) / d := hsum
    _ ≤ K * X := hratio
    _ = K * (Real.log (|t| + 6) + 1) := by
      dsimp [X]

end Commons.NumberTheory.Zeta
