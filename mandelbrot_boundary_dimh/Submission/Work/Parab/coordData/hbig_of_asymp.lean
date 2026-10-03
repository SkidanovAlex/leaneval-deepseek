import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Parab.coordData.exists_log_threshold

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Work.Parab.coordData

/-- Reverse triangle inequality in the form needed below: `|x| - |y| ≤ |x + y|`. -/
private lemma abs_sub_le_abs_add (x y : ℝ) : |x| - |y| ≤ |x + y| := by
  have h := abs_add_le (x + y) (-y)
  have h' : (x + y) + -y = x := by ring
  rw [h', abs_neg] at h
  linarith

/-- **The imaginary-part bound at the bases of the ends argument** (`hbig` of the maximal-domain
construction).  If `u` lies in the repelling sector `QLeft ξ₀`, has `|Im u| ≥ η` and is confined
to the strip `‖u‖ ≤ |Im u| + ξ₀ + 3` (which is exactly what the bases
`u = w - (⌈Re w + ξ₀⌉ + 1)` of the ends argument satisfy), then the imaginary part of `τ u` is at
least `2 / ρ + c (1 + log (2 + ‖τ u‖))`.  This is precisely the hypothesis of
`Work.Parab.coordData.orbit_bound` with `R := 1 / ρ`. -/
theorem hbig_of_asymp {τ : ℂ → ℂ} {a b : ℂ} {ξ₀ ρ c : ℝ}
    (hξ₀ : 0 < ξ₀) (hρ : 0 < ρ) (hc : 0 ≤ c)
    (hτasym : ∀ ε > 0, ∃ R : ℝ, ∀ u ∈ MandelDim.QLeft ξ₀, R < ‖u‖ →
      ‖τ u - (u + a * Complex.log (-u) + b)‖ < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ u ∈ MandelDim.QLeft ξ₀, η ≤ |u.im| → ‖u‖ ≤ |u.im| + ξ₀ + 3 →
      2 * (1 / ρ) + c * (1 + Real.log (2 + ‖τ u‖)) ≤ |(τ u).im| := by
  -- the asymptotic is used at `ε = 1`, and later at any `t ≥ T`
  obtain ⟨R, hR⟩ := hτasym 1 (by norm_num)
  -- constants of the asymptotic
  set K : ℝ := ‖a‖ with hKdef
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  set L : ℝ := ‖a‖ * Real.pi + ‖b‖ + 1 with hLdef
  have hL0 : 0 ≤ L := by rw [hLdef]; positivity
  have h1KL : 1 ≤ 1 + K + L := by linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- the slope of `log (2 + ‖τ u‖)` as a function of `log (2 + ‖u‖)`
  set D : ℝ := 1 + Real.log (1 + K + L) / Real.log 2 with hDdef
  have hD0 : 0 ≤ D := by
    rw [hDdef]
    have : 0 ≤ Real.log (1 + K + L) / Real.log 2 :=
      div_nonneg (Real.log_nonneg h1KL) hlog2pos.le
    linarith
  have hKcD : 0 ≤ K + c * D := by
    have : 0 ≤ c * D := mul_nonneg hc hD0
    linarith
  -- the threshold coming from `log = o(t)`
  obtain ⟨T, hT1, hT⟩ := exists_log_threshold (K + c * D)
      ((K + c * D) * Real.log (1 + (ξ₀ + 3)) + L + 2 * (1 / ρ) + c - (K + c * D)) 0 1
  refine ⟨max T (max 1 (R + 1)), ?_, ?_⟩
  · have h : (1 : ℝ) ≤ max T (max 1 (R + 1)) :=
      le_trans (le_max_left 1 (R + 1)) (le_max_right T (max 1 (R + 1)))
    linarith
  · intro u huQ hy hstrip
    have hη1 : (1 : ℝ) ≤ max T (max 1 (R + 1)) :=
      le_trans (le_max_left 1 (R + 1)) (le_max_right T (max 1 (R + 1)))
    have hηT : T ≤ max T (max 1 (R + 1)) := le_max_left _ _
    have hηR : R + 1 ≤ max T (max 1 (R + 1)) :=
      le_trans (le_max_right 1 (R + 1)) (le_max_right T (max 1 (R + 1)))
    have hy1 : (1 : ℝ) ≤ |u.im| := le_trans hη1 hy
    have hyT : T ≤ |u.im| := le_trans hηT hy
    have hyR : R + 1 ≤ |u.im| := le_trans hηR hy
    have hsy : |u.im| ≤ ‖u‖ := Complex.abs_im_le_norm u
    have hs1 : (1 : ℝ) ≤ ‖u‖ := le_trans hy1 hsy
    have hspos : 0 < ‖u‖ := lt_of_lt_of_le zero_lt_one hs1
    have hsR : R < ‖u‖ := by linarith
    -- abbreviation for `log (2 + ‖u‖)`
    set A : ℝ := Real.log (2 + ‖u‖) with hAdef
    have hA' : Real.log (2 + ‖u‖) = A := hAdef.symm
    have hA2 : Real.log 2 ≤ A := by
      rw [hAdef]
      exact Real.log_le_log (by norm_num) (by linarith [norm_nonneg u])
    have hA0 : 0 ≤ A := le_trans (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)) hA2
    have hAle : A ≤ 2 + ‖u‖ := by
      rw [hAdef]; exact Real.log_le_self (by linarith [norm_nonneg u])
    -- the model `z = u + a log (-u) + b` of `τ u`
    set z : ℂ := u + a * Complex.log (-u) + b with hzdef
    have hclose : ‖τ u - z‖ < 1 := by rw [hzdef]; exact hR u huQ hsR
    -- `‖log (-u)‖ ≤ log ‖u‖ + π`
    have hlogn : ‖Complex.log (-u)‖ ≤ A + Real.pi := by
      have h1 : |(Complex.log (-u)).re| = Real.log ‖u‖ := by
        rw [Complex.log_re, norm_neg, abs_of_nonneg (Real.log_nonneg hs1)]
      have h2 : |(Complex.log (-u)).im| ≤ Real.pi := by
        rw [Complex.log_im]; exact Complex.abs_arg_le_pi _
      have h3 : Real.log ‖u‖ ≤ A := by
        rw [hAdef]; exact Real.log_le_log hspos (by linarith)
      calc ‖Complex.log (-u)‖ ≤ |(Complex.log (-u)).re| + |(Complex.log (-u)).im| :=
            Complex.norm_le_abs_re_add_abs_im _
        _ ≤ A + Real.pi := by linarith
    -- the imaginary part of `a log (-u) + b` is `O (log ‖u‖)`
    have him_ab : |(a * Complex.log (-u) + b).im| ≤ K * (A + Real.pi) + ‖b‖ := by
      have h1 : |(a * Complex.log (-u)).im| ≤ K * (A + Real.pi) := by
        have hnorm : ‖a * Complex.log (-u)‖ = K * ‖Complex.log (-u)‖ := by
          rw [Complex.norm_mul, hKdef]
        calc |(a * Complex.log (-u)).im| ≤ ‖a * Complex.log (-u)‖ := Complex.abs_im_le_norm _
          _ = K * ‖Complex.log (-u)‖ := hnorm
          _ ≤ K * (A + Real.pi) := mul_le_mul_of_nonneg_left hlogn hK0
      have h2 : |b.im| ≤ ‖b‖ := Complex.abs_im_le_norm b
      have h3 : (a * Complex.log (-u) + b).im = (a * Complex.log (-u)).im + b.im := by
        rw [Complex.add_im]
      rw [h3]
      have h4 : |(a * Complex.log (-u)).im + b.im| ≤ |(a * Complex.log (-u)).im| + |b.im| :=
        abs_add_le _ _
      linarith
    -- `‖z‖ ≤ ‖u‖ + K log ‖u‖ + (L - 1)`
    have hznorm : ‖z‖ ≤ ‖u‖ + K * A + (L - 1) := by
      have h1 : ‖z‖ ≤ ‖u + a * Complex.log (-u)‖ + ‖b‖ := by
        rw [hzdef]; exact norm_add_le _ _
      have h2 : ‖u + a * Complex.log (-u)‖ ≤ ‖u‖ + K * (A + Real.pi) := by
        have h3 := norm_add_le u (a * Complex.log (-u))
        have h4 : ‖a * Complex.log (-u)‖ = K * ‖Complex.log (-u)‖ := by
          rw [Complex.norm_mul, hKdef]
        have h5 := mul_le_mul_of_nonneg_left hlogn hK0
        rw [h4] at h3
        linarith
      have h6 : K * A + K * Real.pi = K * A + (L - 1) - ‖b‖ := by rw [hLdef]; ring
      linarith
    have hτnorm : ‖τ u‖ ≤ ‖u‖ + K * A + L := by
      have h1 : ‖τ u‖ ≤ ‖z‖ + ‖τ u - z‖ := by
        have h := norm_add_le z (τ u - z)
        have heq : z + (τ u - z) = τ u := by ring
        rwa [heq] at h
      linarith [h1, hznorm, hclose.le]
    -- `|Im τ u| ≥ |Im u| - K A - L`
    have hz_im : z.im = u.im + (a * Complex.log (-u) + b).im := by
      rw [hzdef]
      simp only [Complex.add_im]
      ring
    have himτ : |u.im| - K * A - L ≤ |(τ u).im| := by
      have h1 : |u.im| - |(a * Complex.log (-u) + b).im| ≤ |z.im| := by
        rw [hz_im]; exact abs_sub_le_abs_add u.im _
      have h2 : |z.im| - ‖τ u - z‖ ≤ |(τ u).im| := by
        have h := abs_sub_le_abs_add z.im (τ u - z).im
        have heq : z.im + (τ u - z).im = (τ u).im := by
          rw [← Complex.add_im]; congr 1; ring
        rw [heq] at h
        have h3 : |(τ u - z).im| ≤ ‖τ u - z‖ := Complex.abs_im_le_norm _
        linarith
      linarith
    -- `log (2 + ‖τ u‖)` grows at most like `D log (2 + ‖u‖)`
    have hlogτ : Real.log (2 + ‖τ u‖) ≤ D * A := by
      have hb1 : K * A ≤ K * (2 + ‖u‖) := mul_le_mul_of_nonneg_left hAle hK0
      have hb2 : L ≤ L * (2 + ‖u‖) := by
        have h2u : (1 : ℝ) ≤ 2 + ‖u‖ := by linarith [norm_nonneg u]
        nlinarith [hL0, h2u]
      have h2τ : 2 + ‖τ u‖ ≤ (2 + ‖u‖) * (1 + K + L) := by
        nlinarith [hτnorm, hb1, hb2, norm_nonneg u]
      have h1 : Real.log (2 + ‖τ u‖) ≤ Real.log ((2 + ‖u‖) * (1 + K + L)) :=
        Real.log_le_log (by linarith [norm_nonneg (τ u)]) h2τ
      rw [Real.log_mul (by linarith [norm_nonneg u]) (by linarith), hA'] at h1
      have hD : Real.log (1 + K + L) ≤ Real.log (1 + K + L) / Real.log 2 * A := by
        have hc0 : 0 ≤ Real.log (1 + K + L) / Real.log 2 :=
          div_nonneg (Real.log_nonneg h1KL) hlog2pos.le
        calc Real.log (1 + K + L) = Real.log (1 + K + L) / Real.log 2 * Real.log 2 := by
              field_simp
          _ ≤ Real.log (1 + K + L) / Real.log 2 * A := mul_le_mul_of_nonneg_left hA2 hc0
      have hDexp : D * A = A + Real.log (1 + K + L) / Real.log 2 * A := by
        rw [hDdef]; ring
      linarith
    -- `log (2 + ‖u‖) ≤ log (2 + |Im u|) + log (1 + (ξ₀ + 3))` from the strip condition
    have hAB : A ≤ Real.log (2 + |u.im|) + Real.log (1 + (ξ₀ + 3)) := by
      have hb3 : ξ₀ + 3 ≤ (ξ₀ + 3) * (2 + |u.im|) := by
        nlinarith [hy1, le_of_lt hξ₀]
      have h2 : 2 + ‖u‖ ≤ (2 + |u.im|) * (1 + (ξ₀ + 3)) := by
        nlinarith [hstrip, hy1, hb3, norm_nonneg u]
      calc A = Real.log (2 + ‖u‖) := hAdef
        _ ≤ Real.log ((2 + |u.im|) * (1 + (ξ₀ + 3))) := Real.log_le_log (by linarith) h2
        _ = Real.log (2 + |u.im|) + Real.log (1 + (ξ₀ + 3)) :=
            Real.log_mul (by linarith) (by linarith)
    -- the threshold, in expanded form
    have hTapp : (K + c * D) * Real.log (2 + |u.im|)
        + (K + c * D) * Real.log (1 + (ξ₀ + 3)) + L + 2 * (1 / ρ) + c < |u.im| := by
      have h := hT |u.im| hyT
      simp only [zero_add, one_mul] at h
      ring_nf at h
      ring_nf
      linarith [h]
    have hG1 : c * Real.log (2 + ‖τ u‖) ≤ c * (D * A) := mul_le_mul_of_nonneg_left hlogτ hc
    have hABw : (K + c * D) * A
        ≤ (K + c * D) * (Real.log (2 + |u.im|) + Real.log (1 + (ξ₀ + 3))) :=
      mul_le_mul_of_nonneg_left hAB hKcD
    nlinarith [himτ, hG1, hABw, hTapp]

end Work.Parab.coordData
