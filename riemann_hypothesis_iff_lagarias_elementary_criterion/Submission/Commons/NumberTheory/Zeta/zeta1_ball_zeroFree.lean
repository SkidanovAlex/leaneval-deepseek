import Mathlib.NumberTheory.Harmonic.ZetaAsymp

namespace Commons.NumberTheory.Zeta

theorem zeta1_ball_zeroFree (h : RiemannHypothesis) :
    ∀ T Tp δ : ℝ, 5 ≤ T → T ≤ Tp → Tp ≤ T + 1 → 0 < δ → δ ≤ 1 →
      (∀ ρ : ℂ, riemannZeta ρ = 0 → |ρ.im - Tp| ≤ δ → False) →
      ∀ w : ℂ, ‖w - ((2 : ℂ) + Complex.I * (Tp : ℂ))‖ < (3 / 2 : ℝ) + δ ^ 2 / 4 →
        riemannZeta₁ w ≠ 0 := by
  intro T Tp δ hT hTTp hTp1 hδpos hδle hnozero w hw hnz
  set c : ℂ := (2 : ℂ) + Complex.I * (Tp : ℂ) with hc
  -- the ball is contained in the disk of radius 2 around `2 + i Tp`
  have hlt2 : ‖w - c‖ < 2 := by
    nlinarith [hw, hδle, hδpos, sq_nonneg δ]
  -- hence `0 < re w`
  have hre_pos : 0 < w.re := by
    have h1 : |(w - c).re| ≤ ‖w - c‖ := Complex.abs_re_le_norm _
    have h2 : (w - c).re = w.re - 2 := by simp [hc]
    rw [h2] at h1
    have h3 : |w.re - 2| < 2 := lt_of_le_of_lt h1 hlt2
    rw [abs_lt] at h3
    linarith [h3.1]
  -- `w ≠ 1`
  have hw1 : w ≠ 1 := by
    rintro rfl
    simp at hnz
  -- `w` is a zero of `riemannZeta`
  have hzeta : riemannZeta w = 0 := by
    rw [riemannZeta_eq_inv_sub_mul hw1, hnz, mul_zero]
  -- `w` is not a trivial zero
  have hnottriv : ¬∃ n : ℕ, w = -2 * (n + 1) := by
    rintro ⟨n, hn⟩
    rw [hn] at hre_pos
    have hre : ((-2 : ℂ) * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by norm_num
    rw [hre] at hre_pos
    have hn0 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    nlinarith
  -- Riemann hypothesis puts `w` on the critical line
  have hhalf : w.re = 1 / 2 := h w hzeta hnottriv hw1
  -- geometry of the ball
  have hcval : c = (⟨2, Tp⟩ : ℂ) := by
    rw [hc]
    apply Complex.ext <;> simp
  have hdiff : w - c = (⟨w.re - 2, w.im - Tp⟩ : ℂ) := by
    rw [hcval]
    apply Complex.ext <;> simp
  have hsq : ‖w - c‖ ^ 2 = (w.re - 2) ^ 2 + (w.im - Tp) ^ 2 := by
    rw [Complex.sq_norm, hdiff, Complex.normSq_mk]
    ring
  have hsq_lt : ‖w - c‖ ^ 2 < (3 / 2 + δ ^ 2 / 4) ^ 2 :=
    (sq_lt_sq₀ (norm_nonneg _) (by positivity)).mpr hw
  have hIm2 : (w.im - Tp) ^ 2 < 3 * δ ^ 2 / 4 + δ ^ 4 / 16 := by
    have hre2 : (w.re - 2) ^ 2 = 9 / 4 := by rw [hhalf]; norm_num
    nlinarith [hsq_lt, hsq, hre2]
  have hδ2le : δ ^ 2 ≤ 1 := by nlinarith [hδpos, hδle]
  have hδ4le : δ ^ 4 ≤ δ ^ 2 := by nlinarith [hδ2le, sq_nonneg δ]
  have hIm2' : (w.im - Tp) ^ 2 < δ ^ 2 := by
    nlinarith [hIm2, hδ4le, hδpos]
  have hImabs : |w.im - Tp| < δ := abs_lt_of_sq_lt_sq hIm2' (le_of_lt hδpos)
  exact hnozero w hzeta (le_of_lt hImabs)

end Commons.NumberTheory.Zeta