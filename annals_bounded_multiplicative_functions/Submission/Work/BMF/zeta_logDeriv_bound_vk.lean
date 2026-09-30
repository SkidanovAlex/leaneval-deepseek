import Mathlib
import Submission.Work.BMF.VKdenom
import Submission.Work.BMF.VK.VKd_ge_half
import Submission.Work.BMF.vk_L_lower
import Submission.Work.BMF.vk_L_upper
import Submission.Work.BMF.V4prelim
import Submission.Commons.NumberTheory.Zeta.zeta_lower_bound_right_of_one
import Submission.Commons.NumberTheory.Zeta.zeta_strip_growth
import Submission.Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound_analytic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1000000

/-!
# The `ζ′/ζ`-bound in the Vinogradov–Korobov zero-free region, from the zero-free region

From the Vinogradov–Korobov zero-free region for `ζ` (a constant `c₁ > 0` with
`ζ(σ+it) ≠ 0` whenever `|t| ≥ 3` and `1 - c₁/VKd(|t|+3) ≤ σ ≤ 1`) we derive the
log-derivative bound `‖ζ′/ζ(σ+it)‖ ≤ B (log(|t|+3))²` in the (possibly narrower) region
`1 - c₂/VKd(|t|+3) ≤ σ ≤ 2`, with `c₂ = min (c₁/8) (1/64)`.

Three regimes: bounded heights (`3 ≤ |t| ≤ 16`, compactness); large heights with
`σ ≥ 1 + 2c₂/VKd(|t|+3)` (disc of radius `c₂/(2VKd)` around `σ+it`, inside `Re > 1`); and
large heights with `σ ≤ 1 + 2c₂/VKd(|t|+3)` (disc of radius `3c₂/VKd` around
`1 + c₂/VKd + it`, zero-free by hypothesis, growth controlled by the strip bound).
-/

namespace Work.BMF

open Complex Metric Set Filter
open scoped Real Topology

noncomputable section

/-! ## Euler-product bounds on `Re s > 1` -/

private lemma zeta_norm_le_complex {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s‖ ≤ 1 + 1 / (s.re - 1) := by
  have h := vk_L_upper (1 : DirichletCharacter ℂ 1) (s := s) hs
  rw [DirichletCharacter.LFunction_modOne_eq] at h
  have h2 : (riemannZeta (s.re : ℂ)).re ≤ 1 + 1 / (s.re - 1) := by
    have h3 := riemannZeta_norm_le_one_add_inv s.re hs
    have h4 := Complex.re_le_norm (riemannZeta (s.re : ℂ))
    exact le_trans h4 h3
  exact le_trans h h2

private lemma zeta_norm_ge_complex {s : ℂ} (hs : 1 < s.re) :
    ((riemannZeta (s.re : ℂ)).re)⁻¹ ≤ ‖riemannZeta s‖ := by
  have h := vk_L_lower (1 : DirichletCharacter ℂ 1) (s := s) hs
  rw [DirichletCharacter.LFunction_modOne_eq] at h
  have hζpos : 0 < (riemannZeta (s.re : ℂ)).re := riemannZeta_re_pos_of_one_lt hs
  rw [← one_div, div_le_iff₀ hζpos]
  linarith

/-! ## Bounded heights: compactness -/

private lemma VKd_abs_im_le : ∀ z : ℂ, 3 ≤ |z.im| → |z.im| ≤ 16 → VKd (|z.im| + 3) ≤ 8 * VKd 6 := by
  intro z h3 h16
  have hy3 : 3 ≤ |z.im| + 3 := by linarith [abs_nonneg z.im]
  have hlog19 : Real.log 19 ≤ 3 := by
    rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 19)]
    have h3' : Real.exp 3 = (Real.exp 1) ^ 3 := by
      have h := Real.exp_nat_mul (1 : ℝ) 3
      simpa using h
    rw [h3']
    have h2 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h4 : (2.7 : ℝ) ^ 3 < (Real.exp 1) ^ 3 :=
      pow_lt_pow_left₀ h2 (by norm_num) (by norm_num)
    have h5 : (19 : ℝ) ≤ (2.7 : ℝ) ^ 3 := by norm_num
    linarith
  have h1 : VKd (|z.im| + 3) ≤ Real.log (|z.im| + 3) := VKd_le_log hy3
  have h2 : Real.log (|z.im| + 3) ≤ Real.log 19 :=
    Real.log_le_log (by linarith [abs_nonneg z.im]) (by linarith)
  have h6 : (1 / 2 : ℝ) ≤ VKd 6 := VK.VKd_ge_half (by norm_num)
  linarith

private lemma logDeriv_bounded_height' (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hc₂c₁ : 8 * c₂ ≤ c₁) (hc₂le : c₂ ≤ 1 / 64)
    (hzf : ∀ t σ : ℝ, 3 ≤ |t| → 1 - c₁ / VKd (|t| + 3) ≤ σ → σ ≤ 1 →
      riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ t σ : ℝ, 3 ≤ |t| → |t| ≤ 16 →
      1 - c₂ / VKd (|t| + 3) ≤ σ → σ ≤ 2 →
      ‖deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) /
        riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C * (Real.log (|t| + 3)) ^ 2 := by
  have hV6pos : 0 < VKd 6 := VKd_pos (by norm_num)
  let K : Set ℂ := {z : ℂ | 1 - c₂ / VKd 6 ≤ z.re ∧ z.re ≤ 2 ∧ 3 ≤ |z.im| ∧ |z.im| ≤ 16}
  have hKclosed : IsClosed K := by
    dsimp [K]
    rw [show ({z : ℂ | 1 - c₂ / VKd 6 ≤ z.re ∧ z.re ≤ 2 ∧ 3 ≤ |z.im| ∧ |z.im| ≤ 16} : Set ℂ)
        = {z : ℂ | 1 - c₂ / VKd 6 ≤ z.re} ∩ {z : ℂ | z.re ≤ 2} ∩ {z : ℂ | 3 ≤ |z.im|} ∩
          {z : ℂ | |z.im| ≤ 16} by
          ext z
          simp [and_assoc]]
    refine IsClosed.inter ?_ ?_
    · refine IsClosed.inter ?_ ?_
      · refine IsClosed.inter ?_ ?_
        · exact isClosed_le continuous_const Complex.continuous_re
        · exact isClosed_le Complex.continuous_re continuous_const
      · exact isClosed_le continuous_const (Continuous.comp continuous_abs Complex.continuous_im)
    · exact isClosed_le (Continuous.comp continuous_abs Complex.continuous_im) continuous_const
  have hKbdd : Bornology.IsBounded K := by
    refine isBounded_iff_forall_norm_le.mpr ⟨21, ?_⟩
    intro z hz
    dsimp [K] at hz
    obtain ⟨hz1, hz2, hz3, hz4⟩ := hz
    have hrelo : 0 ≤ z.re := by
      have h6 : (1 / 2 : ℝ) ≤ VKd 6 := VK.VKd_ge_half (by norm_num)
      have h2 : c₂ / VKd 6 ≤ 1 := by
        rw [div_le_iff₀ hV6pos]
        calc c₂ ≤ 1 / 64 := hc₂le
          _ ≤ 1 / 2 := by norm_num
          _ ≤ VKd 6 := h6
          _ = 1 * VKd 6 := by ring
      have h3 : (0 : ℝ) ≤ 1 - c₂ / VKd 6 := by linarith
      exact le_trans h3 hz1
    have hre_abs : |z.re| ≤ 2 := by
      rw [abs_of_nonneg hrelo]
      exact hz2
    have hnorm : ‖z‖ ≤ |z.re| + |z.im| := by
      have hdecomp : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := (Complex.re_add_im z).symm
      calc ‖z‖ = ‖(z.re : ℂ) + (z.im : ℂ) * Complex.I‖ := by
            conv_lhs => rw [hdecomp]
        _ ≤ ‖(z.re : ℂ)‖ + ‖(z.im : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = |z.re| + |z.im| := by simp [Complex.norm_real, Real.norm_eq_abs]
    linarith
  have hKcompact : IsCompact K := by
    rw [Metric.isCompact_iff_isClosed_bounded]
    exact ⟨hKclosed, hKbdd⟩
  have hKsub : K ⊆ ({1}ᶜ : Set ℂ) := by
    intro z hz
    dsimp [K] at hz
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h1
    have h := hz.2.2.1
    rw [h1] at h
    simp at h
    linarith
  have hdgC : ContinuousOn (deriv riemannZeta) K :=
    ((analyticOn_riemannZeta.mono hKsub).deriv).continuousOn
  have hzC : ContinuousOn riemannZeta K := (analyticOn_riemannZeta.mono hKsub).continuousOn
  have hneK : ∀ z ∈ K, riemannZeta z ≠ 0 := by
    intro z hz
    dsimp [K] at hz
    obtain ⟨hz1, hz2, hz3, hz4⟩ := hz
    by_cases hzre : (1 : ℝ) ≤ z.re
    · exact riemannZeta_ne_zero_of_one_le_re hzre
    · push Not at hzre
      have hy3 : 3 ≤ |z.im| + 3 := by linarith [abs_nonneg z.im]
      have hWpos : 0 < VKd (|z.im| + 3) := VKd_pos hy3
      have hcmp : c₂ / VKd 6 ≤ c₁ / VKd (|z.im| + 3) := by
        rw [div_le_div_iff₀ hV6pos hWpos]
        have h8 := VKd_abs_im_le z (by linarith) hz4
        calc c₂ * VKd (|z.im| + 3) ≤ c₂ * (8 * VKd 6) := mul_le_mul_of_nonneg_left h8 hc₂.le
          _ = 8 * c₂ * VKd 6 := by ring
          _ ≤ c₁ * VKd 6 := mul_le_mul_of_nonneg_right hc₂c₁ hV6pos.le
      have hineq : 1 - c₁ / VKd (|z.im| + 3) ≤ z.re := by linarith
      have hz0 := hzf z.im z.re hz3 hineq (le_of_lt hzre)
      rwa [Complex.re_add_im z] at hz0
  have hcont : ContinuousOn (fun z : ℂ => deriv riemannZeta z / riemannZeta z) K :=
    ContinuousOn.div hdgC hzC hneK
  obtain ⟨C₀, hC₀⟩ := IsCompact.exists_bound_of_continuousOn hKcompact hcont
  have hmaxpos : (0 : ℝ) < max C₀ 1 := lt_of_lt_of_le zero_lt_one (le_max_right C₀ 1)
  refine ⟨max C₀ 1, hmaxpos, ?_⟩
  intro t σ ht ht16 hσlo hσ2
  have hy3 : 3 ≤ |t| + 3 := by linarith [abs_nonneg t]
  have hVpos : 0 < VKd (|t| + 3) := VKd_pos hy3
  have hV6le : VKd 6 ≤ VKd (|t| + 3) := VKd_mono (by norm_num) (by linarith)
  have hzK : ((σ : ℂ) + (t : ℂ) * Complex.I) ∈ K := by
    dsimp [K]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h1 : c₂ / VKd (|t| + 3) ≤ c₂ / VKd 6 := by
        rw [div_le_div_iff₀ hVpos hV6pos]
        exact mul_le_mul_of_nonneg_left hV6le hc₂.le
      have h2 : 1 - c₂ / VKd 6 ≤ σ := by linarith
      simpa using h2
    · simpa using hσ2
    · simpa using ht
    · simpa using ht16
  have hbd := hC₀ _ hzK
  have hL1 : 1 ≤ Real.log (|t| + 3) := one_le_log hy3
  have hpow1 : (1 : ℝ) ≤ (Real.log (|t| + 3)) ^ 2 := by
    calc (1 : ℝ) = 1 ^ 2 := by norm_num
      _ ≤ (Real.log (|t| + 3)) ^ 2 := pow_le_pow_left₀ (by norm_num) hL1 2
  have h0C₀ : (0 : ℝ) ≤ C₀ := le_trans (norm_nonneg _) hbd
  have hpow_nonneg : (0 : ℝ) ≤ (Real.log (|t| + 3)) ^ 2 := sq_nonneg _
  calc ‖deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) /
        riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C₀ := hbd
    _ ≤ C₀ * (Real.log (|t| + 3)) ^ 2 := by nlinarith [hbd, hpow1, h0C₀]
    _ ≤ max C₀ 1 * (Real.log (|t| + 3)) ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_left C₀ 1) hpow_nonneg

/-! ## Large `σ`: the disc centred at `σ + it` lies in `Re > 1` -/

private lemma logDeriv_large_sigma' (c₂ : ℝ) (hc₂ : 0 < c₂) (hc₂le : c₂ ≤ 1 / 64)
    (hV : ∀ t : ℝ, 3 ≤ |t| → 1 / 2 ≤ VKd (|t| + 3)) :
    ∃ C : ℝ, 0 < C ∧ ∀ t σ : ℝ, 3 ≤ |t| →
      1 + 2 * c₂ / VKd (|t| + 3) ≤ σ → σ ≤ 2 →
      ‖deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) /
        riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C * (Real.log (|t| + 3)) ^ 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogc : 0 ≤ Real.log (1 / c₂) := by
    apply Real.log_nonneg
    rw [one_div, one_le_inv₀ hc₂]
    linarith
  set Kk : ℝ := Real.log 2 + 2 * Real.log (1 / c₂) + 2 with hKk
  have hKkpos : 0 < Kk := by rw [hKk]; linarith
  refine ⟨8 * Kk / c₂, div_pos (mul_pos (by norm_num) hKkpos) hc₂, ?_⟩
  intro t σ ht hσ hσ2
  have hy3 : 3 ≤ |t| + 3 := by linarith [abs_nonneg t]
  set V : ℝ := VKd (|t| + 3) with hVdef
  set L : ℝ := Real.log (|t| + 3) with hLdef
  have hVpos : 0 < V := VKd_pos hy3
  have hVhalf : 1 / 2 ≤ V := hV t ht
  have hL1 : 1 ≤ L := one_le_log hy3
  have hVL : V ≤ L := VKd_le_log hy3
  have hLnonneg : 0 ≤ L := le_of_lt (lt_of_lt_of_le zero_lt_one hL1)
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  set X : ℝ := c₂ / V with hXdef
  have hXpos : 0 < X := div_pos hc₂ hVpos
  have hXle : X ≤ 1 / 32 := by
    rw [hXdef, div_le_iff₀ hVpos]
    linarith [hVhalf, hc₂le]
  have hσ' : 1 + 2 * X ≤ σ := by
    change 1 + 2 * (c₂ / V) ≤ σ
    rw [show 2 * (c₂ / V) = 2 * c₂ / V by ring]
    exact hσ
  have hσ1 : 1 < σ := by linarith [hXpos, hσ']
  set z₀ : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hz₀def
  have hz₀re : z₀.re = σ := by rw [hz₀def]; simp
  set R₁ : ℝ := X / 2 with hR₁def
  set ρ : ℝ := X / 4 with hρdef
  have hR₁pos : 0 < R₁ := by rw [hR₁def]; linarith
  have hρpos : 0 < ρ := by rw [hρdef]; linarith
  have hρlt : ρ < R₁ - ‖z₀ - z₀‖ := by
    rw [sub_self, norm_zero, sub_zero, hR₁def, hρdef]
    linarith
  have hz₀ball : z₀ ∈ Metric.ball z₀ R₁ := by
    rw [Metric.mem_ball, dist_self]
    exact hR₁pos
  have hre_gt : ∀ w : ℂ, w ∈ Metric.ball z₀ R₁ → 1 < w.re := by
    intro w hw
    have hwR : ‖w - z₀‖ < R₁ := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    have h1 : |w.re - σ| ≤ ‖w - z₀‖ := by
      have h2 := Complex.abs_re_le_norm (w - z₀)
      rwa [show (w - z₀).re = w.re - σ by simp [hz₀def]] at h2
    have h3 : σ - R₁ < w.re := by
      have h4 := (abs_le.mp h1).1
      linarith
    have h5 : 1 + 3 * X / 2 ≤ σ - R₁ := by
      rw [hR₁def]
      linarith [hσ']
    linarith [hXpos, h3, h5]
  have hball1 : Metric.ball z₀ R₁ ⊆ ({1}ᶜ : Set ℂ) := by
    intro w hw
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hw1
    have h1 := hre_gt w hw
    rw [hw1] at h1
    exact absurd h1 (by norm_num)
  have hgan : AnalyticOnNhd ℂ riemannZeta (Metric.ball z₀ R₁) :=
    analyticOn_riemannZeta.mono hball1
  have hgne : ∀ w : ℂ, w ∈ Metric.ball z₀ R₁ → riemannZeta w ≠ 0 :=
    fun w hw => riemannZeta_ne_zero_of_one_le_re (le_of_lt (hre_gt w hw))
  have hM : ∀ w : ℂ, w ∈ Metric.ball z₀ R₁ → ‖riemannZeta w‖ ≤ 1 + 2 / (3 * X) := by
    intro w hw
    have hwR : ‖w - z₀‖ < R₁ := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    have h1 : |w.re - σ| ≤ ‖w - z₀‖ := by
      have h2 := Complex.abs_re_le_norm (w - z₀)
      rwa [show (w - z₀).re = w.re - σ by simp [hz₀def]] at h2
    have h3 : σ - R₁ < w.re := by
      have h4 := (abs_le.mp h1).1
      linarith
    have h4 : 3 * X / 2 ≤ w.re - 1 := by
      rw [hR₁def] at h3
      linarith [hσ', h3]
    have h5 : 1 < w.re := by linarith [hXpos, h4]
    have h6 := zeta_norm_le_complex (s := w) h5
    have h7 : 1 / (w.re - 1) ≤ 2 / (3 * X) := by
      have h8 : 1 / (w.re - 1) ≤ 1 / (3 * X / 2) :=
        one_div_le_one_div_of_le (by linarith [hXpos] : (0 : ℝ) < 3 * X / 2) h4
      have h9 : 1 / (3 * X / 2) = 2 / (3 * X) := by
        rw [one_div, inv_div]
      linarith [h8, h9]
    linarith [h6, h7]
  have hmpos : 0 < (σ - 1) / 2 := by linarith
  have hmM : (σ - 1) / 2 ≤ 1 + 2 / (3 * X) := by
    have h1 : 0 < 2 / (3 * X) := div_pos (by norm_num) (by linarith [hXpos])
    linarith
  have hmle : (σ - 1) / 2 ≤ ‖riemannZeta z₀‖ := by
    have hz₀1 : 1 < z₀.re := by rw [hz₀re]; exact hσ1
    have hlow := zeta_norm_ge_complex (s := z₀) hz₀1
    rw [hz₀re] at hlow
    have hApos : 0 < (riemannZeta (σ : ℂ)).re := riemannZeta_re_pos_of_one_lt hσ1
    have hAle : (riemannZeta (σ : ℂ)).re ≤ σ / (σ - 1) := by
      have h1 : ‖riemannZeta (σ : ℂ)‖ ≤ 1 + 1 / (σ - 1) := by
        have h := zeta_norm_le_complex (s := (σ : ℂ)) hσ1
        simpa using h
      have h2 : (riemannZeta (σ : ℂ)).re ≤ ‖riemannZeta (σ : ℂ)‖ := Complex.re_le_norm _
      have h3 : 1 + 1 / (σ - 1) = σ / (σ - 1) := by
        have hne : σ - 1 ≠ 0 := by linarith
        rw [eq_div_iff hne, add_mul, one_mul, div_mul_cancel₀ _ hne]
        ring
      linarith
    have hkey : (σ - 1) / 2 * ((riemannZeta (σ : ℂ)).re) ≤ 1 := by
      have h4 : (σ - 1) * ((riemannZeta (σ : ℂ)).re) ≤ σ := by
        have h5 : (σ - 1) * ((riemannZeta (σ : ℂ)).re) ≤ (σ - 1) * (σ / (σ - 1)) :=
          mul_le_mul_of_nonneg_left hAle (by linarith)
        have h6 : (σ - 1) * (σ / (σ - 1)) = σ := by
          rw [mul_div_assoc', mul_comm (σ - 1) σ,
              mul_div_cancel_right₀ σ (by linarith : σ - 1 ≠ 0)]
        linarith
      have h7 : (σ - 1) / 2 * ((riemannZeta (σ : ℂ)).re) =
          (σ - 1) * ((riemannZeta (σ : ℂ)).re) / 2 := by ring
      rw [h7]
      linarith
    have hfin : (σ - 1) / 2 ≤ ((riemannZeta (σ : ℂ)).re)⁻¹ := by
      calc (σ - 1) / 2
          = (σ - 1) / 2 * ((riemannZeta (σ : ℂ)).re) / ((riemannZeta (σ : ℂ)).re) := by
            rw [mul_div_cancel_right₀ _ hApos.ne']
        _ ≤ 1 / ((riemannZeta (σ : ℂ)).re) := div_le_div_of_nonneg_right hkey hApos.le
        _ = ((riemannZeta (σ : ℂ)).re)⁻¹ := by rw [one_div]
    linarith
  have hball := Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound_analytic
      (g := riemannZeta) (c := z₀) (R := R₁) (m := (σ - 1) / 2) (M := 1 + 2 / (3 * X))
      hR₁pos hmpos hmM hgan hgne hM hmle
  have hmain := hball hz₀ball ρ hρpos hρlt
  have hRρ : R₁ - ρ = ρ := by
    rw [hR₁def, hρdef]
    ring
  have hgeo : (‖z₀ - z₀‖ + ρ) / ((R₁ - ‖z₀ - z₀‖ - ρ) * ρ) = 4 / X := by
    have hρne : ρ ≠ 0 := hρpos.ne'
    have h1 : (‖z₀ - z₀‖ + ρ) = ρ := by rw [sub_self, norm_zero, zero_add]
    have h2 : (R₁ - ‖z₀ - z₀‖ - ρ) = ρ := by rw [sub_self, norm_zero, sub_zero, hRρ]
    have h3 : ρ / (ρ * ρ) = 1 / ρ := by
      rw [div_mul_eq_div_div, div_self hρne, one_div]
    rw [h1, h2, h3, hρdef]
    rw [one_div, inv_div]
  have hmain' : ‖deriv riemannZeta z₀ / riemannZeta z₀‖ ≤
      2 * (Real.log (2 * (1 + 2 / (3 * X))) - Real.log ((σ - 1) / 2)) * (4 / X) := by
    have h := hmain
    rw [mul_div_assoc, hgeo] at h
    exact h
  have hlogV : Real.log V ≤ L := by
    have h := Real.log_le_sub_one_of_pos hVpos
    linarith
  have hlog2M : Real.log (2 * (1 + 2 / (3 * X))) ≤ Real.log 2 + L + Real.log (1 / c₂) := by
    have h2M : 2 * (1 + 2 / (3 * X)) ≤ 2 * V / c₂ := by
      change 2 * (1 + 2 / (3 * (c₂ / V))) ≤ 2 * V / c₂
      have h3c : 0 < 3 * c₂ := by linarith
      have heq2 : 2 * (1 + 2 / (3 * (c₂ / V))) = 2 + 4 * V / (3 * c₂) := by
        field_simp
        ring
      rw [heq2]
      have h4 : 2 + 4 * V / (3 * c₂) = (6 * c₂ + 4 * V) / (3 * c₂) := by
        field_simp
        ring
      rw [h4, div_le_div_iff₀ h3c hc₂]
      nlinarith [hVhalf, hc₂le, hVpos, hc₂]
    have hpos2M : 0 < 2 * (1 + 2 / (3 * X)) := by
      have h1 : 0 < 2 / (3 * X) := div_pos (by norm_num) (by linarith [hXpos])
      linarith
    have h1 : Real.log (2 * (1 + 2 / (3 * X))) ≤ Real.log (2 * V / c₂) :=
      Real.log_le_log hpos2M h2M
    have hsplit : Real.log (2 * V / c₂) = Real.log 2 + Real.log V - Real.log c₂ := by
      rw [Real.log_div (by positivity : 2 * V ≠ 0) hc₂.ne',
          Real.log_mul (by norm_num) hVpos.ne']
    have hinv : Real.log (1 / c₂) = -Real.log c₂ := by rw [one_div, Real.log_inv]
    rw [hsplit] at h1
    rw [hinv]
    linarith
  have hnegm : -Real.log ((σ - 1) / 2) ≤ L + Real.log (1 / c₂) := by
    have h1 : X ≤ (σ - 1) / 2 := by linarith [hσ']
    have h2 : Real.log X ≤ Real.log ((σ - 1) / 2) := Real.log_le_log hXpos h1
    have h3 : Real.log X = Real.log c₂ - Real.log V := by
      rw [hXdef, Real.log_div hc₂.ne' hVpos.ne']
    have h4 : -Real.log ((σ - 1) / 2) ≤ Real.log V - Real.log c₂ := by linarith
    have h6 : -Real.log c₂ = Real.log (1 / c₂) := by rw [one_div, Real.log_inv]
    linarith
  have hlogbound : Real.log (2 * (1 + 2 / (3 * X))) - Real.log ((σ - 1) / 2) ≤ Kk * L := by
    have hsum : Real.log (2 * (1 + 2 / (3 * X))) - Real.log ((σ - 1) / 2) ≤
        Real.log 2 + 2 * L + 2 * Real.log (1 / c₂) := by linarith
    have hA : Real.log 2 ≤ Real.log 2 * L := by
      have h := mul_le_mul_of_nonneg_left hL1 (le_of_lt hlog2)
      simpa using h
    have hB : Real.log (1 / c₂) ≤ Real.log (1 / c₂) * L := by
      have h := mul_le_mul_of_nonneg_left hL1 hlogc
      simpa using h
    have hC : Real.log 2 + 2 * L + 2 * Real.log (1 / c₂) ≤
        Real.log 2 * L + 2 * L + 2 * (Real.log (1 / c₂) * L) := by linarith
    have hexp : Kk * L = Real.log 2 * L + 2 * (Real.log (1 / c₂) * L) + 2 * L := by
      rw [hKk]; ring
    rw [hexp]
    linarith
  have hfin : ‖deriv riemannZeta z₀ / riemannZeta z₀‖ ≤ (8 * Kk / c₂) * L ^ 2 := by
    have hstep1 : ‖deriv riemannZeta z₀ / riemannZeta z₀‖ ≤ 2 * (Kk * L) * (4 / X) := by
      refine le_trans hmain' ?_
      have h20 : 0 ≤ 2 * (4 / X) := by
        have h1 : 0 < 4 / X := div_pos (by norm_num) hXpos
        linarith
      have h3 := mul_le_mul_of_nonneg_right hlogbound h20
      have heq2 : 2 * (Real.log (2 * (1 + 2 / (3 * X))) - Real.log ((σ - 1) / 2)) * (4 / X)
          = (Real.log (2 * (1 + 2 / (3 * X))) - Real.log ((σ - 1) / 2)) * (2 * (4 / X)) := by
        ring
      have heq : 2 * (Kk * L) * (4 / X) = (Kk * L) * (2 * (4 / X)) := by ring
      rw [heq2, heq]
      exact h3
    have hstep2 : 2 * (Kk * L) * (4 / X) ≤ (8 * Kk / c₂) * L ^ 2 := by
      have h1 : c₂ ≤ L * X := by
        rw [hXdef]
        rw [show L * (c₂ / V) = L * c₂ / V by ring, le_div_iff₀ hVpos]
        nlinarith [hVL, hc₂]
      have hkey : 8 * Kk * L * c₂ ≤ 8 * Kk * L * L * X := by
        have hcoef : 0 ≤ 8 * Kk * L := by nlinarith [hKkpos, hLpos]
        have h2 := mul_le_mul_of_nonneg_left h1 hcoef
        have heq : 8 * Kk * L * (L * X) = 8 * Kk * L * L * X := by ring
        linarith [h2, heq]
      rw [show 2 * (Kk * L) * (4 / X) = (8 * Kk * L) / X by ring,
          show (8 * Kk / c₂) * L ^ 2 = (8 * Kk * L * L) / c₂ by ring,
          div_le_div_iff₀ hXpos hc₂]
      exact hkey
    linarith
  exact hfin

/-! ## Zero-freeness of `ζ` on the Vinogradov–Korobov disc -/

private lemma zeta_ne_zero_on_ball' (c₁ c₂ t : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hc₂c₁ : 8 * c₂ ≤ c₁) (hc₂le : c₂ ≤ 1 / 8) (ht : 9 ≤ |t|)
    (hV : 1 / 2 ≤ VKd (|t| + 3))
    (hzf : ∀ t σ : ℝ, 3 ≤ |t| → 1 - c₁ / VKd (|t| + 3) ≤ σ → σ ≤ 1 →
      riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0) :
    ∀ w : ℂ, w ∈ Metric.ball
        (((1 + c₂ / VKd (|t| + 3) : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        (3 * (c₂ / VKd (|t| + 3))) → riemannZeta w ≠ 0 := by
  have hy3 : 3 ≤ |t| + 3 := by linarith [abs_nonneg t]
  have hy12 : 12 ≤ |t| + 3 := by linarith
  have hVpos : 0 < VKd (|t| + 3) := VKd_pos hy3
  have hhpos : 0 < c₂ / VKd (|t| + 3) := div_pos hc₂ hVpos
  have hhle : c₂ / VKd (|t| + 3) ≤ 1 / 4 := by
    rw [div_le_iff₀ hVpos]
    linarith
  intro w hw
  by_cases hwre : (1 : ℝ) ≤ w.re
  · exact riemannZeta_ne_zero_of_one_le_re hwre
  · push Not at hwre
    have hwR : ‖w - (((1 + c₂ / VKd (|t| + 3) : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
        < 3 * (c₂ / VKd (|t| + 3)) := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    have hrew : (w - (((1 + c₂ / VKd (|t| + 3) : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re
        = w.re - (1 + c₂ / VKd (|t| + 3)) := by simp
    have himw : (w - (((1 + c₂ / VKd (|t| + 3) : ℝ) : ℂ) + (t : ℂ) * Complex.I)).im
        = w.im - t := by simp
    have hre1 : |w.re - (1 + c₂ / VKd (|t| + 3))| ≤
        ‖w - (((1 + c₂ / VKd (|t| + 3) : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := by
      have h1 := Complex.abs_re_le_norm
        (w - (((1 + c₂ / VKd (|t| + 3) : ℝ) : ℂ) + (t : ℂ) * Complex.I))
      rwa [hrew] at h1
    have him1 : |w.im - t| ≤
        ‖w - (((1 + c₂ / VKd (|t| + 3) : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := by
      have h1 := Complex.abs_im_le_norm
        (w - (((1 + c₂ / VKd (|t| + 3) : ℝ) : ℂ) + (t : ℂ) * Complex.I))
      rwa [himw] at h1
    have h3h1 : 3 * (c₂ / VKd (|t| + 3)) ≤ 1 := by linarith
    have hgap : |w.im - t| < 3 * (c₂ / VKd (|t| + 3)) := lt_of_le_of_lt him1 hwR
    have hv_lo : 3 ≤ |w.im| := by
      have h1 : |t| ≤ |t - w.im| + |w.im| := by
        calc |t| = |(t - w.im) + w.im| := by ring_nf
          _ ≤ |t - w.im| + |w.im| := abs_add_le _ _
      have h2 : |t - w.im| = |w.im - t| := abs_sub_comm t w.im
      linarith
    have hbase : |w.im| + 3 ≤ 2 * (|t| + 3) := by
      have h2 : |w.im| ≤ |t| + |w.im - t| := by
        calc |w.im| = |t + (w.im - t)| := by ring_nf
          _ ≤ |t| + |w.im - t| := abs_add_le _ _
      linarith
    have hVKle : VKd (|w.im| + 3) ≤ 3 * VKd (|t| + 3) := by
      have h3 : 3 ≤ |w.im| + 3 := by linarith
      have hmono : VKd (|w.im| + 3) ≤ VKd (2 * (|t| + 3)) := VKd_mono h3 hbase
      have h2m : VKd (2 * (|t| + 3)) ≤ 3 * VKd (|t| + 3) := VKd_two_mul_le_three hy12
      linarith
    have hWpos : 0 < VKd (|w.im| + 3) := VKd_pos (by linarith)
    have h3Vpos : 0 < 3 * VKd (|t| + 3) := by linarith
    have hcmp : c₁ / (3 * VKd (|t| + 3)) ≤ c₁ / VKd (|w.im| + 3) := by
      rw [div_le_div_iff₀ h3Vpos hWpos]
      nlinarith [hVKle, hc₁]
    have h2h : 2 * (c₂ / VKd (|t| + 3)) ≤ c₁ / (3 * VKd (|t| + 3)) := by
      have hL : 2 * (c₂ / VKd (|t| + 3)) = 2 * c₂ / VKd (|t| + 3) := by ring
      rw [hL, div_le_div_iff₀ hVpos h3Vpos]
      nlinarith [hc₂c₁, hc₂, hVpos]
    have hwre' : 1 - 2 * (c₂ / VKd (|t| + 3)) ≤ w.re := by
      have h1 := (abs_le.mp hre1).1
      linarith
    have hineq : 1 - c₁ / VKd (|w.im| + 3) ≤ w.re := by linarith
    have hres : riemannZeta ((w.re : ℂ) + (w.im : ℂ) * Complex.I) ≠ 0 :=
      hzf w.im w.re hv_lo hineq (le_of_lt hwre)
    have hdecomp : w = (w.re : ℂ) + (w.im : ℂ) * Complex.I := (Complex.re_add_im w).symm
    rw [hdecomp]
    exact hres

/-! ## Large heights, small `σ`: disc around `1 + c₂/VKd + i t` -/

private lemma logDeriv_large_height_small_sigma (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hc₂c₁ : 8 * c₂ ≤ c₁) (hc₂le : c₂ ≤ 1 / 64)
    (hzf : ∀ t σ : ℝ, 3 ≤ |t| → 1 - c₁ / VKd (|t| + 3) ≤ σ → σ ≤ 1 →
      riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ t σ : ℝ, 9 ≤ |t| →
      1 - c₂ / VKd (|t| + 3) ≤ σ → σ ≤ 1 + 2 * c₂ / VKd (|t| + 3) → σ ≤ 2 →
      ‖deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) /
        riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C * (Real.log (|t| + 3)) ^ 2 := by
  obtain ⟨C₀, hC₀pos, hsg⟩ := Commons.NumberTheory.Zeta.zeta_strip_growth
  obtain ⟨cL, hcLpos, hlow⟩ := Commons.NumberTheory.Zeta.zeta_lower_bound_right_of_one
  set K₂ : ℝ := Real.log (4 + 10 * C₀ + cL) + max (Real.log (1 / (cL * c₂))) 0 + 8 with hK₂def
  have hK₂pos : 0 < K₂ := by
    rw [hK₂def]
    have h1 : 0 < Real.log (4 + 10 * C₀ + cL) := Real.log_pos (by linarith [hC₀pos, hcLpos])
    have h2 : 0 ≤ max (Real.log (1 / (cL * c₂))) 0 := le_max_right _ _
    linarith
  refine ⟨100 * K₂ / c₂, div_pos (mul_pos (by norm_num) hK₂pos) hc₂, ?_⟩
  intro t σ ht hσlo hσhi hσ2
  have hlog3 : 1 ≤ Real.log (|t| + 3) := one_le_log (by linarith [abs_nonneg t])
  have hVdhalf : 1 / 2 ≤ VKd (|t| + 3) :=
    VK.VKd_ge_half (by linarith [abs_nonneg t])
  set y : ℝ := |t| + 3 with hydef
  set V : ℝ := VKd y with hVdef
  set h : ℝ := c₂ / V with hhdef
  set P : ℝ := (2 * y) ^ (1 / 4 + h) with hPdef
  set A : ℝ := C₀ * 5 * P with hAdef
  set M : ℝ := 1 + A + cL * h with hMdef
  set K₁ : ℝ := 4 + 10 * C₀ + cL with hK₁def
  set c : ℂ := ((1 + h : ℝ) : ℂ) + (t : ℂ) * Complex.I with hcdef
  set z₀ : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hz₀def
  have hypos : 0 < y := by rw [hydef]; linarith [abs_nonneg t]
  have hy2 : (1 : ℝ) ≤ 2 * y := by rw [hydef]; linarith [abs_nonneg t]
  have hVpos : 0 < V := by rw [hVdef, hydef]; exact VKd_pos (by linarith [abs_nonneg t])
  have hVhalf : 1 / 2 ≤ V := by rw [hVdef, hydef]; exact hVdhalf
  have hLy : 1 ≤ Real.log y := by rw [hydef]; exact hlog3
  have hVL : V ≤ Real.log y := by
    rw [hVdef, hydef]; exact VKd_le_log (by linarith [abs_nonneg t])
  have hVLraw : V ≤ y := by
    have h1 : Real.log y ≤ y := Real.log_le_self (le_of_lt hypos)
    linarith
  have hLpos : 0 < Real.log y := lt_of_lt_of_le zero_lt_one hLy
  have hVn : 0 ≤ V := le_of_lt hVpos
  have hhpos : 0 < h := by rw [hhdef]; exact div_pos hc₂ hVpos
  have hhle32 : h ≤ 1 / 32 := by
    rw [hhdef, div_le_iff₀ hVpos]
    linarith [hVhalf, hc₂le]
  have hhle4 : h ≤ 1 / 4 := by linarith
  have hhle1 : h ≤ 1 := by linarith
  have hP1 : 1 ≤ P := by
    rw [hPdef]
    calc (1 : ℝ) = (2 * y) ^ (0 : ℝ) := by rw [Real.rpow_zero]
      _ ≤ (2 * y) ^ (1 / 4 + h) := Real.rpow_le_rpow_of_exponent_le hy2 (by positivity)
  have hPpos : 0 < P := lt_of_lt_of_le zero_lt_one hP1
  have hApos : 0 < A := by rw [hAdef]; positivity
  have hcLhpos : 0 < cL * h := mul_pos hcLpos hhpos
  have hMpos : 0 < M := by rw [hMdef]; linarith [hApos, hcLhpos]
  have hσlo' : 1 - h ≤ σ := by
    rw [hhdef, hVdef, hydef]
    exact hσlo
  have hσhi' : σ ≤ 1 + 2 * h := by
    rw [hhdef]
    rw [show 2 * (c₂ / V) = 2 * c₂ / V by ring, hVdef, hydef]
    exact hσhi
  have hdle : ‖z₀ - c‖ ≤ 2 * h := by
    have hz₀c : z₀ - c = ((σ - (1 + h) : ℝ) : ℂ) := by
      rw [hz₀def, hcdef]
      apply Complex.ext <;> simp
    rw [hz₀c, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hz₀ball : z₀ ∈ Metric.ball c (3 * h) := by
    rw [Metric.mem_ball, dist_eq_norm]
    linarith [hdle, hhpos]
  have hρpos : 0 < h / 2 := by linarith
  have hρlt : h / 2 < 3 * h - ‖z₀ - c‖ := by linarith [hdle]
  have h3h1 : 3 * h ≤ 1 := by linarith
  have hc1norm : 9 ≤ ‖c - 1‖ := by
    have hc1im : (c - 1).im = t := by rw [hcdef]; simp
    calc 9 ≤ |t| := ht
      _ = |(c - 1).im| := by rw [hc1im]
      _ ≤ ‖c - 1‖ := Complex.abs_im_le_norm _
  have hball1 : Metric.ball c (3 * h) ⊆ ({1}ᶜ : Set ℂ) := by
    intro w hw
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hw1
    have hwR : ‖w - c‖ < 3 * h := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    have hcw : ‖c - w‖ < 3 * h := by rw [norm_sub_rev]; exact hwR
    have hw1' : ‖w - (1 : ℂ)‖ = 0 := by rw [hw1]; simp
    have hdecomp : c - 1 = (c - w) + (w - 1) := by ring
    have htri : ‖c - 1‖ ≤ ‖c - w‖ + ‖w - 1‖ := by
      calc ‖c - 1‖ = ‖(c - w) + (w - 1)‖ := by rw [hdecomp]
        _ ≤ ‖c - w‖ + ‖w - 1‖ := norm_add_le _ _
    linarith
  have hgan : AnalyticOnNhd ℂ riemannZeta (Metric.ball c (3 * h)) :=
    analyticOn_riemannZeta.mono hball1
  have hgne : ∀ w : ℂ, w ∈ Metric.ball c (3 * h) → riemannZeta w ≠ 0 := by
    intro w hw
    have hzw := zeta_ne_zero_on_ball' c₁ c₂ t hc₁ hc₂ hc₂c₁ (by linarith : c₂ ≤ 1 / 8)
      (by linarith : 9 ≤ |t|) hVdhalf hzf
    refine hzw w ?_
    have hw' : w ∈ Metric.ball (((1 + c₂ / VKd (|t| + 3) : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        (3 * (c₂ / VKd (|t| + 3))) := by
      simpa only [hcdef, hhdef, hVdef, hydef] using hw
    exact hw'
  have hgM : ∀ w : ℂ, w ∈ Metric.ball c (3 * h) → ‖riemannZeta w‖ ≤ M := by
    intro w hw
    have hwR : ‖w - c‖ < 3 * h := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    have hrew : (w - c).re = w.re - (1 + h) := by rw [hcdef]; simp
    have himw : (w - c).im = w.im - t := by rw [hcdef]; simp
    have hre1 : |w.re - (1 + h)| ≤ ‖w - c‖ := by
      have h1 := Complex.abs_re_le_norm (w - c)
      rwa [hrew] at h1
    have him1 : |w.im - t| ≤ ‖w - c‖ := by
      have h1 := Complex.abs_im_le_norm (w - c)
      rwa [himw] at h1
    have hre_lo : 1 - 2 * h ≤ w.re := by
      have h3 := (abs_le.mp hre1).1
      linarith
    have hre_hi : w.re ≤ 1 + 4 * h := by
      have h3 := (abs_le.mp hre1).2
      linarith
    have hu2 : w.re ≤ 2 := by linarith [hre_hi, hhle32]
    have hδpos : 0 < w.re - 1 / 2 := by linarith [hre_lo, hhle32]
    have hδle1 : w.re - 1 / 2 ≤ 1 := by linarith [hre_hi, hhle32]
    have hδnonneg : 0 ≤ 1 / 2 - (w.re - 1 / 2) / 2 := by linarith [hδle1]
    have hv_lo : 8 ≤ |w.im| := by
      have h1 : |t| ≤ |t - w.im| + |w.im| := by
        calc |t| = |(t - w.im) + w.im| := by ring_nf
          _ ≤ |t - w.im| + |w.im| := abs_add_le _ _
      have h2 : |t - w.im| = |w.im - t| := abs_sub_comm t w.im
      have h3 : |w.im - t| < 3 * h := lt_of_le_of_lt him1 hwR
      linarith
    have h1v : 1 ≤ |w.im| := by linarith
    have hhalf : 1 / 2 + (w.re - 1 / 2) ≤ w.re := by linarith
    have hstrip := hsg (w.re - 1 / 2) w.re w.im hδpos hδle1 hhalf hu2 h1v
    have hstrip' := hstrip
    rw [mul_comm Complex.I (w.im : ℂ)] at hstrip'
    have h1δ : 1 + 1 / (w.re - 1 / 2) ≤ 5 := by
      have h4 : 1 / (w.re - 1 / 2) ≤ 4 := by
        rw [div_le_iff₀ hδpos]
        linarith
      linarith
    have hbase : |w.im| + 3 ≤ 2 * y := by
      have h2 : |w.im| ≤ |t| + |w.im - t| := by
        calc |w.im| = |t + (w.im - t)| := by ring_nf
          _ ≤ |t| + |w.im - t| := abs_add_le _ _
      have h3 : |w.im - t| < 3 * h := lt_of_le_of_lt him1 hwR
      have h4 : 3 * h ≤ 1 := h3h1
      rw [hydef]
      linarith
    have hpowle : (|w.im| + 3) ^ (1 / 2 - (w.re - 1 / 2) / 2) ≤ P := by
      rw [hPdef]
      have hexp : 1 / 2 - (w.re - 1 / 2) / 2 ≤ 1 / 4 + h := by linarith [hre_lo]
      calc (|w.im| + 3) ^ (1 / 2 - (w.re - 1 / 2) / 2)
          ≤ (2 * y) ^ (1 / 2 - (w.re - 1 / 2) / 2) :=
            Real.rpow_le_rpow (by positivity) hbase hδnonneg
        _ ≤ (2 * y) ^ (1 / 4 + h) := Real.rpow_le_rpow_of_exponent_le hy2 hexp
    have hwdecomp : w = (w.re : ℂ) + (w.im : ℂ) * Complex.I := (Complex.re_add_im w).symm
    calc ‖riemannZeta w‖ = ‖riemannZeta ((w.re : ℂ) + (w.im : ℂ) * Complex.I)‖ := by
          conv_lhs => rw [hwdecomp]
      _ ≤ C₀ * (1 + 1 / (w.re - 1 / 2)) * (|w.im| + 3) ^ (1 / 2 - (w.re - 1 / 2) / 2) := hstrip'
      _ ≤ C₀ * 5 * P := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left h1δ hC₀pos.le
          · exact hpowle
          · positivity
          · positivity
      _ = A := by rw [hAdef]
      _ ≤ M := by rw [hMdef]; nlinarith [hcLpos, hhpos, hApos]
  have hmM : cL * h ≤ M := by rw [hMdef]; linarith [hApos]
  have hmle : cL * h ≤ ‖riemannZeta c‖ := by
    have h2 := hlow h t hhpos hhle4
    rw [mul_comm Complex.I (t : ℂ)] at h2
    rw [hcdef]
    exact h2
  have hball := Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound_analytic
      (g := riemannZeta) (c := c) (R := 3 * h) (m := cL * h) (M := M)
      (by linarith : 0 < 3 * h) hcLhpos hmM hgan hgne hgM hmle
  have hmain := hball hz₀ball (h / 2) hρpos hρlt
  have hnum : ‖z₀ - c‖ + h / 2 ≤ 5 * h / 2 := by linarith [hdle]
  have hden : h ^ 2 / 4 ≤ (3 * h - ‖z₀ - c‖ - h / 2) * (h / 2) := by
    nlinarith [hdle, hhpos]
  have hdenpos : 0 < (3 * h - ‖z₀ - c‖ - h / 2) * (h / 2) := by
    have h1 : 0 < 3 * h - ‖z₀ - c‖ - h / 2 := by linarith [hdle]
    exact mul_pos h1 hρpos
  have h10V : 0 ≤ 10 * V / c₂ := le_of_lt (div_pos (by linarith) hc₂)
  have hVh : V * h = c₂ := by
    rw [hhdef, mul_div_assoc', mul_comm V c₂, mul_div_cancel_right₀ c₂ hVpos.ne']
  have hid : (10 * V / c₂) * (h ^ 2 / 4) = 5 * h / 2 := by
    have h1 : (10 * V / c₂) * (h ^ 2 / 4) = (5 / 2) * (V * h / c₂) * h := by ring
    have h2 : V * h / c₂ = 1 := by rw [hVh, div_self hc₂.ne']
    rw [h1, h2]
    ring
  have hgeo : (‖z₀ - c‖ + h / 2) / ((3 * h - ‖z₀ - c‖ - h / 2) * (h / 2)) ≤ 10 * V / c₂ := by
    rw [div_le_iff₀ hdenpos]
    calc ‖z₀ - c‖ + h / 2 ≤ 5 * h / 2 := hnum
      _ = (10 * V / c₂) * (h ^ 2 / 4) := hid.symm
      _ ≤ (10 * V / c₂) * ((3 * h - ‖z₀ - c‖ - h / 2) * (h / 2)) :=
          mul_le_mul_of_nonneg_left hden h10V
  have hMle : 2 * M ≤ K₁ * P := by
    have h1 : 2 * A ≤ 10 * C₀ * P := by
      rw [hAdef]
      nlinarith [hC₀pos]
    have h2 : 2 * (cL * h) ≤ cL * P := by
      have hh : 2 * h ≤ 1 := by linarith
      nlinarith [hP1, hcLpos, hhpos, hh]
    have h3 : (2 : ℝ) ≤ 2 * P := by linarith [hP1]
    rw [hMdef, hK₁def]
    nlinarith [h1, h2, h3]
  have hlog2M : Real.log (2 * M) ≤ Real.log K₁ + (1 / 4 + h) * (Real.log 2 + Real.log y) := by
    have hK1pos : 0 < K₁ := by rw [hK₁def]; linarith [hC₀pos, hcLpos]
    have h1 : Real.log (2 * M) ≤ Real.log (K₁ * P) :=
      Real.log_le_log (by linarith [hcLhpos, hApos]) hMle
    have h2 : Real.log (K₁ * P) = Real.log K₁ + Real.log P := Real.log_mul hK1pos.ne' hPpos.ne'
    have h3 : Real.log P = (1 / 4 + h) * Real.log (2 * y) := by
      rw [hPdef, Real.log_rpow (by rw [hydef]; linarith [abs_nonneg t])]
    have h4 : Real.log (2 * y) = Real.log 2 + Real.log y :=
      Real.log_mul (by norm_num) hypos.ne'
    calc Real.log (2 * M) ≤ Real.log (K₁ * P) := h1
      _ = Real.log K₁ + Real.log P := h2
      _ = Real.log K₁ + (1 / 4 + h) * Real.log (2 * y) := by rw [h3]
      _ = Real.log K₁ + (1 / 4 + h) * (Real.log 2 + Real.log y) := by rw [h4]
  have hneglm : -Real.log (cL * h) ≤ max (Real.log (1 / (cL * c₂))) 0 + Real.log y := by
    have h1 : cL * c₂ / y ≤ cL * h := by
      rw [hhdef]
      rw [show cL * (c₂ / V) = cL * c₂ / V by ring]
      rw [div_le_div_iff₀ hypos hVpos]
      exact mul_le_mul_of_nonneg_left hVLraw (by positivity)
    have h2 : 0 < cL * c₂ / y := div_pos (by positivity) hypos
    have h3 : -Real.log (cL * h) ≤ -Real.log (cL * c₂ / y) :=
      neg_le_neg (Real.log_le_log h2 h1)
    have h4 : -Real.log (cL * c₂ / y) = Real.log (1 / (cL * c₂)) + Real.log y := by
      rw [Real.log_div (by positivity : cL * c₂ ≠ 0) hypos.ne', neg_sub]
      have h5 : Real.log (1 / (cL * c₂)) = -Real.log (cL * c₂) := by
        rw [Real.log_div one_ne_zero (by positivity : cL * c₂ ≠ 0), Real.log_one]
        ring
      rw [h5]
      ring
    have h6 : Real.log (1 / (cL * c₂)) ≤ max (Real.log (1 / (cL * c₂))) 0 := le_max_left _ _
    linarith
  have hlogM : Real.log (2 * M) - Real.log (cL * h) ≤ K₂ * Real.log y := by
    have hsum : Real.log (2 * M) - Real.log (cL * h) ≤
        Real.log K₁ + (1 / 4 + h) * (Real.log 2 + Real.log y) +
          (max (Real.log (1 / (cL * c₂))) 0 + Real.log y) := by linarith [hlog2M, hneglm]
    have hlogK₁n : 0 ≤ Real.log K₁ := by
      apply Real.log_nonneg
      rw [hK₁def]
      linarith [hC₀pos, hcLpos]
    have hlogK : Real.log K₁ ≤ Real.log K₁ * Real.log y := by
      have h := mul_le_mul_of_nonneg_left hLy hlogK₁n
      simpa using h
    have hmax : max (Real.log (1 / (cL * c₂))) 0 ≤
        max (Real.log (1 / (cL * c₂))) 0 * Real.log y := by
      have h := mul_le_mul_of_nonneg_left hLy (le_max_right (Real.log (1 / (cL * c₂))) 0)
      simpa using h
    have hlog2 : (1 / 4 + h) * Real.log 2 ≤ Real.log y := by
      have h1 : (1 / 4 + h) ≤ 1 / 2 := by linarith
      have h2 : Real.log 2 ≤ 1 := by
        have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        linarith
      have h3 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      calc (1 / 4 + h) * Real.log 2 ≤ (1 / 2) * Real.log 2 := mul_le_mul_of_nonneg_right h1 h3
        _ ≤ (1 / 2) * 1 := by linarith
        _ ≤ Real.log y := by linarith
    have hlogh : (1 / 4 + h) * Real.log y ≤ (1 / 2) * Real.log y := by
      have h1 : (1 / 4 + h) ≤ 1 / 2 := by linarith
      exact mul_le_mul_of_nonneg_right h1 (le_of_lt hLpos)
    rw [hK₂def]
    linarith
  have hmain' : ‖deriv riemannZeta z₀ / riemannZeta z₀‖ ≤
      2 * (Real.log (2 * M) - Real.log (cL * h)) *
        ((‖z₀ - c‖ + h / 2) / ((3 * h - ‖z₀ - c‖ - h / 2) * (h / 2))) := by
    have hb := hmain
    rw [mul_div_assoc] at hb
    exact hb
  have hA2 : 2 * (Real.log (2 * M) - Real.log (cL * h)) ≤ 2 * (K₂ * Real.log y) :=
    mul_le_mul_of_nonneg_left hlogM (by norm_num)
  have h2nn : 0 ≤ 2 * (K₂ * Real.log y) := by
    have h3 : 0 < K₂ * Real.log y := mul_pos hK₂pos hLpos
    linarith
  have h3nn : 0 ≤ (‖z₀ - c‖ + h / 2) / ((3 * h - ‖z₀ - c‖ - h / 2) * (h / 2)) := by
    have h1 : 0 < ‖z₀ - c‖ + h / 2 := by
      have h2 : 0 ≤ ‖z₀ - c‖ := norm_nonneg _
      linarith
    exact le_of_lt (div_pos h1 hdenpos)
  have hstep2 : ‖deriv riemannZeta z₀ / riemannZeta z₀‖ ≤ 2 * (K₂ * Real.log y) * (10 * V / c₂) := by
    refine le_trans hmain' ?_
    exact mul_le_mul hA2 hgeo h3nn h2nn
  have hstep3 : 2 * (K₂ * Real.log y) * (10 * V / c₂) ≤ (100 * K₂ / c₂) * (Real.log y) ^ 2 := by
    have hprod : K₂ * Real.log y * V ≤ K₂ * Real.log y * Real.log y :=
      mul_le_mul_of_nonneg_left hVL (by positivity)
    have hkey : 2 * (K₂ * Real.log y) * (10 * V) ≤ 100 * K₂ * (Real.log y) * Real.log y := by
      have h1 : 20 * (K₂ * Real.log y * V) ≤ 20 * (K₂ * Real.log y * Real.log y) :=
        mul_le_mul_of_nonneg_left hprod (by norm_num)
      nlinarith [h1]
    calc 2 * (K₂ * Real.log y) * (10 * V / c₂)
        = (2 * (K₂ * Real.log y) * (10 * V)) / c₂ := by ring
      _ ≤ (100 * K₂ * (Real.log y) * Real.log y) / c₂ := div_le_div_of_nonneg_right hkey hc₂.le
      _ = (100 * K₂ / c₂) * (Real.log y) ^ 2 := by ring
  exact le_trans hstep2 hstep3


/-- The `ζ′/ζ`-bound in the Vinogradov–Korobov zero-free region, *from* the zero-free region.

If `ζ(σ+it) ≠ 0` for `|t| ≥ 3` and `1 - c₁/VKd(|t|+3) ≤ σ ≤ 1`, then there are `c₂ > 0` and `B > 0`
with `‖ζ′/ζ(σ+it)‖ ≤ B (log(|t|+3))²` for `|t| ≥ 3` and `1 - c₂/VKd(|t|+3) ≤ σ ≤ 2`.

Route.  Take `c₂ ≤ c₁/8`.  For a point `z₀ = σ+it` use
`Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound_analytic` on a disc around a centre `c`
with `Re c > 1` (so `m ≤ ‖ζ c‖` is available from the Euler product: `‖ζ(u+iv)‖ ≥ 1/ζ(u)` for
`u > 1`, and `ζ(u) ≤ 1/(u-1) + 1`): for `σ ≥ 1+2c₂/VKd` centre at `z₀` with radius `c₂/(2VKd)`
(no zeros there by the hypothesis, and `M ≪ VKd`); for `σ ≤ 1+2c₂/VKd` centre at `1+c₂/VKd+it`
with radius `3c₂/VKd` (again zero-free, using `VKd(2y) ≤ 3VKd(y)`).  On the part of the disc with
`Re s ≤ 1` (i.e. `1-2c₂/VKd ≤ Re s < 1`) use `Commons.NumberTheory.Zeta.zeta_strip_growth`:
`‖ζ(u+iv)‖ ≤ 10^6 (1+1/(u-1/2)) (|v|+3)^{1/2-(u-1/2)/2} ≤ 3·10^6 (|t|+3)^{1/4+2c₂/VKd}`, so
`log M ≤ ℓ/4 + O(1)` with `ℓ = log(|t|+3)`; on the part with `Re s ≥ 1` use the Euler product
`‖ζ(u+iv)‖ ≤ ζ(u) ≤ 1/(u-1) + 1 ≤ VKd/c₂`.  With `m ≳ c₂/VKd` the ball bound gives
`‖ζ′/ζ(z₀)‖ ≤ 2(log(2M)-log m)(d+ρ)/((R-d-ρ)ρ) ≲ 5 VKd ℓ/c₂ ≤ B ℓ²` for large `ℓ`, since
`VKd = ℓ^{2/3}(log ℓ)^{1/3} ≪ ℓ`.  Bounded heights `3 ≤ |t| ≤ T₀` are absorbed into `B` by
compactness (`ζ` is continuous on the compact set `3 ≤ |Im| ≤ T₀`, `1/2 ≤ Re ≤ 2`, which avoids the
pole and the zeros with `Re ≥ 1`). -/
theorem zeta_logDeriv_bound_vk (c₁ : ℝ) (hc₁ : 0 < c₁)
    (hzf : ∀ t σ : ℝ, 3 ≤ |t| → 1 - c₁ / VKd (|t| + 3) ≤ σ → σ ≤ 1 →
        riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0) :
    ∃ c₂ B : ℝ, 0 < c₂ ∧ 0 < B ∧ ∀ t σ : ℝ, 3 ≤ |t| →
        1 - c₂ / VKd (|t| + 3) ≤ σ → σ ≤ 2 →
        ‖deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) /
          riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ B * (Real.log (|t| + 3)) ^ 2 := by
  set cc : ℝ := min (c₁ / 8) (1 / 64) with hccdef
  have hccpos : 0 < cc := by rw [hccdef]; positivity
  have hcc8 : 8 * cc ≤ c₁ := by
    rw [hccdef]
    have h : min (c₁ / 8) (1 / 64) ≤ c₁ / 8 := min_le_left _ _
    linarith
  have hccle : cc ≤ 1 / 64 := by rw [hccdef]; exact min_le_right _ _
  have hV : ∀ t : ℝ, 3 ≤ |t| → 1 / 2 ≤ VKd (|t| + 3) :=
    fun t ht => VK.VKd_ge_half (by linarith [abs_nonneg t])
  obtain ⟨C₁, hC₁pos, h₁⟩ := logDeriv_bounded_height' c₁ cc hc₁ hccpos hcc8 hccle hzf
  obtain ⟨C₂, hC₂pos, h₂⟩ := logDeriv_large_sigma' cc hccpos hccle hV
  obtain ⟨C₃, hC₃pos, h₃⟩ := logDeriv_large_height_small_sigma c₁ cc hc₁ hccpos hcc8 hccle hzf
  have hC₁le : C₁ ≤ max (max C₁ C₂) C₃ := le_trans (le_max_left C₁ C₂) (le_max_left _ C₃)
  have hC₂le : C₂ ≤ max (max C₁ C₂) C₃ := le_trans (le_max_right C₁ C₂) (le_max_left _ C₃)
  have hC₃le : C₃ ≤ max (max C₁ C₂) C₃ := le_max_right _ C₃
  have hBpos : 0 < max (max C₁ C₂) C₃ := lt_of_lt_of_le hC₁pos hC₁le
  refine ⟨cc, max (max C₁ C₂) C₃, hccpos, hBpos, ?_⟩
  intro t σ ht hσlo hσ2
  have hpow : 0 ≤ (Real.log (|t| + 3)) ^ 2 := sq_nonneg _
  by_cases ht16 : |t| ≤ 16
  · have h := h₁ t σ ht ht16 hσlo hσ2
    calc ‖deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) /
          riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C₁ * (Real.log (|t| + 3)) ^ 2 := h
      _ ≤ max (max C₁ C₂) C₃ * (Real.log (|t| + 3)) ^ 2 :=
          mul_le_mul_of_nonneg_right hC₁le hpow
  · have ht9 : 9 ≤ |t| := by
      have h : 16 < |t| := lt_of_not_ge ht16
      linarith
    by_cases hcase : 1 + 2 * cc / VKd (|t| + 3) ≤ σ
    · have h := h₂ t σ ht hcase hσ2
      calc ‖deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) /
            riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C₂ * (Real.log (|t| + 3)) ^ 2 := h
        _ ≤ max (max C₁ C₂) C₃ * (Real.log (|t| + 3)) ^ 2 :=
            mul_le_mul_of_nonneg_right hC₂le hpow
    · have hle : σ ≤ 1 + 2 * cc / VKd (|t| + 3) := le_of_lt (lt_of_not_ge hcase)
      have h := h₃ t σ ht9 hσlo hle hσ2
      calc ‖deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) /
            riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C₃ * (Real.log (|t| + 3)) ^ 2 := h
        _ ≤ max (max C₁ C₂) C₃ * (Real.log (|t| + 3)) ^ 2 :=
            mul_le_mul_of_nonneg_right hC₃le hpow

end

end Work.BMF
