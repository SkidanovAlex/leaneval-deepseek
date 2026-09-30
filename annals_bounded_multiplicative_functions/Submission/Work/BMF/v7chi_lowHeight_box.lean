import Mathlib
import Submission.Work.BMF.LFunction_lowHeight
import Submission.Work.BMF.vk_L_lower
import Submission.Work.BMF.LFunction_lower_one_add
import Submission.Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound_analytic
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_offAxis_uniform
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_uniform_realAxis
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_realZero_siegel_uniform
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_norm_half_plane

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! # Low heights `|t| ≤ 4` for `L(s,χ)` (node V5 of the N10 sub-design)

For every `ε > 0` there are `c, C > 0` such that for every primitive non-principal character `χ`
modulo `N`, every `σ ≥ 1 - c N^{-ε}` with `σ ≤ 2` and every `|t| ≤ 4`, the function `L(·,χ)` has no
zero at `σ + it` and its logarithmic derivative is bounded by `C (N^ε + log(N+2)^2)`.

The zero-free input is `Work.BMF.lowWidth_zero_free_sub` (from the Commons off-axis, real-axis and
Siegel regions); the logarithmic-derivative bound is the Borel–Carathéodory ball estimate
`Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound_analytic` applied to the ball centred at
`c₀ = (1 + h) + i t`, `h = max (w/2) (σ - 1)`, of radius `h + w/2`, where `w` is the zero-free
half-width in the strip `|Im s| ≤ 6`.  That ball lies in `{Re > 1 - w/2}` and in `{‖·‖ ≤ 29/4}`,
and `m = h/2 ≥ w/4` bounds `‖L(c₀)‖` from below by `Work.BMF.LFunction_lower_one_add`. -/

namespace Work.BMF

open Complex Metric DirichletCharacter Filter
open scoped Topology

noncomputable section

set_option maxHeartbeats 4000000 in
theorem v7chi_lowHeight_box (ε : ℝ) (hε : 0 < ε) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ.IsPrimitive → χ ≠ 1 → ∀ σ t : ℝ, |t| ≤ 4 →
      1 - c * (N : ℝ) ^ (-ε) ≤ σ → σ ≤ 2 →
      DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 ∧
      ‖logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C * ((N : ℝ) ^ ε + Real.log ((N : ℝ) + 2) ^ 2) := by
  obtain ⟨a, ha, hOff0⟩ :=
    Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_offAxis_uniform
  obtain ⟨b, hb, hReal0⟩ :=
    Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_uniform_realAxis
  obtain ⟨Cd, hCd, hSieg0⟩ :=
    Commons.NumberTheory.DirichletCharacter.LFunction_realZero_siegel_uniform (ε / 4)
      (by linarith)
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  set K : ℝ := 2 + 2 * (8 : ℝ) ^ (ε / 2) / (a * ε) + 2 * (2 : ℝ) ^ (ε / 2) / (b * ε) + 1 / Cd
    with hKdef
  have hK2 : 2 ≤ K := by
    rw [hKdef]
    have h1 : 0 ≤ 2 * (8 : ℝ) ^ (ε / 2) / (a * ε) :=
      div_nonneg (mul_nonneg (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _).le)
        (by positivity)
    have h2 : 0 ≤ 2 * (2 : ℝ) ^ (ε / 2) / (b * ε) :=
      div_nonneg (mul_nonneg (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _).le)
        (by positivity)
    have h3 : 0 ≤ 1 / Cd := by positivity
    linarith only [h1, h2, h3]
  have hKpos : 0 < K := by linarith only [hK2]
  have hCpos : 0 < 500 * K * (1 + ε) * (Real.log 40 + Real.log 4 + Real.log K + 1) := by
    have h1 : 0 < 500 * K := by linarith only [hKpos]
    have h2 : 0 < 1 + ε := by linarith
    have h3 : 0 < Real.log 40 + Real.log 4 + Real.log K + 1 := by
      have h4 : 0 ≤ Real.log 40 := Real.log_nonneg (by norm_num)
      have h5 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      have h6 : 0 ≤ Real.log K := Real.log_nonneg (by linarith only [hK2])
      linarith only [h4, h5, h6]
    exact mul_pos (mul_pos h1 h2) h3
  refine ⟨1 / (4 * K),
    500 * K * (1 + ε) * (Real.log 40 + Real.log 4 + Real.log K + 1), by positivity,
    hCpos, ?_⟩
  intro N _inst χ hprim hχne σ t ht4 hσ hσ2
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith only [hN1]
  set w : ℝ := lowWidth (ε / 2) a b Cd N with hwdef
  have hwpos : 0 < w := lowWidth_pos (ε / 2) a b Cd ha hb hCd N
  have hwle : w ≤ 1 / 2 := lowWidth_le_half (ε / 2) a b Cd ha hb hCd N
  have hw_1 : w = 1 / lowWidthInv (ε / 2) a b Cd N := by rw [hwdef]; rfl
  -- (2) zero-freeness in the strip `|Im| ≤ 6`
  have hZ : ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → |ρ.im| ≤ 6 → ρ.re ≤ 1 - w := by
    refine lowWidth_zero_free_sub (ε / 2) a b Cd ha hb hCd ?_ ?_ ?_ N χ hprim hχne
    · intro N' _ χ' h1 h2 σ' t' ht' h
      exact hOff0 χ' h1 h2 σ' t' ht' h
    · intro N' _ χ' h1 h2 hsq σ' h
      exact hReal0 N' χ' h1 h2 hsq σ' h
    · intro N' _ χ' h1 h2 hsq β hβ0 hβ1 hz
      have h3 := hSieg0 N' χ' h1 h2 hsq β hβ0 hβ1 hz
      simpa only [show -(ε / 4) = -(ε / 2 / 2) by ring] using h3
  -- (3) `lowWidthInv ≤ K N^{ε/2}`
  have hNhalf : (1 : ℝ) ≤ (N : ℝ) ^ (ε / 2) := Real.one_le_rpow hN1 hε2.le
  have hwInv : lowWidthInv (ε / 2) a b Cd N ≤ K * (N : ℝ) ^ (ε / 2) := by
    have hlog8 : Real.log (8 * (N : ℝ)) ≤ 2 * (8 : ℝ) ^ (ε / 2) / ε * (N : ℝ) ^ (ε / 2) := by
      have h := Real.log_le_rpow_div (show (0 : ℝ) ≤ 8 * (N : ℝ) by positivity) hε2
      rw [Real.mul_rpow (by norm_num) hNpos.le] at h
      have he : (8 : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) / (ε / 2)
          = 2 * (8 : ℝ) ^ (ε / 2) / ε * (N : ℝ) ^ (ε / 2) := by
        field_simp
      rwa [he] at h
    have hlog2 : Real.log (2 * (N : ℝ)) ≤ 2 * (2 : ℝ) ^ (ε / 2) / ε * (N : ℝ) ^ (ε / 2) := by
      have h := Real.log_le_rpow_div (show (0 : ℝ) ≤ 2 * (N : ℝ) by positivity) hε2
      rw [Real.mul_rpow (by norm_num) hNpos.le] at h
      have he : (2 : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) / (ε / 2)
          = 2 * (2 : ℝ) ^ (ε / 2) / ε * (N : ℝ) ^ (ε / 2) := by
        field_simp
      rwa [he] at h
    have hNpow : (N : ℝ) ^ (ε / 4) ≤ (N : ℝ) ^ (ε / 2) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have hdiv1 : Real.log (8 * (N : ℝ)) / a
        ≤ (2 * (8 : ℝ) ^ (ε / 2) / (a * ε)) * (N : ℝ) ^ (ε / 2) := by
      calc Real.log (8 * (N : ℝ)) / a
          ≤ (2 * (8 : ℝ) ^ (ε / 2) / ε * (N : ℝ) ^ (ε / 2)) / a :=
            div_le_div_of_nonneg_right hlog8 ha.le
        _ = (2 * (8 : ℝ) ^ (ε / 2) / (a * ε)) * (N : ℝ) ^ (ε / 2) := by
            field_simp
    have hdiv2 : Real.log (2 * (N : ℝ)) / b
        ≤ (2 * (2 : ℝ) ^ (ε / 2) / (b * ε)) * (N : ℝ) ^ (ε / 2) := by
      calc Real.log (2 * (N : ℝ)) / b
          ≤ (2 * (2 : ℝ) ^ (ε / 2) / ε * (N : ℝ) ^ (ε / 2)) / b :=
            div_le_div_of_nonneg_right hlog2 hb.le
        _ = (2 * (2 : ℝ) ^ (ε / 2) / (b * ε)) * (N : ℝ) ^ (ε / 2) := by
            field_simp
    have hdiv3 : (N : ℝ) ^ (ε / 4) / Cd ≤ (1 / Cd) * (N : ℝ) ^ (ε / 2) := by
      calc (N : ℝ) ^ (ε / 4) / Cd ≤ (N : ℝ) ^ (ε / 2) / Cd :=
            div_le_div_of_nonneg_right hNpow hCd.le
        _ = (1 / Cd) * (N : ℝ) ^ (ε / 2) := by ring
    have h2le : (2 : ℝ) ≤ 2 * (N : ℝ) ^ (ε / 2) := by linarith only [hNhalf]
    have hstep : 2 + Real.log (8 * (N : ℝ)) / a + Real.log (2 * (N : ℝ)) / b
        + (N : ℝ) ^ (ε / 4) / Cd
        ≤ 2 * (N : ℝ) ^ (ε / 2) + (2 * (8 : ℝ) ^ (ε / 2) / (a * ε)) * (N : ℝ) ^ (ε / 2)
          + (2 * (2 : ℝ) ^ (ε / 2) / (b * ε)) * (N : ℝ) ^ (ε / 2)
          + (1 / Cd) * (N : ℝ) ^ (ε / 2) := by
      linarith only [hdiv1, hdiv2, hdiv3, h2le]
    have hKexp : 2 * (N : ℝ) ^ (ε / 2) + (2 * (8 : ℝ) ^ (ε / 2) / (a * ε)) * (N : ℝ) ^ (ε / 2)
          + (2 * (2 : ℝ) ^ (ε / 2) / (b * ε)) * (N : ℝ) ^ (ε / 2)
          + (1 / Cd) * (N : ℝ) ^ (ε / 2)
        = K * (N : ℝ) ^ (ε / 2) := by
      rw [hKdef]; ring
    rw [lowWidthInv]
    simpa only [show ε / 4 = ε / 2 / 2 by ring] using hstep.trans hKexp.le
  have hw_ge : (N : ℝ) ^ (-(ε / 2)) / K ≤ w := by
    have h5 : 0 < lowWidthInv (ε / 2) a b Cd N := lowWidthInv_pos (ε / 2) a b Cd ha hb hCd N
    have h7 : 1 / (K * (N : ℝ) ^ (ε / 2)) ≤ 1 / lowWidthInv (ε / 2) a b Cd N :=
      one_div_le_one_div_of_le h5 hwInv
    have h8 : 1 / (K * (N : ℝ) ^ (ε / 2)) = (N : ℝ) ^ (-(ε / 2)) / K := by
      rw [Real.rpow_neg hNpos.le]; field_simp
    rw [h8] at h7
    rwa [← hw_1] at h7
  -- the region `1 - c N^{-ε}` lies in the zero-free region
  have hcw : (1 / (4 * K)) * (N : ℝ) ^ (-ε) ≤ w / 4 := by
    have h2 : (N : ℝ) ^ (-ε) ≤ (N : ℝ) ^ (-(ε / 2)) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have h6 : (1 / (4 * K)) * (N : ℝ) ^ (-ε) ≤ (N : ℝ) ^ (-(ε / 2)) / (4 * K) := by
      have h7 : (0 : ℝ) ≤ 1 / (4 * K) := by positivity
      calc (1 / (4 * K)) * (N : ℝ) ^ (-ε) ≤ (1 / (4 * K)) * (N : ℝ) ^ (-(ε / 2)) :=
            mul_le_mul_of_nonneg_left h2 h7
        _ = (N : ℝ) ^ (-(ε / 2)) / (4 * K) := by ring
    have h3 : (N : ℝ) ^ (-(ε / 2)) / (4 * K) ≤ w / 4 := by
      have h4 : (N : ℝ) ^ (-(ε / 2)) / (4 * K) = ((N : ℝ) ^ (-(ε / 2)) / K) / 4 := by
        rw [div_div, mul_comm K 4]
      rw [h4]
      exact div_le_div_of_nonneg_right hw_ge (by norm_num)
    linarith only [h6, h3]
  have hσ1 : 1 - w ≤ σ := by
    have h1 : 1 - (1 / (4 * K)) * (N : ℝ) ^ (-ε) ≤ σ := by
      have h2 : 1 - (1 / (4 * K)) * (N : ℝ) ^ (-ε)
          = 1 - (1 / (4 * K) * (N : ℝ) ^ (-ε)) := by ring
      rw [h2] at hσ
      exact hσ
    have h4 : (1 / (4 * K)) * (N : ℝ) ^ (-ε) ≤ w := by linarith only [hcw, hwpos]
    linarith only [h1, h4]
  -- (4) the ball and the Borel--Caratheodory estimate
  set h : ℝ := max (w / 2) (σ - 1) with hhdef
  have hh_ge : w / 2 ≤ h := le_max_left _ _
  have hh_ge' : σ - 1 ≤ h := le_max_right _ _
  have hhpos : 0 < h := by linarith only [hh_ge, hwpos]
  have hh1 : h ≤ 1 := by
    have h1 : w / 2 ≤ 1 := by linarith only [hwle]
    have h2 : σ - 1 ≤ 1 := by linarith only [hσ2]
    rw [hhdef]
    exact max_le h1 h2
  set c₀ : ℂ := (((1 + h : ℝ)) : ℂ) + (t : ℂ) * Complex.I with hc₀def
  set R : ℝ := h + w / 2 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; linarith only [hhpos, hwpos]
  have hc₀re : c₀.re = 1 + h := by simp [hc₀def]
  have hc₀im : c₀.im = t := by simp [hc₀def]
  have hc₀norm : ‖c₀‖ ≤ 1 + h + 4 := by
    have h1 : ‖c₀‖ = Real.sqrt ((1 + h) ^ 2 + t ^ 2) := by
      rw [hc₀def]; exact Complex.norm_add_mul_I _ _
    have ht1 := (abs_le.mp ht4).1
    have ht2 := (abs_le.mp ht4).2
    rw [h1, Real.sqrt_le_iff]
    refine ⟨by linarith only [hhpos], ?_⟩
    nlinarith only [ht1, ht2, hhpos, hh1]
  have hd_ball : ∀ z : ℂ, z ∈ ball c₀ R → ‖z - c₀‖ < R := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    exact hz
  -- the ball is zero-free and `‖L‖ ≤ 20N` on it
  have hball : ∀ z : ℂ, z ∈ ball c₀ R → 1 - w < z.re ∧ |z.im| ≤ 6 ∧
      3 / 4 ≤ z.re ∧ ‖z‖ ≤ 29 / 4 := by
    intro z hz
    have hd := hd_ball z hz
    have h2 : |z.re - c₀.re| ≤ ‖z - c₀‖ := by
      have := Complex.abs_re_le_norm (z - c₀); rwa [Complex.sub_re] at this
    have h3 : |z.im - c₀.im| ≤ ‖z - c₀‖ := by
      have := Complex.abs_im_le_norm (z - c₀); rwa [Complex.sub_im] at this
    rw [hc₀re] at h2
    rw [hc₀im] at h3
    have ht1 := (abs_le.mp ht4).1
    have ht2 := (abs_le.mp ht4).2
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- `1 - w < z.re`
      have h5 := (abs_le.mp h2).1
      rw [hRdef] at hd
      linarith only [h5, hd, hwpos]
    · rw [abs_le]
      have h5 := (abs_le.mp h3).1
      have h6 := (abs_le.mp h3).2
      rw [hRdef] at hd
      constructor <;> linarith only [h5, h6, ht1, ht2, hd, hh1, hwle]
    · have h5 := (abs_le.mp h2).1
      rw [hRdef] at hd
      linarith only [h5, hd, hwle, hwpos]
    · -- `‖z‖ ≤ 29/4`
      have h4 : ‖z‖ ≤ ‖c₀‖ + ‖z - c₀‖ := by
        calc ‖z‖ = ‖c₀ + (z - c₀)‖ := by ring_nf
          _ ≤ ‖c₀‖ + ‖z - c₀‖ := norm_add_le _ _
      rw [hRdef] at hd
      linarith only [h4, hc₀norm, hd, hh1, hwle]
  have hne : ∀ z ∈ ball c₀ R, DirichletCharacter.LFunction χ z ≠ 0 := by
    intro z hz hz0
    have h1 := hZ z hz0 (hball z hz).2.1
    linarith only [h1, (hball z hz).1]
  have hM : ∀ z ∈ ball c₀ R, ‖DirichletCharacter.LFunction χ z‖ ≤ 20 * (N : ℝ) := by
    intro z hz
    have h1 := Commons.NumberTheory.DirichletCharacter.LFunction_norm_half_plane χ hχne
      (by linarith only [(hball z hz).2.2.1])
    have h2 : 2 * (N : ℝ) * ‖z‖ / z.re ≤ 20 * (N : ℝ) := by
      rw [div_le_iff₀ (by linarith only [(hball z hz).2.2.1])]
      have h3 : 2 * (N : ℝ) * ‖z‖ ≤ 2 * (N : ℝ) * (29 / 4) :=
        mul_le_mul_of_nonneg_left (hball z hz).2.2.2 (by positivity)
      have h4 : 20 * (N : ℝ) * (3 / 4) ≤ 20 * (N : ℝ) * z.re :=
        mul_le_mul_of_nonneg_left (hball z hz).2.2.1 (by positivity)
      linarith only [h3, h4, hNpos]
    linarith only [h1, h2]
  have hm : h / 2 ≤ ‖DirichletCharacter.LFunction χ c₀‖ := by
    have hlow := LFunction_lower_one_add χ hχne h t hhpos hh1
    have h2 : (((1 + h : ℝ)) : ℂ) + (t : ℂ) * Complex.I = c₀ := by rw [hc₀def]
    rwa [h2] at hlow
  have hMm : h / 2 ≤ 20 * (N : ℝ) := by
    have h1 : h / 2 ≤ 1 / 2 := by linarith only [hh1]
    have h2 : (1 : ℝ) ≤ 20 * (N : ℝ) := by nlinarith only [hN1]
    linarith only [h1, h2]
  have hBC := Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound_analytic
    (g := DirichletCharacter.LFunction χ) (c := c₀) (R := R) (m := h / 2)
    (M := 20 * (N : ℝ)) hRpos (by linarith only [hhpos]) hMm
    ((DirichletCharacter.differentiable_LFunction hχne).differentiableOn.analyticOnNhd
      Metric.isOpen_ball) hne hM hm
  -- the point `s = σ + it` lies in the ball, with `R - ‖s - c₀‖ ≥ w/4`
  have hsball : ((σ : ℂ) + (t : ℂ) * Complex.I) ∈ ball c₀ R := by
    rw [mem_ball, dist_eq_norm]
    have h1 : ((σ : ℂ) + (t : ℂ) * Complex.I) - c₀ = ((σ - (1 + h) : ℝ) : ℂ) := by
      rw [hc₀def]; push_cast; ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs]
    have h2 : |σ - (1 + h)| = h - (σ - 1) := by
      rw [abs_of_nonpos (by linarith only [hh_ge'])]; ring
    rw [h2]
    rw [hRdef]
    linarith only [hσ, hcw, hwpos]
  have hgap : w / 4 ≤ R - ‖((σ : ℂ) + (t : ℂ) * Complex.I) - c₀‖ := by
    have h1 : ((σ : ℂ) + (t : ℂ) * Complex.I) - c₀ = ((σ - (1 + h) : ℝ) : ℂ) := by
      rw [hc₀def]; push_cast; ring
    have h2 : ‖((σ : ℂ) + (t : ℂ) * Complex.I) - c₀‖ = h - (σ - 1) := by
      rw [h1, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (by linarith only [hh_ge'])]
      ring
    rw [h2, hRdef]
    have h3 : (1 / (4 * K)) * (N : ℝ) ^ (-ε) ≤ w / 4 := hcw
    have h4 : 1 - σ ≤ (1 / (4 * K)) * (N : ℝ) ^ (-ε) := by linarith only [hσ]
    linarith only [h3, h4]
  have hsnorm : ‖((σ : ℂ) + (t : ℂ) * Complex.I) - c₀‖ = h - (σ - 1) := by
    have h1 : ((σ : ℂ) + (t : ℂ) * Complex.I) - c₀ = ((σ - (1 + h) : ℝ) : ℂ) := by
      rw [hc₀def]; push_cast; ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith only [hh_ge'])]
    ring
  set d : ℝ := ‖((σ : ℂ) + (t : ℂ) * Complex.I) - c₀‖ with hddef
  have hd_eq : d = h - (σ - 1) := by rw [hddef]; exact hsnorm
  have hkey := hBC hsball ((R - d) / 2)
    (by linarith only [hgap, hwpos])
    (by linarith only [hgap, hwpos])
  refine ⟨hne _ hsball, ?_⟩
  rw [logDeriv_apply]
  have hlog40 : Real.log (2 * (20 * (N : ℝ))) = Real.log (40 * (N : ℝ)) := by
    rw [show (2 : ℝ) * (20 * (N : ℝ)) = 40 * (N : ℝ) by ring]
  rw [hlog40] at hkey
  rw [← hddef] at hkey
  rw [mul_div_assoc] at hkey
  -- the fractional factor is at most `56/w`
  have h3R : (0 : ℝ) < R - d := by linarith only [hgap, hwpos]
  have hfrac : (d + (R - d) / 2) / ((R - d - (R - d) / 2) * ((R - d) / 2)) ≤ 56 / w := by
    have heq : (d + (R - d) / 2) / ((R - d - (R - d) / 2) * ((R - d) / 2))
        = 2 * (R + d) / (R - d) ^ 2 := by
      rw [show d + (R - d) / 2 = (R + d) / 2 by ring,
        show R - d - (R - d) / 2 = (R - d) / 2 by ring]
      field_simp
    rw [heq]
    by_cases hcase : σ - 1 ≤ w / 2
    · have hh : h = w / 2 := max_eq_left hcase
      have hre : R - d = w / 2 + (σ - 1) := by linarith only [hd_eq, hRdef, hh]
      have hdle : d ≤ 3 * w / 4 := by
        have h2 : w / 2 - (σ - 1) ≤ 3 * w / 4 := by linarith only [hre, hgap]
        have h3 : d = w / 2 - (σ - 1) := by linarith only [hd_eq, hh]
        linarith only [h3, h2]
      have hsum : R + d ≤ 7 * w / 4 := by
        have h3 : R = w := by linarith only [hRdef, hh]
        linarith only [h3, hdle]
      rw [div_le_iff₀ (by nlinarith only [hgap, hwpos] : (0 : ℝ) < (R - d) ^ 2)]
      have hnum : 2 * (R + d) ≤ 7 * w / 2 := by linarith only [hsum]
      have hden : w ^ 2 / 16 ≤ (R - d) ^ 2 := by nlinarith only [hgap, hwpos]
      have hmid : 7 * w / 2 ≤ 56 / w * (R - d) ^ 2 := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hwpos]
        nlinarith only [hden]
      linarith only [hnum, hmid]
    · have hh : h = σ - 1 := max_eq_right (le_of_lt (not_le.mp hcase))
      have hd0 : d = 0 := by linarith only [hd_eq, hh]
      have hRge : w / 2 ≤ R := by linarith only [hRdef, hh_ge, hwpos]
      rw [hd0]
      rw [div_le_iff₀ (by nlinarith only [hRge, hwpos] : (0 : ℝ) < (R - 0) ^ 2)]
      rw [show 56 / w * (R - 0) ^ 2 = 56 * (R - 0) ^ 2 / w by ring]
      rw [le_div_iff₀ hwpos]
      nlinarith only [hRge, hwpos]
  have hnon : (0 : ℝ) ≤ (d + (R - d) / 2) / ((R - d - (R - d) / 2) * ((R - d) / 2)) := by
    have h1 : R - d - (R - d) / 2 = (R - d) / 2 := by ring
    rw [h1]
    have h2 : (0 : ℝ) < (R - d) / 2 := by linarith only [h3R]
    have h4 : (0 : ℝ) ≤ d := norm_nonneg _
    positivity
  have hlogh : Real.log 2 - Real.log h ≤ Real.log (4 / w) := by
    have h1 : Real.log 2 - Real.log h = Real.log (2 / h) :=
      (Real.log_div (by norm_num) (ne_of_gt hhpos)).symm
    rw [h1]
    apply Real.log_le_log (by positivity)
    rw [div_le_iff₀ hhpos, div_mul_eq_mul_div, le_div_iff₀ hwpos]
    linarith only [hh_ge]
  have hmono : 2 * (Real.log (40 * (N : ℝ)) - Real.log (h / 2)) *
        ((d + (R - d) / 2) / ((R - d - (R - d) / 2) * ((R - d) / 2)))
      ≤ 112 * (Real.log (40 * (N : ℝ)) + Real.log (4 / w)) / w := by
    have h5 : Real.log (40 * (N : ℝ)) - Real.log (h / 2)
        ≤ Real.log (40 * (N : ℝ)) + Real.log (4 / w) := by
      have h1 : Real.log (h / 2) = Real.log h - Real.log 2 :=
        Real.log_div (ne_of_gt hhpos) (by norm_num)
      rw [h1]
      linarith only [hlogh]
    have h6 : (0 : ℝ) ≤ 2 * (Real.log (40 * (N : ℝ)) + Real.log (4 / w)) := by
      have h7 : 0 ≤ Real.log (40 * (N : ℝ)) := by
        apply Real.log_nonneg; nlinarith only [hN1]
      have h8 : 0 ≤ Real.log (4 / w) := by
        apply Real.log_nonneg
        rw [le_div_iff₀ hwpos]
        linarith only [hwle]
      linarith only [h7, h8]
    have h7 : 0 ≤ Real.log (40 * (N : ℝ)) - Real.log (h / 2) := by
      have h8 : h / 2 ≤ 40 * (N : ℝ) := by
        have h9 : h / 2 ≤ 1 / 2 := by linarith only [hh1]
        have h9' : (1 : ℝ) ≤ 40 * (N : ℝ) := by nlinarith only [hN1]
        linarith only [h9, h9']
      linarith only [Real.log_le_log (by positivity) h8]
    have h9 : 2 * (Real.log (40 * (N : ℝ)) - Real.log (h / 2))
        ≤ 2 * (Real.log (40 * (N : ℝ)) + Real.log (4 / w)) := by linarith only [h5]
    calc 2 * (Real.log (40 * (N : ℝ)) - Real.log (h / 2)) *
          ((d + (R - d) / 2) / ((R - d - (R - d) / 2) * ((R - d) / 2)))
        ≤ 2 * (Real.log (40 * (N : ℝ)) + Real.log (4 / w)) * (56 / w) :=
          mul_le_mul h9 hfrac hnon h6
      _ = 112 * (Real.log (40 * (N : ℝ)) + Real.log (4 / w)) / w := by ring
  refine le_trans hkey (le_trans hmono ?_)
  -- final numerics
  have hw1 : 1 / w ≤ K * (N : ℝ) ^ (ε / 2) := by
    rw [hw_1, one_div_one_div]
    exact hwInv
  have hlogN0 : 0 ≤ Real.log ((N : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hNε0 : (0 : ℝ) ≤ (N : ℝ) ^ ε := Real.rpow_nonneg hNpos.le _
  have hNhalfN : (N : ℝ) ^ (ε / 2) ≤ (N : ℝ) ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hAMGM : (N : ℝ) ^ (ε / 2) * Real.log ((N : ℝ) + 2)
      ≤ ((N : ℝ) ^ ε + Real.log ((N : ℝ) + 2) ^ 2) / 2 := by
    have h := sq_nonneg ((N : ℝ) ^ (ε / 2) - Real.log ((N : ℝ) + 2))
    have h1 : ((N : ℝ) ^ (ε / 2)) ^ 2 = (N : ℝ) ^ ε := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]; norm_num
    nlinarith only [h, h1, hNε0, hlogN0]
  have hlogw : Real.log (4 / w) ≤ Real.log 4 + Real.log K + (ε / 2) * Real.log (N : ℝ) := by
    have h1 : 4 / w = 4 * (1 / w) := by ring
    rw [h1, Real.log_mul (by norm_num) (by positivity)]
    have h2 : Real.log (1 / w) ≤ Real.log (K * (N : ℝ) ^ (ε / 2)) :=
      Real.log_le_log (by positivity) hw1
    rw [Real.log_mul (by linarith only [hKpos]) (by positivity), Real.log_rpow hNpos] at h2
    linarith only [h2]
  have hlogNle : Real.log (N : ℝ) ≤ Real.log ((N : ℝ) + 2) :=
    Real.log_le_log hNpos (by linarith)
  have hBN : (0 : ℝ) ≤ Real.log 40 + Real.log 4 + Real.log K := by
    have h3 : 0 ≤ Real.log 40 := Real.log_nonneg (by norm_num)
    have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have h5 : 0 ≤ Real.log K := Real.log_nonneg (by linarith only [hK2])
    linarith only [h3, h4, h5]
  set S' : ℝ := Real.log 40 + Real.log 4 + Real.log K + 1 with hS'def
  set Lp : ℝ := 1 + Real.log ((N : ℝ) + 2) with hLpdef
  set Np : ℝ := (N : ℝ) ^ (ε / 2) with hNpdef
  set X : ℝ := (N : ℝ) ^ ε + Real.log ((N : ℝ) + 2) ^ 2 with hXdef
  have hS'0 : 0 ≤ S' := by rw [hS'def]; linarith only [hBN]
  have hNp1 : 1 ≤ Np := by rw [hNpdef]; exact hNhalf
  have hX0 : 0 ≤ X := by rw [hXdef]; positivity
  have hQ1 : 1 ≤ 1 + ε / 2 := by linarith
  have hkey1 : Real.log (40 * (N : ℝ)) + Real.log (4 / w) ≤ S' * (1 + ε / 2) * Lp := by
    have h1 : Real.log (40 * (N : ℝ)) = Real.log 40 + Real.log (N : ℝ) :=
      Real.log_mul (by norm_num) (ne_of_gt hNpos)
    rw [h1]
    have hmul : (1 + ε / 2) * Real.log (N : ℝ) ≤ (1 + ε / 2) * Real.log ((N : ℝ) + 2) :=
      mul_le_mul_of_nonneg_left hlogNle (by linarith)
    have hstep : Real.log 40 + Real.log (N : ℝ) + Real.log (4 / w)
        ≤ (Real.log 40 + Real.log 4 + Real.log K) + (1 + ε / 2) * Real.log ((N : ℝ) + 2) :=
      by linarith only [hlogw, hmul]
    have hstep2 : (Real.log 40 + Real.log 4 + Real.log K) + (1 + ε / 2) * Real.log ((N : ℝ) + 2)
        ≤ S' * (1 + ε / 2) * Lp := by
      rw [hS'def, hLpdef]
      have hQR : 1 ≤ (1 + ε / 2) * (1 + Real.log ((N : ℝ) + 2)) := by
        nlinarith only [hQ1, hlogN0]
      have h1 : Real.log 40 + Real.log 4 + Real.log K
          ≤ (Real.log 40 + Real.log 4 + Real.log K)
            * ((1 + ε / 2) * (1 + Real.log ((N : ℝ) + 2))) :=
        le_mul_of_one_le_right hBN hQR
      have h2 : (1 + ε / 2) * Real.log ((N : ℝ) + 2)
          ≤ (1 + ε / 2) * (1 + Real.log ((N : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left (by linarith only [hlogN0]) (by linarith)
      nlinarith only [h1, h2]
    linarith only [hstep, hstep2]
  have hkey2 : Np * Lp ≤ (3 / 2) * X := by
    rw [hNpdef, hLpdef, hXdef]
    have h5 : (N : ℝ) ^ (ε / 2) * 1 ≤ (N : ℝ) ^ ε := by linarith only [hNhalfN]
    nlinarith only [h5, hAMGM, hNε0, hlogN0]
  have hstep1 : 112 * (Real.log (40 * (N : ℝ)) + Real.log (4 / w)) / w
      ≤ 112 * (K * Np) * (S' * (1 + ε / 2) * Lp) := by
    have h5 : 112 * (Real.log (40 * (N : ℝ)) + Real.log (4 / w)) / w
        = 112 * (1 / w) * (Real.log (40 * (N : ℝ)) + Real.log (4 / w)) := by ring
    rw [h5]
    have h6 : (0 : ℝ) ≤ Real.log (40 * (N : ℝ)) + Real.log (4 / w) := by
      have h7 : 0 ≤ Real.log (40 * (N : ℝ)) := by
        apply Real.log_nonneg; nlinarith only [hN1]
      have h8 : 0 ≤ Real.log (4 / w) := by
        apply Real.log_nonneg
        rw [le_div_iff₀ hwpos]
        linarith only [hwle]
      linarith only [h7, h8]
    have h9 : 112 * (1 / w) ≤ 112 * (K * Np) := by
      rw [hNpdef]; linarith only [hw1]
    exact mul_le_mul h9 hkey1 h6 (by positivity)
  have hfin : 112 * (K * Np) * (S' * (1 + ε / 2) * Lp)
      ≤ 500 * K * (1 + ε) * S' * X := by
    have h1 : 112 * (K * Np) * (S' * (1 + ε / 2) * Lp)
        = 112 * K * S' * (1 + ε / 2) * (Np * Lp) := by ring
    rw [h1]
    have h2 : 112 * K * S' * (1 + ε / 2) * (Np * Lp)
        ≤ 112 * K * S' * (1 + ε / 2) * ((3 / 2) * X) :=
      mul_le_mul_of_nonneg_left hkey2 (by positivity)
    have h3 : 112 * K * S' * (1 + ε / 2) * ((3 / 2) * X)
        ≤ 500 * K * (1 + ε) * S' * X := by
      have hc : 112 * (1 + ε / 2) * (3 / 2) ≤ 500 * (1 + ε) := by linarith only [hε]
      rw [show 112 * K * S' * (1 + ε / 2) * ((3 / 2) * X)
            = (112 * (1 + ε / 2) * (3 / 2)) * (K * S' * X) by ring,
          show 500 * K * (1 + ε) * S' * X = (500 * (1 + ε)) * (K * S' * X) by ring]
      exact mul_le_mul_of_nonneg_right hc (mul_nonneg (mul_nonneg hKpos.le hS'0) hX0)
    linarith only [h2, h3]
  calc 112 * (Real.log (40 * (N : ℝ)) + Real.log (4 / w)) / w
      ≤ 112 * (K * Np) * (S' * (1 + ε / 2) * Lp) := hstep1
    _ ≤ 500 * K * (1 + ε) * S' * X := hfin
    _ = 500 * K * (1 + ε) * (Real.log 40 + Real.log 4 + Real.log K + 1)
          * ((N : ℝ) ^ ε + Real.log ((N : ℝ) + 2) ^ 2) := by
        rw [hS'def, hXdef]

end

end Work.BMF
