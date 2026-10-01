import Mathlib
import Submission.Work.LinnikAreas.ZetaTentPrelude
import Submission.Work.LinnikAreas.Zeta1Aux.zeta1_zero_strip
import Submission.Work.LinnikAreas.Zeta1Aux.zeta1_windowZeroCount
import Submission.Work.LinnikAreas.Zeta1Aux.zeta1_goodHeight_pointwise
import Submission.Work.LinnikAreas.Zeta1Aux.zeta1_logDeriv_pointwise_bound
import Submission.Work.LinnikAreas.Zeta1Aux.zeta_strip_polyGrowth_far_left
import Submission.Work.LinnikAreas.Zeta1Aux.tendsto_inv_sq_mul_log_sq

open Filter MeasureTheory

namespace Work.LinnikAreas

set_option linter.unusedVariables false

private lemma vanishing_aux {L K : ℝ} (hK : 0 < K) (h2K : 2 * K < L) {q : ℕ} (hq : 2 ≤ q)
    (g : ℝ → ℝ) (M Cd c : ℝ) (hM : 0 < M) (hCd : 0 < Cd) (hc : 0 < c) (hc1 : c ≤ 1)
    (hg7 : ∀ T : ℝ, 8 ≤ T → 7 ≤ |g T|)
    (hginf : Tendsto (fun T : ℝ => |g T|) atTop atTop)
    (hD : ∀ v : ℝ, 7 ≤ |v| → ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      (∀ ρ : ℂ, riemannZeta₁ ρ = 0 → δ ≤ |ρ.im - v|) →
      ∀ x : ℝ, x ∈ Set.Icc (-(1/2)) 2 →
        ‖logDeriv riemannZeta₁ ((x : ℂ) + (v : ℂ) * Complex.I)‖ ≤
          Cd * Real.log (|v| + 3) * (Real.log (|v| + 3) + 1/δ))
    (hΦ : ∀ u : ℂ, u.re ≤ 2 →
      ‖Commons.NumberTheory.Linnik.tentPhi L K q u‖ ≤ M / (1 + ‖u‖^2))
    (hsep : ∀ T : ℝ, 8 ≤ T → ∀ ρ : ℂ, riemannZeta₁ ρ = 0 →
      c / Real.log (|g T| + 3) ≤ |ρ.im - g T|)
    (hF : Tendsto (fun t : ℝ =>
      (M / (1 + t^2)) * (Cd * (1 + 1/c) * (Real.log (t + 3))^2)) atTop (nhds 0)) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in (-1/2)..2,
        logDeriv riemannZeta₁ ((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I) *
          Commons.NumberTheory.Linnik.tentPhi L K q ((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I))
      atTop (nhds 0) := by
  have hG : Tendsto (fun T : ℝ => (M / (1 + |g T|^2)) *
      (Cd * (1 + 1/c) * (Real.log (|g T| + 3))^2)) atTop (nhds 0) := hF.comp hginf
  have hpt : ∀ T : ℝ, 8 ≤ T → ∀ x : ℝ, x ∈ Set.uIoc (-1/2 : ℝ) 2 →
      ‖logDeriv riemannZeta₁ ((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I) *
        Commons.NumberTheory.Linnik.tentPhi L K q ((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I)‖
      ≤ (M / (1 + |g T|^2)) * (Cd * (1 + 1/c) * (Real.log (|g T| + 3))^2) := by
    intro T hT x hx
    have hg7T : 7 ≤ |g T| := hg7 T hT
    have hlogpos : 0 < Real.log (|g T| + 3) := Real.log_pos (by linarith)
    have hδpos : 0 < c / Real.log (|g T| + 3) := div_pos hc hlogpos
    have hδ1 : c / Real.log (|g T| + 3) ≤ 1 := by
      rw [div_le_one hlogpos]
      have h1 : 1 ≤ Real.log (|g T| + 3) := by
        rw [Real.le_log_iff_exp_le (by linarith)]
        have := Real.exp_one_lt_d9; linarith
      linarith
    rw [Set.uIoc_of_le (by norm_num : (-1/2:ℝ) ≤ 2)] at hx
    have hxIcc : x ∈ Set.Icc (-(1/2)) 2 := ⟨by linarith [hx.1], hx.2⟩
    rw [norm_mul]
    have hkey := hD (g T) hg7T (c / Real.log (|g T| + 3)) hδpos hδ1 (hsep T hT) x hxIcc
    rw [one_div_div] at hkey
    have hΦx : ‖Commons.NumberTheory.Linnik.tentPhi L K q
        ((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I)‖ ≤ M / (1 + |g T|^2) := by
      have hre : ((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I).re = x := by simp
      have hb := hΦ _ (by rw [hre]; exact hxIcc.2)
      have hn2 : (g T)^2 ≤ ‖((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I)‖^2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; simp; nlinarith [sq_nonneg x]
      have hden : 1 + |g T|^2 ≤ 1 + ‖((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I)‖^2 := by
        rw [sq_abs]; linarith
      exact hb.trans (div_le_div_of_nonneg_left (le_of_lt hM) (by positivity) hden)
    calc ‖logDeriv riemannZeta₁ ((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I)‖ *
          ‖Commons.NumberTheory.Linnik.tentPhi L K q ((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I)‖
        ≤ (Cd * Real.log (|g T| + 3) * (Real.log (|g T| + 3) + Real.log (|g T| + 3) / c)) *
            (M / (1 + |g T|^2)) :=
          mul_le_mul hkey hΦx (norm_nonneg _) (by positivity)
      _ = (M / (1 + |g T|^2)) * (Cd * (1 + 1/c) * (Real.log (|g T| + 3))^2) := by field_simp
  have hbnd : ∀ᶠ T in atTop, ‖∫ x : ℝ in (-1/2)..2,
        logDeriv riemannZeta₁ ((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I) *
          Commons.NumberTheory.Linnik.tentPhi L K q ((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I)‖
      ≤ (5/2) * ((M / (1 + |g T|^2)) * (Cd * (1 + 1/c) * (Real.log (|g T| + 3))^2)) := by
    filter_upwards [eventually_ge_atTop (8:ℝ)] with T hT
    have hint := intervalIntegral.norm_integral_le_of_norm_le_const (hpt T hT)
    rw [show |(2:ℝ) - (-1/2)| = 5/2 by norm_num] at hint
    calc ‖∫ x : ℝ in (-1/2)..2, logDeriv riemannZeta₁ ((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I) *
          Commons.NumberTheory.Linnik.tentPhi L K q ((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I)‖
        ≤ ((M / (1 + |g T|^2)) * (Cd * (1 + 1/c) * (Real.log (|g T| + 3))^2)) * (5/2) := hint
      _ = (5/2) * ((M / (1 + |g T|^2)) * (Cd * (1 + 1/c) * (Real.log (|g T| + 3))^2)) := by ring
  have hlim : Tendsto (fun T : ℝ => (5/2) * ((M / (1 + |g T|^2)) *
      (Cd * (1 + 1/c) * (Real.log (|g T| + 3))^2))) atTop (nhds 0) := by
    simpa using hG.const_mul (5/2 : ℝ)
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero' (Eventually.of_forall (fun T => norm_nonneg _)) hbnd hlim)

theorem zeta1_goodHeight_horizontal_vanishing {L K : ℝ} (hK : 0 < K) (h2K : 2 * K < L)
    {q : ℕ} (hq : 2 ≤ q) :
    ∃ c : ℝ, 0 < c ∧ ∃ T' : ℝ → ℝ,
      (∀ T : ℝ, 1 ≤ T → T + 1 ≤ T' T ∧ T' T ≤ T + 2) ∧
      (∀ T : ℝ, 1 ≤ T → ∀ ρ : ℂ, riemannZeta₁ ρ = 0 →
        c / Real.log (T' T + 3) ≤ |ρ.im - T' T| ∧
        c / Real.log (T' T + 3) ≤ |ρ.im + T' T|) ∧
      (Filter.Tendsto (fun T : ℝ => ∫ x : ℝ in (-1/2)..2,
          logDeriv riemannZeta₁ ((x : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I) *
            Commons.NumberTheory.Linnik.tentPhi L K q ((x : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I))
          Filter.atTop (nhds 0)) ∧
      (Filter.Tendsto (fun T : ℝ => ∫ x : ℝ in (-1/2)..2,
          logDeriv riemannZeta₁ ((x : ℂ) - ((T' T : ℝ) : ℂ) * Complex.I) *
            Commons.NumberTheory.Linnik.tentPhi L K q ((x : ℂ) - ((T' T : ℝ) : ℂ) * Complex.I))
          Filter.atTop (nhds 0)) := by
  have hstrip : ∀ ρ : ℂ, riemannZeta₁ ρ = 0 → ρ.im ≠ 0 → 0 < ρ.re ∧ ρ.re < 1 :=
    fun ρ hρ him => Zeta1Aux.zeta1_zero_strip hρ him
  obtain ⟨Cw, hCwpos, hCw⟩ := Zeta1Aux.zeta1_windowZeroCount hstrip
  obtain ⟨c₀, hc₀pos, hgood⟩ := Zeta1Aux.zeta1_goodHeight_pointwise hstrip ⟨Cw, hCwpos, hCw⟩
  obtain ⟨Cgf, hCgfpos, hCgf⟩ := Zeta1Aux.zeta_strip_polyGrowth_far_left
  obtain ⟨Cgn, hCgnpos, hCgn⟩ := Commons.NumberTheory.Zeta.zeta_strip_polyGrowth_neg
  have hgrowth : ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, -4 ≤ σ → σ ≤ -1 → 1 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤ C * (|t| + 3) ^ 12 := by
    refine ⟨max Cgf Cgn, lt_max_of_lt_left hCgfpos, ?_⟩
    intro σ t hσ4 hσ1 ht
    have hnn : (0:ℝ) ≤ (|t| + 3) ^ 12 := by positivity
    rcases le_total σ (-2) with h | h
    · exact (hCgf σ t hσ4 h ht).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hnn)
    · exact (hCgn σ t h hσ1 ht).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hnn)
  obtain ⟨Cd, hCdpos, hD⟩ := Zeta1Aux.zeta1_logDeriv_pointwise_bound ⟨Cw, hCwpos, hCw⟩ hgrowth
  obtain ⟨M, hMpos, hM⟩ := Commons.NumberTheory.Linnik.exists_norm_tentPhi_bound hK h2K hq
  let Tf : ℝ → ℝ := fun T => if h : 1 ≤ T then Classical.choose (hgood T h) else T + 1
  have hTf : ∀ T : ℝ, ∀ hT : 1 ≤ T, T + 1 ≤ Tf T ∧ Tf T ≤ T + 2 ∧
      (∀ ρ : ℂ, riemannZeta₁ ρ = 0 → c₀ / Real.log (Tf T + 3) ≤ |ρ.im - Tf T|) ∧
      (∀ ρ : ℂ, riemannZeta₁ ρ = 0 → c₀ / Real.log (Tf T + 3) ≤ |ρ.im + Tf T|) := by
    intro T hT
    have h := Classical.choose_spec (hgood T hT)
    simpa only [Tf, dif_pos hT] using h
  have hTf_ge : ∀ T : ℝ, 1 ≤ T → T + 1 ≤ Tf T := fun T hT => (hTf T hT).1
  have hTfp : ∀ T : ℝ, 1 ≤ T → 0 < Tf T + 3 := by
    intro T hT
    have h := hTf_ge T hT
    linarith
  have hTflog : ∀ T : ℝ, 1 ≤ T → 0 < Real.log (Tf T + 3) := by
    intro T hT
    exact Real.log_pos (by have h := hTf_ge T hT; linarith)
  have hTfnn : ∀ T : ℝ, 1 ≤ T → 0 ≤ Tf T := by
    intro T hT
    have h := hTf_ge T hT
    linarith
  have hcle1 : min (min c₀ 1) Cd ≤ 1 := le_trans (min_le_left _ _) (min_le_right _ _)
  refine ⟨min (min c₀ 1) Cd, lt_min (lt_min hc₀pos one_pos) hCdpos, Tf, ?_, ?_, ?_, ?_⟩
  · intro T hT
    exact ⟨(hTf T hT).1, (hTf T hT).2.1⟩
  · intro T hT ρ hρ
    obtain ⟨_, _, h1, h2⟩ := hTf T hT
    have hlog := hTflog T hT
    constructor
    · calc min (min c₀ 1) Cd / Real.log (Tf T + 3)
          ≤ min c₀ 1 / Real.log (Tf T + 3) :=
            div_le_div_of_nonneg_right (min_le_left _ _) (le_of_lt hlog)
        _ ≤ c₀ / Real.log (Tf T + 3) :=
            div_le_div_of_nonneg_right (min_le_left _ _) (le_of_lt hlog)
        _ ≤ |ρ.im - Tf T| := h1 ρ hρ
    · calc min (min c₀ 1) Cd / Real.log (Tf T + 3)
          ≤ min c₀ 1 / Real.log (Tf T + 3) :=
            div_le_div_of_nonneg_right (min_le_left _ _) (le_of_lt hlog)
        _ ≤ c₀ / Real.log (Tf T + 3) :=
            div_le_div_of_nonneg_right (min_le_left _ _) (le_of_lt hlog)
        _ ≤ |ρ.im + Tf T| := h2 ρ hρ
  · refine vanishing_aux hK h2K hq Tf M Cd (min (min c₀ 1) Cd) hMpos hCdpos
      (lt_min (lt_min hc₀pos one_pos) hCdpos) hcle1 ?_ ?_ hD hM ?_
      (Zeta1Aux.tendsto_inv_sq_mul_log_sq hMpos hCdpos (lt_min (lt_min hc₀pos one_pos) hCdpos))
    · intro T hT
      have h := hTf_ge T (by linarith : 1 ≤ T)
      rw [abs_of_nonneg (hTfnn T (by linarith))]
      linarith
    · have h1 : Tendsto (fun T : ℝ => T + 1) atTop atTop :=
        tendsto_atTop_add_const_right _ 1 tendsto_id
      refine tendsto_atTop_mono' atTop ?_ h1
      filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
      rw [abs_of_nonneg (hTfnn T hT)]
      exact hTf_ge T hT
    · intro T hT ρ hρ
      have hlog := hTflog T (by linarith : 1 ≤ T)
      have h1 := (hTf T (by linarith : 1 ≤ T)).2.2.1 ρ hρ
      calc min (min c₀ 1) Cd / Real.log (|Tf T| + 3)
          = min (min c₀ 1) Cd / Real.log (Tf T + 3) := by
            rw [abs_of_nonneg (hTfnn T (by linarith))]
        _ ≤ min c₀ 1 / Real.log (Tf T + 3) :=
            div_le_div_of_nonneg_right (min_le_left _ _) (le_of_lt hlog)
        _ ≤ c₀ / Real.log (Tf T + 3) :=
            div_le_div_of_nonneg_right (min_le_left _ _) (le_of_lt hlog)
        _ ≤ |ρ.im - Tf T| := h1
  · have hmain : Tendsto (fun T : ℝ => ∫ x : ℝ in (-1/2)..2,
        logDeriv riemannZeta₁ ((x : ℂ) + ((-(Tf T) : ℝ) : ℂ) * Complex.I) *
          Commons.NumberTheory.Linnik.tentPhi L K q ((x : ℂ) + ((-(Tf T) : ℝ) : ℂ) * Complex.I))
        atTop (nhds 0) := by
      refine vanishing_aux hK h2K hq (fun T => -Tf T) M Cd (min (min c₀ 1) Cd) hMpos
        hCdpos (lt_min (lt_min hc₀pos one_pos) hCdpos) hcle1 ?_ ?_ hD hM ?_
        (Zeta1Aux.tendsto_inv_sq_mul_log_sq hMpos hCdpos (lt_min (lt_min hc₀pos one_pos) hCdpos))
      · intro T hT
        have h := hTf_ge T (by linarith : 1 ≤ T)
        rw [abs_neg, abs_of_nonneg (hTfnn T (by linarith))]
        linarith
      · have h1 : Tendsto (fun T : ℝ => T + 1) atTop atTop :=
          tendsto_atTop_add_const_right _ 1 tendsto_id
        have h2 : Tendsto (fun T : ℝ => |Tf T|) atTop atTop := by
          refine tendsto_atTop_mono' atTop ?_ h1
          filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
          rw [abs_of_nonneg (hTfnn T hT)]
          exact hTf_ge T hT
        simpa only [abs_neg] using h2
      · intro T hT ρ hρ
        have hlog := hTflog T (by linarith : 1 ≤ T)
        have h2 := (hTf T (by linarith : 1 ≤ T)).2.2.2 ρ hρ
        rw [abs_neg, sub_neg_eq_add]
        calc min (min c₀ 1) Cd / Real.log (|Tf T| + 3)
            = min (min c₀ 1) Cd / Real.log (Tf T + 3) := by
              rw [abs_of_nonneg (hTfnn T (by linarith))]
          _ ≤ min c₀ 1 / Real.log (Tf T + 3) :=
              div_le_div_of_nonneg_right (min_le_left _ _) (le_of_lt hlog)
          _ ≤ c₀ / Real.log (Tf T + 3) :=
              div_le_div_of_nonneg_right (min_le_left _ _) (le_of_lt hlog)
          _ ≤ |ρ.im + Tf T| := h2
    simpa only [Complex.ofReal_neg, neg_mul, sub_eq_add_neg] using hmain

end Work.LinnikAreas
