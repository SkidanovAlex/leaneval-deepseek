import Mathlib
import Submission.Work.ZeroFreeTables.HB94.hbLemma6_2_engine_restricted
import Submission.Work.ZeroFreeTables.hbLemma6_2_engine_v2

open Complex DirichletCharacter Metric BigOperators
open scoped BigOperators
noncomputable section

namespace Work.ZeroFreeTables.HB94

open Work.LinnikContract

/-- **HB Lemma 6.2 engine, restricted constants, with a wide second zero.**  This is
`Work.ZeroFreeTables.HB94.hbLemma6_2_engine_restricted` (same file dir, PROVED) with the hypothesis
`IsZ χ₂ ρ₂` replaced by its two useful components plus a wide height bound: `zeroMult χ₂ ρ₂ ≠ 0`,
`χ₂ ≠ 1`, `|ρ₂.im| ≤ 8`.  Copy the restricted file and edit only those hypotheses: in its proof
`IsZ χ₂ ρ₂` is used only as `hzm₂ : zeroMult χ₂ ρ₂ ≠ 0` and `hγ₂le : |γ₂| ≤ 1`, and the latter only
in the window-height bounds `|s₂.im|+δ ≤ 9 ≤ 10`, `|s₃.im|+δ ≤ 1+8+δ < 10`, `|s₄.im|+δ < 10`
and in `|s_k.im| ≤ 10·log q` (which holds once `log q ≥ 1`, already enforced by the engine's
threshold).  Everything else (the strip membership of `ρ₂` from `re_mem_Ioo_of_zeroMult_v2`, the
`[NeZero …conductor]` instances, the four `L52Hyp` hypotheses) is unchanged. -/
theorem hbLemma6_2_engine_wide (T : Work.ZeroFreeTables.TestFn) (c ε δ : ℝ)
    (hε : 0 < ε) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q) (ρ₁ ρ₂ : ℂ)
      [NeZero χ₁.conductor] [NeZero χ₂.conductor] [NeZero (χ₁ * χ₂).conductor]
      [NeZero (χ₁ * χ₂⁻¹).conductor],
      Commons.NumberTheory.Linnik.L52Hyp χ₁ c ε δ →
      Commons.NumberTheory.Linnik.L52Hyp χ₂ c ε δ →
      Commons.NumberTheory.Linnik.L52Hyp (χ₁ * χ₂) c ε δ →
      Commons.NumberTheory.Linnik.L52Hyp (χ₁ * χ₂⁻¹) c ε δ →
      Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → Work.LinnikContract.IsZ χ₁ ρ₁ →
      Work.LinnikContract.zeroMult χ₂ ρ₂ ≠ 0 → χ₂ ≠ 1 → χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ →
      |ρ₂.im| ≤ 8 → Work.LinnikContract.lamOf q ρ₁ ≤ 1 → Work.LinnikContract.lamOf q ρ₂ ≤ 1 →
      0 ≤ T.F (-(Work.LinnikContract.lamOf q ρ₁)) - T.F 0
          - T.F (Work.LinnikContract.lamOf q ρ₂ - Work.LinnikContract.lamOf q ρ₁)
          + T.f 0 * (3 * (c + ε)) := by
  obtain ⟨B, hB0, hBnd⟩ := T.f_bound
  have hF : ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ (∫ t in (0:ℝ)..T.x₀, Complex.exp (-(z * (t : ℂ))) * ((T.f t : ℝ) : ℂ)).re := by
    intro z hz; rw [← T.Fc_spec z]; exact T.Fc_re_nonneg z hz
  set ep : ℝ := ε / 2 with hep
  set cK : ℝ := c + ε / 8 with hcK
  set e0 : ℝ := ε / 4 with he0
  have hep0 : 0 < ep := by rw [hep]; linarith only [hε]
  have he00 : 0 < e0 := by rw [he0]; linarith only [hε]
  have hcKep : cK + ep / 4 = c + ε / 4 := by rw [hcK, hep]; ring
  obtain ⟨q₀p, hq₀p⟩ := Commons.NumberTheory.Linnik.Ksum_principal_le T.x₀ B T.x₀_pos hB0
    T.f_cont T.f_supp T.f_diff hBnd he00 T.f0_pos
  obtain ⟨q₀a, hq₀a⟩ := Commons.NumberTheory.Linnik.Ksum_le_self_of_L52_phi T.x₀ B cK T.x₀_pos hB0
    T.f_cont T.f_supp T.f_diff hBnd T.f0_pos hF hep0 hδ0 hδ1
  obtain ⟨q₀b, hq₀b⟩ := Commons.NumberTheory.Linnik.Ksum_le_single_of_L52_phi T.x₀ B cK T.x₀_pos hB0
    T.f_cont T.f_supp T.f_diff hBnd T.f0_pos hF hep0 hδ0 hδ1
  refine ⟨max (max (max q₀p q₀a) q₀b) (Nat.ceil (Real.exp (Real.exp (max 1 (1/δ)))) + 1), ?_⟩
  intro q hqq _inst χ₁ χ₂ ρ₁ ρ₂ hc₁ hc₂ hcA hcB
    hL52₁ hL52₂ hL52A hL52B hmin hZ₁ hzm2 hχ₂ hne21 hne21' hγ₂wide hLm1 hLm2
  haveI : NeZero χ₁.conductor := hc₁
  haveI : NeZero χ₂.conductor := hc₂
  haveI : NeZero (χ₁ * χ₂).conductor := hcA
  haveI : NeZero (χ₁ * χ₂⁻¹).conductor := hcB
  have hq0p : q₀p ≤ q := by omega
  have hq0a : q₀a ≤ q := by omega
  have hq0b : q₀b ≤ q := by omega
  have hqC : Nat.ceil (Real.exp (Real.exp (max 1 (1/δ)))) + 1 ≤ q := by omega
  set L : ℝ := Real.log (q : ℝ) with hLdef
  set β₁ : ℝ := ρ₁.re with hβ₁def
  set β₂ : ℝ := ρ₂.re with hβ₂def
  set γ₁ : ℝ := ρ₁.im with hγ₁def
  set γ₂ : ℝ := ρ₂.im with hγ₂def
  set Lam1 : ℝ := lamOf q ρ₁ with hLam1def
  set Lam2 : ℝ := lamOf q ρ₂ with hLam2def
  have hLam1eq : Lam1 = (1 - β₁) * L := by simp only [hLam1def, hβ₁def, hLdef, lamOf]
  have hLam2eq : Lam2 = (1 - β₂) * L := by simp only [hLam2def, hβ₂def, hLdef, lamOf]
  have hT1 : 1 ≤ max 1 (1/δ) := le_max_left _ _
  have hTd : 1/δ ≤ max 1 (1/δ) := le_max_right _ _
  have hexp_le : Real.exp (Real.exp (max 1 (1/δ))) ≤ (q : ℝ) := by
    have h1 : (Nat.ceil (Real.exp (Real.exp (max 1 (1/δ)))) : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast (le_trans (Nat.le_succ _) hqC)
    exact le_trans (Nat.le_ceil _) h1
  have hLge : Real.exp (max 1 (1/δ)) ≤ L := by
    rw [hLdef]
    have h := Real.log_le_log (Real.exp_pos (Real.exp (max 1 (1/δ)))) hexp_le
    rwa [Real.log_exp] at h
  have hLpos : 0 < L := lt_of_lt_of_le (Real.exp_pos (max 1 (1/δ))) hLge
  have hTle : max 1 (1/δ) ≤ Real.exp (max 1 (1/δ)) := by
    linarith only [Real.add_one_le_exp (max 1 (1/δ)), hδ0, hδ1]
  have hLgeT : max 1 (1/δ) ≤ L := le_trans hTle hLge
  have hL1 : 1 ≤ L := le_trans hT1 hLgeT
  have hlogLge1 : 1 ≤ Real.log L := by
    have h := Real.log_le_log (Real.exp_pos (max 1 (1/δ))) hLge
    rw [Real.log_exp] at h
    linarith only [hT1, h]
  have hsqrt_ge1 : 1 ≤ Real.sqrt (Real.log L) := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hlogLge1
  have hLnn : 0 ≤ Real.log (q : ℝ) := by rw [← hLdef]; exact hLpos.le
  have hδL : 1 ≤ δ * L := by
    have h : δ * (1/δ) ≤ δ * L := mul_le_mul_of_nonneg_left (le_trans hTd hLgeT) hδ0.le
    rwa [mul_one_div_cancel hδ0.ne'] at h
  have hzm₁ : zeroMult χ₁ ρ₁ ≠ 0 := hZ₁.2.1
  have hzm₂ : zeroMult χ₂ ρ₂ ≠ 0 := hzm2
  have hχ₁ : χ₁ ≠ 1 := hZ₁.1
  have hγ₁le : |γ₁| ≤ 1 := by rw [hγ₁def]; exact hZ₁.2.2
  have hγ₂le : |γ₂| ≤ 8 := by rw [hγ₂def]; exact hγ₂wide
  have hstrip₁ := re_mem_Ioo_of_zeroMult_v2 χ₁ hχ₁ hzm₁
  have hstrip₂ := re_mem_Ioo_of_zeroMult_v2 χ₂ hχ₂ hzm₂
  have hβ₁pos : 0 < β₁ := by rw [hβ₁def]; exact hstrip₁.1
  have hβ₁lt : β₁ < 1 := by rw [hβ₁def]; exact hstrip₁.2
  have hβ₂pos : 0 < β₂ := by rw [hβ₂def]; exact hstrip₂.1
  have hβ₂lt : β₂ < 1 := by rw [hβ₂def]; exact hstrip₂.2
  have hLam1' : Lam1 ≤ 1 := by rw [hLam1def]; exact hLm1
  have hLam2' : Lam2 ≤ 1 := by rw [hLam2def]; exact hLm2
  have hLposq : 0 < Real.log (q : ℝ) := by rw [← hLdef]; exact hLpos
  have habsβ₁ : |β₁ - 1| ≤ Real.sqrt (Real.log L) / L := by
    have h1 : 1 - β₁ = Lam1 / L := by rw [hLam1eq, mul_div_cancel_right₀ _ hLpos.ne']
    rw [abs_of_neg (by linarith only [hstrip₁] : β₁ - 1 < 0), neg_sub, h1]
    exact div_le_div_of_nonneg_right (le_trans hLam1' hsqrt_ge1) hLpos.le
  have habsβ₁' : |β₁ - 1| ≤
      Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) := by
    rw [← hLdef]; exact habsβ₁
  have hβ₁ge : 1 - Real.sqrt (Real.log L) / L ≤ β₁ := by
    have h1 : 1 - β₁ = Lam1 / L := by rw [hLam1eq, mul_div_cancel_right₀ _ hLpos.ne']
    have h2 : Lam1 / L ≤ Real.sqrt (Real.log L) / L :=
      div_le_div_of_nonneg_right (le_trans hLam1' hsqrt_ge1) hLpos.le
    linarith only [h1, h2]
  set s₁ : ℂ := (β₁ : ℂ) + (γ₁ : ℂ) * Complex.I with hs₁
  set s₂ : ℂ := (β₁ : ℂ) + (γ₂ : ℂ) * Complex.I with hs₂
  set s₃ : ℂ := (β₁ : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ)) * Complex.I with hs₃
  set s₄ : ℂ := (β₁ : ℂ) + ((γ₁ : ℂ) - (γ₂ : ℂ)) * Complex.I with hs₄
  have hs₁re : s₁.re = β₁ := by simp [hs₁]
  have hs₂re : s₂.re = β₁ := by simp [hs₂]
  have hs₃re : s₃.re = β₁ := by simp [hs₃]
  have hs₄re : s₄.re = β₁ := by simp [hs₄]
  have hs₁im : s₁.im = γ₁ := by simp [hs₁]
  have hs₂im : s₂.im = γ₂ := by simp [hs₂]
  have hs₃im : s₃.im = γ₁ + γ₂ := by simp [hs₃]
  have hs₄im : s₄.im = γ₁ - γ₂ := by simp [hs₄]
  have hs₁eq : s₁ = ρ₁ := by rw [hs₁, hβ₁def, hγ₁def]; exact Complex.re_add_im ρ₁
  have hρ₂eq : ((β₂ : ℂ) + (γ₂ : ℂ) * Complex.I) = ρ₂ := by
    rw [hβ₂def, hγ₂def]; exact Complex.re_add_im ρ₂
  have hneA : χ₁ * χ₂ ≠ 1 := fun h => hne21' (eq_inv_of_mul_eq_one_right h)
  have hneB : χ₁ * χ₂⁻¹ ≠ 1 := fun h => hne21 ((mul_inv_eq_one.mp h).symm)
  have hre₁ : ((β₁ : ℂ) + (γ₁ : ℂ) * Complex.I).re = β₁ := by simp
  have hre₂ : ((β₂ : ℂ) + (γ₂ : ℂ) * Complex.I).re = β₂ := by simp
  have hmem₁ : s₁ ∈ Metric.closedBall (0:ℂ) (|s₁.im| + 2) :=
    mem_closedBall_of_absre_le_one_v2 (by rw [hs₁, hre₁, abs_of_pos hβ₁pos]; linarith only [hstrip₁])
  have hmem₂ : ((β₂ : ℂ) + (γ₂ : ℂ) * Complex.I) ∈
      Metric.closedBall (0:ℂ) (|s₂.im| + 2) := by
    have hzi : ((β₂ : ℂ) + (γ₂ : ℂ) * Complex.I).im = s₂.im := by simp [hs₂]
    rw [← hzi]
    exact mem_closedBall_of_absre_le_one_v2 (by rw [hre₂, abs_of_pos hβ₂pos]; linarith only [hstrip₂])
  have hL52K₁ : Commons.NumberTheory.Linnik.L52Hyp χ₁ cK ep δ := by
    intro s h1 h2 h3
    have h := hL52₁ s h1 h2 h3
    simpa only [hcKep] using h
  have hL52K₂ : Commons.NumberTheory.Linnik.L52Hyp χ₂ cK ep δ := by
    intro s h1 h2 h3
    have h := hL52₂ s h1 h2 h3
    simpa only [hcKep] using h
  have hL52KA : Commons.NumberTheory.Linnik.L52Hyp (χ₁ * χ₂) cK ep δ := by
    intro s h1 h2 h3
    have h := hL52A s h1 h2 h3
    simpa only [hcKep] using h
  have hL52KB : Commons.NumberTheory.Linnik.L52Hyp (χ₁ * χ₂⁻¹) cK ep δ := by
    intro s h1 h2 h3
    have h := hL52B s h1 h2 h3
    simpa only [hcKep] using h
  have hIm₁ : |s₁.im| + δ ≤ 10 := by rw [hs₁im]; linarith only [hγ₁le, hδ1, hδ0]
  have hIm₂ : |s₂.im| + δ ≤ 10 := by rw [hs₂im]; linarith only [hγ₂le, hδ1, hδ0, hγ₂wide]
  have hIm₃ : |s₃.im| + δ ≤ 10 := by
    rw [hs₃im]; have h := abs_add_le γ₁ γ₂; linarith only [h, hγ₁le, hγ₂le, hδ1, hγ₂wide]
  have hIm₄ : |s₄.im| + δ ≤ 10 := by
    rw [hs₄im]; have h : |γ₁ - γ₂| ≤ |γ₁| + |γ₂| := by
      simpa [sub_eq_add_neg] using abs_add_le γ₁ (-γ₂)
    linarith only [h, hγ₁le, hγ₂le, hδ1, hγ₂wide]
  have h0 : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            ((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ (β₁ : ℂ)).re
              * T.f (Real.log n / L))
          ≤ L * (∫ t in (0:ℝ)..T.x₀, Real.exp (Lam1 * t) * T.f t) + T.f 0 * e0 * L := by
    have h := hq₀p (q := q) hq0p (β := β₁) (lam := Lam1)
      (by rw [hLam1eq, hLdef]; ring) habsβ₁'
    rwa [← hLdef] at h
  have h1 : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            (χ₁ (n : ZMod q) / (n : ℂ) ^ ((β₁ : ℂ) + (γ₁ : ℂ) * Complex.I)).re
              * T.f (Real.log n / L))
          ≤ -L * (∫ t in (0:ℝ)..T.x₀, T.f t) + T.f 0 * (cK + ep) * L := by
    have hb := hq₀b (q := q) (s := s₁) (ρ := s₁) hq0b χ₁ hχ₁
      (by rw [hs₁re]; exact habsβ₁')
      (by rw [hs₁im, ← hLdef]; linarith only [hγ₁le, hL1, hδ0, hδ1, hT1, hLge, hTle])
      (by rw [hs₁re, ← hLdef]; exact hβ₁ge)
      hL52K₁
      (divisor_ne_zero_of_zeroMult_v2 χ₁ hχ₁ hmem₁ (by rw [hs₁eq]; exact hzm₁))
      (by
        have hc : (1:ℂ) + (s₁.im : ℂ) * Complex.I - s₁ = ((1 - β₁ : ℝ) : ℂ) := by
          rw [hs₁im, hs₁]; push_cast; ring
        rw [hc, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by linarith only [hstrip₁] : (0:ℝ) < 1 - β₁)]
        have h1e : 1 - β₁ = Lam1 / L := by rw [hLam1eq, mul_div_cancel_right₀ _ hLpos.ne']
        rw [h1e, div_le_iff₀ hLpos]
        linarith only [hLam1', hδL, hLm1])
      (by
        intro u hdiv hwin
        have h := hmin.hzw_of_window_v2 (s := s₁) (δ := δ) hLposq χ₁ hχ₁ hIm₁ u hdiv hwin
        rwa [hs₁re, hβ₁def])
    rw [← hLdef] at hb
    have hF0 : (∫ t in (0:ℝ)..T.x₀,
        Complex.exp (-(((s₁ - s₁) * (L : ℂ)) * (t : ℂ))) * ((T.f t : ℝ) : ℂ)).re
        = ∫ t in (0:ℝ)..T.x₀, T.f t := by
      have hpt : ∀ t : ℝ,
          Complex.exp (-(((s₁ - s₁) * (L : ℂ)) * (t : ℂ))) * ((T.f t : ℝ) : ℂ)
            = ((T.f t : ℝ) : ℂ) := by intro t; simp
      simp only [hpt]
      rw [intervalIntegral.integral_ofReal, Complex.ofReal_re]
    rw [hF0, hs₁] at hb
    exact hb
  have h2 : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            (χ₂ (n : ZMod q) / (n : ℂ) ^ ((β₁ : ℂ) + (γ₂ : ℂ) * Complex.I)).re
              * T.f (Real.log n / L))
          ≤ -L * (∫ t in (0:ℝ)..T.x₀, Real.exp (-(Lam2 - Lam1) * t) * T.f t)
              + T.f 0 * (cK + ep) * L := by
    have hb := hq₀b (q := q) (s := s₂) (ρ := ((β₂ : ℂ) + (γ₂ : ℂ) * Complex.I)) hq0b χ₂ hχ₂
      (by rw [hs₂re]; exact habsβ₁')
      (by rw [hs₂im, ← hLdef]; linarith only [hγ₂le, hL1, hδ0, hδ1, hγ₂wide, hT1, hLge, hTle])
      (by rw [hs₂re, ← hLdef]; exact hβ₁ge)
      hL52K₂
      (divisor_ne_zero_of_zeroMult_v2 χ₂ hχ₂ hmem₂ (by rw [hρ₂eq]; exact hzm₂))
      (by
        have hc : (1:ℂ) + (s₂.im : ℂ) * Complex.I - ((β₂ : ℂ) + (γ₂ : ℂ) * Complex.I)
            = ((1 - β₂ : ℝ) : ℂ) := by rw [hs₂im]; push_cast; ring
        rw [hc, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by linarith only [hstrip₂] : (0:ℝ) < 1 - β₂)]
        have h1e : 1 - β₂ = Lam2 / L := by rw [hLam2eq, mul_div_cancel_right₀ _ hLpos.ne']
        rw [h1e, div_le_iff₀ hLpos]
        linarith only [hLam2', hδL, hLm2])
      (by
        intro u hdiv hwin
        have h := hmin.hzw_of_window_v2 (s := s₂) (δ := δ) hLposq χ₂ hχ₂ hIm₂ u hdiv hwin
        rwa [hs₂re, hβ₁def])
    rw [← hLdef] at hb
    have hF2 : (∫ t in (0:ℝ)..T.x₀,
        Complex.exp (-(((s₂ - ((β₂ : ℂ) + (γ₂ : ℂ) * Complex.I)) * (L : ℂ)) * (t : ℂ)))
          * ((T.f t : ℝ) : ℂ)).re
        = ∫ t in (0:ℝ)..T.x₀, Real.exp (-(Lam2 - Lam1) * t) * T.f t := by
      have hpt : ∀ t : ℝ,
          Complex.exp (-(((s₂ - ((β₂ : ℂ) + (γ₂ : ℂ) * Complex.I)) * (L : ℂ)) * (t : ℂ)))
            * ((T.f t : ℝ) : ℂ)
            = ((Real.exp (-(Lam2 - Lam1) * t) * T.f t : ℝ) : ℂ) := by
        intro t
        have hexp : -(((s₂ - ((β₂ : ℂ) + (γ₂ : ℂ) * Complex.I)) * (L : ℂ)) * (t : ℂ))
            = ((-(Lam2 - Lam1) * t : ℝ) : ℂ) := by
          rw [hs₂, hLam1eq, hLam2eq]; push_cast; ring
        rw [hexp, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
      simp only [hpt]
      rw [intervalIntegral.integral_ofReal, Complex.ofReal_re]
    rw [hF2, hs₂] at hb
    exact hb
  have h3 : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            ((χ₁ * χ₂) (n : ZMod q) /
              (n : ℂ) ^ ((β₁ : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ)) * Complex.I)).re
              * T.f (Real.log n / L))
          ≤ T.f 0 * (cK + ep) * L := by
    have hb := hq₀a (q := q) (s := s₃) hq0a (χ₁ * χ₂) hneA
      (by rw [hs₃re]; exact habsβ₁')
      (by rw [hs₃im, ← hLdef]
          have h := abs_add_le γ₁ γ₂; linarith only [h, hγ₁le, hγ₂le, hL1, hδ0, hδ1, hγ₂wide, hT1, hLge, hTle])
      (by rw [hs₃re, ← hLdef]; exact hβ₁ge)
      hL52KA
      (by
        intro u hdiv hwin
        have h := hmin.hzw_of_window_v2 (s := s₃) (δ := δ) hLposq (χ₁ * χ₂) hneA hIm₃ u hdiv hwin
        rwa [hs₃re, hβ₁def])
    rw [← hLdef, hs₃] at hb
    exact hb
  have h4 : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            ((χ₁ * χ₂⁻¹) (n : ZMod q) /
              (n : ℂ) ^ ((β₁ : ℂ) + ((γ₁ : ℂ) - (γ₂ : ℂ)) * Complex.I)).re
              * T.f (Real.log n / L))
          ≤ T.f 0 * (cK + ep) * L := by
    have hb := hq₀a (q := q) (s := s₄) hq0a (χ₁ * χ₂⁻¹) hneB
      (by rw [hs₄re]; exact habsβ₁')
      (by rw [hs₄im, ← hLdef]
          have h : |γ₁ - γ₂| ≤ |γ₁| + |γ₂| := by
            simpa [sub_eq_add_neg] using abs_add_le γ₁ (-γ₂)
          linarith only [h, hγ₁le, hγ₂le, hL1, hδ0, hδ1, hγ₂wide, hT1, hLge, hTle])
      (by rw [hs₄re, ← hLdef]; exact hβ₁ge)
      hL52KB
      (by
        intro u hdiv hwin
        have h := hmin.hzw_of_window_v2 (s := s₄) (δ := δ) hLposq (χ₁ * χ₂⁻¹) hneB hIm₄ u hdiv hwin
        rwa [hs₄re, hβ₁def])
    rw [← hLdef, hs₄] at hb
    exact hb
  have key : 0 ≤ (∫ t in (0:ℝ)..T.x₀, Real.exp (Lam1 * t) * T.f t)
      - (∫ t in (0:ℝ)..T.x₀, T.f t)
      - (∫ t in (0:ℝ)..T.x₀, Real.exp (-(Lam2 - Lam1) * t) * T.f t)
      + T.f 0 * (3 * cK + 3 * ep + e0) :=
    lemma6_2_assembly_gen_v2 (q := q) (x₀ := T.x₀) (L := L) (β₁ := β₁) (γ₁ := γ₁) (γ₂ := γ₂)
      (lam₁ := Lam1) (lam₂ := Lam2) (c := cK) (ε₁ := ep) (ε₀ := e0)
      T.f_nonneg T.x₀_pos hLpos T.f_supp χ₁ χ₂ h0 h1 h2 h3 h4
  have hF1 : T.F (-Lam1) = ∫ t in (0:ℝ)..T.x₀, Real.exp (Lam1 * t) * T.f t := by
    rw [TestFn_F_eq_integral T (-Lam1)]
    apply intervalIntegral.integral_congr
    intro t _
    exact congrArg (fun u => Real.exp u * T.f t) (by ring)
  have hF0I : T.F 0 = ∫ t in (0:ℝ)..T.x₀, T.f t := by
    rw [TestFn_F_eq_integral T 0]
    apply intervalIntegral.integral_congr
    intro t _
    simp
  have hF2I : T.F (Lam2 - Lam1)
      = ∫ t in (0:ℝ)..T.x₀, Real.exp (-(Lam2 - Lam1) * t) * T.f t := by
    rw [TestFn_F_eq_integral T (Lam2 - Lam1)]
    apply intervalIntegral.integral_congr
    intro t _
    exact congrArg (fun u => Real.exp u * T.f t) (by ring)
  have key' : 0 ≤ T.F (-Lam1) - T.F 0 - T.F (Lam2 - Lam1) + T.f 0 * (3 * cK + 3 * ep + e0) := by
    rw [← hF1, ← hF0I, ← hF2I] at key
    exact key
  have hcoef : T.f 0 * (3 * cK + 3 * ep + e0) ≤ T.f 0 * (3 * (c + ε)) := by
    apply mul_le_mul_of_nonneg_left _ T.f0_pos.le
    rw [hcK, hep, he0]; linarith only [he0, he00]
  have key'' : 0 ≤ T.F (-Lam1) - T.F 0 - T.F (Lam2 - Lam1) + T.f 0 * (3 * (c + ε)) := by
    linarith only [key', hcoef, key, hF1, hF0I, hF2I]
  rw [hLam1def, hLam2def] at key''
  exact key''
end Work.ZeroFreeTables.HB94
