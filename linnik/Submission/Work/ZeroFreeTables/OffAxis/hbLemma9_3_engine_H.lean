import Mathlib
import Submission.Work.ZeroFreeTables.hbLemma9_3_engine
import Submission.Work.ZeroFreeTables.OffAxis.WideDefs

open scoped BigOperators

namespace Work.ZeroFreeTables.OffAxis

/-- Copy `Submission/Work/ZeroFreeTables/hbLemma9_3_engine.lean` (the proved case `H = 1`, `W = 10`) and replace the height literals by the parameters: `IsMin1WideAt 10 χ₁ ρ₁` + `IsZ χ₁ ρ₁` → `Work.ZeroFreeTables.IsMinWideAt H W χ₁ ρ₁` (API in `Submission/Work/ZeroFreeTables/OffAxis/WideDefs.lean`, window lemmas `IsMinWideAt.hzw`/`.hmax` generalise `IsMin1WideAt.hzw_of_window_v2`/`.hmax_v2`); `IsZ χ₂ ρ₂` → `zeroMult χ₂ ρ₂ ≠ 0`, `χ₂ ≠ 1`, `|ρ₂.im| ≤ H`; the shift bounds `|y| ≤ 3` → `|y| ≤ 3*H` (the shifts are `γ₁, γ₂, γ₁±γ₂, 2γ₂, γ₁±2γ₂`, all `≤ 3H`), so the window heights are `≤ 3H + δ ≤ W` by `hHW`; the derived `|s_k.im| ≤ 10 * Real.log q` from the new hypothesis `H ≤ Real.log q`. Everything else verbatim (`Ksum_principal_le`, `Ksum_le_self_of_L52_phi`, `Ksum_le_single_ne_of_L52_phi`, `c₁ = c + ε/8`, `ε₁ = ε/2`). -/
theorem hbLemma9_3_engine_H (T : Work.ZeroFreeTables.TestFn) (k c ε δ H W : ℝ) (hk : 0 ≤ k)
    (hε : 0 < ε) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hH0 : 0 ≤ H) (hHW : 3 * H + δ ≤ W) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ₁ χ₂ : DirichletCharacter ℂ q) (ρ₁ ρ₂ : ℂ),
      (∀ (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 →
        Commons.NumberTheory.Linnik.L52Hyp χ c ε δ) →
      H ≤ Real.log (q : ℝ) →
      Work.ZeroFreeTables.IsMinWideAt H W χ₁ ρ₁ →
      Work.LinnikContract.zeroMult χ₂ ρ₂ ≠ 0 → χ₂ ≠ 1 → |ρ₂.im| ≤ H →
      χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ → χ₂ ^ 2 ≠ 1 → χ₂ ^ 2 ≠ χ₁ → χ₂ ^ 2 ≠ χ₁⁻¹ →
      Work.LinnikContract.lamOf q ρ₁ ≤ 1 → Work.LinnikContract.lamOf q ρ₂ ≤ 1 →
      0 ≤ (k ^ 2 + 1 / 2) * (T.F (-(Work.LinnikContract.lamOf q ρ₁)) - T.F 0) -
            2 * k * T.F (Work.LinnikContract.lamOf q ρ₂ - Work.LinnikContract.lamOf q ρ₁) +
            T.f 0 * ((k ^ 2 + 4 * k + 3 / 2) * (c + ε)) := by
  obtain ⟨B, hB, hBnd⟩ := T.f_bound
  set c₁ : ℝ := c + ε / 8 with hc₁
  set ε₁ : ℝ := ε / 2 with hε₁
  have hcε : c₁ + ε₁ / 4 = c + ε / 4 := by rw [hc₁, hε₁]; ring
  have hε₁pos : 0 < ε₁ := by rw [hε₁]; linarith only [hε]
  set εp : ℝ := 3 * (k ^ 2 + 4 * k + 3 / 2) * ε / (8 * (k ^ 2 + 1 / 2)) with hεp
  have hεppos : 0 < εp := by
    rw [hεp]
    apply div_pos (by positivity)
    positivity
  have hnum : (k ^ 2 + 1 / 2) * εp + (k ^ 2 + 4 * k + 3 / 2) * (c₁ + ε₁)
      = (k ^ 2 + 4 * k + 3 / 2) * (c + ε) := by
    rw [hεp, hc₁, hε₁]
    have hw : (0:ℝ) < 8 * (k ^ 2 + 1 / 2) := by positivity
    field_simp
    ring
  have hF : ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ (∫ t in (0:ℝ)..T.x₀, Complex.exp (-(z * (t:ℂ))) * ((T.f t : ℝ):ℂ)).re :=
    fun z hz => by rw [← T.Fc_spec]; exact T.Fc_re_nonneg z hz
  obtain ⟨qP, hqP⟩ := Commons.NumberTheory.Linnik.Ksum_principal_le T.x₀ B T.x₀_pos hB
    T.f_cont T.f_supp T.f_diff hBnd hεppos T.f0_pos
  obtain ⟨qS, hqS⟩ := Commons.NumberTheory.Linnik.Ksum_le_self_of_L52_phi T.x₀ B c₁
    T.x₀_pos hB T.f_cont T.f_supp T.f_diff hBnd T.f0_pos hF hε₁pos hδ0 hδ1
  obtain ⟨qN, hqN⟩ := Work.LinnikAreas.DhRepel.Ksum_le_single_ne_of_L52_phi T.x₀ B c₁
    T.x₀_pos hB T.f_cont T.f_supp T.f_diff hBnd T.f0_pos hF hε₁pos hδ0 hδ1
  set R : ℕ := max (max qP qS) qN with hRdef
  set S : ℕ := max 16 (Nat.ceil (Real.exp (1 / δ)) + 1) with hSdef
  refine ⟨max R S + 1, ?_⟩
  intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hL52 hHL hmin hzm₂ hχ₂ hγ₂ hneA hneB hneC hneD hneE hlam₁ hlam₂
  have hRq : R ≤ q := by omega
  have hSq : S ≤ q := by omega
  have hqP'' : qP ≤ q := by
    have : qP ≤ R := by rw [hRdef]; exact le_trans (le_max_left _ _) (le_max_left _ _)
    omega
  have hqS'' : qS ≤ q := by
    have : qS ≤ R := by rw [hRdef]; exact le_trans (le_max_right _ _) (le_max_left _ _)
    omega
  have hqN'' : qN ≤ q := by
    have : qN ≤ R := by rw [hRdef]; exact le_max_right _ _
    omega
  have hq16 : 16 ≤ q := by
    have : 16 ≤ S := by rw [hSdef]; exact le_max_left _ _
    omega
  have hexp : Real.exp (1 / δ) ≤ (q : ℝ) := by
    have h1 : Nat.ceil (Real.exp (1 / δ)) + 1 ≤ S := by rw [hSdef]; exact le_max_right _ _
    have h2 : Real.exp (1 / δ) ≤ ((Nat.ceil (Real.exp (1 / δ)) : ℕ) : ℝ) := Nat.le_ceil _
    have h3 : (Nat.ceil (Real.exp (1 / δ)) + 1) ≤ q := le_trans h1 hSq
    have h4 : ((Nat.ceil (Real.exp (1 / δ)) : ℕ) : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast h3
    linarith only [h2, h4]
  have hq1 : 1 < q := by omega
  have hLpos : 0 < Real.log (q:ℝ) := Real.log_pos (by exact_mod_cast hq1)
  have hlog2 : (0.69 : ℝ) < Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hlog16 : (2.75 : ℝ) < Real.log 16 := by
    rw [show (16:ℝ) = 2^4 by norm_num, Real.log_pow]
    push_cast
    linarith only [hlog2]
  have hL27 : (2.75 : ℝ) < Real.log (q:ℝ) :=
    lt_of_lt_of_le hlog16 (Real.log_le_log (by norm_num) (by exact_mod_cast hq16))
  have hL1 : 1 ≤ Real.log (q:ℝ) := by linarith only [hL27]
  have hLL1 : 1 ≤ Real.log (Real.log (q:ℝ)) := by
    have he1 : Real.exp 1 < 2.75 := by linarith only [Real.exp_one_lt_d9]
    have h : Real.exp 1 ≤ Real.log (q:ℝ) := by linarith only [he1, hL27]
    have := Real.log_le_log (Real.exp_pos 1) h
    rwa [Real.log_exp] at this
  have hsqrt1 : 1 ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) := Real.one_le_sqrt.mpr hLL1
  have hδL : 1 ≤ δ * Real.log (q:ℝ) := by
    have h : 1 / δ ≤ Real.log (q:ℝ) := by
      have := Real.log_le_log (by positivity) hexp
      rwa [Real.log_exp] at this
    have h2 : δ * (1 / δ) = 1 := by field_simp
    calc (1:ℝ) = δ * (1 / δ) := h2.symm
      _ ≤ δ * Real.log (q:ℝ) := mul_le_mul_of_nonneg_left h hδ0.le
  have hzm₁ : Work.LinnikContract.zeroMult χ₁ ρ₁ ≠ 0 := hmin.2.1
  have hχ₁ : χ₁ ≠ 1 := hmin.1
  have hγ₁ : |ρ₁.im| ≤ H := hmin.2.2.1
  have hstrip₁ : 0 < ρ₁.re ∧ ρ₁.re < 1 := zeroMult_re_mem_strip hχ₁ hzm₁
  have hstrip₂ : 0 < ρ₂.re ∧ ρ₂.re < 1 := zeroMult_re_mem_strip hχ₂ hzm₂
  haveI hinst₁ : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
  haveI hinst₂ : NeZero χ₂.conductor := ⟨χ₂.conductor_ne_zero⟩
  have hlam₁nn : 0 ≤ Work.LinnikContract.lamOf q ρ₁ := by
    rw [Work.LinnikContract.lamOf]
    exact mul_nonneg (by linarith only [hstrip₁.2]) hLpos.le
  have hminle : Work.LinnikContract.lamOf q ρ₁ ≤ Work.LinnikContract.lamOf q ρ₂ :=
    hmin.2.2.2 χ₂ ρ₂ hχ₂ hzm₂ (by linarith only [hγ₂, hHW, hH0, hδ0.le])
  have hsqle : |Work.LinnikContract.lamOf q ρ₁| ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) := by
    rw [abs_of_nonneg hlam₁nn]
    exact le_trans hlam₁ hsqrt1
  have hbase₁ : (1 - ρ₁.re) * Real.log (q:ℝ) ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) := by
    have h := hsqle
    rw [Work.LinnikContract.lamOf] at h
    rwa [abs_of_nonneg (mul_nonneg (by linarith only [hstrip₁.2]) hLpos.le)] at h
  have hbase₂ : (1 - ρ₂.re) * Real.log (q:ℝ) ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) := by
    have h2 : 0 ≤ Work.LinnikContract.lamOf q ρ₂ := by
      rw [Work.LinnikContract.lamOf]
      exact mul_nonneg (by linarith only [hstrip₂.2]) hLpos.le
    have h : |Work.LinnikContract.lamOf q ρ₂| ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) := by
      rw [abs_of_nonneg h2]; exact le_trans hlam₂ hsqrt1
    rw [Work.LinnikContract.lamOf] at h
    rwa [abs_of_nonneg (mul_nonneg (by linarith only [hstrip₂.2]) hLpos.le)] at h
  have hreg1 : |ρ₁.re - 1| ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith only [hstrip₁.2]), le_div_iff₀ hLpos]
    exact hbase₁
  have hreg2 : 1 - Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) ≤ ρ₁.re := by
    rw [sub_le_comm, le_div_iff₀ hLpos]
    exact hbase₁
  have hrept : ∀ y : ℝ, (((ρ₁.re : ℂ) + (y : ℂ) * Complex.I).re) = ρ₁.re := fun y => by simp
  have himpt : ∀ y : ℝ, (((ρ₁.re : ℂ) + (y : ℂ) * Complex.I).im) = y := fun y => by simp
  have hR₁ : ‖ρ₁‖ ≤ |ρ₁.im| + 2 := by
    have h1 : ‖ρ₁‖ ≤ |ρ₁.re| + |ρ₁.im| := Complex.norm_le_abs_re_add_abs_im ρ₁
    have h2 : |ρ₁.re| < 1 := by rw [abs_of_pos hstrip₁.1]; exact hstrip₁.2
    linarith only [h1, h2]
  have hR₂ : ‖ρ₂‖ ≤ |ρ₂.im| + 2 := by
    have h1 : ‖ρ₂‖ ≤ |ρ₂.re| + |ρ₂.im| := Complex.norm_le_abs_re_add_abs_im ρ₂
    have h2 : |ρ₂.re| < 1 := by rw [abs_of_pos hstrip₂.1]; exact hstrip₂.2
    linarith only [h1, h2]
  have hdiv₁ : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
      (Metric.closedBall 0 (|ρ₁.im| + 2))) ρ₁ ≠ 0 :=
    divisor_ne_zero_of_zeroMult93 hχ₁ hR₁ hzm₁
  have hdiv₂ : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₂.primitiveCharacter)
      (Metric.closedBall 0 (|ρ₂.im| + 2))) ρ₂ ≠ 0 :=
    divisor_ne_zero_of_zeroMult93 hχ₂ hR₂ hzm₂
  have hzwz : ∀ (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 →
      ∀ (y : ℝ), |y| + δ ≤ W → ∀ u : ℂ, Work.LinnikContract.zeroMult χ u ≠ 0 →
      ‖(1:ℂ) + (y : ℂ) * Complex.I - u‖ ≤ δ →
      u.re ≤ (((ρ₁.re : ℂ) + (y : ℂ) * Complex.I).re) := by
    intro χ inst hχ y hy u hzm hwin
    have hle := hmin.2.2.2 χ u hχ hzm (by
      have h1 : |u.im| ≤ |y| + δ := by
        have hthis := Complex.abs_im_le_norm ((1:ℂ) + (y : ℂ) * Complex.I - u)
        have h2 : (((1:ℂ) + (y : ℂ) * Complex.I - u).im) = y - u.im := by simp
        rw [h2] at hthis
        have h3 : |u.im| ≤ |y| + |y - u.im| := by
          calc |u.im| = |y - (y - u.im)| := by ring_nf
            _ ≤ |y| + |y - u.im| := abs_sub _ _
        linarith only [hthis, h3, hwin]
      linarith only [h1, hy])
    simp only [Work.LinnikContract.lamOf] at hle
    have hle2 : 1 - ρ₁.re ≤ 1 - u.re := le_of_mul_le_mul_right hle hLpos
    have hre : (((ρ₁.re : ℂ) + (y : ℂ) * Complex.I).re) = ρ₁.re := by simp
    rw [hre]
    linarith only [hle2]
  have hwinχ : ∀ (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 → ∀ (y : ℝ),
      |y| + δ ≤ W → ∀ u : ℂ,
      (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|(((ρ₁.re : ℂ) + (y : ℂ) * Complex.I).im)| + 2))) u ≠ 0 →
      ‖(1:ℂ) + ((((ρ₁.re : ℂ) + (y : ℂ) * Complex.I).im) : ℂ) * Complex.I - u‖ ≤ δ →
      u.re ≤ (((ρ₁.re : ℂ) + (y : ℂ) * Complex.I).re) := by
    intro χ inst hχ y hy u hdiv hwin
    rw [himpt y] at hdiv hwin
    exact hzwz χ hχ y hy u (zeroMult_ne_zero_of_divisor93 hχ hdiv) hwin
  have hw₁ : ‖(1:ℂ) + ((ρ₁.im : ℂ)) * Complex.I - ρ₁‖ ≤ δ := by
    have h1 : (1:ℂ) + ((ρ₁.im : ℂ)) * Complex.I - ρ₁ = ((1 - ρ₁.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [h1, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith only [hstrip₁.2])]
    have hlam₁' := hlam₁
    rw [Work.LinnikContract.lamOf] at hlam₁'
    have h2 : (1 - ρ₁.re) * Real.log (q:ℝ) ≤ δ * Real.log (q:ℝ) := by
      linarith only [hlam₁', hδL]
    exact le_of_mul_le_mul_right h2 hLpos
  have hw₂ : ‖(1:ℂ) + ((ρ₂.im : ℂ)) * Complex.I - ρ₂‖ ≤ δ := by
    have h1 : (1:ℂ) + ((ρ₂.im : ℂ)) * Complex.I - ρ₂ = ((1 - ρ₂.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [h1, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith only [hstrip₂.2])]
    have hlam₂' := hlam₂
    rw [Work.LinnikContract.lamOf] at hlam₂'
    have h2 : (1 - ρ₂.re) * Real.log (q:ℝ) ≤ δ * Real.log (q:ℝ) := by
      linarith only [hlam₂', hδL]
    exact le_of_mul_le_mul_right h2 hLpos
  have hρnn₁ : 0 ≤ (∫ t in (0:ℝ)..T.x₀,
      Complex.exp (-(((((ρ₁.re : ℂ) + (ρ₁.im : ℂ) * Complex.I) - ρ₁) * (Real.log (q:ℝ))) * (t:ℂ)))
        * ((T.f t : ℝ):ℂ)).re := by
    have h0 : (((ρ₁.re : ℂ) + (ρ₁.im : ℂ) * Complex.I) - ρ₁) * (Real.log (q:ℝ)) = 0 := by
      have h1 : ((ρ₁.re : ℂ) + (ρ₁.im : ℂ) * Complex.I) - ρ₁ = 0 := by
        apply Complex.ext <;> simp
      rw [h1, zero_mul]
    rw [h0]
    simp only [zero_mul, neg_zero, Complex.exp_zero, one_mul]
    rw [intervalIntegral.integral_ofReal, Complex.ofReal_re]
    exact intervalIntegral.integral_nonneg (le_of_lt T.x₀_pos) (fun t _ => T.f_nonneg t)
  have hpt₂ : ((ρ₁.re : ℂ) + (ρ₂.im : ℂ) * Complex.I) - ρ₂ = ((ρ₁.re - ρ₂.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  have hcast₂ : (((ρ₁.re : ℂ) + (ρ₂.im : ℂ) * Complex.I) - ρ₂) * (Real.log (q:ℝ))
      = ((Work.LinnikContract.lamOf q ρ₂ - Work.LinnikContract.lamOf q ρ₁ : ℝ) : ℂ) := by
    rw [hpt₂, ← Complex.ofReal_mul]
    congr 1
    rw [Work.LinnikContract.lamOf, Work.LinnikContract.lamOf]; ring
  have hρnn₂ : 0 ≤ (∫ t in (0:ℝ)..T.x₀,
      Complex.exp (-(((((ρ₁.re : ℂ) + (ρ₂.im : ℂ) * Complex.I) - ρ₂) * (Real.log (q:ℝ))) * (t:ℂ)))
        * ((T.f t : ℝ):ℂ)).re := by
    rw [hcast₂, TestFn_re_integral_eq_F T (by simp), Complex.ofReal_re]
    exact TestFn_F_nonneg T _
  have hI1 : (∫ t in (0:ℝ)..T.x₀,
      Complex.exp (-(((((ρ₁.re : ℂ) + (ρ₁.im : ℂ) * Complex.I) - ρ₁) * (Real.log (q:ℝ))) * (t:ℂ)))
        * ((T.f t : ℝ):ℂ)).re = T.F 0 := by
    have h0 : (((ρ₁.re : ℂ) + (ρ₁.im : ℂ) * Complex.I) - ρ₁) * (Real.log (q:ℝ)) = 0 := by
      have h1 : ((ρ₁.re : ℂ) + (ρ₁.im : ℂ) * Complex.I) - ρ₁ = 0 := by
        apply Complex.ext <;> simp
      rw [h1, zero_mul]
    rw [h0]
    simp only [zero_mul, neg_zero, Complex.exp_zero, one_mul]
    rw [intervalIntegral.integral_ofReal, Complex.ofReal_re, TestFn_F_eq_integral T 0]
    apply intervalIntegral.integral_congr
    intro t _
    simp
  have hI2 : (∫ t in (0:ℝ)..T.x₀,
      Complex.exp (-(((((ρ₁.re : ℂ) + (ρ₂.im : ℂ) * Complex.I) - ρ₂) * (Real.log (q:ℝ))) * (t:ℂ)))
        * ((T.f t : ℝ):ℂ)).re
      = T.F (Work.LinnikContract.lamOf q ρ₂ - Work.LinnikContract.lamOf q ρ₁) := by
    rw [hcast₂, TestFn_re_integral_eq_F T (by simp), Complex.ofReal_re]
  have hK0 : Ksum q T.f (Real.log (q:ℝ)) (ρ₁.re : ℂ) (1 : DirichletCharacter ℂ q)
      ≤ Real.log (q:ℝ) * T.F (-(Work.LinnikContract.lamOf q ρ₁))
        + T.f 0 * εp * Real.log (q:ℝ) := by
    have h := hqP (q := q) hqP'' (β := ρ₁.re) (lam := Work.LinnikContract.lamOf q ρ₁)
      (by rw [Work.LinnikContract.lamOf]; ring) hreg1
    rw [← TestFn_F_neg_eq_integral T (Work.LinnikContract.lamOf q ρ₁)] at h
    exact h
  have hself : ∀ (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 →
      ∀ (y : ℝ) (s : ℂ), s = ((ρ₁.re : ℂ) + (y : ℂ) * Complex.I) → |y| ≤ 3 * H →
      Ksum q T.f (Real.log (q:ℝ)) s χ ≤ T.f 0 * (c₁ + ε₁) * Real.log (q:ℝ) := by
    intro χ inst hχ y s hs hy
    subst hs
    haveI : NeZero χ.conductor := inst
    refine hqS (q := q) hqS'' χ hχ ?_ ?_ ?_ ?_ ?_
    · rw [hrept y]; exact hreg1
    · rw [himpt y]; linarith only [hy, hHL, hL1]
    · rw [hrept y]; exact hreg2
    · exact L52Hyp_reparam hcε (hL52 χ hχ)
    · exact hwinχ χ hχ y (by linarith only [hy, hHW, hH0, hδ0.le])
  have hy34 : |ρ₁.im + ρ₂.im| ≤ 3 * H := by
    have h : |ρ₁.im + ρ₂.im| ≤ |ρ₁.im| + |ρ₂.im| := abs_add_le _ _
    linarith only [h, hγ₁, hγ₂, hH0]
  have hy56 : |ρ₁.im - ρ₂.im| ≤ 3 * H := by
    have h : |ρ₁.im - ρ₂.im| ≤ |ρ₁.im| + |ρ₂.im| := by
      calc |ρ₁.im - ρ₂.im| = |ρ₁.im + -ρ₂.im| := by ring_nf
        _ ≤ |ρ₁.im| + |-ρ₂.im| := abs_add_le _ _
        _ = |ρ₁.im| + |ρ₂.im| := by rw [abs_neg]
    linarith only [h, hγ₁, hγ₂, hH0]
  have hy5 : |ρ₂.im + ρ₂.im| ≤ 3 * H := by
    have h : |ρ₂.im + ρ₂.im| ≤ |ρ₂.im| + |ρ₂.im| := abs_add_le _ _
    linarith only [h, hγ₂, hH0]
  have hy67 : |ρ₁.im + 2 * ρ₂.im| ≤ 3 * H := by
    have h : |ρ₁.im + 2 * ρ₂.im| ≤ |ρ₁.im| + |2 * ρ₂.im| := abs_add_le _ _
    have h2 : |2 * ρ₂.im| = 2 * |ρ₂.im| := by rw [abs_mul]; norm_num
    linarith only [h, h2, hγ₁, hγ₂, hH0]
  have hy77 : |ρ₁.im - 2 * ρ₂.im| ≤ 3 * H := by
    have h : |ρ₁.im - 2 * ρ₂.im| ≤ |ρ₁.im| + |2 * ρ₂.im| := by
      calc |ρ₁.im - 2 * ρ₂.im| = |ρ₁.im + -(2 * ρ₂.im)| := by ring_nf
        _ ≤ |ρ₁.im| + |-(2 * ρ₂.im)| := abs_add_le _ _
        _ = |ρ₁.im| + |2 * ρ₂.im| := by rw [abs_neg]
    have h2 : |2 * ρ₂.im| = 2 * |ρ₂.im| := by rw [abs_mul]; norm_num
    linarith only [h, h2, hγ₁, hγ₂, hH0]
  have hK1 : Ksum q T.f (Real.log (q:ℝ)) ((ρ₁.re : ℂ) + (ρ₁.im : ℂ) * Complex.I) χ₁
      ≤ -(Real.log (q:ℝ)) * T.F 0 + T.f 0 * (c₁ + ε₁) * Real.log (q:ℝ) := by
    have h := hqN (q := q) hqN'' χ₁ hχ₁
      (s := ((ρ₁.re : ℂ) + (ρ₁.im : ℂ) * Complex.I)) (ρ := ρ₁)
      (by rw [hrept ρ₁.im]; exact hreg1)
      (by rw [himpt ρ₁.im]; linarith only [hγ₁, hHL, hL1])
      (by rw [hrept ρ₁.im]; exact hreg2)
      (L52Hyp_reparam hcε (hL52 χ₁ hχ₁))
      (by rw [himpt ρ₁.im]; exact hdiv₁)
      (by rw [himpt ρ₁.im]; exact hw₁)
      hρnn₁
      (fun u hdiv hwin _ => hwinχ χ₁ hχ₁ ρ₁.im (by linarith only [hγ₁, hHW, hH0, hδ0.le]) u hdiv hwin)
    rw [hI1] at h
    exact h
  have hK2 : Ksum q T.f (Real.log (q:ℝ)) ((ρ₁.re : ℂ) + (ρ₂.im : ℂ) * Complex.I) χ₂
      ≤ -(Real.log (q:ℝ)) * T.F (Work.LinnikContract.lamOf q ρ₂ - Work.LinnikContract.lamOf q ρ₁)
        + T.f 0 * (c₁ + ε₁) * Real.log (q:ℝ) := by
    have h := hqN (q := q) hqN'' χ₂ hχ₂
      (s := ((ρ₁.re : ℂ) + (ρ₂.im : ℂ) * Complex.I)) (ρ := ρ₂)
      (by rw [hrept ρ₂.im]; exact hreg1)
      (by rw [himpt ρ₂.im]; linarith only [hγ₂, hHL, hL1])
      (by rw [hrept ρ₂.im]; exact hreg2)
      (L52Hyp_reparam hcε (hL52 χ₂ hχ₂))
      (by rw [himpt ρ₂.im]; exact hdiv₂)
      (by rw [himpt ρ₂.im]; exact hw₂)
      hρnn₂
      (fun u hdiv hwin _ => hwinχ χ₂ hχ₂ ρ₂.im (by linarith only [hγ₂, hHW, hH0, hδ0.le]) u hdiv hwin)
    rw [hI2] at h
    exact h
  have hK3 : Ksum q T.f (Real.log (q:ℝ))
      ((ρ₁.re : ℂ) + ((ρ₁.im : ℂ) + (ρ₂.im : ℂ)) * Complex.I) (χ₁ * χ₂)
      ≤ T.f 0 * (c₁ + ε₁) * Real.log (q:ℝ) := by
    haveI : NeZero (χ₁ * χ₂).conductor := ⟨(χ₁ * χ₂).conductor_ne_zero⟩
    have hne : χ₁ * χ₂ ≠ 1 := by
      intro hcon
      refine hneB ?_
      have h' := congrArg (fun z => χ₁⁻¹ * z) hcon
      rw [mul_one] at h'
      rw [← h']
      group
    exact hself (χ₁ * χ₂) hne (ρ₁.im + ρ₂.im)
      ((ρ₁.re : ℂ) + ((ρ₁.im : ℂ) + (ρ₂.im : ℂ)) * Complex.I) (by push_cast; ring) hy34
  have hK4 : Ksum q T.f (Real.log (q:ℝ))
      ((ρ₁.re : ℂ) + ((ρ₁.im : ℂ) - (ρ₂.im : ℂ)) * Complex.I) (χ₁ * χ₂⁻¹)
      ≤ T.f 0 * (c₁ + ε₁) * Real.log (q:ℝ) := by
    haveI : NeZero (χ₁ * χ₂⁻¹).conductor := ⟨(χ₁ * χ₂⁻¹).conductor_ne_zero⟩
    have hne : χ₁ * χ₂⁻¹ ≠ 1 := by
      intro hcon
      refine hneA ?_
      have h' := congrArg (fun z => z * χ₂) hcon
      rw [one_mul] at h'
      rw [← h']
      group
    exact hself (χ₁ * χ₂⁻¹) hne (ρ₁.im - ρ₂.im)
      ((ρ₁.re : ℂ) + ((ρ₁.im : ℂ) - (ρ₂.im : ℂ)) * Complex.I) (by push_cast; ring) hy56
  have hK5 : Ksum q T.f (Real.log (q:ℝ))
      ((ρ₁.re : ℂ) + ((ρ₂.im : ℂ) + (ρ₂.im : ℂ)) * Complex.I) (χ₂ ^ 2)
      ≤ T.f 0 * (c₁ + ε₁) * Real.log (q:ℝ) := by
    haveI : NeZero (χ₂ ^ 2).conductor := ⟨(χ₂ ^ 2).conductor_ne_zero⟩
    exact hself (χ₂ ^ 2) hneC (ρ₂.im + ρ₂.im)
      ((ρ₁.re : ℂ) + ((ρ₂.im : ℂ) + (ρ₂.im : ℂ)) * Complex.I) (by push_cast; ring) hy5
  have hK6 : Ksum q T.f (Real.log (q:ℝ))
      ((ρ₁.re : ℂ) + ((ρ₁.im : ℂ) + 2 * (ρ₂.im : ℂ)) * Complex.I) (χ₁ * χ₂ ^ 2)
      ≤ T.f 0 * (c₁ + ε₁) * Real.log (q:ℝ) := by
    haveI : NeZero (χ₁ * χ₂ ^ 2).conductor := ⟨(χ₁ * χ₂ ^ 2).conductor_ne_zero⟩
    have hne : χ₁ * χ₂ ^ 2 ≠ 1 := by
      intro hcon
      refine hneE ?_
      have h' := congrArg (fun z => χ₁⁻¹ * z) hcon
      rw [mul_one] at h'
      rw [← h']
      group
    exact hself (χ₁ * χ₂ ^ 2) hne (ρ₁.im + 2 * ρ₂.im)
      ((ρ₁.re : ℂ) + ((ρ₁.im : ℂ) + 2 * (ρ₂.im : ℂ)) * Complex.I) (by push_cast; ring) hy67
  have hK7 : Ksum q T.f (Real.log (q:ℝ))
      ((ρ₁.re : ℂ) + ((ρ₁.im : ℂ) - 2 * (ρ₂.im : ℂ)) * Complex.I) (χ₁ * ((χ₂⁻¹) ^ 2))
      ≤ T.f 0 * (c₁ + ε₁) * Real.log (q:ℝ) := by
    haveI : NeZero (χ₁ * ((χ₂⁻¹) ^ 2)).conductor := ⟨(χ₁ * ((χ₂⁻¹) ^ 2)).conductor_ne_zero⟩
    have hne : χ₁ * ((χ₂⁻¹) ^ 2) ≠ 1 := by
      intro hcon
      refine hneD ?_
      have h' := congrArg (fun z => z * χ₂ ^ 2) hcon
      rw [one_mul] at h'
      rw [← h']
      group
    exact hself (χ₁ * ((χ₂⁻¹) ^ 2)) hne (ρ₁.im - 2 * ρ₂.im)
      ((ρ₁.re : ℂ) + ((ρ₁.im : ℂ) - 2 * (ρ₂.im : ℂ)) * Complex.I) (by push_cast; ring) hy77
  -- the positivity
  have hpos := ksum_positivity_L93 (q := q) T.f_nonneg T.x₀_pos hLpos hk T.f_supp χ₁ χ₂
    (L := Real.log (q:ℝ)) (β := ρ₁.re) (γ₁ := ρ₁.im) (γ₂ := ρ₂.im) (k := k)
  -- weighted bounds
  have hw0 : 0 ≤ k ^ 2 + 1 / 2 := by positivity
  have h2k : 0 ≤ 2 * k := by linarith only [hk]
  have hk0 : 0 ≤ k := hk
  have h12 : 0 ≤ (1/2 : ℝ) := by norm_num
  have h14 : 0 ≤ (1/4 : ℝ) := by norm_num
  have hK0w := mul_le_mul_of_nonneg_left hK0 hw0
  have hK1w := mul_le_mul_of_nonneg_left hK1 hw0
  have hK2w := mul_le_mul_of_nonneg_left hK2 h2k
  have hK3w := mul_le_mul_of_nonneg_left hK3 hk0
  have hK4w := mul_le_mul_of_nonneg_left hK4 hk0
  have hK5w := mul_le_mul_of_nonneg_left hK5 h12
  have hK6w := mul_le_mul_of_nonneg_left hK6 h14
  have hK7w := mul_le_mul_of_nonneg_left hK7 h14
  have hcomb : 0 ≤ (k ^ 2 + 1 / 2) *
        ((Real.log (q:ℝ) * T.F (-(Work.LinnikContract.lamOf q ρ₁))
            + T.f 0 * εp * Real.log (q:ℝ))
          + (-(Real.log (q:ℝ)) * T.F 0 + T.f 0 * (c₁ + ε₁) * Real.log (q:ℝ)))
      + 2 * k * (-(Real.log (q:ℝ)) * T.F (Work.LinnikContract.lamOf q ρ₂ - Work.LinnikContract.lamOf q ρ₁)
          + T.f 0 * (c₁ + ε₁) * Real.log (q:ℝ))
      + k * (T.f 0 * (c₁ + ε₁) * Real.log (q:ℝ))
      + k * (T.f 0 * (c₁ + ε₁) * Real.log (q:ℝ))
      + (1/2) * (T.f 0 * (c₁ + ε₁) * Real.log (q:ℝ))
      + (1/4) * (T.f 0 * (c₁ + ε₁) * Real.log (q:ℝ))
      + (1/4) * (T.f 0 * (c₁ + ε₁) * Real.log (q:ℝ)) := by
    linarith only [hpos, hK0w, hK1w, hK2w, hK3w, hK4w, hK5w, hK6w, hK7w]
  have hkey : Real.log (q:ℝ) * ((k ^ 2 + 1 / 2) * (T.F (-(Work.LinnikContract.lamOf q ρ₁)) - T.F 0)
        - 2 * k * T.F (Work.LinnikContract.lamOf q ρ₂ - Work.LinnikContract.lamOf q ρ₁)
        + T.f 0 * ((k ^ 2 + 4 * k + 3 / 2) * (c + ε)))
      = (k ^ 2 + 1 / 2) *
        ((Real.log (q:ℝ) * T.F (-(Work.LinnikContract.lamOf q ρ₁))
            + T.f 0 * εp * Real.log (q:ℝ))
          + (-(Real.log (q:ℝ)) * T.F 0 + T.f 0 * (c₁ + ε₁) * Real.log (q:ℝ)))
      + 2 * k * (-(Real.log (q:ℝ)) * T.F (Work.LinnikContract.lamOf q ρ₂ - Work.LinnikContract.lamOf q ρ₁)
          + T.f 0 * (c₁ + ε₁) * Real.log (q:ℝ))
      + k * (T.f 0 * (c₁ + ε₁) * Real.log (q:ℝ))
      + k * (T.f 0 * (c₁ + ε₁) * Real.log (q:ℝ))
      + (1/2) * (T.f 0 * (c₁ + ε₁) * Real.log (q:ℝ))
      + (1/4) * (T.f 0 * (c₁ + ε₁) * Real.log (q:ℝ))
      + (1/4) * (T.f 0 * (c₁ + ε₁) * Real.log (q:ℝ)) := by
    rw [← hnum]
    ring
  rw [← hkey] at hcomb
  exact (mul_nonneg_iff_of_pos_left hLpos).mp hcomb

end Work.ZeroFreeTables.OffAxis
