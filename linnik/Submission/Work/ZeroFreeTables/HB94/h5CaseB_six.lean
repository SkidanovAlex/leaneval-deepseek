import Mathlib
import Submission.Work.ZeroFreeTables.HB94.Ksum_single_ne
import Submission.Work.ZeroFreeTables.HB94.Lam2GeWide
import Submission.Work.ZeroFreeTables.HB94.HB94Aux
import Submission.Work.ZeroFreeTables.HB95plus.Main
import Submission.Work.ZeroFreeTables.HB95plus.tf72_numeric_inputs
import Submission.Work.ZeroFreeTables.HBProps

set_option maxHeartbeats 4000000

namespace Work.ZeroFreeTables.HB94

open Work.ZeroFreeTables

/-- `χ ^ 2 ≠ 1` when `6 ≤ orderOf χ`. -/
theorem sq_ne_one_of_orderOf_ge_six {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (h : 6 ≤ orderOf χ) : χ ^ 2 ≠ 1 := by
  intro h1
  have hdvd : orderOf χ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h1
  have hle : orderOf χ ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-- For `2 ≤ k ≤ 4` and `6 ≤ orderOf χ`, the character `χ ^ k` is neither principal, nor `χ`,
nor `χ⁻¹`. -/
theorem pow_ne_one_self_inv_of_orderOf_ge_six {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    {k : ℕ} (h : 6 ≤ orderOf χ) (hk2 : 2 ≤ k) (hk4 : k ≤ 4) :
    χ ^ k ≠ 1 ∧ χ ^ k ≠ χ ∧ χ ^ k ≠ χ⁻¹ := by
  have hlt : ∀ n : ℕ, 0 < n → n < orderOf χ → χ ^ n ≠ 1 := by
    intro n hnpos hn h1
    have hdvd : orderOf χ ∣ n := orderOf_dvd_iff_pow_eq_one.mpr h1
    have hle : orderOf χ ≤ n := Nat.le_of_dvd hnpos hdvd
    omega
  refine ⟨hlt k (by omega) (by omega), ?_, ?_⟩
  · intro h1
    have h3 : χ ^ (k - 1) * χ = χ ^ k := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ k)]
    have h5 : χ ^ (k - 1) = 1 := mul_right_cancel (by rw [h3, h1, one_mul])
    exact hlt (k - 1) (by omega) (by omega) h5
  · intro h1
    have h3 : χ ^ k * χ = χ ^ (k + 1) := by rw [pow_succ]
    have h4 : χ ^ k * χ = 1 := by rw [h1, inv_mul_cancel]
    have h5 : χ ^ (k + 1) = 1 := by rw [← h3]; exact h4
    exact hlt (k + 1) (by omega) (by omega) h5

/-- **Case B of HB Lemma 9.5's `h ≥ 5` regime** (HB, p. 57, the argument following (9.16)),
in the form in which the order-`≥ 6` case is needed.  Let `L = log q`, `λ₁ = lamOf q ρ₁`,
`γ₁ = ρ₁.im` and `λ* := λ₁ + 472/1000`.  For `6 ≤ orderOf χ₁` the four characters `χ₁ᵏ`
(`k = 1,2,3,4`) are non-principal and distinct from `χ₁, χ₁⁻¹`, so HB's pointwise inequality (9.15)
gives `0 ≤ Σ_{k≤4} c95 k · K(β + ikγ₁, χ₁ᵏ)` with `β = 1 - λ*/L`
(`Work.ZeroFreeTables.ksum_trigPoly_nonneg`, `c95_hP`).  Since `λ* = λ₁ + 472/1000 ≤ 82/100` and
`λ* ≤ λ₀` (`hLam0`) resp. `λ* ≤ λ₂` (`hLam2`), the five `K`-sums are bounded by
`Ksum_principal_le` (principal term `≤ L·F(-λ*) + f(0)εL`), `Ksum_le_single_of_L52_phi_ne`
(`χ₁`, retaining `ρ₁`, which lies in the window since `‖(1:ℂ) + iγ₁ − ρ₁‖ = λ₁/L ≤ δ` for large
`q`; this is the retained-zero variant of HB (6.7) proved in
`Submission/Work/ZeroFreeTables/HB94/Ksum_single_ne.lean`, whose extra hypothesis is
`0 ≤ Re F((s-ρ₁)L) = ∫ e^{(λ*-λ₁)t} f ≥ 0`), and `Ksum_le_self_of_L52_phi` for `χ₁², χ₁³, χ₁⁴`
(all their window zeros have `|Im| ≤ 4 + δ ≤ 8`, so `hLam2` gives `λ ≥ λ*`).  With the test
function `tf72T (3/4)` (`F 0 = 8/9`, `f 0 = 4/5`, `x₀ = 8/3`, support `[0,8/3]`) the combination is
`0 ≤ L·[14379·∫e^{λ*t}f − 24480·∫e^{(λ*−λ₁)t}f + (4/5)(14379·ε + 46630·(1/6+ε))]`, whose bracket is
negative: `∫e^{λ*t}f ≤ ∫e^{0.82t}f ≤ 1706/1000` and `∫e^{(λ*−λ₁)t}f ≥ ∫e^{0.472t}f ≥ 1262/1000`
(`Work.ZeroFreeTables.TfNumericInputs` / `HB95plus.tf72_numeric_inputs`) plus
`Work.ZeroFreeTables.caseB_arith`.  Contradiction with `L > 0`.  The file
`Submission/Work/ZeroFreeTables/HB94/h5CaseA.lean` (proved) is the template for the (★)
combination, the thresholds and the window bookkeeping; the arithmetic here uses
`caseB_arith` instead of `caseA_arith`. -/
theorem h5CaseB_six (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (q₁ : ℕ)
    (hL6 : ∀ q : ℕ, q₁ ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
      χ ≠ 1 → Commons.NumberTheory.Linnik.L52Hyp χ ((1:ℝ)/6) (1/1000) δ)
    (hLam0 : ∃ q₂ : ℕ, ∀ q : ℕ, q₂ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 →
      Work.LinnikContract.lamOf q ρ₁ ≤ (348:ℝ)/1000 →
      ∀ ρ : ℂ, Work.LinnikContract.zeroMult χ₁ ρ ≠ 0 → |ρ.im| ≤ 2 → ρ ≠ ρ₁ →
        (82:ℝ)/100 ≤ Work.LinnikContract.lamOf q ρ)
    (hLam2 : ∃ q₃ : ℕ, ∀ q : ℕ, q₃ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ →
      Work.LinnikContract.lamOf q ρ₁ ≤ (348:ℝ)/1000 →
      ∀ (χ : DirichletCharacter ℂ q) (u : ℂ), Work.LinnikContract.zeroMult χ u ≠ 0 →
        χ ≠ 1 → χ ≠ χ₁ → χ ≠ χ₁⁻¹ → |u.im| ≤ 8 →
          Work.LinnikContract.lamOf q ρ₁ + 472/1000 ≤ Work.LinnikContract.lamOf q u) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → 6 ≤ orderOf χ₁ →
      Work.LinnikContract.lamOf q ρ₁ ≤ (348:ℝ)/1000 → False := by
  classical
  obtain ⟨-, hnum2, hnum3, -, -⟩ := Work.ZeroFreeTables.HB95plus.tf72_numeric_inputs
  obtain ⟨q₂, hLam0'⟩ := hLam0
  obtain ⟨q₃, hLam2'⟩ := hLam2
  -- the test function `f = tf72f (3/4)`, supported on `[0, 8/3]`
  set f : ℝ → ℝ := tf72f ((3:ℝ)/4) with hfdef
  have h34 : (0:ℝ) < (3:ℝ)/4 := by norm_num
  have hcut : (2:ℝ) / ((3:ℝ)/4) = (8:ℝ)/3 := by norm_num
  have hfcont : ContinuousOn f (Set.Ici 0) := by rw [hfdef]; exact tf72f_cont _ h34
  have hfsupp : ∀ t : ℝ, (8:ℝ)/3 ≤ t → f t = 0 := by
    intro t ht
    have ht' : (2:ℝ) / ((3:ℝ)/4) ≤ t := by linarith [hcut, ht]
    rw [hfdef]
    exact tf72f_supp _ h34 t ht'
  have hfdiff : ContDiffOn ℝ 2 f (Set.Ioo 0 ((8:ℝ)/3)) := by
    rw [hfdef, ← hcut]
    exact tf72f_diff _ h34
  obtain ⟨B, hB0, hBnd⟩ := tf72f_bound ((3:ℝ)/4) h34
  have hfB : ∀ t ∈ Set.Ioo (0:ℝ) ((8:ℝ)/3), ‖iteratedDeriv 2 f t‖ ≤ B := by
    intro t ht
    have ht' : t ∈ Set.Ioo (0:ℝ) ((2:ℝ) / ((3:ℝ)/4)) := by rw [hcut]; exact ht
    rw [hfdef]
    exact hBnd t ht'
  have hfnn : ∀ t : ℝ, 0 ≤ f t := by rw [hfdef]; exact tf72f_nonneg _ h34
  have hf0pos : 0 < f 0 := by rw [hfdef, tf72f_at_zero _ h34]; norm_num
  have hf0val : f 0 = 4/5 := by rw [hfdef, tf72f_at_zero _ h34]; norm_num
  have hFc : ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ (∫ t in (0:ℝ)..((8:ℝ)/3), Complex.exp (-(z * (t:ℂ))) * ((f t : ℝ):ℂ)).re := by
    intro z hz
    have h := tf72Fc_re_nonneg ((3:ℝ)/4) h34 z hz
    rw [← hcut, hfdef]
    exact h
  -- the three `K`-sum bounds
  obtain ⟨qP, hKP⟩ := Commons.NumberTheory.Linnik.Ksum_principal_le ((8:ℝ)/3) B (by norm_num) hB0
    (f := f) hfcont hfsupp hfdiff hfB (ε := (1:ℝ)/1000) (by norm_num) hf0pos
  obtain ⟨qS, hKS⟩ := Work.ZeroFreeTables.HB94.Ksum_le_single_of_L52_phi_ne ((8:ℝ)/3) B ((1:ℝ)/6)
    (by norm_num) hB0 (f := f) hfcont hfsupp hfdiff hfB hf0pos hFc
    (ε := (1:ℝ)/1000) (by norm_num) hδ0 hδ1
  obtain ⟨qT, hKT⟩ := Commons.NumberTheory.Linnik.Ksum_le_self_of_L52_phi ((8:ℝ)/3) B ((1:ℝ)/6)
    (by norm_num) hB0 (f := f) hfcont hfsupp hfdiff hfB hf0pos hFc
    (ε := (1:ℝ)/1000) (by norm_num) hδ0 hδ1
  refine ⟨q₁ + qP + qS + qT + q₂ + q₃ + 1000000
    + (Nat.ceil (Real.exp (820 / (1000 * δ))) + 1), ?_⟩
  intro q hq hqne χ₁ ρ₁ hm hord hsmall
  have hq1 : q₁ ≤ q := by omega
  have hqP : qP ≤ q := by omega
  have hqS : qS ≤ q := by omega
  have hqT : qT ≤ q := by omega
  have hq₂ : q₂ ≤ q := by omega
  have hq₃ : q₃ ≤ q := by omega
  have hqM : 1000000 ≤ q := by omega
  have hqδ : Nat.ceil (Real.exp (820 / (1000 * δ))) + 1 ≤ q := by omega
  haveI : NeZero q := hqne
  have hq2 : 2 ≤ q := by omega
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hlogq : 0 < Real.log (q:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hL0 : Real.log (q:ℝ) ≠ 0 := ne_of_gt hlogq
  -- `log q ≥ 6`
  have hlog6 : (6:ℝ) ≤ Real.log (q:ℝ) := by
    have h6 : (1000000:ℝ) ≤ (q:ℝ) := by exact_mod_cast hqM
    have h7 := Real.log_le_log (by norm_num : (0:ℝ) < 1000000) h6
    have h8 : Real.log (1000000:ℝ) = 6 * Real.log 10 := by
      rw [show (1000000:ℝ) = 10^6 by norm_num, Real.log_pow]; norm_num
    have h9 : (2:ℝ) ≤ Real.log 10 := by
      rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 10)]
      have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
    rw [h8] at h7
    linarith
  -- `δ log q ≥ 0.82`
  have hδlog : (820:ℝ)/1000 ≤ δ * Real.log (q:ℝ) := by
    have h3 : Real.exp (820 / (1000 * δ)) ≤ (q:ℝ) := by
      have h1 : Real.exp (820 / (1000 * δ)) ≤ (Nat.ceil (Real.exp (820 / (1000 * δ))) : ℝ) :=
        Nat.le_ceil _
      have h2 : (Nat.ceil (Real.exp (820 / (1000 * δ))) : ℝ) ≤ (q:ℝ) := by
        exact_mod_cast (by omega : Nat.ceil (Real.exp (820 / (1000 * δ))) ≤ q)
      linarith
    have h4 : 820 / (1000 * δ) ≤ Real.log (q:ℝ) := by
      rw [Real.le_log_iff_exp_le hqpos]
      exact h3
    have h820 : δ * (820 / (1000 * δ)) = (820:ℝ)/1000 := by
      rw [mul_div_assoc', mul_comm δ 820, mul_div_mul_right _ _ hδ0.ne']
    calc (820:ℝ)/1000 = δ * (820 / (1000 * δ)) := h820.symm
      _ ≤ δ * Real.log (q:ℝ) := mul_le_mul_of_nonneg_left h4 hδ0.le
  have hχ1 : χ₁ ≠ 1 := hm.1.1.1
  have hzm1 : Work.LinnikContract.zeroMult χ₁ ρ₁ ≠ 0 := hm.1.1.2.1
  have hν1 : |ρ₁.im| ≤ 1 := hm.1.1.2.2
  have hlam_nn : 0 ≤ Work.LinnikContract.lamOf q ρ₁ :=
    Work.LinnikContract.API.isZ_lambda_nonneg (χ := χ₁) (ρ := ρ₁) hq2 hm.1.1
  have hχ1sq : χ₁ ^ 2 ≠ 1 := sq_ne_one_of_orderOf_ge_six hord
  set lam1 : ℝ := Work.LinnikContract.lamOf q ρ₁ with hlam1def
  set lamS : ℝ := lam1 + 472/1000 with hlamSdef
  have hlamS_le : lamS ≤ (82:ℝ)/100 := by rw [hlamSdef, hlam1def]; linarith
  have hlamS_nn : 0 ≤ lamS := by rw [hlamSdef, hlam1def]; linarith
  have hδlog1 : lam1 ≤ δ * Real.log (q:ℝ) := by
    rw [hlam1def]; linarith
  have hslice : 1 - ρ₁.re = lam1 / Real.log (q:ℝ) := by
    have h2 : lam1 = (1 - ρ₁.re) * Real.log (q:ℝ) := by rw [hlam1def]; rfl
    rw [h2, mul_div_cancel_right₀ _ hL0]
  have hnn1 : 0 ≤ 1 - ρ₁.re := by
    rw [hslice]; exact div_nonneg (by rw [hlam1def]; exact hlam_nn) hlogq.le
  -- the base point `β = 1 - λ*/L`
  set β : ℝ := 1 - lamS / Real.log (q:ℝ) with hβdef
  have hβeq : lamS = Real.log (q:ℝ) * (1 - β) := by
    have h2 : 1 - β = lamS / Real.log (q:ℝ) := by rw [hβdef]; ring
    rw [h2, mul_div_cancel₀ _ hL0]
  have hsqrtge : (82:ℝ)/100 ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) := by
    have h4 : (82:ℝ)/100 ≤ Real.log (Real.log (q:ℝ)) := by
      have h5 : Real.log 6 ≤ Real.log (Real.log (q:ℝ)) := Real.log_le_log (by norm_num) hlog6
      have h6 : (82:ℝ)/100 ≤ Real.log 6 := by
        rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 6)]
        have h7 : Real.exp ((82:ℝ)/100) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
        linarith [Real.exp_one_lt_three, h7]
      linarith
    calc (82:ℝ)/100 ≤ Real.sqrt ((82:ℝ)/100) := by
          rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
      _ ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) := Real.sqrt_le_sqrt h4
  have hβre : |β - 1| ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) := by
    have h1 : |β - 1| = lamS / Real.log (q:ℝ) := by
      have h2 : β - 1 = -(lamS / Real.log (q:ℝ)) := by rw [hβdef]; ring
      rw [h2, abs_neg, abs_of_nonneg (div_nonneg hlamS_nn hlogq.le)]
    rw [h1]
    exact div_le_div_of_nonneg_right (le_trans hlamS_le hsqrtge) hlogq.le
  have hslor : 1 - Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) ≤ β := by
    have h2 : lamS / Real.log (q:ℝ)
        ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) :=
      div_le_div_of_nonneg_right (le_trans hlamS_le hsqrtge) hlogq.le
    rw [hβdef]; linarith
  -- `ρ₁` lies in the critical strip, in the ball, and in the window of `s₁`
  haveI hc1 : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
  have hstrip1 : 0 < ρ₁.re ∧ ρ₁.re < 1 :=
    Commons.NumberTheory.Linnik.completedL_zero_strip χ₁.primitiveCharacter
      (primitive_ne_one_aux χ₁ hχ1) (DirichletCharacter.primitiveCharacter_isPrimitive χ₁)
      (apply_eq_zero_of_analyticOrderNatAt_ne_zero
        (by simpa only [Work.LinnikContract.zeroMult] using hzm1))
  have hmem1 : ρ₁ ∈ Metric.closedBall (0:ℂ) (|ρ₁.im| + 2) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    have hre : |ρ₁.re| ≤ 1 := by rw [abs_of_pos hstrip1.1]; exact hstrip1.2.le
    calc ‖ρ₁‖ ≤ |ρ₁.re| + |ρ₁.im| := Complex.norm_le_abs_re_add_abs_im ρ₁
      _ ≤ |ρ₁.im| + 1 := by linarith
      _ ≤ |ρ₁.im| + 2 := by linarith
  have hwinpred : ‖(1:ℂ) + (ρ₁.im : ℂ) * Complex.I - ρ₁‖ ≤ δ := by
    have h1 : (1:ℂ) + (ρ₁.im : ℂ) * Complex.I - ρ₁ = ((1 - ρ₁.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn1]
    rw [hslice, div_le_iff₀ hlogq]
    exact hδlog1
  have hwin1 : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
      (Metric.closedBall 0 (|ρ₁.im| + 2))) ρ₁ ≠ 0 :=
    divisor_ne_zero_of_zeroMult_aux χ₁ hχ1 hmem1 hzm1
  have hL52_1 : Commons.NumberTheory.Linnik.L52Hyp χ₁ ((1:ℝ)/6) (1/1000) δ :=
    hL6 q hq1 χ₁ hχ1
  set s1 : ℂ := (β:ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I with hs1def
  have hs1im : s1.im = ρ₁.im := by rw [hs1def]; simp
  have hs1re : s1.re = β := by rw [hs1def]; simp
  have hsim10 : |s1.im| ≤ 10 * Real.log (q:ℝ) := by
    rw [hs1im]; nlinarith [hν1, hlog6]
  -- every other window zero of `χ₁` satisfies `hLam0`
  have hzw1 : ∀ u : ℂ, (MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
      (Metric.closedBall 0 (|s1.im| + 2))) u ≠ 0 →
      ‖(1:ℂ) + (s1.im : ℂ) * Complex.I - u‖ ≤ δ → u ≠ ρ₁ → u.re ≤ s1.re := by
    intro u hdiv hwin hne
    have hzm : Work.LinnikContract.zeroMult χ₁ u ≠ 0 :=
      zeroMult_ne_zero_of_divisor_v2 χ₁ hχ1 hdiv
    have huim2 : |u.im| ≤ 2 := by
      have h3 := Complex.abs_im_le_norm ((1:ℂ) + (s1.im : ℂ) * Complex.I - u)
      have h3b : (((1:ℂ) + (s1.im : ℂ) * Complex.I - u)).im = s1.im - u.im := by simp
      rw [h3b, abs_sub_comm] at h3
      have h4 : |u.im| ≤ |u.im - s1.im| + |s1.im| := by
        calc |u.im| = |(u.im - s1.im) + s1.im| := by ring_nf
          _ ≤ |u.im - s1.im| + |s1.im| := abs_add_le _ _
      have h5 : |s1.im| ≤ 1 := by rw [hs1im]; exact hν1
      linarith [h3, h4, h5, hδ1]
    have h82 : (82:ℝ)/100 ≤ Work.LinnikContract.lamOf q u :=
      hLam0' q hq₂ χ₁ ρ₁ hm hχ1sq hsmall u hzm huim2 hne
    have hle : lamS ≤ Work.LinnikContract.lamOf q u := le_trans hlamS_le h82
    rw [hs1re, hβdef]
    exact re_le_one_sub_of_lam_le hlogq hle
  -- the two integrals appearing in the bounds
  set Ia : ℝ := ∫ t in (0:ℝ)..((8:ℝ)/3), Real.exp (lamS * t) * f t with hIadef
  set Ib : ℝ := ∫ t in (0:ℝ)..((8:ℝ)/3), Real.exp (((472:ℝ)/1000) * t) * f t with hIbdef
  have hIa_le : Ia ≤ (1706:ℝ)/1000 := by
    rw [hIadef]
    have hnum2' : (∫ t in (0:ℝ)..((8:ℝ)/3), Real.exp (((82:ℝ)/100) * t) * f t)
        ≤ (1706:ℝ)/1000 := by rw [hfdef]; exact hnum2
    have hint1 : IntervalIntegrable (fun t : ℝ => Real.exp (lamS * t) * f t) MeasureTheory.volume
        (0:ℝ) ((8:ℝ)/3) := by
      refine ContinuousOn.intervalIntegrable_of_Icc (by norm_num : (0:ℝ) ≤ (8:ℝ)/3) ?_
      exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul
        (hfcont.mono (fun t ht => ht.1))
    have hint2 : IntervalIntegrable (fun t : ℝ => Real.exp (((82:ℝ)/100) * t) * f t)
        MeasureTheory.volume (0:ℝ) ((8:ℝ)/3) := by
      refine ContinuousOn.intervalIntegrable_of_Icc (by norm_num : (0:ℝ) ≤ (8:ℝ)/3) ?_
      exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul
        (hfcont.mono (fun t ht => ht.1))
    have hle : ∀ t ∈ Set.Icc (0:ℝ) ((8:ℝ)/3),
        Real.exp (lamS * t) * f t ≤ Real.exp (((82:ℝ)/100) * t) * f t := by
      intro t ht
      exact mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hlamS_le ht.1)) (hfnn t)
    exact le_trans (intervalIntegral.integral_mono_on (by norm_num) hint1 hint2 hle) hnum2'
  have hIb_ge : (1262:ℝ)/1000 ≤ Ib := by
    rw [hIbdef, hfdef]
    exact hnum3
  have hIb_eq : (∫ t in (0:ℝ)..((8:ℝ)/3), Real.exp ((lamS - lam1) * t) * f t) = Ib := by
    rw [hIbdef]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    have h2 : lamS - lam1 = (472:ℝ)/1000 := by rw [hlamSdef]; ring
    rw [h2]
  have hB_ge : 0 ≤ (∫ t in (0:ℝ)..((8:ℝ)/3), Real.exp ((lamS - lam1) * t) * f t) := by
    rw [hIb_eq]
    linarith [hIb_ge]
  have hBint_pt : (∫ t in (0:ℝ)..((8:ℝ)/3),
        Complex.exp (-(((s1 - ρ₁) * (Real.log (q:ℝ))) * (t:ℂ))) * ((f t : ℝ):ℂ)).re
      = ∫ t in (0:ℝ)..((8:ℝ)/3), Real.exp ((lamS - lam1) * t) * f t := by
    have hsub : s1 - ρ₁ = ((β - ρ₁.re : ℝ) : ℂ) := by
      apply Complex.ext
      · simp [Complex.sub_re, hs1re]
      · simp [Complex.sub_im, hs1im]
    rw [hsub]
    have hβρ : β - ρ₁.re = (lam1 - lamS) / Real.log (q:ℝ) := by
      have h4 : ρ₁.re = 1 - lam1 / Real.log (q:ℝ) := by linarith [hslice]
      rw [hβdef, h4]; ring
    rw [hβρ]
    have hcast : ((↑(((lam1 - lamS) / Real.log (q:ℝ)) : ℝ) : ℂ) * (Real.log (q:ℝ) : ℂ))
        = ((lam1 - lamS : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, div_mul_cancel₀ _ hL0]
    rw [hcast]
    have h1 : ∀ t : ℝ, Complex.exp (-((((lam1 - lamS : ℝ)) : ℂ) * (t:ℂ))) * ((f t : ℝ):ℂ)
        = ((Real.exp ((lamS - lam1) * t) * f t : ℝ) : ℂ) := by
      intro t
      have h2 : -((((lam1 - lamS : ℝ)) : ℂ) * (t:ℂ)) = (((lamS - lam1) * t : ℝ) : ℂ) := by
        push_cast; ring
      rw [h2, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
    rw [intervalIntegral.integral_congr (fun t _ => h1 t), intervalIntegral.integral_ofReal,
      Complex.ofReal_re]
  have hb0 : Ksum q f (Real.log (q:ℝ)) ((β:ℂ)) 1
      ≤ Real.log (q:ℝ) * Ia + f 0 * ((1:ℝ)/1000) * Real.log (q:ℝ) := by
    have h := hKP (q := q) hqP (β := β) (lam := lamS) hβeq hβre
    rw [← Ksum_def_aux] at h
    rw [hIadef]
    exact h
  have hb1 : Ksum q f (Real.log (q:ℝ)) s1 χ₁
      ≤ -(Real.log (q:ℝ)) * Ib + f 0 * ((1:ℝ)/6 + (1:ℝ)/1000) * Real.log (q:ℝ) := by
    have h := hKS (q := q) hqS χ₁ hχ1 (s := s1) (ρ := ρ₁)
      (by rw [hs1re]; exact hβre)
      hsim10
      (by rw [hs1re]; exact hslor)
      hL52_1
      (by rw [hs1im]; exact hwin1)
      (by rw [hs1im]; exact hwinpred)
      (by rw [hBint_pt]; linarith [hB_ge])
      hzw1
    rw [← Ksum_def_aux] at h
    rw [hBint_pt] at h
    rw [hIb_eq] at h
    exact h
  have hbk : ∀ k : ℕ, 2 ≤ k → k ≤ 4 →
      Ksum q f (Real.log (q:ℝ)) ((β:ℂ) + ((k:ℝ):ℂ) * (ρ₁.im:ℂ) * Complex.I) (χ₁^k)
        ≤ f 0 * ((1:ℝ)/6 + (1:ℝ)/1000) * Real.log (q:ℝ) := by
    intro k hk2 hk4
    haveI : NeZero (χ₁^k).conductor := ⟨(χ₁^k).conductor_ne_zero⟩
    obtain ⟨hkne1, hkneχ, hkneinv⟩ := pow_ne_one_self_inv_of_orderOf_ge_six hord hk2 hk4
    have hL52k : Commons.NumberTheory.Linnik.L52Hyp (χ₁^k) ((1:ℝ)/6) (1/1000) δ :=
      hL6 q hq1 (χ₁^k) hkne1
    set sk : ℂ := (β:ℂ) + ((k:ℝ):ℂ) * (ρ₁.im:ℂ) * Complex.I with hskdef
    have hskre : sk.re = β := by rw [hskdef]; simp
    have hskim : sk.im = (k:ℝ) * ρ₁.im := by rw [hskdef]; simp
    have hkR : ((k:ℝ)) ≤ 4 := by exact_mod_cast hk4
    have hsk10 : |sk.im| ≤ 10 * Real.log (q:ℝ) := by
      rw [hskim, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (k:ℝ))]
      nlinarith [hν1, hkR, hlog6]
    have hzwk : ∀ u : ℂ, (MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction (χ₁^k).primitiveCharacter)
        (Metric.closedBall 0 (|sk.im| + 2))) u ≠ 0 →
        ‖(1:ℂ) + (sk.im : ℂ) * Complex.I - u‖ ≤ δ → u.re ≤ sk.re := by
      intro u hdiv hwin
      have hzm : Work.LinnikContract.zeroMult (χ₁^k) u ≠ 0 :=
        zeroMult_ne_zero_of_divisor_v2 (χ₁^k) hkne1 hdiv
      have huim8 : |u.im| ≤ 8 := by
        have h3 := Complex.abs_im_le_norm ((1:ℂ) + (sk.im : ℂ) * Complex.I - u)
        have h3b : (((1:ℂ) + (sk.im : ℂ) * Complex.I - u)).im = sk.im - u.im := by simp
        rw [h3b, abs_sub_comm] at h3
        have h4 : |u.im| ≤ |u.im - sk.im| + |sk.im| := by
          calc |u.im| = |(u.im - sk.im) + sk.im| := by ring_nf
            _ ≤ |u.im - sk.im| + |sk.im| := abs_add_le _ _
        have h5 : |sk.im| ≤ 4 := by
          rw [hskim, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (k:ℝ))]
          nlinarith [hν1, hkR]
        linarith [h3, h4, h5, hδ1]
      have hle := hLam2' q hq₃ χ₁ ρ₁ hm hsmall (χ₁^k) u hzm hkne1 hkneχ hkneinv huim8
      have hle2 : lamS ≤ Work.LinnikContract.lamOf q u := by
        rw [hlamSdef, hlam1def]; exact hle
      rw [hskre, hβdef]
      exact re_le_one_sub_of_lam_le hlogq hle2
    have h := hKT (q := q) hqT (χ₁^k) hkne1 (s := sk)
      (by rw [hskre]; exact hβre)
      hsk10
      (by rw [hskre]; exact hslor)
      hL52k
      hzwk
    rw [← Ksum_def_aux] at h
    simpa only [hskdef] using h
  -- the five `K`-sum bounds, assembled
  set Bd : ℕ → ℝ := fun k =>
    if k = 0 then Real.log (q:ℝ) * Ia + f 0 * ((1:ℝ)/1000) * Real.log (q:ℝ)
    else if k = 1 then -(Real.log (q:ℝ)) * Ib + f 0 * ((1:ℝ)/6 + (1:ℝ)/1000) * Real.log (q:ℝ)
    else f 0 * ((1:ℝ)/6 + (1:ℝ)/1000) * Real.log (q:ℝ) with hBddef
  have hBd0 : Bd 0 = Real.log (q:ℝ) * Ia + f 0 * ((1:ℝ)/1000) * Real.log (q:ℝ) := by
    rw [hBddef]; simp
  have hBd1 : Bd 1
      = -(Real.log (q:ℝ)) * Ib + f 0 * ((1:ℝ)/6 + (1:ℝ)/1000) * Real.log (q:ℝ) := by
    rw [hBddef]; simp
  have hBd2 : Bd 2 = f 0 * ((1:ℝ)/6 + (1:ℝ)/1000) * Real.log (q:ℝ) := by
    rw [hBddef]; simp
  have hBd3 : Bd 3 = f 0 * ((1:ℝ)/6 + (1:ℝ)/1000) * Real.log (q:ℝ) := by
    rw [hBddef]; simp
  have hBd4 : Bd 4 = f 0 * ((1:ℝ)/6 + (1:ℝ)/1000) * Real.log (q:ℝ) := by
    rw [hBddef]; simp
  have hBd : ∀ k ∈ Finset.range 5,
      Ksum q f (Real.log (q:ℝ)) ((β:ℂ) + ((k:ℝ):ℂ) * (ρ₁.im:ℂ) * Complex.I) (χ₁^k) ≤ Bd k := by
    intro k hk
    have hk5 : k < 5 := Finset.mem_range.mp hk
    interval_cases k
    · rw [pow_zero, hBd0]
      simpa using hb0
    · rw [pow_one, hBd1]
      simpa [hs1def] using hb1
    · rw [hBd2]; exact hbk 2 (by norm_num) (by norm_num)
    · rw [hBd3]; exact hbk 3 (by norm_num) (by norm_num)
    · rw [hBd4]; exact hbk 4 (by norm_num) (by norm_num)
  have hmain : 0 ≤ ∑ k ∈ Finset.range 5, c95 k * Bd k :=
    main95_assembly (q := q) (f := f) hfnn (x₀ := (8:ℝ)/3) (L := Real.log (q:ℝ))
      (β := β) (γ := ρ₁.im) hlogq (by norm_num) hfsupp χ₁ (Bd := Bd) hBd
  have hval : (∑ k ∈ Finset.range 5, c95 k * Bd k)
      = Real.log (q:ℝ) * ((14379:ℝ) * Ia - 24480 * Ib
          + (4/5) * (14379 * ((1:ℝ)/1000) + 46630 * ((1:ℝ)/6 + (1:ℝ)/1000))) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [hBd0, hBd1, hBd2, hBd3, hBd4, hf0val]
    norm_num [c95]
    ring
  have hneg : (14379:ℝ) * Ia - 24480 * Ib
      + (4/5) * (14379 * ((1:ℝ)/1000) + 46630 * ((1:ℝ)/6 + (1:ℝ)/1000)) < 0 := by
    have harg := caseB_arith hIa_le hIb_ge
    linarith [harg]
  have hlt0 : Real.log (q:ℝ) * ((14379:ℝ) * Ia - 24480 * Ib
      + (4/5) * (14379 * ((1:ℝ)/1000) + 46630 * ((1:ℝ)/6 + (1:ℝ)/1000))) < 0 :=
    mul_neg_of_pos_of_neg hlogq hneg
  linarith [hmain, hval, hlt0]

end Work.ZeroFreeTables.HB94
