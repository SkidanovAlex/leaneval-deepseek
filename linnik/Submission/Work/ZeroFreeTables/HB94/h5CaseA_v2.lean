import Mathlib
import Submission.Work.ZeroFreeTables.HB94.HB94Aux
import Submission.Work.ZeroFreeTables.HB94.L52supply18
import Submission.Work.ZeroFreeTables.HB94.L52supply_pow

set_option maxHeartbeats 4000000

namespace Work.ZeroFreeTables.HB94

/-- `χ ^ k ≠ 1` for `1 ≤ k ≤ 4` when `orderOf χ ≥ 5`. -/
private theorem pow_ne_one_of_orderOf_ge_aux {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    {k : ℕ} (h : 5 ≤ orderOf χ) (hk : 1 ≤ k) (hk4 : k ≤ 4) : χ ^ k ≠ 1 := by
  intro h1
  have hdvd : orderOf χ ∣ k := orderOf_dvd_iff_pow_eq_one.mpr h1
  have hle : orderOf χ ≤ k := Nat.le_of_dvd hk hdvd
  omega


/-- **Case A of HB Lemma 9.5's `h ≥ 5` regime, with a disjunctive `1/8`-supply hypothesis.**
This is a verbatim copy of `Work.ZeroFreeTables.HB94.h5CaseA`
(`Submission/Work/ZeroFreeTables/HB94/h5CaseA.lean`, proved and axiom-clean) with its supply
hypothesis
`hL8 : ∀ q ≥ q₁, ∀ χ ≠ 1, (orderOf χ : ℝ) ≤ log(χ.conductor) → L52Hyp χ (1/8) (1/1000) δ`
weakened to the *disjunction* `(orderOf χ : ℝ) ≤ log(χ.conductor) ∨ χ ^ 60 = 1`.  Both disjuncts
give the `1/8` supply (HB Lemma 2.5's `φ = 1/4`), the second one through `L52supply_pow`
(`χ ^ 60 = 1`); the disjunction is what the order-`5` case needs, where every power `χ₁ᵏ` has
order `5 ∣ 60` while the conductor may be too small.  The proof is unchanged except that the four
instantiations of `hL8` at `χ₁ᵏ` are fed `hord k …` (of the disjunctive type) directly.  So:
`cp h5CaseA.lean h5CaseA_v2.lean`, rename the theorem, and change the hypothesis's type (and its
four applications at lines 217–226 of that file). -/
theorem h5CaseA_v2 (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (q₁ : ℕ)
    (hL8 : ∀ q : ℕ, q₁ ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
      χ ≠ 1 → ((orderOf χ : ℝ) ≤ Real.log (((χ.conductor : ℕ) : ℝ)) ∨ χ ^ 60 = 1) →
        Commons.NumberTheory.Linnik.L52Hyp χ ((1:ℝ)/8) (1/1000) δ) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → 5 ≤ orderOf χ₁ →
      Work.LinnikContract.lamOf q ρ₁ ≤ 348/1000 →
      (∀ k : ℕ, 1 ≤ k → k ≤ 4 →
        ((orderOf (χ₁ ^ k) : ℝ) ≤ Real.log ((((χ₁ ^ k).conductor : ℕ) : ℝ)) ∨ (χ₁ ^ k) ^ 60 = 1)) →
      False := by
  classical
  obtain ⟨hnum1, _⟩ := Work.ZeroFreeTables.HB95plus.tf72_numeric_inputs
  set f : ℝ → ℝ := tf72f ((3:ℝ)/4) with hfdef
  have h34 : (0:ℝ) < (3:ℝ)/4 := by norm_num
  have hfcont : ContinuousOn f (Set.Ici 0) := by rw [hfdef]; exact tf72f_cont _ h34
  have hfsupp : ∀ t : ℝ, (8:ℝ)/3 ≤ t → f t = 0 := by
    intro t ht
    have h2 : (2:ℝ) / ((3:ℝ)/4) = (8:ℝ)/3 := by norm_num
    rw [hfdef]
    exact tf72f_supp _ h34 t (by rw [h2]; exact ht)
  have hfdiff : ContDiffOn ℝ 2 f (Set.Ioo 0 ((8:ℝ)/3)) := by
    have h2 : (2:ℝ) / ((3:ℝ)/4) = (8:ℝ)/3 := by norm_num
    rw [hfdef, ← h2]
    exact tf72f_diff _ h34
  obtain ⟨B, hB0, hBnd⟩ := tf72f_bound ((3:ℝ)/4) h34
  have hfB : ∀ t ∈ Set.Ioo (0:ℝ) ((8:ℝ)/3), ‖iteratedDeriv 2 f t‖ ≤ B := by
    intro t ht
    have h2 : (2:ℝ) / ((3:ℝ)/4) = (8:ℝ)/3 := by norm_num
    rw [hfdef]
    exact hBnd t (by rwa [← h2] at ht)
  have hfnn : ∀ t : ℝ, 0 ≤ f t := by rw [hfdef]; exact tf72f_nonneg _ h34
  have hf0pos : 0 < f 0 := by rw [hfdef, tf72f_at_zero _ h34]; norm_num
  have hf0val : f 0 = 4/5 := by rw [hfdef, tf72f_at_zero _ h34]; norm_num
  have hFc : ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ (∫ t in (0:ℝ)..((8:ℝ)/3), Complex.exp (-(z * (t:ℂ))) * ((f t : ℝ):ℂ)).re := by
    intro z hz
    have h2 : (2:ℝ) / ((3:ℝ)/4) = (8:ℝ)/3 := by norm_num
    have h := tf72Fc_re_nonneg ((3:ℝ)/4) h34 z hz
    rw [hfdef, ← h2]
    exact h
  have hF0 : (∫ t in (0:ℝ)..((8:ℝ)/3), f t) = 8/9 := by
    have h2 : (2:ℝ) / ((3:ℝ)/4) = (8:ℝ)/3 := by norm_num
    rw [hfdef, ← h2]
    exact tf72f_intervalIntegral _ h34
  obtain ⟨qP, hKP⟩ := Commons.NumberTheory.Linnik.Ksum_principal_le ((8:ℝ)/3) B (by norm_num) hB0
    (f := f) hfcont hfsupp hfdiff hfB (ε := (1:ℝ)/1000) (by norm_num) hf0pos
  obtain ⟨qS, hKS⟩ := Commons.NumberTheory.Linnik.Ksum_le_single_of_L52_phi ((8:ℝ)/3) B ((1:ℝ)/8)
    (by norm_num) hB0 (f := f) hfcont hfsupp hfdiff hfB hf0pos hFc
    (ε := (1:ℝ)/1000) (by norm_num) hδ0 hδ1
  obtain ⟨qT, hKT⟩ := Commons.NumberTheory.Linnik.Ksum_le_self_of_L52_phi ((8:ℝ)/3) B ((1:ℝ)/8)
    (by norm_num) hB0 (f := f) hfcont hfsupp hfdiff hfB hf0pos hFc
    (ε := (1:ℝ)/1000) (by norm_num) hδ0 hδ1
  refine ⟨q₁ + qP + qS + qT + 1000000 + (Nat.ceil (Real.exp (348 / (1000 * δ))) + 1), ?_⟩
  intro q hq hqne χ₁ ρ₁ hm h5 hsmall hord
  have hq1 : q₁ ≤ q := by omega
  have hqP : qP ≤ q := by omega
  have hqS : qS ≤ q := by omega
  have hqT : qT ≤ q := by omega
  have hqM : 1000000 ≤ q := by omega
  have hqδ : Nat.ceil (Real.exp (348 / (1000 * δ))) + 1 ≤ q := by omega
  haveI : NeZero q := hqne
  have hq2 : 2 ≤ q := by omega
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hlogq : 0 < Real.log (q:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hlog6 : (6:ℝ) ≤ Real.log (q:ℝ) := by
    have h6 : (1000000:ℝ) ≤ (q:ℝ) := by exact_mod_cast hqM
    have h7 := Real.log_le_log (by norm_num : (0:ℝ) < 1000000) h6
    have h8 : Real.log (1000000:ℝ) = 6 * Real.log 10 := by
      rw [show (1000000:ℝ) = 10^6 by norm_num, Real.log_pow]; norm_num
    have h9 : (2:ℝ) ≤ Real.log 10 := by
      rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 10)]
      have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
    rw [h8] at h7; linarith
  have hδlog : (348:ℝ)/1000 ≤ δ * Real.log (q:ℝ) := by
    have h3 : Real.exp (348 / (1000 * δ)) ≤ (q:ℝ) := by
      have h1 : Real.exp (348 / (1000 * δ)) ≤ (Nat.ceil (Real.exp (348 / (1000 * δ))) : ℝ) :=
        Nat.le_ceil _
      have h2 : (Nat.ceil (Real.exp (348 / (1000 * δ))) : ℝ) ≤ (q:ℝ) := by
        exact_mod_cast (by omega : Nat.ceil (Real.exp (348 / (1000 * δ))) ≤ q)
      linarith
    have h4 : 348 / (1000 * δ) ≤ Real.log (q:ℝ) := by
      rw [Real.le_log_iff_exp_le hqpos]
      exact h3
    calc (348:ℝ)/1000 = δ * (348 / (1000 * δ)) := by field_simp
      _ ≤ δ * Real.log (q:ℝ) := mul_le_mul_of_nonneg_left h4 hδ0.le
  have hχ1 : χ₁ ≠ 1 := hm.1.1.1
  have hzm1 : Work.LinnikContract.zeroMult χ₁ ρ₁ ≠ 0 := hm.1.1.2.1
  have hν1 : |ρ₁.im| ≤ 1 := hm.1.1.2.2
  have hwide := hm.2
  have hlam_nn : 0 ≤ Work.LinnikContract.lamOf q ρ₁ :=
    Work.LinnikContract.API.isZ_lambda_nonneg hq2 hm.1.1
  have hsqrtge : (348:ℝ)/1000 ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) := by
    have h4 : (348:ℝ)/1000 ≤ Real.log (Real.log (q:ℝ)) := by
      have h5 : Real.log 6 ≤ Real.log (Real.log (q:ℝ)) := Real.log_le_log (by norm_num) hlog6
      have h6 : (348:ℝ)/1000 ≤ Real.log 6 := by
        rw [Real.le_log_iff_exp_le (by norm_num)]
        have h7 : Real.exp (348/1000) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
        linarith [Real.exp_one_lt_three, h7]
      linarith [h5, h6]
    calc (348:ℝ)/1000 ≤ Real.sqrt ((348:ℝ)/1000) := by
          rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
      _ ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) := Real.sqrt_le_sqrt h4
  have hβre : |ρ₁.re - 1| ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) := by
    have h1 : 1 - ρ₁.re = Work.LinnikContract.lamOf q ρ₁ / Real.log (q:ℝ) := by
      rw [Work.LinnikContract.lamOf]; field_simp
    have h2 : |ρ₁.re - 1| = 1 - ρ₁.re := by
      have h3 : 0 ≤ 1 - ρ₁.re := by rw [h1]; exact div_nonneg hlam_nn hlogq.le
      rw [abs_of_nonpos (by linarith)]; ring
    rw [h2, h1]
    exact div_le_div_of_nonneg_right (le_trans hsmall hsqrtge) hlogq.le
  have hslo : 1 - Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) ≤ ρ₁.re := by
    have h1 : -|ρ₁.re - 1| ≤ ρ₁.re - 1 := neg_abs_le _
    linarith [hβre, h1]
  haveI hc1 : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
  haveI hc2 : NeZero (χ₁^2).conductor := ⟨(χ₁^2).conductor_ne_zero⟩
  haveI hc3 : NeZero (χ₁^3).conductor := ⟨(χ₁^3).conductor_ne_zero⟩
  haveI hc4 : NeZero (χ₁^4).conductor := ⟨(χ₁^4).conductor_ne_zero⟩
  have hnn1 : 0 ≤ 1 - ρ₁.re := by
    have h2 : 1 - ρ₁.re = Work.LinnikContract.lamOf q ρ₁ / Real.log (q:ℝ) := by
      rw [Work.LinnikContract.lamOf]; field_simp
    rw [h2]; exact div_nonneg hlam_nn hlogq.le
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
  have hsr1 : ((ρ₁.re : ℂ) + ((1:ℝ)*ρ₁.im : ℂ)*Complex.I).re = ρ₁.re := by simp
  have hsi1 : ((ρ₁.re : ℂ) + ((1:ℝ)*ρ₁.im : ℂ)*Complex.I).im = ρ₁.im := by simp
  have hwinpred : ‖(1:ℂ) + (((ρ₁.re : ℂ) + ((1:ℝ)*ρ₁.im : ℂ)*Complex.I).im : ℂ) * Complex.I - ρ₁‖ ≤ δ := by
    have h1 : (1:ℂ) + (((ρ₁.re : ℂ) + ((1:ℝ)*ρ₁.im : ℂ)*Complex.I).im : ℂ) * Complex.I - ρ₁
        = ((1 - ρ₁.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn1]
    have h2 : 1 - ρ₁.re = Work.LinnikContract.lamOf q ρ₁ / Real.log (q:ℝ) := by
      rw [Work.LinnikContract.lamOf]; field_simp
    rw [h2, div_le_iff₀ hlogq]
    nlinarith [hsmall, hδlog]
  have hwin1 : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
      (Metric.closedBall 0 (|((ρ₁.re : ℂ) + ((1:ℝ)*ρ₁.im : ℂ)*Complex.I).im| + 2))) ρ₁ ≠ 0 :=
    divisor_ne_zero_of_zeroMult_aux χ₁ hχ1 (by simpa using hmem1) hzm1
  have hsim1 : |ρ₁.im| ≤ 10 * Real.log (q:ℝ) := by
    have h10 : (1:ℝ) ≤ 10 * Real.log (q:ℝ) := by linarith
    linarith [hν1]
  have habs : ∀ {s u : ℂ}, |s.im| ≤ 8 → ‖(1:ℂ) + (s.im:ℂ)*Complex.I - u‖ ≤ δ → |u.im| ≤ 10 := by
    intro s u hs h
    have h3 := Complex.abs_im_le_norm ((1:ℂ) + (s.im:ℂ)*Complex.I - u)
    have h3b : (((1:ℂ) + (s.im:ℂ)*Complex.I - u)).im = s.im - u.im := by simp
    rw [h3b, abs_sub_comm] at h3
    have h4 : |u.im| ≤ |u.im - s.im| + |s.im| := by
      calc |u.im| = |(u.im - s.im) + s.im| := by ring_nf
        _ ≤ |u.im - s.im| + |s.im| := abs_add_le _ _
    linarith [le_trans h3 h, h4, hs, hδ1]
  have hzwgen : ∀ (m : ℕ) [NeZero (χ₁^m).conductor], χ₁^m ≠ 1 → ∀ (s : ℂ), s.re = ρ₁.re →
      |s.im| ≤ 8 → (∀ u : ℂ, (MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction ((χ₁^m).primitiveCharacter))
        (Metric.closedBall 0 (|s.im| + 2))) u ≠ 0 →
        ‖(1:ℂ) + (s.im:ℂ)*Complex.I - u‖ ≤ δ → u.re ≤ s.re) := by
    intro m _inst hne s hsre hsim u hdiv hwin
    have hzm : Work.LinnikContract.zeroMult (χ₁^m) u ≠ 0 :=
      zeroMult_ne_zero_of_divisor_v2 (χ₁^m) hne hdiv
    have huim : |u.im| ≤ 10 := habs hsim hwin
    have hle := hwide (χ₁^m) u hne hzm huim
    rw [show Work.LinnikContract.lamOf q u = (1 - u.re) * Real.log (q:ℝ) from rfl,
      show Work.LinnikContract.lamOf q ρ₁ = (1 - ρ₁.re) * Real.log (q:ℝ) from rfl] at hle
    rw [hsre]
    nlinarith [hle, hlogq]
  have hL52_1 : Commons.NumberTheory.Linnik.L52Hyp χ₁ ((1:ℝ)/8) (1/1000) δ :=
    hL8 q hq1 χ₁ hχ1 (by simpa only [pow_one] using hord 1 (by norm_num) (by norm_num))
  have hL52_2 : Commons.NumberTheory.Linnik.L52Hyp (χ₁^2) ((1:ℝ)/8) (1/1000) δ :=
    hL8 q hq1 (χ₁^2) (pow_ne_one_of_orderOf_ge_aux h5 (by norm_num) (by norm_num))
      (hord 2 (by norm_num) (by norm_num))
  have hL52_3 : Commons.NumberTheory.Linnik.L52Hyp (χ₁^3) ((1:ℝ)/8) (1/1000) δ :=
    hL8 q hq1 (χ₁^3) (pow_ne_one_of_orderOf_ge_aux h5 (by norm_num) (by norm_num))
      (hord 3 (by norm_num) (by norm_num))
  have hL52_4 : Commons.NumberTheory.Linnik.L52Hyp (χ₁^4) ((1:ℝ)/8) (1/1000) δ :=
    hL8 q hq1 (χ₁^4) (pow_ne_one_of_orderOf_ge_aux h5 (by norm_num) (by norm_num))
      (hord 4 (by norm_num) (by norm_num))
  have hs2re : ((ρ₁.re : ℂ) + ((2:ℝ)*ρ₁.im : ℂ)*Complex.I).re = ρ₁.re := by simp
  have hs2im : ((ρ₁.re : ℂ) + ((2:ℝ)*ρ₁.im : ℂ)*Complex.I).im = 2 * ρ₁.im := by simp
  have hs3re : ((ρ₁.re : ℂ) + ((3:ℝ)*ρ₁.im : ℂ)*Complex.I).re = ρ₁.re := by simp
  have hs3im : ((ρ₁.re : ℂ) + ((3:ℝ)*ρ₁.im : ℂ)*Complex.I).im = 3 * ρ₁.im := by simp
  have hs4re : ((ρ₁.re : ℂ) + ((4:ℝ)*ρ₁.im : ℂ)*Complex.I).re = ρ₁.re := by simp
  have hs4im : ((ρ₁.re : ℂ) + ((4:ℝ)*ρ₁.im : ℂ)*Complex.I).im = 4 * ρ₁.im := by simp
  have hs2abs : |((ρ₁.re : ℂ) + ((2:ℝ)*ρ₁.im : ℂ)*Complex.I).im| ≤ 8 := by
    rw [hs2im]
    have h2 : |(2:ℝ) * ρ₁.im| ≤ 2 := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]; linarith [hν1]
    linarith
  have hs3abs : |((ρ₁.re : ℂ) + ((3:ℝ)*ρ₁.im : ℂ)*Complex.I).im| ≤ 8 := by
    rw [hs3im]
    have h2 : |(3:ℝ) * ρ₁.im| ≤ 3 := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3)]; linarith [hν1]
    linarith
  have hs4abs : |((ρ₁.re : ℂ) + ((4:ℝ)*ρ₁.im : ℂ)*Complex.I).im| ≤ 8 := by
    rw [hs4im]
    have h2 : |(4:ℝ) * ρ₁.im| ≤ 4 := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)]; linarith [hν1]
    linarith
  have hs2ten : |((ρ₁.re : ℂ) + ((2:ℝ)*ρ₁.im : ℂ)*Complex.I).im| ≤ 10 * Real.log (q:ℝ) := by
    rw [hs2im]; have h2 : |(2:ℝ) * ρ₁.im| ≤ 2 := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]; linarith [hν1]
    linarith [hlog6, h2]
  have hs3ten : |((ρ₁.re : ℂ) + ((3:ℝ)*ρ₁.im : ℂ)*Complex.I).im| ≤ 10 * Real.log (q:ℝ) := by
    rw [hs3im]; have h2 : |(3:ℝ) * ρ₁.im| ≤ 3 := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3)]; linarith [hν1]
    linarith [hlog6, h2]
  have hs4ten : |((ρ₁.re : ℂ) + ((4:ℝ)*ρ₁.im : ℂ)*Complex.I).im| ≤ 10 * Real.log (q:ℝ) := by
    rw [hs4im]; have h2 : |(4:ℝ) * ρ₁.im| ≤ 4 := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)]; linarith [hν1]
    linarith [hlog6, h2]
  set Aint : ℝ := ∫ t in (0:ℝ)..((8:ℝ)/3),
    Real.exp (Work.LinnikContract.lamOf q ρ₁ * t) * f t with hAdef
  have hA : Aint ≤ (118:ℝ)/100 := by
    have hnum1' : (∫ t in (0:ℝ)..((8:ℝ)/3),
        Real.exp (((348:ℝ)/1000) * t) * f t) ≤ (118:ℝ)/100 := by
      rw [hfdef]; exact hnum1
    have hint1 : IntervalIntegrable (fun t : ℝ =>
        Real.exp (Work.LinnikContract.lamOf q ρ₁ * t) * f t) MeasureTheory.volume
        (0:ℝ) ((8:ℝ)/3) := by
      refine ContinuousOn.intervalIntegrable_of_Icc (by norm_num : (0:ℝ) ≤ (8:ℝ)/3) ?_
      exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul
        (hfcont.mono (fun t ht => ht.1))
    have hint2 : IntervalIntegrable (fun t : ℝ =>
        Real.exp (((348:ℝ)/1000) * t) * f t) MeasureTheory.volume (0:ℝ) ((8:ℝ)/3) := by
      refine ContinuousOn.intervalIntegrable_of_Icc (by norm_num : (0:ℝ) ≤ (8:ℝ)/3) ?_
      exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul
        (hfcont.mono (fun t ht => ht.1))
    have hle : ∀ t ∈ Set.Icc (0:ℝ) ((8:ℝ)/3),
        Real.exp (Work.LinnikContract.lamOf q ρ₁ * t) * f t
          ≤ Real.exp (((348:ℝ)/1000) * t) * f t := by
      intro t ht
      exact mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hsmall ht.1)) (hfnn t)
    rw [hAdef]
    exact le_trans (intervalIntegral.integral_mono_on (by norm_num) hint1 hint2 hle) hnum1'
  have hzw1 : ∀ u : ℂ, (MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
      (Metric.closedBall 0 (|((ρ₁.re : ℂ) + ((1:ℝ)*ρ₁.im : ℂ)*Complex.I).im| + 2))) u ≠ 0 →
      ‖(1:ℂ) + ((((ρ₁.re : ℂ) + ((1:ℝ)*ρ₁.im : ℂ)*Complex.I).im : ℂ)) * Complex.I - u‖ ≤ δ →
      u.re ≤ ((ρ₁.re : ℂ) + ((1:ℝ)*ρ₁.im : ℂ)*Complex.I).re := by
    intro u hdiv hwin
    have hzm : Work.LinnikContract.zeroMult χ₁ u ≠ 0 :=
      zeroMult_ne_zero_of_divisor_v2 χ₁ hχ1 hdiv
    have huim : |u.im| ≤ 10 := habs
      (s := ((ρ₁.re : ℂ) + ((1:ℝ)*ρ₁.im : ℂ)*Complex.I))
      (by rw [hsi1]; linarith [hν1]) hwin
    have hle := hwide χ₁ u hχ1 hzm huim
    rw [show Work.LinnikContract.lamOf q u = (1 - u.re) * Real.log (q:ℝ) from rfl,
      show Work.LinnikContract.lamOf q ρ₁ = (1 - ρ₁.re) * Real.log (q:ℝ) from rfl] at hle
    rw [hsr1]
    nlinarith [hle, hlogq]
  have hs1abs : |((ρ₁.re : ℂ) + ((1:ℝ)*ρ₁.im : ℂ)*Complex.I).im| ≤ 8 := by
    rw [hsi1]; linarith [hν1]
  have hb0 : Ksum q f (Real.log (q:ℝ)) ((ρ₁.re : ℂ)) 1
      ≤ Real.log (q:ℝ) * Aint + f 0 * ((1:ℝ)/1000) * Real.log (q:ℝ) := by
    have h := hKP (q := q) hqP (β := ρ₁.re) (lam := Work.LinnikContract.lamOf q ρ₁)
      (by rw [Work.LinnikContract.lamOf]; ring) hβre
    rw [← Ksum_def_aux] at h
    rw [← hAdef] at h
    exact h
  have hb1 : Ksum q f (Real.log (q:ℝ)) ((ρ₁.re : ℂ) + ((1:ℝ)*ρ₁.im : ℂ)*Complex.I) χ₁
      ≤ -(Real.log (q:ℝ)) * (8/9) + f 0 * ((1:ℝ)/8 + (1:ℝ)/1000) * Real.log (q:ℝ) := by
    have hs_eq : ((ρ₁.re : ℂ) + ((1:ℝ)*ρ₁.im : ℂ)*Complex.I) - ρ₁ = 0 := by
      have h1 : ((ρ₁.re : ℂ) + ((1:ℝ)*ρ₁.im : ℂ)*Complex.I) = ρ₁ := by
        have h2 : ((1:ℝ)*ρ₁.im : ℂ) = (ρ₁.im : ℂ) := by simp
        rw [h2]; exact Complex.re_add_im ρ₁
      rw [h1, sub_self]
    have hF0c0 : (∫ t in (0:ℝ)..((8:ℝ)/3),
        Complex.exp (-(((0:ℂ) * (Real.log (q:ℝ)) * (t:ℂ)))) * ((f t : ℝ):ℂ)).re = 8/9 := by
      have h1 : ∀ t : ℝ, Complex.exp (-(((0:ℂ) * (Real.log (q:ℝ)) * (t:ℂ))))
          * ((f t : ℝ):ℂ) = ((f t : ℝ):ℂ) := by
        intro t
        rw [zero_mul, zero_mul, neg_zero, Complex.exp_zero, one_mul]
      rw [intervalIntegral.integral_congr (fun t _ => h1 t), intervalIntegral.integral_ofReal]
      simp only [Complex.ofReal_re]
      exact hF0
    have h := hKS (q := q) hqS χ₁ hχ1 (s := (ρ₁.re : ℂ) + ((1:ℝ)*ρ₁.im : ℂ)*Complex.I) (ρ := ρ₁)
      (by rw [hsr1]; exact hβre) (by rw [hsi1]; exact hsim1) (by rw [hsr1]; exact hslo)
      hL52_1 hwin1 hwinpred hzw1
    rw [hs_eq] at h
    rw [hF0c0] at h
    rw [← Ksum_def_aux] at h
    exact h
  have hb2 : Ksum q f (Real.log (q:ℝ)) ((ρ₁.re : ℂ) + ((2:ℝ)*ρ₁.im : ℂ)*Complex.I) (χ₁^2)
      ≤ f 0 * ((1:ℝ)/8 + (1:ℝ)/1000) * Real.log (q:ℝ) := by
    have h := hKT (q := q) hqT (χ₁^2) (pow_ne_one_of_orderOf_ge_aux h5 (by norm_num) (by norm_num))
      (s := (ρ₁.re : ℂ) + ((2:ℝ)*ρ₁.im : ℂ)*Complex.I)
      (by rw [hs2re]; exact hβre) (by simpa only [hs2im] using hs2ten) (by rw [hs2re]; exact hslo)
      hL52_2 (hzwgen 2 (pow_ne_one_of_orderOf_ge_aux h5 (by norm_num) (by norm_num))
        ((ρ₁.re : ℂ) + ((2:ℝ)*ρ₁.im : ℂ)*Complex.I) hs2re hs2abs)
    rw [← Ksum_def_aux] at h
    exact h
  have hb3 : Ksum q f (Real.log (q:ℝ)) ((ρ₁.re : ℂ) + ((3:ℝ)*ρ₁.im : ℂ)*Complex.I) (χ₁^3)
      ≤ f 0 * ((1:ℝ)/8 + (1:ℝ)/1000) * Real.log (q:ℝ) := by
    have h := hKT (q := q) hqT (χ₁^3) (pow_ne_one_of_orderOf_ge_aux h5 (by norm_num) (by norm_num))
      (s := (ρ₁.re : ℂ) + ((3:ℝ)*ρ₁.im : ℂ)*Complex.I)
      (by rw [hs3re]; exact hβre) (by simpa only [hs3im] using hs3ten) (by rw [hs3re]; exact hslo)
      hL52_3 (hzwgen 3 (pow_ne_one_of_orderOf_ge_aux h5 (by norm_num) (by norm_num))
        ((ρ₁.re : ℂ) + ((3:ℝ)*ρ₁.im : ℂ)*Complex.I) hs3re hs3abs)
    rw [← Ksum_def_aux] at h
    exact h
  have hb4 : Ksum q f (Real.log (q:ℝ)) ((ρ₁.re : ℂ) + ((4:ℝ)*ρ₁.im : ℂ)*Complex.I) (χ₁^4)
      ≤ f 0 * ((1:ℝ)/8 + (1:ℝ)/1000) * Real.log (q:ℝ) := by
    have h := hKT (q := q) hqT (χ₁^4) (pow_ne_one_of_orderOf_ge_aux h5 (by norm_num) (by norm_num))
      (s := (ρ₁.re : ℂ) + ((4:ℝ)*ρ₁.im : ℂ)*Complex.I)
      (by rw [hs4re]; exact hβre) (by simpa only [hs4im] using hs4ten) (by rw [hs4re]; exact hslo)
      hL52_4 (hzwgen 4 (pow_ne_one_of_orderOf_ge_aux h5 (by norm_num) (by norm_num))
        ((ρ₁.re : ℂ) + ((4:ℝ)*ρ₁.im : ℂ)*Complex.I) hs4re hs4abs)
    rw [← Ksum_def_aux] at h
    exact h
  have hneg : (14379:ℝ) * Aint - 24480 * (8/9)
      + (4/5) * (14379 * ((1:ℝ)/1000) + 46630 * ((1:ℝ)/8 + (1:ℝ)/1000)) < 0 := by
    have harg := caseA_arith hA
    linarith [harg]
  have hlt0 : Real.log (q:ℝ) * ((14379:ℝ) * Aint - 24480 * (8/9)
      + (4/5) * (14379 * ((1:ℝ)/1000) + 46630 * ((1:ℝ)/8 + (1:ℝ)/1000))) < 0 :=
    mul_neg_of_pos_of_neg hlogq hneg
  have hcomb := ksum_trigPoly_nonneg (q := q) (f := f) hfnn (x₀ := (8:ℝ)/3)
    (L := Real.log (q:ℝ)) (β := ρ₁.re) (γ := ρ₁.im) hlogq (by norm_num) hfsupp
    (c := c95) (d := 4) c95_hP χ₁
  have hexp : (∑ k ∈ Finset.range 5, c95 k *
        Ksum q f (Real.log (q:ℝ)) ((ρ₁.re : ℂ) + ((k:ℝ) * ρ₁.im : ℂ) * Complex.I) (χ₁^k))
      = (14379:ℝ) * Ksum q f (Real.log (q:ℝ)) ((ρ₁.re : ℂ)) 1
        + 24480 * Ksum q f (Real.log (q:ℝ)) ((ρ₁.re : ℂ) + ((1:ℝ)*ρ₁.im : ℂ)*Complex.I) χ₁
        + 14900 * Ksum q f (Real.log (q:ℝ)) ((ρ₁.re : ℂ) + ((2:ℝ)*ρ₁.im : ℂ)*Complex.I) (χ₁^2)
        + 6000 * Ksum q f (Real.log (q:ℝ)) ((ρ₁.re : ℂ) + ((3:ℝ)*ρ₁.im : ℂ)*Complex.I) (χ₁^3)
        + 1250 * Ksum q f (Real.log (q:ℝ)) ((ρ₁.re : ℂ) + ((4:ℝ)*ρ₁.im : ℂ)*Complex.I) (χ₁^4) := by
    norm_num [Finset.sum_range_succ, Finset.sum_range_zero, c95, pow_zero, pow_one]
  rw [hexp] at hcomb
  have hsum1 : (14379:ℝ) * Ksum q f (Real.log (q:ℝ)) ((ρ₁.re : ℂ)) 1
      + 24480 * Ksum q f (Real.log (q:ℝ)) ((ρ₁.re : ℂ) + ((1:ℝ)*ρ₁.im : ℂ)*Complex.I) χ₁
      + 14900 * Ksum q f (Real.log (q:ℝ)) ((ρ₁.re : ℂ) + ((2:ℝ)*ρ₁.im : ℂ)*Complex.I) (χ₁^2)
      + 6000 * Ksum q f (Real.log (q:ℝ)) ((ρ₁.re : ℂ) + ((3:ℝ)*ρ₁.im : ℂ)*Complex.I) (χ₁^3)
      + 1250 * Ksum q f (Real.log (q:ℝ)) ((ρ₁.re : ℂ) + ((4:ℝ)*ρ₁.im : ℂ)*Complex.I) (χ₁^4)
      ≤ (14379:ℝ) * (Real.log (q:ℝ) * Aint + f 0 * ((1:ℝ)/1000) * Real.log (q:ℝ))
        + 24480 * (-(Real.log (q:ℝ)) * (8/9) + f 0 * ((1:ℝ)/8 + (1:ℝ)/1000) * Real.log (q:ℝ))
        + 14900 * (f 0 * ((1:ℝ)/8 + (1:ℝ)/1000) * Real.log (q:ℝ))
        + 6000 * (f 0 * ((1:ℝ)/8 + (1:ℝ)/1000) * Real.log (q:ℝ))
        + 1250 * (f 0 * ((1:ℝ)/8 + (1:ℝ)/1000) * Real.log (q:ℝ)) := by
    have e0 := mul_le_mul_of_nonneg_left hb0 (by norm_num : (0:ℝ) ≤ 14379)
    have e1 := mul_le_mul_of_nonneg_left hb1 (by norm_num : (0:ℝ) ≤ 24480)
    have e2 := mul_le_mul_of_nonneg_left hb2 (by norm_num : (0:ℝ) ≤ 14900)
    have e3 := mul_le_mul_of_nonneg_left hb3 (by norm_num : (0:ℝ) ≤ 6000)
    have e4 := mul_le_mul_of_nonneg_left hb4 (by norm_num : (0:ℝ) ≤ 1250)
    linarith [e0, e1, e2, e3, e4]
  have hsum2 : (14379:ℝ) * (Real.log (q:ℝ) * Aint + f 0 * ((1:ℝ)/1000) * Real.log (q:ℝ))
        + 24480 * (-(Real.log (q:ℝ)) * (8/9) + f 0 * ((1:ℝ)/8 + (1:ℝ)/1000) * Real.log (q:ℝ))
        + 14900 * (f 0 * ((1:ℝ)/8 + (1:ℝ)/1000) * Real.log (q:ℝ))
        + 6000 * (f 0 * ((1:ℝ)/8 + (1:ℝ)/1000) * Real.log (q:ℝ))
        + 1250 * (f 0 * ((1:ℝ)/8 + (1:ℝ)/1000) * Real.log (q:ℝ))
      = Real.log (q:ℝ) * ((14379:ℝ) * Aint - 24480 * (8/9)
          + (4/5) * (14379 * ((1:ℝ)/1000) + 46630 * ((1:ℝ)/8 + (1:ℝ)/1000))) := by
    rw [hf0val]; ring
  linarith [hcomb, hsum1, hsum2, hlt0]

end Work.ZeroFreeTables.HB94
