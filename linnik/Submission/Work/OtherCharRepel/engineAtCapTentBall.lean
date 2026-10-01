import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.LinnikAreas.DhRepel.lemma8_5
import Submission.Work.LinnikAreas.DhRepel.l52Hyp_supply
import Submission.Work.LinnikAreas.OtherCharRepel.tentLaplaceReNonneg
import Submission.Work.LinnikAreas.OtherCharRepel.lemma85pt
import Submission.Work.LinnikAreas.OtherCharRepel.l52HypTwo
import Submission.Work.LinnikAreas.OtherCharRepel.zeroMultTransfer
import Submission.Work.LinnikAreas.OtherCharRepel.maximalityOfMinimality
import Submission.Work.LinnikAreas.OtherCharRepel.zeroMultStripPos
import Submission.Work.LinnikAreas.OtherCharRepel.logThresholdThirteen
import Submission.Work.LinnikAreas.triangle_hFnn

namespace Work.OtherCharRepel

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open DirichletCharacter Complex MeasureTheory intervalIntegral
open Work.LinnikAreas.OtherCharRepel

private lemma iteratedDeriv_two_tent32 {t : ℝ} (ht : t ∈ Set.Ioo (0:ℝ) 32) :
    iteratedDeriv 2 (fun s : ℝ => max (32 - s) 0) t = 0 := by
  have hcongr : Set.EqOn (fun s : ℝ => max (32 - s) 0) (fun s : ℝ => 32 - s)
      (Set.Ioo (0:ℝ) 32) :=
    fun s hs => max_eq_left (by linarith [hs.2])
  have h1 := Set.EqOn.iteratedDeriv_of_isOpen hcongr isOpen_Ioo 2 ht
  rw [h1]
  simp [iteratedDeriv_succ, iteratedDeriv_const, iteratedDeriv_id]

/-- `∫₀^{32} max (32 - t) 0 dt = 512`. -/
private lemma integral_tent32 : (∫ t in (0:ℝ)..32, max (32 - t) 0) = 512 := by
  have hcongr : (∫ t in (0:ℝ)..32, max (32 - t) 0) = ∫ t in (0:ℝ)..32, (32 - t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 32)] at ht
    exact max_eq_left (by linarith [ht.2])
  rw [hcongr]
  have hsub := intervalIntegral.integral_sub (μ := MeasureTheory.volume) (a := (0:ℝ)) (b := 32)
    (f := fun _ : ℝ => (32:ℝ)) (g := fun s : ℝ => s)
    (continuous_const.intervalIntegrable _ _) (continuous_id.intervalIntegrable _ _)
  simp only [intervalIntegral.integral_const, integral_id, smul_eq_mul] at hsub
  rw [hsub]; norm_num

/-- **Extraction from Heath-Brown 8.5 at the tent of width `32`.**

If the Laplace-difference inequality produced by Heath-Brown's Lemma 8.5 (at the tent
`t ↦ (32-t)₊`, with the explicit constants `c = 2`, `ε = 1/64`) holds, then the product
`λ₀ · ∫₀³² t (32-t) e^{λ₂ t} dt` is at least `256`.

The point is that the difference of the two Laplace transforms is a difference of two
exponentials, and `e^{λ₂ t} - e^{(λ₂-λ₀)t} ≤ λ₀ t e^{λ₂ t}` pointwise, so
`A(λ₂) - A(λ₂-λ₀) ≤ λ₀ I(λ₂)` where `A(λ) = ∫₀³² e^{λ t}(32-t) dt` and `I = A′`; the
Lemma 8.5 inequality gives `A(λ₂) - A(λ₂-λ₀) ≥ 318`. -/
theorem tent32Extract {lam₀ lam₂ : ℝ}
    (h : 0 ≤ (∫ t in (0:ℝ)..32, Real.exp (lam₂ * t) * (32 - t))
        - (∫ t in (0:ℝ)..32, Real.exp ((lam₂ - lam₀) * t) * (32 - t)) - 318) :
    256 ≤ lam₀ * (∫ t in (0:ℝ)..32, t * (32 - t) * Real.exp (lam₂ * t)) := by
  have hsub : (∫ t in (0:ℝ)..32, Real.exp (lam₂ * t) * (32 - t))
      - (∫ t in (0:ℝ)..32, Real.exp ((lam₂ - lam₀) * t) * (32 - t))
      = ∫ t in (0:ℝ)..32, (Real.exp (lam₂ * t) - Real.exp ((lam₂ - lam₀) * t)) * (32 - t) := by
    rw [← intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  have hpt : ∀ t ∈ Set.Icc (0:ℝ) 32,
      (Real.exp (lam₂ * t) - Real.exp ((lam₂ - lam₀) * t)) * (32 - t)
        ≤ lam₀ * (t * (32 - t) * Real.exp (lam₂ * t)) := by
    intro t ht
    have h32t : 0 ≤ 32 - t := by linarith [ht.2]
    have hstep : Real.exp (lam₂ * t) - Real.exp ((lam₂ - lam₀) * t)
        ≤ lam₀ * t * Real.exp (lam₂ * t) := by
      have h1 : Real.exp (lam₀ * t) - 1 ≤ lam₀ * t * Real.exp (lam₀ * t) := by
        have h2 := Real.log_le_sub_one_of_pos (Real.exp_pos (-(lam₀ * t)))
        rw [Real.log_exp] at h2
        have h3 : 1 - Real.exp (-(lam₀ * t)) ≤ lam₀ * t := by linarith
        have h4 : Real.exp (lam₀ * t) * (1 - Real.exp (-(lam₀ * t)))
            ≤ Real.exp (lam₀ * t) * (lam₀ * t) :=
          mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
        have hexp0 : Real.exp (lam₀ * t) * Real.exp (-(lam₀ * t)) = 1 := by
          rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
        have h5 : Real.exp (lam₀ * t) * (1 - Real.exp (-(lam₀ * t))) = Real.exp (lam₀ * t) - 1 := by
          rw [mul_sub, mul_one, hexp0]
        rw [h5] at h4
        linarith [h4]
      have h6 : Real.exp (lam₂ * t) = Real.exp ((lam₂ - lam₀) * t) * Real.exp (lam₀ * t) := by
        rw [← Real.exp_add]; ring_nf
      have heq : Real.exp (lam₂*t) - Real.exp ((lam₂-lam₀)*t)
          = Real.exp ((lam₂-lam₀)*t) * (Real.exp (lam₀*t) - 1) := by
        rw [h6]; ring
      rw [heq]
      calc Real.exp ((lam₂-lam₀)*t) * (Real.exp (lam₀*t) - 1)
          ≤ Real.exp ((lam₂-lam₀)*t) * (lam₀*t*Real.exp (lam₀*t)) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = lam₀*t*Real.exp (lam₂*t) := by rw [h6]; ring
    calc (Real.exp (lam₂ * t) - Real.exp ((lam₂ - lam₀) * t)) * (32 - t)
        ≤ (lam₀ * t * Real.exp (lam₂ * t)) * (32 - t) := mul_le_mul_of_nonneg_right hstep h32t
      _ = lam₀ * (t * (32 - t) * Real.exp (lam₂ * t)) := by ring
  have hmono : (∫ t in (0:ℝ)..32, (Real.exp (lam₂ * t) - Real.exp ((lam₂ - lam₀) * t)) * (32 - t))
      ≤ ∫ t in (0:ℝ)..32, lam₀ * (t * (32 - t) * Real.exp (lam₂ * t)) :=
    intervalIntegral.integral_mono_on (by norm_num)
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)
      hpt
  have hcm : (∫ t in (0:ℝ)..32, lam₀ * (t * (32 - t) * Real.exp (lam₂ * t)))
      = lam₀ * ∫ t in (0:ℝ)..32, t * (32 - t) * Real.exp (lam₂ * t) :=
    intervalIntegral.integral_const_mul lam₀ _
  linarith [h, hsub, hmono, hcm]

theorem engineAtCapTentBall : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₀ : DirichletCharacter ℂ q) (ρ₀ : ℂ) (χ₂ : DirichletCharacter ℂ q) (ρ₂ : ℂ),
    Work.LinnikContract.IsMin1 χ₀ ρ₀ → χ₀ ^ 2 = 1 → ρ₀.im = 0 →
    Work.LinnikContract.lamOf q ρ₀ ≤ 1 / 100 →
    χ₂ ≠ χ₀ → χ₂ ≠ 1 → Work.LinnikContract.zeroMult χ₂ ρ₂ ≠ 0 →
    Work.LinnikContract.lamOf q ρ₀ ≤ Work.LinnikContract.lamOf q ρ₂ →
    Work.LinnikContract.lamOf q ρ₂ ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) →
    |ρ₂.im| + 1 ≤ 10 * Real.log (q : ℝ) →
    (∀ (ψ : DirichletCharacter ℂ q) (u : ℂ), ψ ≠ 1 → Work.LinnikContract.zeroMult ψ u ≠ 0 →
      |u.im| ≤ |ρ₂.im| + 1 → (ψ, u) ≠ (χ₀, ρ₀) →
        Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q u) →
    (256 : ℝ) ≤ Work.LinnikContract.lamOf q ρ₀ *
      (∫ t in (0:ℝ)..32, t * (32 - t) * Real.exp (Work.LinnikContract.lamOf q ρ₂ * t)) := by
  -- Heath-Brown Lemma 8.5 at the tent test function of width `32`
  obtain ⟨qT, hT⟩ := lemma85pt 32 0 2 (by norm_num) le_rfl
    (f := fun t : ℝ => max (32 - t) 0)
    (by fun_prop)
    (fun t ht => max_eq_right (by linarith [ht]))
    (by
      have haff : ContDiffOn ℝ 2 (fun t : ℝ => 32 - t) (Set.Ioo (0:ℝ) 32) :=
        contDiffOn_const.sub contDiffOn_id
      exact haff.congr (fun t ht => max_eq_left (by linarith [ht.2])))
    (fun t ht => by rw [iteratedDeriv_two_tent32 ht]; norm_num)
    (by rw [sub_zero, max_eq_left (by norm_num : (0:ℝ) ≤ 32)]; norm_num)
    (fun t => le_max_right _ _)
    (Work.LinnikAreas.triangle_hFnn (by norm_num))
    (ε := (1/64 : ℝ)) (by norm_num) (δ := (1/2 : ℝ)) (by norm_num) (by norm_num)
  -- Heath-Brown Lemma 3.1 with the explicit constant `2`, and the log thresholds
  obtain ⟨qL, hL⟩ := l52HypTwo
  obtain ⟨qThr, hThr⟩ := logThresholdThirteen
  refine ⟨max (max qT qL) qThr, ?_⟩
  intro q hq _inst χ₀ ρ₀ χ₂ ρ₂ hmin1 hsq him0 hlam0 hχ₂neχ₀ hχ₂ne1 hzm₂ hle hlecap hbb hminimal
  have hqqT : qT ≤ q := by omega
  have hqqL : qL ≤ q := by omega
  have hqqThr : qThr ≤ q := by omega
  obtain ⟨hlogpos, hlog12, hloglog2, hδpos, hδlt1, hsqrtge⟩ := hThr q hqqThr
  have hqpos_nat : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos_nat
  have hq2 : 2 ≤ q := by
    have h := Real.log_le_sub_one_of_pos hqpos
    have h2 : (2 : ℝ) ≤ (q : ℝ) := by linarith
    exact_mod_cast h2
  -- conductor instances
  letI : NeZero χ₀.conductor := ⟨χ₀.conductor_ne_zero⟩
  letI : NeZero χ₂.conductor := ⟨χ₂.conductor_ne_zero⟩
  letI : NeZero (χ₀ * χ₂).conductor := ⟨(χ₀ * χ₂).conductor_ne_zero⟩
  letI : NeZero (χ₀ * χ₂⁻¹).conductor := ⟨(χ₀ * χ₂⁻¹).conductor_ne_zero⟩
  -- basic data about the two zeros
  have hχ₀ne1 : χ₀ ≠ 1 := hmin1.1.1
  have hzm₀ : Work.LinnikContract.zeroMult χ₀ ρ₀ ≠ 0 := hmin1.1.2.1
  obtain ⟨hρ₀re, hρ₀re1, hlam₀pos⟩ := zeroMultStripPos hq2 hχ₀ne1 hzm₀
  obtain ⟨hρ₂re, hρ₂re1, hlam₂pos⟩ := zeroMultStripPos hq2 hχ₂ne1 hzm₂
  -- product/non-principality facts
  have hsq' : χ₀ * χ₀ = 1 := by rw [← pow_two]; exact hsq
  have hχ₁χ₂ : χ₀ * χ₂ ≠ 1 := by
    intro hh
    have h2 : χ₂ = χ₀ := by
      calc χ₂ = 1 * χ₂ := (one_mul _).symm
        _ = (χ₀⁻¹ * χ₀) * χ₂ := by rw [inv_mul_cancel χ₀]
        _ = χ₀⁻¹ * (χ₀ * χ₂) := by rw [mul_assoc]
        _ = χ₀⁻¹ * 1 := by rw [hh]
        _ = χ₀⁻¹ := mul_one _
        _ = χ₀ := inv_eq_of_mul_eq_one_left hsq'
    exact hχ₂neχ₀ h2
  have hχ₁χ₂' : χ₀ * χ₂⁻¹ ≠ 1 := by
    intro hh
    have h2 : χ₀ = χ₂ := by
      calc χ₀ = χ₀ * 1 := (mul_one _).symm
        _ = χ₀ * (χ₂⁻¹ * χ₂) := by rw [inv_mul_cancel χ₂]
        _ = (χ₀ * χ₂⁻¹) * χ₂ := by rw [mul_assoc]
        _ = 1 * χ₂ := by rw [hh]
        _ = χ₂ := one_mul _
    exact hχ₂neχ₀ h2.symm
  have hneA : χ₀ * χ₂ ≠ χ₀ := by
    intro hh
    have h2 : χ₂ = 1 := by
      calc χ₂ = 1 * χ₂ := (one_mul _).symm
        _ = (χ₀⁻¹ * χ₀) * χ₂ := by rw [inv_mul_cancel χ₀]
        _ = χ₀⁻¹ * (χ₀ * χ₂) := by rw [mul_assoc]
        _ = χ₀⁻¹ * χ₀ := by rw [hh]
        _ = 1 := inv_mul_cancel χ₀
    exact hχ₂ne1 h2
  have hneB : χ₀ * χ₂⁻¹ ≠ χ₀ := by
    intro hh
    have h2 : χ₂⁻¹ = 1 := by
      calc χ₂⁻¹ = 1 * χ₂⁻¹ := (one_mul _).symm
        _ = (χ₀⁻¹ * χ₀) * χ₂⁻¹ := by rw [inv_mul_cancel χ₀]
        _ = χ₀⁻¹ * (χ₀ * χ₂⁻¹) := by rw [mul_assoc]
        _ = χ₀⁻¹ * χ₀ := by rw [hh]
        _ = 1 := inv_mul_cancel χ₀
    have h3 : χ₂ = 1 := by simpa using congrArg Inv.inv h2
    exact hχ₂ne1 h3
  -- the minimality hypothesis at the height cut-off `|ρ₂.im| + 1`
  have hminim' := hminimal
  -- the maximality transfers
  have hmaxA := maximalityOfMinimality χ₀ ρ₀ ρ₂ hρ₂re hlogpos hminim' (χ₀ * χ₂) hχ₁χ₂ hneA
  have hmaxB := maximalityOfMinimality χ₀ ρ₀ ρ₂ hρ₂re hlogpos hminim' (χ₀ * χ₂⁻¹) hχ₁χ₂' hneB
  have hmaxD := maximalityOfMinimality χ₀ ρ₀ ρ₂ hρ₂re hlogpos hminim' χ₂ hχ₂ne1 hχ₂neχ₀
  have hχ₀prim : χ₀.primitiveCharacter ≠ 1 := primitiveCharacter_ne_one χ₀ hχ₀ne1
  have hmaxC : ∀ u : ℂ, DirichletCharacter.LFunction χ₀.primitiveCharacter u = 0 →
      |u.im| ≤ |ρ₂.im| + 1 → u = (ρ₀.re : ℂ) ∨ u.re ≤ ρ₂.re := by
    intro u hu him
    by_cases hre : u.re ≤ 0
    · exact Or.inr (le_trans hre hρ₂re.le)
    · push_neg at hre
      have hre1 : u.re < 1 := by
        by_contra hc
        push_neg at hc
        exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ₀.primitiveCharacter
          (Or.inl hχ₀prim) hc) hu
      have hzm : Work.LinnikContract.zeroMult χ₀ u ≠ 0 :=
        (zeroMultTransfer χ₀ hχ₀ne1).2.2 u hu hre hre1
      by_cases hueq : u = ρ₀
      · left
        rw [hueq]
        apply Complex.ext <;> simp [him0]
      · right
        have hne : (χ₀, u) ≠ (χ₀, ρ₀) := by
          intro h
          exact hueq (Prod.mk.inj h).2
        have h := hminim' χ₀ u hχ₀ne1 hzm him hne
        rw [Work.LinnikContract.lamOf, Work.LinnikContract.lamOf] at h
        nlinarith [h, hlogpos]
  -- zeros of the (level-`q`) `L`-functions
  have hρ₀eq : (ρ₀.re : ℂ) = ρ₀ := by
    apply Complex.ext <;> simp [him0]
  have hzero₁ : DirichletCharacter.LFunction χ₀ (ρ₀.re : ℂ) = 0 := by
    rw [hρ₀eq]
    exact (zeroMultTransfer χ₀ hχ₀ne1).1 ρ₀ hzm₀
  have hzero₂ : DirichletCharacter.LFunction χ₂ ((ρ₂.re : ℂ) + (ρ₂.im : ℂ) * Complex.I) = 0 := by
    rw [Complex.re_add_im]
    exact (zeroMultTransfer χ₂ hχ₂ne1).1 ρ₂ hzm₂
  -- non-vanishing divisors of the completed `L`-functions of the primitive characters
  have hmemC : ρ₀ ∈ Metric.closedBall (0:ℂ) (|ρ₂.im| + 2) := by
    rw [Metric.mem_closedBall, dist_zero_right, ← hρ₀eq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hρ₀re]
    linarith [abs_nonneg ρ₂.im]
  have hdivC : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₀.primitiveCharacter)
      (Metric.closedBall (0:ℂ) (|ρ₂.im| + 2))) (ρ₀.re : ℂ) ≠ 0 := by
    rw [hρ₀eq]
    exact (zeroMultTransfer χ₀ hχ₀ne1).2.1 ρ₀ (|ρ₂.im| + 2) hzm₀ hmemC
  have hmemD : ρ₂ ∈ Metric.closedBall (0:ℂ) (|ρ₂.im| + 2) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    refine le_trans (Complex.norm_le_abs_re_add_abs_im ρ₂) ?_
    rw [abs_of_pos hρ₂re]
    linarith [abs_nonneg ρ₂.im, le_of_lt hρ₂re1]
  have hdivD : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₂.primitiveCharacter)
      (Metric.closedBall (0:ℂ) (|ρ₂.im| + 2))) ((ρ₂.re : ℂ) + (ρ₂.im : ℂ) * Complex.I) ≠ 0 := by
    rw [Complex.re_add_im]
    exact (zeroMultTransfer χ₂ hχ₂ne1).2.1 ρ₂ (|ρ₂.im| + 2) hzm₂ hmemD
  -- L52 inputs
  have H₁ : Commons.NumberTheory.Linnik.L52Hyp χ₀ 2 (1/64) (1/2) :=
    hL q hqqL χ₀ hχ₀ne1 (by norm_num) (by norm_num) (by norm_num)
  have H₂ : Commons.NumberTheory.Linnik.L52Hyp χ₂ 2 (1/64) (1/2) :=
    hL q hqqL χ₂ hχ₂ne1 (by norm_num) (by norm_num) (by norm_num)
  have H₃ : Commons.NumberTheory.Linnik.L52Hyp (χ₀ * χ₂) 2 (1/64) (1/2) :=
    hL q hqqL (χ₀ * χ₂) hχ₁χ₂ (by norm_num) (by norm_num) (by norm_num)
  have H₄ : Commons.NumberTheory.Linnik.L52Hyp (χ₀ * χ₂⁻¹) 2 (1/64) (1/2) :=
    hL q hqqL (χ₀ * χ₂⁻¹) hχ₁χ₂' (by norm_num) (by norm_num) (by norm_num)
  -- the window data
  have hlam₀div : 1 - ρ₀.re ≤ (1/100) / Real.log (q : ℝ) := by
    have h := hlam0
    rw [Work.LinnikContract.lamOf] at h
    rw [le_div_iff₀ hlogpos]
    linarith
  have hlam₂div : 1 - ρ₂.re ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) := by
    have h := hlecap
    rw [Work.LinnikContract.lamOf] at h
    rw [le_div_iff₀ hlogpos]
    linarith
  have hsqrtle : Real.sqrt (Real.log (Real.log (q : ℝ))) ≤ Real.log (q : ℝ) / 2 := by
    have h1 : Real.log (Real.log (q : ℝ)) ≤ (Real.log (q : ℝ))^2 / 4 := by
      have h2 : Real.log (Real.log (q : ℝ)) ≤ Real.log (q : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos hlogpos
      nlinarith [sq_nonneg (Real.log (q : ℝ) - 2)]
    have h3 : Real.sqrt ((Real.log (q : ℝ))^2 / 4) = Real.log (q : ℝ) / 2 := by
      rw [show (Real.log (q : ℝ))^2 / 4 = (Real.log (q : ℝ) / 2)^2 by ring,
        Real.sqrt_sq (by linarith)]
    calc Real.sqrt (Real.log (Real.log (q : ℝ)))
        ≤ Real.sqrt ((Real.log (q : ℝ))^2 / 4) := Real.sqrt_le_sqrt h1
      _ = Real.log (q : ℝ) / 2 := h3
  have hβ₁ : |1 - ρ₀.re| ≤ (1/2 : ℝ) := by
    rw [abs_of_pos (by linarith : (0:ℝ) < 1 - ρ₀.re)]
    have h2 : (1/100) / Real.log (q : ℝ) ≤ (1/2 : ℝ) := by
      rw [div_le_iff₀ hlogpos]; linarith
    linarith [hlam₀div, h2]
  have hβ₂ : |1 - ρ₂.re| ≤ (1/2 : ℝ) := by
    rw [abs_of_pos (by linarith : (0:ℝ) < 1 - ρ₂.re)]
    have h2 : Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) ≤ (1/2 : ℝ) := by
      rw [div_le_iff₀ hlogpos]; linarith
    linarith [hlam₂div, h2]
  have hβ₂β₁ : ρ₂.re ≤ ρ₀.re := by
    have h := hle
    rw [Work.LinnikContract.lamOf, Work.LinnikContract.lamOf] at h
    nlinarith [h, hlogpos]
  have hγ₂ := hbb
  have hpt₁ : |1 - ρ₀.re| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) := by
    rw [abs_of_pos (by linarith : (0:ℝ) < 1 - ρ₀.re)]
    have h2 : (1/100) / Real.log (q : ℝ)
        ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) :=
      div_le_div_of_nonneg_right (by linarith [hsqrtge]) hlogpos.le
    linarith [hlam₀div, h2]
  have hpt₂ : |1 - ρ₂.re| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) := by
    rw [abs_of_pos (by linarith : (0:ℝ) < 1 - ρ₂.re)]
    exact hlam₂div
  -- Heath-Brown Lemma 8.5 for our data
  have hfive := hT (q := q) hqqT χ₀ χ₂ hχ₀ne1 hχ₂ne1 hχ₂neχ₀ hχ₁χ₂ hχ₁χ₂'
    (β₁ := ρ₀.re) (β₂ := ρ₂.re) (γ₂ := ρ₂.im) hβ₁ hβ₂ hβ₂β₁ hγ₂ hpt₁ hpt₂
    hzero₁ hzero₂ hmaxA hmaxB hmaxC hmaxD hdivC hdivD H₁ H₂ H₃ H₄
  have hl2 : Real.log (q : ℝ) * (1 - ρ₂.re) = Work.LinnikContract.lamOf q ρ₂ := by
    rw [Work.LinnikContract.lamOf]; ring
  have hdiff : -((Real.log (q : ℝ) * (1 - ρ₀.re)) - (Real.log (q : ℝ) * (1 - ρ₂.re)))
      = Work.LinnikContract.lamOf q ρ₂ - Work.LinnikContract.lamOf q ρ₀ := by
    rw [Work.LinnikContract.lamOf, Work.LinnikContract.lamOf]; ring
  rw [hdiff, hl2] at hfive
  -- final rewriting of the tent integrals into the shape of the extractor
  have hrew1 : (∫ t in (0:ℝ)..32, Real.exp ((Work.LinnikContract.lamOf q ρ₂) * t) * max (32 - t) 0)
      = ∫ t in (0:ℝ)..32, Real.exp ((Work.LinnikContract.lamOf q ρ₂) * t) * (32 - t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 32)] at ht
    show Real.exp ((Work.LinnikContract.lamOf q ρ₂) * t) * max (32 - t) 0
      = Real.exp ((Work.LinnikContract.lamOf q ρ₂) * t) * (32 - t)
    rw [max_eq_left (by linarith [ht.2])]
  have hrew2 : (∫ t in (0:ℝ)..32,
        Real.exp ((Work.LinnikContract.lamOf q ρ₂ - Work.LinnikContract.lamOf q ρ₀) * t)
          * max (32 - t) 0)
      = ∫ t in (0:ℝ)..32,
          Real.exp ((Work.LinnikContract.lamOf q ρ₂ - Work.LinnikContract.lamOf q ρ₀) * t) * (32 - t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 32)] at ht
    show Real.exp ((Work.LinnikContract.lamOf q ρ₂ - Work.LinnikContract.lamOf q ρ₀) * t) * max (32 - t) 0
      = Real.exp ((Work.LinnikContract.lamOf q ρ₂ - Work.LinnikContract.lamOf q ρ₀) * t) * (32 - t)
    rw [max_eq_left (by linarith [ht.2])]
  have h32c : max (32 - (0:ℝ)) 0 = (32 : ℝ) := by
    rw [sub_zero]; exact max_eq_left (by norm_num)
  have hc : (3 : ℝ) * 2 + 4 * (1/64) = 97/16 := by norm_num
  rw [hrew1, hrew2, integral_tent32, h32c, hc] at hfive
  have hfive' : 0 ≤ (∫ t in (0:ℝ)..32, Real.exp ((Work.LinnikContract.lamOf q ρ₂) * t) * (32 - t))
      - (∫ t in (0:ℝ)..32, Real.exp ((Work.LinnikContract.lamOf q ρ₂ - Work.LinnikContract.lamOf q ρ₀) * t) * (32 - t))
      - 318 := by
    norm_num at hfive ⊢
    linarith [hfive]
  exact tent32Extract hfive'

end Work.OtherCharRepel
