import Mathlib
import Submission.Work.LinnikAreas.OtherCharRepel.lemma85pt
import Submission.Work.LinnikAreas.OtherCharRepel.cosSqTheta
import Submission.Work.LinnikAreas.OtherCharRepel.l52HypTwo
import Submission.Work.LinnikAreas.DhRepel.extremalPackage
import Submission.Work.LinnikAreas.DhRepel.extCosFtestProps
import Submission.Work.LinnikAreas.OtherCharRepel.zeroMultTransfer
import Submission.Work.LinnikAreas.OtherCharRepel.zeroMultStripPos
import Submission.Work.LinnikContract.Defs

namespace Work.LinnikAreas.OtherCharRepel

set_option maxHeartbeats 4000000

open DirichletCharacter Complex MeasureTheory
open scoped Classical BigOperators

/-- Auxiliary: `30` is a modulus threshold guaranteeing `3 ≤ log q`. -/
private lemma log_thirty_le {q : ℕ} (hq : 30 ≤ q) : (3 : ℝ) ≤ Real.log (q : ℝ) := by
  have hq' : (30 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hexp3 : Real.exp 3 ≤ (30 : ℝ) := by
    calc Real.exp 3 = (Real.exp 1) ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ 3 ^ 3 := pow_le_pow_left₀ (Real.exp_pos 1).le (le_of_lt Real.exp_one_lt_three) 3
      _ ≤ 30 := by norm_num
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  rw [Real.le_log_iff_exp_le hqpos]
  exact le_trans hexp3 hq'


/-- Transfer from the minimality of `ρ₂` (among `zeroMult`-zeros of non-principal characters) to
the maximal-real-part statement for zeros of the ordinary `L`-function of a primitive character.
(Private copy of `Work.LinnikAreas.OtherCharRepel.maximalityOfMinimality`.) -/
private theorem maximalityAux {q : ℕ} [NeZero q] (χ₀ : DirichletCharacter ℂ q)
    (ρ₀ ρ₂ : ℂ) (hβ₂pos : 0 < ρ₂.re) (hlogq : 0 < Real.log q)
    (hmin : ∀ (ψ : DirichletCharacter ℂ q) (u : ℂ), ψ ≠ 1 → Work.LinnikContract.zeroMult ψ u ≠ 0 →
      |u.im| ≤ |ρ₂.im| + 1 → (ψ, u) ≠ (χ₀, ρ₀) →
        Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q u)
    (ψ : DirichletCharacter ℂ q) (hψ : ψ ≠ 1) (hne : ψ ≠ χ₀) [NeZero ψ.conductor] :
    ∀ u : ℂ, DirichletCharacter.LFunction ψ.primitiveCharacter u = 0 →
      |u.im| ≤ |ρ₂.im| + 1 → u.re ≤ ρ₂.re := by
  intro u hu him
  by_cases hre : u.re ≤ 0
  · exact le_trans hre hβ₂pos.le
  · push_neg at hre
    have hre1 : u.re < 1 := by
      by_contra hc
      push_neg at hc
      exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ.primitiveCharacter
        (Or.inl (primitiveCharacter_ne_one ψ hψ)) hc) hu
    have hzm : Work.LinnikContract.zeroMult ψ u ≠ 0 :=
      (zeroMultTransfer ψ hψ).2.2 u hu hre hre1
    have hneq : (ψ, u) ≠ (χ₀, ρ₀) := by
      intro h
      exact hne (Prod.mk.inj h).1
    have h := hmin ψ u hψ hzm him hneq
    rw [Work.LinnikContract.lamOf, Work.LinnikContract.lamOf] at h
    nlinarith [h, hlogq]

theorem dhApply85 : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₀ : DirichletCharacter ℂ q) (ρ₀ : ℂ) (χ₂ : DirichletCharacter ℂ q) (ρ₂ : ℂ),
    Work.LinnikContract.IsMin1 χ₀ ρ₀ → χ₀ ^ 2 = 1 → ρ₀.im = 0 →
    Work.LinnikContract.lamOf q ρ₀ ≤ 1 / 100 →
    χ₂ ≠ 1 → χ₂ ≠ χ₀ →
    Work.LinnikContract.zeroMult χ₂ ρ₂ ≠ 0 →
    Work.LinnikContract.lamOf q ρ₀ ≤ Work.LinnikContract.lamOf q ρ₂ →
    Work.LinnikContract.lamOf q ρ₂ ≤ 1 →
    |ρ₂.im| + 1 ≤ 10 * Real.log (q : ℝ) →
    (∀ (ψ : DirichletCharacter ℂ q) (u : ℂ), ψ ≠ 1 → Work.LinnikContract.zeroMult ψ u ≠ 0 →
      |u.im| ≤ |ρ₂.im| + 1 → (ψ, u) ≠ (χ₀, ρ₀) →
        Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q u) →
    (1/25 : ℝ) ≤ Work.LinnikContract.lamOf q ρ₂ := by
  -- the extremal test-function package of Heath-Brown §7
  obtain ⟨θ, κ, hθ0, hθπ2, heq, hκpos, hf0pos, hfnn, hcont, hsupp, hFnn, hlap, hκbound⟩ :=
    Work.LinnikAreas.DhRepel.extremalPackage
  have hcosgt : (49/200 : ℝ) < Real.cos θ ^ 2 := cosSqTheta θ hθ0 hθπ2 heq
  -- the test function `f = extCosF θ (1/25)` and its support bound
  let f : ℝ → ℝ := fun t => Commons.NumberTheory.Linnik.extCosF θ (1/25) t
  let x₀ : ℝ := 2 * (θ / ((1/25) * Real.tan θ))
  have hx₀pos : 0 < x₀ := by
    have htan : 0 < Real.tan θ := Real.tan_pos_of_pos_of_lt_pi_div_two hθ0 hθπ2
    dsimp only [x₀]
    positivity
  obtain ⟨hf2X, B, hBndX⟩ :=
    Work.LinnikAreas.DhRepel.extCosFtestProps (θ := θ) (lam := (1/25 : ℝ)) hθ0 hθπ2 (by norm_num)
  have hBndX' : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ max B 0 :=
    fun t ht => le_trans (hBndX t ht) (le_max_left _ _)
  have hcontX : ContinuousOn f (Set.Ici 0) := hcont (1/25) (by norm_num)
  have hsuppX : ∀ t : ℝ, x₀ ≤ t → f t = 0 := fun t ht => hsupp (1/25) (by norm_num) t ht
  have hf0X : 0 < f 0 := hf0pos (1/25) (by norm_num)
  have hfnnX : ∀ t : ℝ, 0 ≤ f t := by
    intro t
    by_cases ht : 0 ≤ t
    · exact hfnn (1/25) (by norm_num) t ht
    · have hz : Commons.NumberTheory.Linnik.extCosF θ (1/25) t = 0 := by
        rw [Commons.NumberTheory.Linnik.extCosF, if_neg (by intro h; exact absurd h.1 (not_le.mpr (not_le.mp ht)))]
      change 0 ≤ Commons.NumberTheory.Linnik.extCosF θ (1/25) t
      rw [hz]
  have hFX : ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)).re :=
    hFnn (1/25) (by norm_num)
  -- Heath-Brown Lemma 8.5 in point-condition form, with the fixed test function `f`
  obtain ⟨qT, hT⟩ := lemma85pt x₀ (max B 0) 2 hx₀pos (le_max_right B 0)
    (f := f) hcontX hsuppX hf2X hBndX' hf0X hfnnX hFX
    (ε := (1/64 : ℝ)) (by norm_num) (δ := (1/2 : ℝ)) (by norm_num) (by norm_num)
  -- Heath-Brown's Lemma 3.1 with the explicit constant `2`
  obtain ⟨qL, hL⟩ := l52HypTwo
  refine ⟨max (max qT qL) 30, ?_⟩
  intro q hq _inst χ₀ ρ₀ χ₂ ρ₂ hmin1 hsq him0 hlam0 hχ₂ne1 hχ₂neχ₀ hzm₂ hle20 hlam21 hgamma hminimal
  have hqqT : qT ≤ q := by omega
  have hqqL : qL ≤ q := by omega
  have hq30 : 30 ≤ q := by omega
  have hq2 : 2 ≤ q := by omega
  have hq1 : 1 < q := by omega
  have hlogq3 : (3 : ℝ) ≤ Real.log (q : ℝ) := log_thirty_le hq30
  have hlogqpos : 0 < Real.log (q : ℝ) := by linarith
  -- conductor instances
  letI : NeZero χ₀.conductor := ⟨χ₀.conductor_ne_zero⟩
  letI : NeZero χ₂.conductor := ⟨χ₂.conductor_ne_zero⟩
  letI : NeZero (χ₀ * χ₂).conductor := ⟨(χ₀ * χ₂).conductor_ne_zero⟩
  letI : NeZero (χ₀ * χ₂⁻¹).conductor := ⟨(χ₀ * χ₂⁻¹).conductor_ne_zero⟩
  -- basic data about the two zeros
  have hχ₀ne1 : χ₀ ≠ 1 := hmin1.1.1
  have hzm₀ : Work.LinnikContract.zeroMult χ₀ ρ₀ ≠ 0 := hmin1.1.2.1
  have hstrip₀ := zeroMultStripPos hq2 hχ₀ne1 hzm₀
  have hstrip₂ := zeroMultStripPos hq2 hχ₂ne1 hzm₂
  obtain ⟨hρ₀re, hρ₀re1, hlam₀pos⟩ := hstrip₀
  obtain ⟨hρ₂re, hρ₂re1, hlam₂pos⟩ := hstrip₂
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
  -- the maximality transfers
  have hmaxA := maximalityAux χ₀ ρ₀ ρ₂ hρ₂re hlogqpos hminimal (χ₀ * χ₂) hχ₁χ₂ hneA
  have hmaxB := maximalityAux χ₀ ρ₀ ρ₂ hρ₂re hlogqpos hminimal (χ₀ * χ₂⁻¹) hχ₁χ₂' hneB
  have hmaxD := maximalityAux χ₀ ρ₀ ρ₂ hρ₂re hlogqpos hminimal χ₂ hχ₂ne1 hχ₂neχ₀
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
        have h := hminimal χ₀ u hχ₀ne1 hzm him hne
        rw [Work.LinnikContract.lamOf, Work.LinnikContract.lamOf] at h
        nlinarith [h, hlogqpos]
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
  -- by contradiction
  by_contra hcon
  rw [not_le] at hcon
  have hle25 : Work.LinnikContract.lamOf q ρ₂ ≤ 1/25 := le_of_lt hcon
  -- the window radius conditions
  have hlam₀div : 1 - ρ₀.re ≤ (1/100) / Real.log (q : ℝ) := by
    have h := hlam0
    rw [Work.LinnikContract.lamOf] at h
    rw [le_div_iff₀ hlogqpos]
    nlinarith [h]
  have hlam₂div : 1 - ρ₂.re ≤ (1/25) / Real.log (q : ℝ) := by
    have h := hcon
    rw [Work.LinnikContract.lamOf] at h
    rw [le_div_iff₀ hlogqpos]
    nlinarith [h]
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := by
    have hloglog1 : (1 : ℝ) ≤ Real.log (Real.log (q : ℝ)) := by
      rw [Real.le_log_iff_exp_le hlogqpos]
      calc Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
        _ ≤ Real.log (q : ℝ) := hlogq3
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    simpa using hloglog1
  have hβ₁ : |1 - ρ₀.re| ≤ (1/2 : ℝ) := by
    rw [abs_of_pos (by linarith : (0:ℝ) < 1 - ρ₀.re)]
    have h2 : (1/100) / Real.log (q : ℝ) ≤ 1/2 := by
      rw [div_le_iff₀ hlogqpos]; linarith
    linarith [hlam₀div, h2]
  have hβ₂ : |1 - ρ₂.re| ≤ (1/2 : ℝ) := by
    rw [abs_of_pos (by linarith : (0:ℝ) < 1 - ρ₂.re)]
    have h2 : (1/25) / Real.log (q : ℝ) ≤ 1/2 := by
      rw [div_le_iff₀ hlogqpos]; linarith
    linarith [hlam₂div, h2]
  have hβ₂β₁ : ρ₂.re ≤ ρ₀.re := by
    have h := hle20
    rw [Work.LinnikContract.lamOf, Work.LinnikContract.lamOf] at h
    nlinarith [h, hlogqpos]
  have hpt₁ : |1 - ρ₀.re| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) := by
    rw [abs_of_pos (by linarith : (0:ℝ) < 1 - ρ₀.re)]
    have h2 : (1/100) / Real.log (q : ℝ)
        ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) :=
      div_le_div_of_nonneg_right (le_trans (by norm_num) hsqrt1) hlogqpos.le
    linarith [hlam₀div, h2]
  have hpt₂ : |1 - ρ₂.re| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) := by
    rw [abs_of_pos (by linarith : (0:ℝ) < 1 - ρ₂.re)]
    have h2 : (1/25) / Real.log (q : ℝ)
        ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) :=
      div_le_div_of_nonneg_right (le_trans (by norm_num) hsqrt1) hlogqpos.le
    linarith [hlam₂div, h2]
  -- Heath-Brown Lemma 8.5 for our data
  have hfive := hT (q := q) hqqT χ₀ χ₂ hχ₀ne1 hχ₂ne1 hχ₂neχ₀ hχ₁χ₂ hχ₁χ₂'
    (β₁ := ρ₀.re) (β₂ := ρ₂.re) (γ₂ := ρ₂.im) hβ₁ hβ₂ hβ₂β₁ hgamma hpt₁ hpt₂
    hzero₁ hzero₂ hmaxA hmaxB hmaxC hmaxD hdivC hdivD H₁ H₂ H₃ H₄
  have hl2 : Real.log (q : ℝ) * (1 - ρ₂.re) = Work.LinnikContract.lamOf q ρ₂ := by
    rw [Work.LinnikContract.lamOf]; ring
  have hdiff : -((Real.log (q : ℝ) * (1 - ρ₀.re)) - (Real.log (q : ℝ) * (1 - ρ₂.re)))
      = Work.LinnikContract.lamOf q ρ₂ - Work.LinnikContract.lamOf q ρ₀ := by
    rw [Work.LinnikContract.lamOf, Work.LinnikContract.lamOf]; ring
  rw [hdiff, hl2] at hfive
  -- integrability and the two monotonicity comparisons
  have hcontu : ContinuousOn f (Set.uIcc (0:ℝ) x₀) :=
    hcontX.mono (fun x hx => by rw [Set.uIcc_of_le hx₀pos.le] at hx; exact hx.1)
  have hint1 : IntervalIntegrable f volume (0:ℝ) x₀ := hcontu.intervalIntegrable
  have hHge : (∫ t in (0:ℝ)..x₀, f t)
      ≤ ∫ t in (0:ℝ)..x₀, Real.exp ((Work.LinnikContract.lamOf q ρ₂ - Work.LinnikContract.lamOf q ρ₀) * t) * f t := by
    apply intervalIntegral.integral_mono_on hx₀pos.le hint1
    · apply ContinuousOn.intervalIntegrable
      fun_prop
    · intro t ht
      have hexp : 1 ≤ Real.exp ((Work.LinnikContract.lamOf q ρ₂ - Work.LinnikContract.lamOf q ρ₀) * t) :=
        Real.one_le_exp (mul_nonneg (by linarith [hle20]) ht.1)
      calc f t = 1 * f t := by ring
        _ ≤ Real.exp ((Work.LinnikContract.lamOf q ρ₂ - Work.LinnikContract.lamOf q ρ₀) * t) * f t :=
            mul_le_mul_of_nonneg_right hexp (hfnnX t)
  have hGle : (∫ t in (0:ℝ)..x₀, Real.exp ((Work.LinnikContract.lamOf q ρ₂) * t) * f t)
      ≤ ∫ t in (0:ℝ)..x₀, Real.exp ((1/25) * t) * f t := by
    apply intervalIntegral.integral_mono_on hx₀pos.le
    · apply ContinuousOn.intervalIntegrable
      fun_prop
    · apply ContinuousOn.intervalIntegrable
      fun_prop
    · intro t ht
      have hexp : Real.exp ((Work.LinnikContract.lamOf q ρ₂) * t) ≤ Real.exp ((1/25) * t) :=
        Real.exp_le_exp.mpr (by nlinarith [ht.1, hle25])
      exact mul_le_mul_of_nonneg_right hexp (hfnnX t)
  have hident : (∫ t in (0:ℝ)..x₀, Real.exp ((1/25) * t) * f t)
      - 2 * (∫ t in (0:ℝ)..x₀, f t) = -(1/(1/25)) * f 0 * Real.cos θ ^ 2 :=
    hlap (1/25) (by norm_num)
  -- the numerical conclusion
  have hkey : 0 ≤ -(1/(1/25)) * f 0 * Real.cos θ ^ 2 + f 0 * (3 * 2 + 4 * (1/64)) := by
    have h2 : (∫ t in (0:ℝ)..x₀, Real.exp ((Work.LinnikContract.lamOf q ρ₂) * t) * f t)
        - (∫ t in (0:ℝ)..x₀, Real.exp ((Work.LinnikContract.lamOf q ρ₂ - Work.LinnikContract.lamOf q ρ₀) * t) * f t)
        - (∫ t in (0:ℝ)..x₀, f t) + f 0 * (3 * 2 + 4 * (1/64))
        ≤ (∫ t in (0:ℝ)..x₀, Real.exp ((1/25) * t) * f t)
          - 2 * (∫ t in (0:ℝ)..x₀, f t) + f 0 * (3 * 2 + 4 * (1/64)) := by
      linarith [hHge, hGle]
    rw [hident] at h2
    linarith [hfive, h2]
  have hc2 : (49/200 : ℝ) < Real.cos θ ^ 2 := hcosgt
  have h25 : (49/8 : ℝ) < 25 * Real.cos θ ^ 2 := by nlinarith [hc2]
  nlinarith [hkey, h25, hf0X]

end Work.LinnikAreas.OtherCharRepel
