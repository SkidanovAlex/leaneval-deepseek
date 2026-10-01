import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.LinnikAreas.OtherCharRepel.dhTrianglePtLocal
import Submission.Work.LinnikAreas.DhRepel.sameCharRepelNear
import Submission.Work.LinnikAreas.L52Hyp_of_partialFraction
import Submission.Work.LinnikAreas.DhCapped.SiegelSimple
import Submission.Work.LinnikAreas.OtherCharRepel.zeroMultTransfer
import Submission.Work.LinnikAreas.OtherCharRepel.zeroMultStripPos
import Submission.Work.LinnikAreas.log_unbounded_nat

namespace Work.LinnikAreas.OtherCharRepel

open DirichletCharacter Complex
open scoped Classical BigOperators

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

/-- Arithmetic: if `0 < a ≤ 1/100` and `log (1/a) ≤ 8b + log (64/3)` then `1/25 ≤ b`. -/
private lemma arith_repel25 {a b : ℝ} (ha0 : 0 < a) (ha : a ≤ 1 / 100)
    (h : Real.log (1 / a) ≤ 8 * b + Real.log (64 / 3)) : (1 / 25 : ℝ) ≤ b := by
  have h100 : (100 : ℝ) ≤ 1 / a := by
    have := one_div_le_one_div_of_le ha0 ha
    simpa using this
  have hlog100 : Real.log 100 ≤ Real.log (1 / a) := Real.log_le_log (by norm_num) h100
  have h75 : (8 : ℝ) / 25 ≤ Real.log (75 / 16) := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    calc Real.exp (8 / 25) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
      _ ≤ (3 : ℝ) := le_of_lt Real.exp_one_lt_three
      _ ≤ 75 / 16 := by norm_num
  have hsplit : Real.log 100 - Real.log (64 / 3) = Real.log (75 / 16) := by
    rw [← Real.log_div (by norm_num : (100:ℝ) ≠ 0) (by norm_num : (64/3:ℝ) ≠ 0)]
    norm_num
  linarith [hlog100, h, h75, hsplit]

/-- **Logarithmic same-character repulsion at a given second zero.** -/
private theorem sameCharRepelLogBound : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₀ : DirichletCharacter ℂ q) (ρ₀ ρ' : ℂ),
    Work.LinnikContract.IsMin1 χ₀ ρ₀ → χ₀ ^ 2 = 1 → ρ₀.im = 0 →
    Work.LinnikContract.lamOf q ρ₀ ≤ 1 / 100 →
    Work.LinnikContract.zeroMult χ₀ ρ' ≠ 0 → |ρ'.im| ≤ 1 → ρ' ≠ ρ₀ →
    (∀ (ψ : DirichletCharacter ℂ q) (u : ℂ), ψ ≠ 1 → Work.LinnikContract.zeroMult ψ u ≠ 0 →
      |u.im| ≤ |ρ'.im| + 1 → (ψ, u) ≠ (χ₀, ρ₀) →
        Work.LinnikContract.lamOf q ρ' ≤ Work.LinnikContract.lamOf q u) →
    Work.LinnikContract.lamOf q ρ' ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 →
    Real.log (1 / Work.LinnikContract.lamOf q ρ₀) ≤
      8 * Work.LinnikContract.lamOf q ρ' + Real.log (64 / 3) := by
  obtain ⟨q52, h52⟩ := Work.LinnikAreas.L52Hyp_of_partialFraction (1 / 4) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨qS, hS⟩ := Work.LinnikAreas.DhCapped.siegelZeroSimple'
  obtain ⟨qT, hT⟩ := dhTrianglePtLocal 8 (by norm_num) (1 / 4) (by norm_num) (1 / 2)
    (by norm_num) (by norm_num) 1
  obtain ⟨qL, hL⟩ := Work.LinnikAreas.log_unbounded_nat 100
  refine ⟨max (max (max q52 qS) qT) (max qL 2), ?_⟩
  intro q hq _inst χ₀ ρ₀ ρ' hmin hsq him0 h100 hzm him hne hminimal hcap
  have hq52 : q52 ≤ q := by omega
  have hqS : qS ≤ q := by omega
  have hqT : qT ≤ q := by omega
  have hqL : qL ≤ q := by omega
  have hlogq : (100 : ℝ) ≤ Real.log (q : ℝ) := hL q hqL
  have hlogq0 : (0 : ℝ) < Real.log (q : ℝ) := by linarith
  have hq2 : 2 ≤ q := by omega
  have hχ0 : χ₀ ≠ 1 := hmin.1.1
  have hzm0 : Work.LinnikContract.zeroMult χ₀ ρ₀ ≠ 0 := hmin.1.2.1
  haveI : NeZero χ₀.conductor := ⟨χ₀.conductor_ne_zero⟩
  have hρ0eq : ρ₀ = ((ρ₀.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him0]
  obtain ⟨hρ0re0, hρ0re1, hlam0pos⟩ :=
    Work.LinnikAreas.OtherCharRepel.zeroMultStripPos hq2 hχ0 hzm0
  have hρ0le : Work.LinnikContract.lamOf q ρ₀ ≤ Work.LinnikContract.lamOf q ρ' :=
    hmin.2 χ₀ ρ' ⟨hχ0, hzm, him⟩
  have hβ'β₁ : ρ'.re ≤ ρ₀.re := by
    have h := hρ0le
    rw [Work.LinnikContract.lamOf, Work.LinnikContract.lamOf] at h
    nlinarith [h, hlogq0]
  have hL3' : Work.LinnikContract.lamOf q ρ' ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 :=
    hcap
  have hloglog1 : (1 : ℝ) ≤ Real.log (Real.log (q : ℝ)) := by
    have h1 : Real.log 100 ≤ Real.log (Real.log (q : ℝ)) :=
      Real.log_le_log (by norm_num) hlogq
    have h2 : (1 : ℝ) ≤ Real.log 100 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      calc Real.exp 1 ≤ (2.7182818286 : ℝ) := le_of_lt Real.exp_one_lt_d9
        _ ≤ 100 := by norm_num
    linarith
  have hloglog4 : (4 : ℝ) ≤ Real.log (Real.log (q : ℝ)) := by
    have h1 : Real.log 100 ≤ Real.log (Real.log (q : ℝ)) := Real.log_le_log (by norm_num) hlogq
    have h2 : (4 : ℝ) ≤ Real.log 100 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have he : Real.exp 4 = Real.exp 1 ^ 4 := by
        rw [show (4:ℝ) = ((4:ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
      rw [he]
      calc (Real.exp 1) ^ 4 ≤ (2.7182818286 : ℝ) ^ 4 :=
            pow_le_pow_left₀ (Real.exp_pos 1).le (le_of_lt Real.exp_one_lt_d9) 4
        _ ≤ 100 := by norm_num
    linarith
  have hL3_sqrt : Real.log (Real.log (Real.log (q : ℝ))) / 3
      ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := by
    have h1 : Real.log (Real.log (Real.log (q : ℝ)))
        ≤ 2 * Real.sqrt (Real.log (Real.log (q : ℝ))) := by
      have h := Real.log_le_rpow_div (x := Real.log (Real.log (q : ℝ))) (ε := (1:ℝ)/2)
        (by linarith [hloglog1]) (by norm_num)
      have h2 : Real.log (Real.log (q : ℝ)) ^ ((1:ℝ)/2) / ((1:ℝ)/2)
          = 2 * Real.sqrt (Real.log (Real.log (q : ℝ))) := by
        rw [Real.sqrt_eq_rpow, div_eq_mul_inv, show ((1:ℝ)/2)⁻¹ = 2 by norm_num, mul_comm]
      linarith [h, h2.le, h2.ge]
    linarith [h1]
  have hL3_le : Work.LinnikContract.lamOf q ρ' ≤ Real.log (q : ℝ) / 2 := by
    have h1 : Real.log (Real.log (Real.log (q : ℝ))) ≤ Real.log (q : ℝ) := by
      have ha : Real.log (Real.log (Real.log (q : ℝ))) ≤ Real.log (Real.log (q : ℝ)) :=
        Real.log_le_self (le_trans (by norm_num) hloglog1)
      have hb : Real.log (Real.log (q : ℝ)) ≤ Real.log (q : ℝ) := Real.log_le_self hlogq0.le
      linarith
    linarith [hL3', h1]
  have hL3_big : (1 / 100 : ℝ) ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 := by
    have h1 : Real.log 4 ≤ Real.log (Real.log (Real.log (q : ℝ))) :=
      Real.log_le_log (by norm_num) hloglog4
    have h2 : (1 : ℝ) ≤ Real.log 4 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      calc Real.exp 1 ≤ (2.7182818286 : ℝ) := le_of_lt Real.exp_one_lt_d9
        _ ≤ 4 := by norm_num
    linarith
  have hmax' : ∀ u : ℂ, Work.LinnikContract.zeroMult χ₀ u ≠ 0 → |u.im| ≤ |ρ'.im| + 1 →
      u = ρ₀ ∨ Work.LinnikContract.lamOf q ρ' ≤ Work.LinnikContract.lamOf q u := by
    intro u hzmu himu
    by_cases hu : u = ρ₀
    · exact Or.inl hu
    · refine Or.inr ?_
      have hne1 : (χ₀, u) ≠ (χ₀, ρ₀) := by
        intro h
        exact hu (Prod.mk.inj h).2
      exact hminimal χ₀ u hχ0 hzmu himu hne1
  obtain ⟨hρ're0, hρ're1, hlam'pos⟩ :=
    Work.LinnikAreas.OtherCharRepel.zeroMultStripPos hq2 hχ0 hzm
  have hmaxL := Work.LinnikAreas.DhRepel.re_le_of_LFunction_zero_of_maximality χ₀ hχ0 hzm0 hzm hmax'
  have hmaxL' : ∀ u : ℂ, DirichletCharacter.LFunction χ₀.primitiveCharacter u = 0 →
      |u.im| ≤ |ρ'.im| + 1 → u = ((ρ₀.re : ℝ) : ℂ) ∨ u.re ≤ ρ'.re := by
    intro u h1 h2
    rcases hmaxL u h1 h2 with h | h
    · exact Or.inl (h.trans hρ0eq)
    · exact Or.inr h
  have hne'' : ρ' ≠ ((ρ₀.re : ℝ) : ℂ) := fun h => hne (h.trans hρ0eq.symm)
  have hb1 : (1 : ℝ) - ρ₀.re = Work.LinnikContract.lamOf q ρ₀ / Real.log (q : ℝ) := by
    rw [Work.LinnikContract.lamOf]; field_simp
  have hb2 : (1 : ℝ) - ρ'.re = Work.LinnikContract.lamOf q ρ' / Real.log (q : ℝ) := by
    rw [Work.LinnikContract.lamOf]; field_simp
  have hball' : ρ' ∈ Metric.closedBall (0 : ℂ) (|ρ'.im| + 2) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    refine le_trans (Complex.norm_le_abs_re_add_abs_im ρ') ?_
    have h1 : |ρ'.re| ≤ 2 := by
      rw [abs_le]
      exact ⟨by linarith [hρ're0], by linarith [hρ're1]⟩
    linarith [abs_nonneg ρ'.im]
  have hball1 : ((ρ₀.re : ℝ) : ℂ) ∈ Metric.closedBall (0 : ℂ) (|ρ'.im| + 2) := by
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> [linarith [abs_nonneg ρ'.im, hρ0re0]; linarith [abs_nonneg ρ'.im, hρ0re1]]
  have hdiv' : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₀.primitiveCharacter)
      (Metric.closedBall 0 (|ρ'.im| + 2))) ρ' ≠ 0 :=
    (Work.LinnikAreas.OtherCharRepel.zeroMultTransfer χ₀ hχ0).2.1 ρ' (|ρ'.im| + 2) hzm hball'
  have hdiv1 : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₀.primitiveCharacter)
      (Metric.closedBall 0 (|ρ'.im| + 2))) ((ρ₀.re : ℝ) : ℂ) ≠ 0 := by
    refine (Work.LinnikAreas.OtherCharRepel.zeroMultTransfer χ₀ hχ0).2.1 ((ρ₀.re : ℝ) : ℂ)
      (|ρ'.im| + 2) ?_ hball1
    rw [← hρ0eq]; exact hzm0
  have hmult1 : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₀.primitiveCharacter)
      (Metric.closedBall 0 (|ρ'.im| + 2))) ((ρ₀.re : ℝ) : ℂ) = 1 := by
    have hχ' : χ₀.primitiveCharacter ≠ 1 :=
      Work.LinnikAreas.OtherCharRepel.primitiveCharacter_ne_one χ₀ hχ0
    have han : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ₀.primitiveCharacter)
        (Metric.closedBall (0 : ℂ) (|ρ'.im| + 2)) :=
      fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ').analyticAt z
    rw [Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast han hball1]
    have hord : analyticOrderNatAt (DirichletCharacter.completedLFunction χ₀.primitiveCharacter)
        ((ρ₀.re : ℝ) : ℂ) = 1 := by
      have h := hS q hqS χ₀ ρ₀.re hχ0 hsq hρ0re1 (by rw [← hρ0eq]; exact hzm0)
        (by rw [← hρ0eq]; exact h100)
      simpa only [Work.LinnikContract.zeroMult] using h
    rw [hord]; rfl
  have hβ1 : |1 - ρ₀.re| ≤ (1 / 2 : ℝ) := by
    rw [abs_of_nonneg (by linarith [hρ0re1])]
    rw [hb1, div_le_iff₀ hlogq0]
    linarith
  have hβ' : |1 - ρ'.re| ≤ (1 / 2 : ℝ) := by
    rw [abs_of_nonneg (by linarith [hρ're1])]
    rw [hb2, div_le_iff₀ hlogq0]
    linarith
  have hβ1pt : |1 - ρ₀.re| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) := by
    rw [abs_of_nonneg (by linarith [hρ0re1]), hb1, div_le_div_iff_of_pos_right hlogq0]
    linarith [Real.one_le_sqrt.mpr hloglog1]
  have hρ'pt : |1 - ρ'.re| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) := by
    rw [abs_of_nonneg (by linarith [hρ're1]), hb2, div_le_div_iff_of_pos_right hlogq0]
    exact le_trans hL3' hL3_sqrt
  have hrect1 : Work.LinnikContract.lamOf q ((ρ₀.re : ℝ) : ℂ)
      ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 := by
    have h0 : Work.LinnikContract.lamOf q ρ₀ ≤ 1 / 100 := h100
    rw [hρ0eq] at h0
    exact le_trans h0 hL3_big
  have hrect' : Work.LinnikContract.lamOf q ρ'
      ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 := hL3'
  have H52 : Commons.NumberTheory.Linnik.L52Hyp χ₀ 1 (1 / 4) (1 / 2) :=
    h52 q hq52 χ₀ hχ0
  have htri := hT q hqT χ₀ hχ0 hsq hβ1 hβ' hβ'β₁ him hβ1pt hρ'pt
    hdiv1 hdiv' hne'' hmult1 hmaxL' hrect1 hrect' H52
  have htri' : 0 ≤ 2 * (∫ t in (0:ℝ)..8,
        Real.exp ((Work.LinnikContract.lamOf q ρ') * t) * (8 - t))
      - 2 * (∫ t in (0:ℝ)..8,
        Real.exp ((Work.LinnikContract.lamOf q ρ' - Work.LinnikContract.lamOf q ρ₀) * t) * (8 - t))
      - 8 ^ 2 / 2 + 3 * 8 := by
    have h1 : Work.LinnikContract.lamOf q ρ₀
        = Work.LinnikContract.lamOf q ((ρ₀.re : ℝ) : ℂ) := by rw [← hρ0eq]
    have h2 : (3 : ℝ) * 8 = (2 * (1:ℝ) + 4 * (1/4)) * 8 := by norm_num
    simpa only [h1, h2] using htri
  exact Work.LinnikAreas.DhRepel.sixArith8Gen hlam0pos hlam'pos htri'

theorem sameCharNonRealRepel : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₀ : DirichletCharacter ℂ q) (ρ₀ ρ' : ℂ),
    Work.LinnikContract.IsMin1 χ₀ ρ₀ → χ₀ ^ 2 = 1 → ρ₀.im = 0 →
    Work.LinnikContract.lamOf q ρ₀ ≤ 1 / 100 →
    Work.LinnikContract.zeroMult χ₀ ρ' ≠ 0 → |ρ'.im| ≤ 1 → ρ' ≠ ρ₀ → ρ'.im ≠ 0 →
    (∀ (ψ : DirichletCharacter ℂ q) (u : ℂ), ψ ≠ 1 → Work.LinnikContract.zeroMult ψ u ≠ 0 →
      |u.im| ≤ |ρ'.im| + 1 → (ψ, u) ≠ (χ₀, ρ₀) →
        Work.LinnikContract.lamOf q ρ' ≤ Work.LinnikContract.lamOf q u) →
    (1/25 : ℝ) ≤ Work.LinnikContract.lamOf q ρ' := by
  obtain ⟨qB, hB⟩ := sameCharRepelLogBound
  obtain ⟨qL, hL⟩ := Work.LinnikAreas.log_unbounded_nat (Real.exp (Real.exp (3 / 25)))
  refine ⟨max (max qB qL) 2, ?_⟩
  intro q hq hqne χ₀ ρ₀ ρ' hmin hsq him0 h100 hzm him hne himne hminimal
  have hqB : qB ≤ q := by omega
  have hqL : qL ≤ q := by omega
  have hq2 : 2 ≤ q := by omega
  have hlam0pos : 0 < Work.LinnikContract.lamOf q ρ₀ :=
    (Work.LinnikAreas.OtherCharRepel.zeroMultStripPos hq2 hmin.1.1 hmin.1.2.1).2.2
  by_cases hcap : Work.LinnikContract.lamOf q ρ' ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3
  · have hlog := hB q hqB χ₀ ρ₀ ρ' hmin hsq him0 h100 hzm him hne hminimal hcap
    exact arith_repel25 hlam0pos h100 hlog
  · push_neg at hcap
    have hlll : (1 : ℝ) / 25 ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 := by
      have hM : Real.exp (Real.exp (3 / 25)) ≤ Real.log (q : ℝ) := hL q hqL
      have hlogq0 : (0 : ℝ) < Real.log (q : ℝ) := by
        have : (0 : ℝ) < Real.exp (Real.exp (3 / 25)) := Real.exp_pos _
        linarith
      have hll : Real.exp (3 / 25) ≤ Real.log (Real.log (q : ℝ)) := by
        have h := Real.log_le_log (Real.exp_pos (Real.exp (3 / 25))) hM
        rwa [Real.log_exp] at h
      have hlll' : (3 : ℝ) / 25 ≤ Real.log (Real.log (Real.log (q : ℝ))) := by
        have h := Real.log_le_log (Real.exp_pos (3 / 25)) hll
        rwa [Real.log_exp] at h
      linarith
    linarith

end Work.LinnikAreas.OtherCharRepel
