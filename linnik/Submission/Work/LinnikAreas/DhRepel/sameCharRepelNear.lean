import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.LinnikAreas.DhRepel.dhTrianglePtH
import Submission.Work.LinnikAreas.DhRepel.witnessNear
import Submission.Work.LinnikAreas.boxMaxZero
import Submission.Work.LinnikAreas.DhCapped.SiegelSimple
import Submission.Work.LinnikAreas.L52Hyp_of_partialFraction
import Submission.Work.LinnikAreas.repelPsiSubLe
import Submission.Work.LinnikAreas.repelPsiEval
import Submission.Work.LinnikAreas.log_unbounded_nat
import Submission.Work.LinnikAreas.OtherCharRepel.zeroMultTransfer
import Submission.Work.LinnikAreas.OtherCharRepel.zeroMultStripPos

open DirichletCharacter Complex
open scoped Classical BigOperators

namespace Work.LinnikAreas.DhRepel

/-- **The `x = 8`, `C = 3` arithmetic of the §6 triangle, with no side condition between the two
`λ`s.**  `Work.LinnikAreas.sixArith8` requires `λ₀ ≤ λ₂`; the only place that hypothesis is used in
the proof of `sixArith` is to know `0 < λ₂`.  Since here `λ₂ = λ(ρ') > 0` comes from the critical
strip, we may drop it, which is what lets the §6 inequality be applied to a test zero of *any*
`λ ≤ λ(ρ)`, without first settling whether `λ(ρ') ≥ λ(ρ₀)`.

The proof is that of `sixArith`/`sixArith8` verbatim, with the positivity of `λ₂` taken as a
hypothesis. -/
theorem sixArith8Gen {lam₀ lam₂ : ℝ} (hlam₀ : 0 < lam₀) (hlam₂ : 0 < lam₂)
    (h6 : 0 ≤ 2 * (∫ t in (0:ℝ)..8, Real.exp (lam₂ * t) * (8 - t))
        - 2 * (∫ t in (0:ℝ)..8, Real.exp ((lam₂ - lam₀) * t) * (8 - t))
        - 8 ^ 2 / 2 + 3 * 8) :
    Real.log (1 / lam₀) ≤ 8 * lam₂ + Real.log (64 / 3) := by
  have hx : (0:ℝ) < 8 := by norm_num
  have hx0 : (0:ℝ) ≤ 8 := le_of_lt hx
  have h6psi : 0 ≤ 2 * (8^2 * repelPsi (lam₂ * 8)) - 2 * (8^2 * repelPsi ((lam₂ - lam₀) * 8))
      - 8^2/2 + 3*8 := by
    rw [repelPsiEval 8 lam₂ hx0, repelPsiEval 8 (lam₂ - lam₀) hx0] at h6
    linarith [h6]
  have hr : (8 - 2*3)/(4*8) ≤ repelPsi (lam₂*8) - repelPsi ((lam₂-lam₀)*8) := by
    have hmain : (8^2/2 - 3*8)/(2*8^2) ≤ repelPsi (lam₂*8) - repelPsi ((lam₂-lam₀)*8) := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 2*8^2)]
      linarith [h6psi]
    have heq : (8^2/2 - 3*8)/(2*8^2) = (8-2*(3:ℝ))/(4*8) := by norm_num
    linarith [hmain, heq]
  have hAu : repelPsi (lam₂*8) - repelPsi ((lam₂-lam₀)*8)
      ≤ lam₀ * (8*Real.exp (lam₂*8) / 6) := by
    have h := repelPsiSubLe (u := lam₂*8) (w := lam₀*8)
      (mul_nonneg hlam₂.le hx0) (mul_nonneg hlam₀.le hx0)
    have harg : lam₂*8 - lam₀*8 = (lam₂-lam₀)*8 := by ring
    rw [harg] at h
    refine le_trans h (le_of_eq ?_)
    ring
  have hbound : (8 - 2*(3:ℝ))/(4*8) ≤ lam₀ * (8*Real.exp (lam₂*8) / 6) := le_trans hr hAu
  have hEpos : 0 < 8 * Real.exp (lam₂*8) / 6 := by positivity
  have hstep : (8 - 2*(3:ℝ))/(4*8) / (8 * Real.exp (lam₂*8) / 6) ≤ lam₀ :=
    (div_le_iff₀ hEpos).mpr hbound
  have hval : (8 - 2*(3:ℝ))/(4*8) / (8 * Real.exp (lam₂*8) / 6)
      = 3 / 64 * Real.exp (-(8*lam₂)) := by
    rw [show Real.exp (-(8*lam₂)) = (Real.exp (lam₂*8))⁻¹ by rw [← Real.exp_neg]; ring_nf]
    field_simp
    ring
  have hfin : 3 / 64 * Real.exp (-(8 * lam₂)) ≤ lam₀ := by
    rw [← hval]; exact hstep
  have h2 : Real.log (3 / 64 * Real.exp (-(8*lam₂))) ≤ Real.log lam₀ :=
    Real.log_le_log (by positivity) hfin
  have h3 : Real.log (3 / 64 * Real.exp (-(8*lam₂)))
      = Real.log (3/64) + (-(8*lam₂)) := by
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
  have h4 : Real.log (1/lam₀) = -Real.log lam₀ := by
    rw [one_div, Real.log_inv]
  rw [h3] at h2
  have h5 : Real.log (3/64) = -Real.log (64/3) := by
    rw [show (3:ℝ)/64 = (64/3)⁻¹ by norm_num, Real.log_inv]
  rw [h5] at h2
  rw [h4]
  linarith [h2]

/-- **Converting the "ball maximality" of the witness into the maximality hypothesis of the §6
triangle.**  If every `zeroMult`-zero `u ≠ ρ₀` of `χ₀` of height `|Im u| ≤ Hb` satisfies
`λ(ρ') ≤ λ(u)`, then every *ordinary* zero `u` of `L(·,χ₀*)` of height `≤ Hb` is either `ρ₀` or has
`Re u ≤ Re ρ'`.  (A zero of `L(·,χ₀*)` with `Re u ≤ 0` is trivial, since `Re ρ' > 0` by the
critical strip; otherwise `u` is a `zeroMult`-zero.) -/
theorem re_le_of_LFunction_zero_of_maximality {q : ℕ} [NeZero q] (χ₀ : DirichletCharacter ℂ q)
    [NeZero χ₀.conductor]
    {ρ₀ ρ' : ℂ} {Hb : ℝ} (hχ₀ : χ₀ ≠ 1) (hzm₀ : Work.LinnikContract.zeroMult χ₀ ρ₀ ≠ 0)
    (hzm' : Work.LinnikContract.zeroMult χ₀ ρ' ≠ 0)
    (hmax : ∀ u : ℂ, Work.LinnikContract.zeroMult χ₀ u ≠ 0 → |u.im| ≤ Hb →
      u = ρ₀ ∨ Work.LinnikContract.lamOf q ρ' ≤ Work.LinnikContract.lamOf q u) :
    ∀ u : ℂ, DirichletCharacter.LFunction χ₀.primitiveCharacter u = 0 → |u.im| ≤ Hb →
      u = ρ₀ ∨ u.re ≤ ρ'.re := by
  intro u hzero him
  by_cases h : u = ρ₀
  · exact Or.inl h
  · refine Or.inr ?_
    have hq2 : 2 ≤ q := by
      by_contra hq
      have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
      have hq1 : q = 1 := by omega
      exact hχ₀ (DirichletCharacter.level_one' χ₀ hq1)
    have hρ're : 0 < ρ'.re := (Work.LinnikAreas.OtherCharRepel.zeroMultStripPos hq2 hχ₀ hzm').1
    by_cases hre : u.re ≤ 0
    · linarith
    · have hpos : 0 < u.re := not_le.mp hre
      have hstrip : u.re < 1 := by
        -- `u` is a zero of the completed `L`-function, hence lies in the critical strip
        have hγ : χ₀.primitiveCharacter.gammaFactor u ≠ 0 :=
          Work.LinnikAreas.OtherCharRepel.gammaFactor_ne_zero_of_re_pos _ hpos
        have hu0 : u ≠ 0 := by rintro rfl; simp at hpos
        have hcomp : DirichletCharacter.completedLFunction χ₀.primitiveCharacter u = 0 := by
          rw [Work.LinnikAreas.OtherCharRepel.completedLFunction_eq_LFunction_mul_gammaFactor
            χ₀.primitiveCharacter u (Or.inl hu0) hγ, hzero, zero_mul]
        exact (Commons.NumberTheory.Linnik.completedL_zero_strip χ₀.primitiveCharacter
          (Work.LinnikAreas.OtherCharRepel.primitiveCharacter_ne_one χ₀ hχ₀)
          (DirichletCharacter.primitiveCharacter_isPrimitive χ₀) hcomp).2
      have hzmu : Work.LinnikContract.zeroMult χ₀ u ≠ 0 :=
        (Work.LinnikAreas.OtherCharRepel.zeroMultTransfer χ₀ hχ₀).2.2 u hzero hpos hstrip
      rcases hmax u hzmu him with h' | h'
      · exact absurd h' h
      · rw [Work.LinnikContract.lamOf, Work.LinnikContract.lamOf] at h'
        have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
        nlinarith [h', hlog]

/-- The near-regime repulsion, given the `§6` witness `ρ'` (with its box height) supplied by
`Work.LinnikAreas.DhRepel.witnessOfCount`.  This is the common body of the two wrappers below. -/
theorem sameCharRepelNear_of_witness
    (hWitness : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ₀ : DirichletCharacter ℂ q) (ρ₀ ρ : ℂ),
      Work.LinnikContract.IsMin1 χ₀ ρ₀ → χ₀ ^ 2 = 1 → ρ₀.im = 0 →
      Work.LinnikContract.lamOf q ρ₀ ≤ 1 / 100 →
      Work.LinnikContract.zeroMult χ₀ ρ ≠ 0 → |ρ.im| ≤ 1 → ρ ≠ ρ₀ →
      Work.LinnikContract.lamOf q ρ ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 →
      ∃ (ρ' : ℂ) (Hb : ℝ), Work.LinnikContract.zeroMult χ₀ ρ' ≠ 0 ∧ ρ' ≠ ρ₀ ∧
        |ρ'.im| ≤ 10 * Real.log (q : ℝ) ∧ |ρ'.im| + 1 / 2 ≤ Hb ∧
        Work.LinnikContract.lamOf q ρ' ≤ Work.LinnikContract.lamOf q ρ ∧
        (∀ u : ℂ, Work.LinnikContract.zeroMult χ₀ u ≠ 0 → |u.im| ≤ Hb →
          u = ρ₀ ∨ Work.LinnikContract.lamOf q ρ' ≤ Work.LinnikContract.lamOf q u)) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₀ : DirichletCharacter ℂ q) (ρ₀ : ℂ),
    Work.LinnikContract.IsMin1 χ₀ ρ₀ → χ₀ ^ 2 = 1 → ρ₀.im = 0 →
    Work.LinnikContract.lamOf q ρ₀ ≤ 1 / 100 →
    ∀ ρ : ℂ, Work.LinnikContract.zeroMult χ₀ ρ ≠ 0 → |ρ.im| ≤ 1 → ρ ≠ ρ₀ →
      Work.LinnikContract.lamOf q ρ ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 →
      Real.log (1 / Work.LinnikContract.lamOf q ρ₀) ≤
        8 * Work.LinnikContract.lamOf q ρ + Real.log (64 / 3) := by
  obtain ⟨qW, hW⟩ := hWitness
  obtain ⟨q52, h52⟩ := L52Hyp_of_partialFraction (1 / 4) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨qS, hS⟩ := DhCapped.siegelZeroSimple'
  obtain ⟨qT, hT⟩ := dhTrianglePtH 8 (by norm_num) (1 / 4) (by norm_num) (1 / 2)
    (by norm_num) (by norm_num) 1
  obtain ⟨qL, hL⟩ := Work.LinnikAreas.log_unbounded_nat 100
  refine ⟨max (max (max (max qW q52) qS) qT) (max qL 2), ?_⟩
  intro q hq _inst χ₀ ρ₀ hmin hsq him0 h100 ρ hzm him hne hcap
  have hqW : qW ≤ q := by omega
  have hq52 : q52 ≤ q := by omega
  have hqS : qS ≤ q := by omega
  have hqT : qT ≤ q := by omega
  have hqL : qL ≤ q := by omega
  have hlogq : (100 : ℝ) ≤ Real.log (q : ℝ) := hL q hqL
  have hlogq0 : (0 : ℝ) < Real.log (q : ℝ) := by linarith
  have hq2 : 2 ≤ q := by omega
  -- basic facts
  have hχ0 : χ₀ ≠ 1 := hmin.1.1
  have hzm0 : Work.LinnikContract.zeroMult χ₀ ρ₀ ≠ 0 := hmin.1.2.1
  haveI : NeZero χ₀.conductor := ⟨χ₀.conductor_ne_zero⟩
  have hρ0eq : ρ₀ = ((ρ₀.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him0]
  obtain ⟨hρ0re0, hρ0re1, hlam0pos⟩ :=
    Work.LinnikAreas.OtherCharRepel.zeroMultStripPos hq2 hχ0 hzm0
  have hρ0le : Work.LinnikContract.lamOf q ρ₀ ≤ Work.LinnikContract.lamOf q ρ :=
    hmin.2 χ₀ ρ ⟨hχ0, hzm, him⟩
  have hL3 : Work.LinnikContract.lamOf q ρ ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 := hcap
  -- numerical facts
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
  have hL3_le : Work.LinnikContract.lamOf q ρ ≤ Real.log (q : ℝ) / 2 := by
    have h1 : Real.log (Real.log (Real.log (q : ℝ))) ≤ Real.log (q : ℝ) := by
      have ha : Real.log (Real.log (Real.log (q : ℝ))) ≤ Real.log (Real.log (q : ℝ)) :=
        Real.log_le_self (le_trans (by norm_num) hloglog1)
      have hb : Real.log (Real.log (q : ℝ)) ≤ Real.log (q : ℝ) := Real.log_le_self hlogq0.le
      linarith
    linarith [hL3, h1]
  have hL3_sqrt : Real.log (Real.log (Real.log (q : ℝ))) / 3
      ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := by
    have h1 : Real.log (Real.log (Real.log (q : ℝ))) ≤ 2 * Real.sqrt (Real.log (Real.log (q : ℝ))) := by
      have h := Real.log_le_rpow_div (x := Real.log (Real.log (q : ℝ))) (ε := (1:ℝ)/2)
        (by linarith [hloglog1]) (by norm_num)
      have h2 : Real.log (Real.log (q : ℝ)) ^ ((1:ℝ)/2) / ((1:ℝ)/2)
          = 2 * Real.sqrt (Real.log (Real.log (q : ℝ))) := by
        rw [Real.sqrt_eq_rpow, div_eq_mul_inv, show ((1:ℝ)/2)⁻¹ = 2 by norm_num, mul_comm]
      linarith [h, h2.le, h2.ge]
    linarith [h1]
  have hL3_big : (1 / 100 : ℝ) ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 := by
    have h1 : Real.log 4 ≤ Real.log (Real.log (Real.log (q : ℝ))) :=
      Real.log_le_log (by norm_num) hloglog4
    have h2 : (1 : ℝ) ≤ Real.log 4 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      calc Real.exp 1 ≤ (2.7182818286 : ℝ) := le_of_lt Real.exp_one_lt_d9
        _ ≤ 4 := by norm_num
    linarith
  -- the witness
  obtain ⟨ρ', Hb, hzm', hne', him10, hmargin, hlamle, hmax'⟩ :=
    hW q hqW χ₀ ρ₀ ρ hmin hsq him0 h100 hzm him hne hcap
  have hne'' : ρ' ≠ ((ρ₀.re : ℝ) : ℂ) := fun h => hne' (h.trans hρ0eq.symm)
  obtain ⟨hρ're0, hρ're1, hlam'pos⟩ :=
    Work.LinnikAreas.OtherCharRepel.zeroMultStripPos hq2 hχ0 hzm'
  have hL3' : Work.LinnikContract.lamOf q ρ' ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 :=
    le_trans hlamle hL3
  -- maximality in `L`-function form
  have hmaxL := re_le_of_LFunction_zero_of_maximality χ₀ hχ0 hzm0 hzm' hmax'
  have hmaxL' : ∀ u : ℂ, DirichletCharacter.LFunction χ₀.primitiveCharacter u = 0 →
      |u.im| ≤ Hb → u = ((ρ₀.re : ℝ) : ℂ) ∨ u.re ≤ ρ'.re := by
    intro u h1 h2
    rcases hmaxL u h1 h2 with h | h
    · exact Or.inl (h.trans hρ0eq)
    · exact Or.inr h
  -- the `λ ↔ Re` dictionary
  have hb1 : (1 : ℝ) - ρ₀.re = Work.LinnikContract.lamOf q ρ₀ / Real.log (q : ℝ) := by
    rw [Work.LinnikContract.lamOf]; field_simp
  have hb2 : (1 : ℝ) - ρ'.re = Work.LinnikContract.lamOf q ρ' / Real.log (q : ℝ) := by
    rw [Work.LinnikContract.lamOf]; field_simp
  -- divisor facts
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
    (Work.LinnikAreas.OtherCharRepel.zeroMultTransfer χ₀ hχ0).2.1 ρ' (|ρ'.im| + 2) hzm' hball'
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
  -- point / rectangle conditions
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
  -- the §6 triangle
  have htri := hT q hqT χ₀ hχ0 hsq hβ1 hβ' hmargin him10 hβ1pt hρ'pt
    hdiv1 hdiv' hne'' hmult1 hmaxL' hrect1 hrect' H52
  -- arithmetic
  have htri' : 0 ≤ 2 * (∫ t in (0:ℝ)..8,
        Real.exp ((Work.LinnikContract.lamOf q ρ') * t) * (8 - t))
      - 2 * (∫ t in (0:ℝ)..8,
        Real.exp ((Work.LinnikContract.lamOf q ρ' - Work.LinnikContract.lamOf q ρ₀) * t) * (8 - t))
      - 8 ^ 2 / 2 + 3 * 8 := by
    have h1 : Work.LinnikContract.lamOf q ρ₀
        = Work.LinnikContract.lamOf q ((ρ₀.re : ℝ) : ℂ) := by rw [← hρ0eq]
    have h2 : (3 : ℝ) * 8 = (2 * (1:ℝ) + 4 * (1/4)) * 8 := by norm_num
    simpa only [h1, h2] using htri
  have hfin := sixArith8Gen hlam0pos hlam'pos htri'
  have hlast : 8 * Work.LinnikContract.lamOf q ρ' + Real.log (64 / 3)
      ≤ 8 * Work.LinnikContract.lamOf q ρ + Real.log (64 / 3) := by linarith
  exact le_trans hfin hlast


/-- **The near regime of the same-character Deuring–Heilbronn repulsion, in logarithmic form.**
This is the requested statement.  It is derived here from `Work.LinnikAreas.DhRepel.witnessNear`
(the `λ`-minimal test zero of the §6 triangle, whose existence is the single input the §6 route
needs beyond the material proved in this directory). -/
theorem sameCharRepelNear : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₀ : DirichletCharacter ℂ q) (ρ₀ : ℂ),
    Work.LinnikContract.IsMin1 χ₀ ρ₀ → χ₀ ^ 2 = 1 → ρ₀.im = 0 →
    Work.LinnikContract.lamOf q ρ₀ ≤ 1 / 100 →
    ∀ ρ : ℂ, Work.LinnikContract.zeroMult χ₀ ρ ≠ 0 → |ρ.im| ≤ 1 → ρ ≠ ρ₀ →
      Work.LinnikContract.lamOf q ρ ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 →
      Real.log (1 / Work.LinnikContract.lamOf q ρ₀) ≤
        8 * Work.LinnikContract.lamOf q ρ + Real.log (64 / 3) :=
  sameCharRepelNear_of_witness witnessNear


end Work.LinnikAreas.DhRepel

