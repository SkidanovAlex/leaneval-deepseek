import Mathlib
import Submission.Work.LinnikAreas.BGTZSetup
import Submission.Work.LinnikAreas.HypAAux.prod_le_prod_Icc_of_card
import Submission.Work.LinnikAreas.HypAAux.prod_Icc_two_one_add_rpow_le_exp
import Submission.Commons.NumberTheory.Nat.pow_omega_le_const_mul_rpow
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_bound_third_of_burgess

/-!
# Hypothesis A on the critical line, for imprimitive characters

`Work.LinnikAreas.BGTZ.HypA A θ` bounds `‖L(1/2 + i t, ψ)‖ ≤ A·(N(1+|t|))^θ` for *primitive*
non-principal `ψ` of conductor `N`.  This file upgrades that to the form in which AREA 6 uses it:
for *every* non-principal `χ` modulo `q ≥ 3` (imprimitive included)

`‖L(1/2 + i t, χ)‖ ≤ C·A·q^θ·exp((log q)^{3/4})·(1+|t|)^θ`.

The reduction of `χ` to its primitive part `χ.primitiveCharacter` costs the Euler product
`∏_{p | q} (1 + p^{-1/2})`
(`Commons…LFunction_nonprimitive_le`), which is `≤ exp((log q)^{3/4})` — this is the sharp
`(log q)^{3/4}` form needed by the BGTZ argument (`Work.LinnikAreas.primeFactors_prod_one_add_rpow_le`),
reproved here from the two independent combinatorial/analytic pieces
`HypAAux.prod_le_prod_Icc_of_card` and `HypAAux.prod_Icc_two_one_add_rpow_le_exp`.
-/

open DirichletCharacter

namespace Work.LinnikAreas

/-- The Euler product of the prime divisors of `q` is at most `exp((log q)^{3/4})`.  This is the
specialisation `σ = 1/2` of the bound used in the Deuring--Heilbronn analysis, assembled from
`HypAAux.prod_le_prod_Icc_of_card` (the greedy majorant by the initial segment of the integers)
and `HypAAux.prod_Icc_two_one_add_rpow_le_exp` (`∏_{j ≤ k}(1+j^{-1/2}) ≤ exp((log k!)^{3/4})`),
together with `(ω(q)+1)! ≤ q`. -/
theorem prod_primeFactors_one_add_half_le (q : ℕ) (hq : 3 ≤ q) :
    ∏ p ∈ q.primeFactors, (1 + (p : ℝ) ^ (-(1 / 2 : ℝ)))
      ≤ Real.exp ((Real.log q) ^ (3 / 4 : ℝ)) := by
  have hcard1 : 1 ≤ q.primeFactors.card := by
    have hq0 : q ≠ 0 := by omega
    have hpq : (Nat.minFac q).Prime := Nat.minFac_prime (by omega : q ≠ 1)
    have hmem : Nat.minFac q ∈ q.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpq, Nat.minFac_dvd q, hq0⟩
    exact Finset.card_pos.mpr ⟨_, hmem⟩
  -- the product over the prime factors is dominated by the product over the initial segment
  have hstep2 : ∏ p ∈ q.primeFactors, (1 + (p : ℝ) ^ (-(1 / 2 : ℝ)))
      ≤ ∏ j ∈ Finset.Icc 2 (q.primeFactors.card + 1), (1 + (j : ℝ) ^ (-(1 / 2 : ℝ))) :=
    HypAAux.prod_le_prod_Icc_of_card
      (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
      (fun t => 1 + (t : ℝ) ^ (-(1 / 2 : ℝ)))
      (fun t => by positivity)
      (fun a b _ hab => by
        have ha' : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
        have hle : (b : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (a : ℝ) ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos ha' (by exact_mod_cast hab) (by norm_num)
        linarith)
  -- the analytic core: `∏_{j=2}^{ω+1}(1 + j^{-1/2}) ≤ exp((log (ω+1)!)^{3/4})`
  have hstep3 : ∏ j ∈ Finset.Icc 2 (q.primeFactors.card + 1), (1 + (j : ℝ) ^ (-(1 / 2 : ℝ)))
      ≤ Real.exp ((Real.log ((q.primeFactors.card + 1).factorial : ℝ)) ^ (3 / 4 : ℝ)) :=
    HypAAux.prod_Icc_two_one_add_rpow_le_exp q.primeFactors.card hcard1
  -- `(ω(q)+1)! ≤ q`
  have hq1 : 1 ≤ q := by omega
  have hfac : (q.primeFactors.card + 1).factorial ≤ q :=
    Commons.NumberTheory.Nat.factorial_card_primeFactors_le q hq1
  have hfacR : (((q.primeFactors.card + 1).factorial : ℕ) : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast hfac
  have hfacpos : (0 : ℝ) < (((q.primeFactors.card + 1).factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have hlog_le : Real.log (((q.primeFactors.card + 1).factorial : ℕ) : ℝ) ≤ Real.log (q : ℝ) :=
    Real.log_le_log hfacpos hfacR
  have hlog_nn : 0 ≤ Real.log (((q.primeFactors.card + 1).factorial : ℕ) : ℝ) :=
    Real.log_nonneg (by
      have h : 1 ≤ (q.primeFactors.card + 1).factorial := by
        have := Nat.factorial_pos (q.primeFactors.card + 1); omega
      exact_mod_cast h)
  have hpow_le : (Real.log (((q.primeFactors.card + 1).factorial : ℕ) : ℝ)) ^ (3 / 4 : ℝ)
      ≤ (Real.log (q : ℝ)) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow hlog_nn hlog_le (by norm_num)
  have hexp : Real.exp ((Real.log (((q.primeFactors.card + 1).factorial : ℕ) : ℝ)) ^ (3 / 4 : ℝ))
      ≤ Real.exp ((Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) := Real.exp_le_exp.mpr hpow_le
  exact hstep2.trans (hstep3.trans hexp)

theorem LFunction_half_line_hypA_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → 3 ≤ q →
      ∀ (A θ : ℝ), Work.LinnikAreas.BGTZ.HypA A θ → ∀ t : ℝ,
        ‖DirichletCharacter.LFunction χ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ C * A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ)) * (1 + |t|) ^ θ := by
  refine ⟨1, one_pos, ?_⟩
  intro q _inst χ hχ hq3 A θ hHyp t
  obtain ⟨hApos, hθpos, _hθle, hbound⟩ := hHyp
  -- pass from `χ` to its primitive part
  haveI hcond : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hprim : χ.primitiveCharacter.IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hprimne : χ.primitiveCharacter ≠ 1 :=
    Commons.NumberTheory.DirichletCharacter.primitiveCharacter_ne_one χ hχ
  have hpb := hbound χ.primitiveCharacter hprim hprimne t
  have hred := Commons.NumberTheory.DirichletCharacter.LFunction_nonprimitive_le χ hχ
    (σ := (1 / 2 : ℝ)) (t := t) (by norm_num)
  have hprod := prod_primeFactors_one_add_half_le q hq3
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have h1t : (0 : ℝ) ≤ 1 + |t| := by positivity
  have hNq : (χ.conductor : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hle : (χ.conductor : ℝ) * (1 + |t|) ≤ (q : ℝ) * (1 + |t|) :=
    mul_le_mul_of_nonneg_right hNq h1t
  have hpow : ((χ.conductor : ℝ) * (1 + |t|)) ^ θ ≤ ((q : ℝ) * (1 + |t|)) ^ θ :=
    Real.rpow_le_rpow (by positivity) hle hθpos.le
  have hmul : ((q : ℝ) * (1 + |t|)) ^ θ = (q : ℝ) ^ θ * (1 + |t|) ^ θ :=
    Real.mul_rpow hqpos.le h1t
  calc ‖DirichletCharacter.LFunction χ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ (∏ p ∈ q.primeFactors, (1 + (p : ℝ) ^ (-(1 / 2 : ℝ))))
          * ‖DirichletCharacter.LFunction χ.primitiveCharacter
              (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := hred
    _ ≤ Real.exp ((Real.log q) ^ (3 / 4 : ℝ))
          * (A * (((χ.conductor : ℝ) * (1 + |t|)) ^ θ)) :=
        mul_le_mul hprod hpb (norm_nonneg _) (Real.exp_pos _).le
    _ ≤ Real.exp ((Real.log q) ^ (3 / 4 : ℝ)) * (A * (((q : ℝ) * (1 + |t|)) ^ θ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hApos.le)
          (Real.exp_pos _).le
    _ = Real.exp ((Real.log q) ^ (3 / 4 : ℝ)) * (A * ((q : ℝ) ^ θ * (1 + |t|) ^ θ)) := by
        rw [hmul]
    _ = 1 * A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ)) * (1 + |t|) ^ θ := by
        ring

end Work.LinnikAreas
