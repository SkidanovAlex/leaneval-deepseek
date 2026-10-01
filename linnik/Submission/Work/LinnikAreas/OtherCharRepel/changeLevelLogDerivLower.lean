import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.LinnikAreas.OtherCharRepel.LFunction_eq_primitiveCharacter_mul
import Submission.Work.LinnikAreas.OtherCharRepel.localFactorReLower
import Submission.Work.LinnikAreas.OtherCharRepel.sumPrimeFactorsLogLeLog

namespace Work.LinnikAreas.OtherCharRepel

open DirichletCharacter

/-- **The imprimitivity correction to `Re(L'/L)`.**  There is an absolute constant `C > 0` such that for every modulus `q`, every non-principal `χ` modulo `q` and every real `σ` with `1 < σ ≤ 5/4`, `Re(L'/L)(σ, χ*) - C·(log q + 1) ≤ Re(L'/L)(σ, χ)`, where `χ* = χ.primitiveCharacter` is the primitive character inducing `χ`. (Ingredients already on disk: Mathlib's `DirichletCharacter.LFunction_changeLevel`, and the sibling file `Submission/Work/LinnikAreas/OtherCharRepel/LFunction_eq_primitiveCharacter_mul.lean`.) -/
theorem changeLevelLogDerivLower :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
      χ ≠ 1 → ∀ σ : ℝ, 1 < σ → σ ≤ 5 / 4 →
      (logDeriv (DirichletCharacter.LFunction χ.primitiveCharacter) (σ : ℂ)).re
        - C * (Real.log (q : ℝ) + 1) ≤
        (logDeriv (DirichletCharacter.LFunction χ) (σ : ℂ)).re := by
  refine ⟨1, one_pos, ?_⟩
  intro q _ χ _ hχ σ hσ1 hσ2
  -- the primitive character inducing a non-principal character is non-principal
  have hstar : χ.primitiveCharacter ≠ 1 := by
    intro h
    exact hχ (by rw [← changeLevel_primitiveCharacter (χ := χ), h]; exact changeLevel_one _)
  -- the "imprimitivity" factor `G`, obtained from `LFunction_changeLevel`
  set G : ℂ → ℂ := fun s => ∏ p ∈ q.primeFactors,
      (1 - χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-s)) with hGdef
  have hPrim : ∀ s, DirichletCharacter.LFunction χ s
      = DirichletCharacter.LFunction χ.primitiveCharacter s * G s := by
    intro s
    rw [hGdef]
    exact LFunction_eq_primitiveCharacter_mul χ hχ s
  -- differentiability of the individual `cpow` factors
  have hcpowdiff : ∀ (p : ℕ) (hp : p ∈ q.primeFactors),
      DifferentiableAt ℂ (fun z : ℂ => (p : ℂ) ^ (-z)) (σ : ℂ) := by
    intro p hp
    exact ((hasDerivAt_neg (σ : ℂ)).const_cpow
      (Or.inl (by exact_mod_cast (Nat.pos_of_mem_primeFactors hp).ne'))).differentiableAt
  have hGd : DifferentiableAt ℂ G (σ : ℂ) := by
    rw [hGdef]
    refine DifferentiableAt.fun_finsetProd fun p hp => ?_
    exact (differentiableAt_const (1 : ℂ)).sub
      ((differentiableAt_const _).mul (hcpowdiff p hp))
  -- the factor `G (σ)` does not vanish: each local factor is `1 - z` with `‖z‖ ≤ 1/2`
  have hGne : G (σ : ℂ) ≠ 0 := by
    rw [hGdef, Finset.prod_ne_zero_iff]
    intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have hb : ‖χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-(σ : ℂ))‖ ≤ 1 / 2 := by
      rw [norm_mul]
      have h1 : ‖χ.primitiveCharacter (p : ZMod χ.conductor)‖ ≤ 1 := norm_le_one _ _
      have h2 : ‖(p : ℂ) ^ (-(σ : ℂ))‖ ≤ 1 / 2 := by
        rw [Complex.norm_natCast_cpow_of_pos (by linarith : 0 < p)]
        simp only [Complex.neg_re, Complex.ofReal_re]
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (by linarith : 1 ≤ p)
        have h2' : (p : ℝ) ^ (-σ) ≤ (p : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
        have h3 : (p : ℝ) ^ (-1 : ℝ) ≤ 1 / 2 := by
          rw [Real.rpow_neg_one, ← one_div]
          exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hp2)
        linarith
      nlinarith [norm_nonneg (χ.primitiveCharacter (p : ZMod χ.conductor)),
        norm_nonneg ((p : ℂ) ^ (-(σ : ℂ)))]
    intro hzero
    rw [sub_eq_zero] at hzero
    rw [← hzero, norm_one] at hb
    norm_num at hb
  have hLne : DirichletCharacter.LFunction χ.primitiveCharacter (σ : ℂ) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ.primitiveCharacter
      (Or.inr (by simp; linarith)) (by simp; linarith)
  have hLd : DifferentiableAt ℂ (DirichletCharacter.LFunction χ.primitiveCharacter) (σ : ℂ) :=
    DirichletCharacter.differentiableAt_LFunction χ.primitiveCharacter (σ : ℂ)
      (Or.inl (by simp; linarith))
  -- the multiplicative identity, differentiated logarithmically
  have hstep : logDeriv (DirichletCharacter.LFunction χ) (σ : ℂ)
      = logDeriv (DirichletCharacter.LFunction χ.primitiveCharacter) (σ : ℂ)
        + logDeriv G (σ : ℂ) := by
    rw [show DirichletCharacter.LFunction χ
        = fun s => DirichletCharacter.LFunction χ.primitiveCharacter s * G s from
      funext hPrim]
    exact logDeriv_mul (σ : ℂ) hLne hGne hLd hGd
  have hGlog : logDeriv G (σ : ℂ) = ∑ p ∈ q.primeFactors,
      logDeriv (fun z : ℂ =>
        1 - χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-z)) (σ : ℂ) := by
    rw [hGdef]
    refine Eq.trans ?_ (logDeriv_prod (f := fun (p : ℕ) (z : ℂ) =>
      1 - χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-z)) (fun p hp => ?_) (fun p hp => ?_))
    · rw [Finset.prod_fn]
    · have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
      have hb : ‖χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-(σ : ℂ))‖ ≤ 1 / 2 := by
        rw [norm_mul]
        have h1 : ‖χ.primitiveCharacter (p : ZMod χ.conductor)‖ ≤ 1 := norm_le_one _ _
        have h2 : ‖(p : ℂ) ^ (-(σ : ℂ))‖ ≤ 1 / 2 := by
          rw [Complex.norm_natCast_cpow_of_pos (by linarith : 0 < p)]
          simp only [Complex.neg_re, Complex.ofReal_re]
          have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (by linarith : 1 ≤ p)
          have h2' : (p : ℝ) ^ (-σ) ≤ (p : ℝ) ^ (-1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
          have h3 : (p : ℝ) ^ (-1 : ℝ) ≤ 1 / 2 := by
            rw [Real.rpow_neg_one, ← one_div]
            exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hp2)
          linarith
        nlinarith [norm_nonneg (χ.primitiveCharacter (p : ZMod χ.conductor)),
          norm_nonneg ((p : ℂ) ^ (-(σ : ℂ)))]
      intro hzero
      rw [sub_eq_zero] at hzero
      rw [← hzero, norm_one] at hb
      norm_num at hb
    · exact (differentiableAt_const (1 : ℂ)).sub ((differentiableAt_const _).mul (hcpowdiff p hp))
  -- each summand is bounded below by `-log p`
  have hterms : ∀ p ∈ q.primeFactors,
      -(Real.log p) ≤ (logDeriv (fun z : ℂ =>
        1 - χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-z)) (σ : ℂ)).re :=
    fun p hp => localFactorReLower p (Nat.prime_of_mem_primeFactors hp) _
      (norm_le_one _ _) σ hσ1
  have hsum : -(∑ p ∈ q.primeFactors, Real.log (p : ℝ)) ≤ (logDeriv G (σ : ℂ)).re := by
    rw [hGlog, Complex.re_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum hterms
  have hGbound : -(Real.log (q : ℝ)) ≤ (logDeriv G (σ : ℂ)).re := by
    refine le_trans ?_ hsum
    rw [neg_le_neg_iff]
    exact sumPrimeFactorsLogLeLog q (NeZero.ne q)
  rw [hstep, Complex.add_re]
  linarith

end Work.LinnikAreas.OtherCharRepel
