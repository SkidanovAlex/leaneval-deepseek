import Mathlib
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.CzRowAuxDefs

namespace Work.ZeroDensity.Jutila.LzDiffAux.CzRowAux

open Finset

noncomputable section

/-- The arithmetic function `d ↦ (√d)⁻¹`. -/
private def sqrtInvArith : ArithmeticFunction ℝ :=
  ⟨fun n => (Real.sqrt (n : ℝ))⁻¹, by simp⟩

private lemma sqrtInvArith_apply (n : ℕ) :
    (sqrtInvArith : ℕ → ℝ) n = (Real.sqrt (n : ℝ))⁻¹ := rfl

private lemma sqrtInvArith_isMult : sqrtInvArith.IsMultiplicative := by
  refine ⟨?_, ?_⟩
  · rw [sqrtInvArith_apply, Nat.cast_one, Real.sqrt_one, inv_one]
  · intro m n _
    rw [sqrtInvArith_apply, sqrtInvArith_apply, sqrtInvArith_apply, Nat.cast_mul,
      Real.sqrt_mul (Nat.cast_nonneg m), mul_inv]

/-- `σ_{-1/2}(t)` factorises as `∏_{p ∣ t}(1 + p^{-1/2})` for squarefree `t`. -/
private lemma czSig_eq_prod {t : ℕ} (ht : Squarefree t) :
    Work.ZeroDensity.Jutila.BzCross.czSig t
      = ∏ p ∈ t.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)) := by
  have h := ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_add_of_squarefree
    (R := ℝ) sqrtInvArith_isMult ht
  have hsum : (∑ d ∈ t.divisors, sqrtInvArith d)
      = ∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ) := by
    apply Finset.sum_congr rfl
    intro d _
    rw [sqrtInvArith_apply, one_div]
  have hprod : (∏ p ∈ t.primeFactors, (1 + sqrtInvArith p))
      = ∏ p ∈ t.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)) := by
    apply Finset.prod_congr rfl
    intro p _
    rw [sqrtInvArith_apply, one_div]
  rw [Work.ZeroDensity.Jutila.BzCross.czSig]
  rw [← hsum, ← h, hprod]

/-- For squarefree `t`, `kap t / t = ∏_{p ∣ t}(1 + 1/p)`. -/
private lemma kap_div_eq_prod {t : ℕ} (ht : Squarefree t) :
    Work.ZeroDensity.Jutila.kap t / (t : ℝ)
      = ∏ p ∈ t.primeFactors, (1 + 1 / (p : ℝ)) := by
  have hprod : (∏ p ∈ t.primeFactors, (p : ℝ)) = (t : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree ht]
  rw [Work.ZeroDensity.Jutila.kap, ← hprod]
  rw [← Finset.prod_div_distrib (s := t.primeFactors)
    (f := fun p => ((p : ℝ) + 1)) (g := fun p => (p : ℝ))]
  apply Finset.prod_congr rfl
  intro p hp
  have hp0 : (p : ℝ) ≠ 0 := by
    have := (Nat.prime_of_mem_primeFactors hp).ne_zero
    exact_mod_cast this
  field_simp

lemma kap_div_le_czSig {t : ℕ} (ht : Squarefree t) (ht1 : 1 ≤ t) :
    Work.ZeroDensity.Jutila.kap t / (t : ℝ) ≤ Work.ZeroDensity.Jutila.BzCross.czSig t := by
  rw [kap_div_eq_prod ht, czSig_eq_prod ht]
  apply Finset.prod_le_prod₀
  · intro p hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by
      have h := (Nat.prime_of_mem_primeFactors hp).pos
      exact_mod_cast h
    have h1 : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
    linarith
  · intro p hp
    have hpprime : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      have h := hpprime.two_le
      exact_mod_cast h
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hspos : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hp0
    have hsle : Real.sqrt (p : ℝ) ≤ (p : ℝ) := by
      rw [Real.sqrt_le_iff]
      exact ⟨hp0.le, by nlinarith⟩
    have h := one_div_le_one_div_of_le hspos hsle
    linarith

end

end Work.ZeroDensity.Jutila.LzDiffAux.CzRowAux
