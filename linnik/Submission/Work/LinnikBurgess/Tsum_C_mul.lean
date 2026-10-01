import Mathlib
import Submission.Work.LinnikBurgess.cubic_phase_defs

namespace Work.LinnikBurgess

open Polynomial Finset
open Commons.NumberTheory.GaussSum

/-! ## The scaling identity `Tsum (p^M) (C p * G) = p * Tsum (p^(M-1)) G`

The exponential `E N m = exp (2 π i m / N)` satisfies `E (p^M) (p * m) = E (p^(M-1)) m`,
so multiplying the phase `G` by `p` lowers the level by one `p`-adic power.  Since the
reduced phase `G` is `p^(M-1)`-periodic in the summation variable, the range
`0, …, p^M - 1` consists of `p` full blocks, giving the factor `p`. -/

/-- Lowering the level by one: `E (p^M) (p * m) = E (p^(M-1)) m`. -/
lemma E_mul_C (p M : ℕ) [NeZero p] (hM : 1 ≤ M) (m : ℤ) :
    E (p ^ M) ((p : ℤ) * m) = E (p ^ (M - 1)) m := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
  rw [E_exp, E_exp]
  have hpM : (p : ℂ) ^ (M - 1) * (p : ℂ) = (p : ℂ) ^ M := by
    calc (p : ℂ) ^ (M - 1) * (p : ℂ) = (p : ℂ) ^ (M - 1) * (p : ℂ) ^ 1 := by rw [pow_one]
      _ = (p : ℂ) ^ ((M - 1) + 1) := (pow_add _ _ _).symm
      _ = (p : ℂ) ^ M := by rw [Nat.sub_add_cancel hM]
  push_cast
  rw [← hpM]
  congr 1
  field_simp

/-- A `K`-periodic sum over `0, …, n*K - 1` is `n` times the sum over one period. -/
lemma sum_range_periodic (f : ℕ → ℂ) {K : ℕ} (hf : ∀ j, f (j + K) = f j) :
    ∀ n, ∑ j ∈ Finset.range (n * K), f j = (n : ℂ) * ∑ j ∈ Finset.range K, f j := by
  have hiter : ∀ i j, f (i * K + j) = f j := by
    intro i
    induction i with
    | zero => intro j; simp
    | succ i ih =>
      intro j
      have h : (i + 1) * K + j = (i * K + j) + K := by ring
      rw [h, hf, ih]
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit : (n + 1) * K = n * K + K := by ring
    rw [hsplit, Finset.sum_range_add]
    rw [Finset.sum_congr rfl (fun j _ => hiter n j), ih]
    push_cast
    ring

theorem Tsum_C_mul (p M : ℕ) [Fact p.Prime] (hM : 1 ≤ M) (G : Polynomial ℤ) :
    Commons.NumberTheory.GaussSum.Tsum (p ^ M) (Polynomial.C (p : ℤ) * G)
      = (p : ℂ) * Commons.NumberTheory.GaussSum.Tsum (p ^ (M - 1)) G := by
  have hterm : ∀ j, E (p ^ M) (Polynomial.eval ((j : ℕ) : ℤ) (Polynomial.C (p : ℤ) * G))
      = E (p ^ (M - 1)) (Polynomial.eval ((j : ℕ) : ℤ) G) := by
    intro j
    rw [Polynomial.eval_mul, Polynomial.eval_C]
    exact E_mul_C p M hM (Polynomial.eval (j : ℤ) G)
  have hperiod : ∀ j, E (p ^ (M - 1)) (Polynomial.eval (((j + p ^ (M - 1)) : ℕ) : ℤ) G)
      = E (p ^ (M - 1)) (Polynomial.eval ((j : ℕ) : ℤ) G) := by
    intro j
    refine E_eq_of_dvd_sub _ _ _ ?_
    have h := Polynomial.sub_dvd_eval_sub (((j + p ^ (M - 1) : ℕ) : ℤ)) ((j : ℕ) : ℤ) G
    have hcast : (((j + p ^ (M - 1) : ℕ) : ℤ)) - ((j : ℕ) : ℤ) = ((p ^ (M - 1) : ℕ) : ℤ) := by
      push_cast; ring
    rwa [hcast] at h
  have hmain : ∑ j ∈ Finset.range (p ^ M),
      E (p ^ M) (Polynomial.eval ((j : ℕ) : ℤ) (Polynomial.C (p : ℤ) * G))
      = (p : ℂ) * ∑ j ∈ Finset.range (p ^ (M - 1)),
          E (p ^ (M - 1)) (Polynomial.eval ((j : ℕ) : ℤ) G) := by
    rw [Finset.sum_congr rfl (fun j _ => hterm j)]
    have hpM : p * p ^ (M - 1) = p ^ M := by
      nth_rewrite 1 [← pow_one p]
      rw [← pow_add]
      congr 1; omega
    rw [← hpM]
    exact sum_range_periodic _ hperiod p
  rw [Commons.NumberTheory.GaussSum.Tsum, Commons.NumberTheory.GaussSum.Tsum, hmain]

end Work.LinnikBurgess
