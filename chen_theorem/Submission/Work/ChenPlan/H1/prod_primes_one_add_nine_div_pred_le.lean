import Mathlib
import Submission.Commons.NumberTheory.Sieve.sum_primes_recip_le_loglog

open scoped BigOperators

namespace Work.ChenPlan.H1

/-! ## Two elementary telescoping lemmas

`∑_{2 ≤ n < M} 1/(n(n-1)) ≤ 1`: summing `1/(n(n-1)) = 1/(n-1) - 1/n` telescopes. -/

private lemma tel_range (N : ℕ) :
    (∑ k ∈ Finset.range N, ((1:ℝ)/((k:ℝ)+1) - 1/((k:ℝ)+2))) = 1 - 1/((N:ℝ)+1) := by
  induction N with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      field_simp
      ring

private lemma sum_Ico_inv_mul_pred_le_one (M : ℕ) (hM : 2 ≤ M) :
    (∑ n ∈ Finset.Ico 2 M, (1:ℝ)/((n:ℝ)*((n:ℝ)-1))) ≤ 1 := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hterm : ∀ k : ℕ, (1:ℝ)/((((2+k:ℕ)):ℝ)*((((2+k:ℕ)):ℝ)-1))
      = ((1:ℝ)/((k:ℝ)+1) - 1/((k:ℝ)+2)) := by
    intro k
    have h0 : (((2+k:ℕ)):ℝ) = (k:ℝ)+2 := by push_cast; ring
    have h1 : ((k:ℝ)+1) ≠ 0 := by positivity
    have h2 : ((k:ℝ)+2) ≠ 0 := by positivity
    have h3 : ((k:ℝ)+2) - 1 = (k:ℝ)+1 := by ring
    rw [h0, h3]
    field_simp
    ring
  rw [Finset.sum_congr rfl (fun k (_ : k ∈ Finset.range (M - 2)) => hterm k)]
  rw [tel_range (M - 2)]
  have hcast : ((M - 2 : ℕ) : ℝ) = (M:ℝ) - 2 := by
    rw [Nat.cast_sub hM]; norm_num
  rw [hcast]
  have hM2 : (2:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
  have hnn : (0:ℝ) ≤ 1/((M:ℝ)-2+1) := by
    apply div_nonneg zero_le_one; linarith
  linarith

/-- Mertens-type upper bound for the Euler factor `1 + 9/(p-1)`: the product over the primes
`p ≤ N` is `≤ C (log N)^9`.

A proof can use the Euler–Mertens reciprocal bound
`Commons.NumberTheory.Sieve.sum_primes_recip_le_loglog`
(`∃ C > 0, ∀ N ≥ 2, Σ_{p ∈ Nat.primesBelow N} 1/p ≤ log log N + C`), the elementary
`1/(p-1) ≤ 1/p + 1/(p(p-1))` with `Σ_{p} 1/(p(p-1)) ≤ 1`, and `1 + y ≤ exp y` /
`(1 + 9/(p-1)) ≤ (1 + 1/(p-1))^9`. -/
theorem prod_primes_one_add_nine_div_pred_le :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      (∏ p ∈ Nat.primesBelow (N + 1), (1 + 9 / ((p : ℝ) - 1))) ≤ C * (Real.log (N : ℝ)) ^ 9 := by
  obtain ⟨A, _hA0, hA⟩ := Commons.NumberTheory.Sieve.sum_primes_recip_le_loglog
  refine ⟨Real.exp (9 * (A + 1)) * 512, by positivity, ?_⟩
  intro N hN
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  -- ## Step 1: the product is bounded by the exponential of `9 Σ 1/(p-1)`.
  have hprod_le_exp : (∏ p ∈ Nat.primesBelow (N+1), (1 + 9/((p:ℝ)-1)))
      ≤ Real.exp (9 * ∑ p ∈ Nat.primesBelow (N+1), 1/((p:ℝ)-1)) := by
    have hstep : (∏ p ∈ Nat.primesBelow (N+1), (1 + 9/((p:ℝ)-1)))
        ≤ ∏ p ∈ Nat.primesBelow (N+1), Real.exp (9 * (1/((p:ℝ)-1))) := by
      apply Finset.prod_le_prod₀
      · intro p hp
        have hp2 : 2 ≤ p := Nat.two_le_of_mem_primesBelow hp
        have hp1 : (1:ℝ) < (p:ℝ) := by exact_mod_cast (by omega : 1 < p)
        have hpos : (0:ℝ) < (p:ℝ)-1 := by linarith
        have hq : (0:ℝ) < 9/((p:ℝ)-1) := div_pos (by norm_num) hpos
        linarith
      · intro p hp
        have hp2 : 2 ≤ p := Nat.two_le_of_mem_primesBelow hp
        have hp1 : (1:ℝ) < (p:ℝ) := by exact_mod_cast (by omega : 1 < p)
        have hpos : (0:ℝ) < (p:ℝ)-1 := by linarith
        have h := Real.add_one_le_exp (9 * (1/((p:ℝ)-1)))
        have heq : (1:ℝ) + 9/((p:ℝ)-1) = 9 * (1/((p:ℝ)-1)) + 1 := by ring
        rw [heq]
        exact h
    refine le_trans hstep (le_of_eq ?_)
    calc (∏ p ∈ Nat.primesBelow (N+1), Real.exp (9 * (1/((p:ℝ)-1))))
        = Real.exp (∑ p ∈ Nat.primesBelow (N+1), 9 * (1/((p:ℝ)-1))) :=
          (Real.exp_sum _ _).symm
      _ = Real.exp (9 * ∑ p ∈ Nat.primesBelow (N+1), 1/((p:ℝ)-1)) := by
          congr 1
          rw [Finset.mul_sum]
  -- ## Step 2: `Σ 1/(p-1) ≤ log log (N+1) + A + 1`, splitting off the telescoping correction.
  have hdecomp : (∑ p ∈ Nat.primesBelow (N+1), 1/((p:ℝ)-1))
      = (∑ p ∈ Nat.primesBelow (N+1), 1/(p:ℝ))
        + ∑ p ∈ Nat.primesBelow (N+1), 1/((p:ℝ)*((p:ℝ)-1)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have hp2 : 2 ≤ p := Nat.two_le_of_mem_primesBelow hp
    have hp0 : (p:ℝ) ≠ 0 := by positivity
    have hp1 : ((p:ℝ)-1) ≠ 0 := by
      have : (1:ℝ) < (p:ℝ) := by exact_mod_cast (by omega : 1 < p)
      linarith
    field_simp
    ring
  have hcorr : (∑ p ∈ Nat.primesBelow (N+1), 1/((p:ℝ)*((p:ℝ)-1))) ≤ 1 := by
    have hsub : Nat.primesBelow (N+1) ⊆ Finset.Ico 2 (N+1) := by
      intro p hp
      rw [Finset.mem_Ico]
      exact ⟨Nat.two_le_of_mem_primesBelow hp, (Nat.mem_primesBelow.mp hp).1⟩
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_)
      (sum_Ico_inv_mul_pred_le_one (N+1) (by omega))
    intro p hp _
    simp only [Finset.mem_Ico] at hp
    have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.1
    have hpos : (0:ℝ) < (p:ℝ)*((p:ℝ)-1) := by nlinarith
    exact div_nonneg zero_le_one hpos.le
  have hsum : (∑ p ∈ Nat.primesBelow (N+1), 1/((p:ℝ)-1))
      ≤ Real.log (Real.log ((N+1:ℕ):ℝ)) + A + 1 := by
    have h1 := hA (N+1) (by omega)
    rw [hdecomp]
    linarith
  have hexp : Real.exp (9 * ∑ p ∈ Nat.primesBelow (N+1), 1/((p:ℝ)-1))
      ≤ Real.exp (9 * (Real.log (Real.log ((N+1:ℕ):ℝ)) + A + 1)) :=
    Real.exp_le_exp.mpr (by nlinarith [hsum])
  have hlogM : 0 < Real.log (((N+1:ℕ)):ℝ) := by
    apply Real.log_pos; exact_mod_cast (by omega : 1 < N+1)
  -- ## Step 3: identify the exponential with `(log (N+1))^9`.
  have hrewrite : Real.exp (9 * (Real.log (Real.log ((N+1:ℕ):ℝ)) + A + 1))
      = Real.exp (9*(A+1)) * (Real.log ((N+1:ℕ):ℝ))^9 := by
    rw [show 9 * (Real.log (Real.log ((N+1:ℕ):ℝ)) + A + 1)
          = 9 * Real.log (Real.log ((N+1:ℕ):ℝ)) + 9 * (A+1) from by ring]
    rw [Real.exp_add]
    rw [show (9:ℝ) * Real.log (Real.log ((N+1:ℕ):ℝ))
          = ((9:ℕ):ℝ) * Real.log (Real.log ((N+1:ℕ):ℝ)) by norm_num]
    rw [Real.exp_nat_mul, Real.exp_log hlogM]
    ring
  -- ## Step 4: `log (N+1) ≤ 2 log N`, so `(log (N+1))^9 ≤ 512 (log N)^9`.
  have hpow : (Real.log ((N+1:ℕ):ℝ))^9 ≤ 512 * (Real.log (N:ℝ))^9 := by
    have hN2 : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    have hle : ((N+1:ℕ):ℝ) ≤ 2*(N:ℝ) := by push_cast; linarith
    have hlog2le : Real.log 2 ≤ Real.log (N:ℝ) := Real.log_le_log (by norm_num) hN2
    have hlogsucc : Real.log ((N+1:ℕ):ℝ) ≤ 2 * Real.log (N:ℝ) := by
      calc Real.log ((N+1:ℕ):ℝ) ≤ Real.log (2*(N:ℝ)) := Real.log_le_log (by positivity) hle
        _ = Real.log 2 + Real.log (N:ℝ) := Real.log_mul (by norm_num) (ne_of_gt hNpos)
        _ ≤ 2 * Real.log (N:ℝ) := by linarith
    have hnn : (0:ℝ) ≤ Real.log ((N+1:ℕ):ℝ) := by
      apply Real.log_nonneg; exact_mod_cast (by omega : 1 ≤ N+1)
    calc (Real.log ((N+1:ℕ):ℝ))^9 ≤ (2 * Real.log (N:ℝ))^9 := pow_le_pow_left₀ hnn hlogsucc 9
      _ = 512 * (Real.log (N:ℝ))^9 := by rw [mul_pow]; norm_num
  calc (∏ p ∈ Nat.primesBelow (N+1), (1 + 9/((p:ℝ)-1)))
      ≤ Real.exp (9 * ∑ p ∈ Nat.primesBelow (N+1), 1/((p:ℝ)-1)) := hprod_le_exp
    _ ≤ Real.exp (9 * (Real.log (Real.log ((N+1:ℕ):ℝ)) + A + 1)) := hexp
    _ = Real.exp (9*(A+1)) * (Real.log ((N+1:ℕ):ℝ))^9 := hrewrite
    _ ≤ Real.exp (9*(A+1)) * (512 * (Real.log (N:ℝ))^9) :=
          mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
    _ = (Real.exp (9*(A+1)) * 512) * (Real.log (N:ℝ))^9 := by ring

end Work.ChenPlan.H1
