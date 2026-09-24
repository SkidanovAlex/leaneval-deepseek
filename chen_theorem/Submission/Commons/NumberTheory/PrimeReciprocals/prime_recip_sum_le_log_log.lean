import Mathlib
import Submission.Commons.NumberTheory.Mertens.second_mertens_converges

namespace Commons.NumberTheory.PrimeReciprocals

open scoped BigOperators
open Filter Finset

noncomputable section

/-- `Σ_{p ≤ x} 1/p − log log x`, the function that the second Mertens theorem
says converges as `x → ∞`. -/
private noncomputable def primerecipsSubLogLog (x : ℝ) : ℝ :=
  Commons.NumberTheory.Mertens.primeRecips x - Real.log (Real.log x)

/-- The sum over primes `p ≤ k` of `1/p` (the workspace convention for
`Mertens.primeRecips` at a natural) equals the sum over
`Nat.primesBelow (k + 1)`. -/
private lemma primeRecips_nat (k : ℕ) :
    Commons.NumberTheory.Mertens.primeRecips (k : ℝ) =
      ∑ p ∈ Nat.primesBelow (k + 1), (1 : ℝ) / (p : ℝ) := by
  unfold Commons.NumberTheory.Mertens.primeRecips
  simp [Nat.primesLE]

/-- For a natural `k ≥ 3`, `log (log k) ≥ 0`. -/
private lemma loglog_nonneg_of_three_le {k : ℕ} (hk : 3 ≤ k) :
    0 ≤ Real.log (Real.log (k : ℝ)) := by
  have hlog3 : (1 : ℝ) < Real.log (3 : ℝ) := by
    have h := Real.log_three_gt_d9
    norm_num at h
    linarith
  have hk3 : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hlogk : (1 : ℝ) ≤ Real.log (k : ℝ) := by
    exact le_trans (le_of_lt hlog3) (Real.log_le_log (by norm_num : (0 : ℝ) < 3) hk3)
  exact Real.log_nonneg hlogk

/-- Crude bound: `Σ_{p ≤ k} 1/p ≤ k + 1` (each prime is at least `2`, so each
summand is at most `1`, and there are at most `k + 1` primes `≤ k`). -/
private lemma primeRecips_nat_le (k : ℕ) :
    Commons.NumberTheory.Mertens.primeRecips (k : ℝ) ≤ (k : ℝ) + 1 := by
  rw [primeRecips_nat]
  calc
    (∑ p ∈ Nat.primesBelow (k + 1), (1 : ℝ) / (p : ℝ))
        ≤ (∑ _p ∈ Nat.primesBelow (k + 1), (1 : ℝ)) := by
          refine Finset.sum_le_sum ?_
          intro p hp
          have hp2 : 2 ≤ p := Nat.two_le_of_mem_primesBelow hp
          have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
          have hp1 : (1 : ℝ) ≤ p := by
            exact_mod_cast (by omega : 1 ≤ p)
          exact (div_le_iff₀ hp0).2 (by simpa using hp1)
    _ = ((Nat.primesBelow (k + 1)).card : ℝ) := by simp
    _ ≤ (((k + 1 : ℕ)) : ℝ) := by
      have hsub : Nat.primesBelow (k + 1) ⊆ Finset.range (k + 1) := by
        intro p hp
        simpa using (Nat.mem_primesBelow.mp hp).1
      have hcard : (Nat.primesBelow (k + 1)).card ≤ (Finset.range (k + 1)).card :=
        Finset.card_le_card hsub
      have hcard' : (Nat.primesBelow (k + 1)).card ≤ k + 1 := by simpa using hcard
      exact_mod_cast hcard'
    _ = (k : ℝ) + 1 := by norm_num

/-- The second Mertens theorem (`second_mertens_converges`) gives that
`Σ_{p ≤ k} 1/p − log (log k)` converges as `k → ∞`; any convergent sequence is
bounded above, so there is a constant `C ≥ 0` with
`Σ_{p ≤ N} 1/p ≤ C + log (log N)` for every `N ≥ 3`. -/
private theorem bound_existence :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 3 ≤ N →
      Commons.NumberTheory.Mertens.primeRecips (N : ℝ) ≤ C + Real.log (Real.log (N : ℝ)) := by
  rcases Commons.NumberTheory.Mertens.second_mertens_converges with ⟨M, hM⟩
  have hG : Tendsto primerecipsSubLogLog atTop (nhds M) := by
    change Tendsto (fun x : ℝ => Commons.NumberTheory.Mertens.primeRecips x -
        Real.log (Real.log x)) atTop (nhds M)
    exact hM
  have hgnat : Tendsto (fun k : ℕ => primerecipsSubLogLog (k : ℝ)) atTop (nhds M) :=
    hG.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  rcases (Metric.tendsto_atTop.mp hgnat) 1 zero_lt_one with ⟨N1, hN1⟩
  let N0 : ℕ := max N1 3
  have hN0ge3 : 3 ≤ N0 := le_max_right N1 3
  have hN1leN0 : N1 ≤ N0 := le_max_left N1 3
  let C : ℝ := max (M + 1) (N0 : ℝ)
  refine ⟨C, ?_, ?_⟩
  · have hN0c : (0 : ℝ) ≤ (N0 : ℝ) := by positivity
    have hCge : (N0 : ℝ) ≤ C := le_max_right (M + 1) (N0 : ℝ)
    linarith
  · intro k hk3
    have hmain : primerecipsSubLogLog (k : ℝ) ≤ C := by
      by_cases hkN0 : N0 ≤ k
      · have hd := hN1 k (le_trans hN1leN0 hkN0)
        have habs : |primerecipsSubLogLog (k : ℝ) - M| < 1 := by
          rwa [Real.dist_eq] at hd
        have hlt : primerecipsSubLogLog (k : ℝ) - M < 1 := (abs_lt.mp habs).2
        have hb : primerecipsSubLogLog (k : ℝ) ≤ M + 1 := by linarith
        exact le_trans hb (le_max_left (M + 1) (N0 : ℝ))
      · have hll0 : 0 ≤ Real.log (Real.log (k : ℝ)) := loglog_nonneg_of_three_le hk3
        have hrec : Commons.NumberTheory.Mertens.primeRecips (k : ℝ) ≤ (k : ℝ) + 1 :=
          primeRecips_nat_le k
        have hkin : (k : ℝ) + 1 ≤ (N0 : ℝ) := by
          have hk1 : k + 1 ≤ N0 := by omega
          exact_mod_cast hk1
        have hN0leC : (N0 : ℝ) ≤ C := le_max_right (M + 1) (N0 : ℝ)
        unfold primerecipsSubLogLog
        nlinarith
    unfold primerecipsSubLogLog at hmain
    nlinarith

/-- Euler–Mertens: the sum of `1/p` over primes `p ≤ N` is `O(log log N)`.

Explicitly: there is a constant `C` such that for every `N ≥ 3`,
`Σ_{p prime, p ≤ N} 1/p ≤ C + log(log N)`. -/
theorem prime_recip_sum_le_log_log :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 3 ≤ N →
      (∑ p ∈ Nat.primesBelow (N + 1), (1 : ℝ) / (p : ℝ)) ≤ C + Real.log (Real.log (N : ℝ)) := by
  rcases bound_existence with ⟨C, hC0, hC⟩
  refine ⟨C, hC0, ?_⟩
  intro N hN
  rw [← primeRecips_nat N]
  exact hC N hN

end
