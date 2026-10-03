import Mathlib
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound

open Finset

namespace Commons.NumberTheory.Mertens

/-!
# `∑_{p ≤ x} 1/p − log log x` is bounded for all natural `x ≥ 3`

`primeRecips_sub_loglog_bound` proves the uniform bound for real `x ≥ 11`.
For a natural `x ≥ 11` the floor `⌊(x : ℝ)⌋₊` equals `x`, so the very same
bound applies.  The remaining finitely many arguments `3 ≤ x ≤ 10` are
controlled crudely: the prime-reciprocal sum is at most its number of terms,
`≤ 12`, while `|log log x| ≤ 9` on `[3, 11]` (there `log x ∈ [log 3, log 11]`
is comfortably inside `(0, 10]`).  Adding the two constants and absorbing the
`21` into the positive constant `C₀` yields the claim.
-/

/-- For `x ≤ 11` the sum of prime reciprocals up to `x` is at most `12`
(the number of summands). -/
private lemma primesLE_sum_le_twelve (x : ℕ) (hx : x ≤ 11) :
    (∑ p ∈ Nat.primesLE x, (1 : ℝ) / p) ≤ 12 := by
  calc (∑ p ∈ Nat.primesLE x, (1 : ℝ) / p)
      ≤ ∑ _p ∈ Nat.primesLE x, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        rw [Nat.mem_primesLE] at hp
        have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.2.one_le
        rw [div_le_one (by linarith : (0 : ℝ) < (p : ℝ))]
        exact hp1
    _ = ((Nat.primesLE x).card : ℝ) := by simp
    _ ≤ 12 := by
        have hsub : Nat.primesLE x ⊆ Finset.range (x + 1) := by
          intro p hp
          rw [Nat.mem_primesLE] at hp
          exact Finset.mem_range.mpr (Nat.lt_succ_of_le hp.1)
        have h1 := Finset.card_le_card hsub
        rw [Finset.card_range] at h1
        have h2 : x + 1 ≤ 12 := by omega
        exact_mod_cast le_trans h1 h2

/-- For `3 ≤ x ≤ 11` we have `|log log x| ≤ 9`. -/
private lemma abs_loglog_le_nine {x : ℕ} (hx : 3 ≤ x) (hx11 : x ≤ 11) :
    |Real.log (Real.log (x : ℝ))| ≤ 9 := by
  have hxpos : 0 < (x : ℝ) := by
    have : (0 : ℕ) < x := by omega
    exact_mod_cast this
  have h3 : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hx11' : (x : ℝ) ≤ 11 := by exact_mod_cast hx11
  have hlogxpos : 0 < Real.log (x : ℝ) := Real.log_pos (by linarith)
  have hlogxle : Real.log (x : ℝ) ≤ 10 := by
    have := Real.log_le_sub_one_of_pos hxpos
    linarith
  have hupper : Real.log (Real.log (x : ℝ)) ≤ 9 := by
    have h : Real.log (Real.log (x : ℝ)) ≤ Real.log 10 := Real.log_le_log hlogxpos hlogxle
    have h10 : Real.log 10 ≤ 9 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10)
      linarith
    linarith
  have hnonneg : 0 ≤ Real.log (Real.log (x : ℝ)) := by
    have hexp : Real.exp 1 < (x : ℝ) := lt_of_lt_of_le Real.exp_one_lt_three h3
    have h1 : 1 < Real.log (x : ℝ) := (Real.lt_log_iff_exp_lt hxpos).mpr hexp
    exact Real.log_nonneg (le_of_lt h1)
  rw [abs_of_nonneg hnonneg]
  exact hupper

theorem primeRecips_sub_loglog_bound_ge_three :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, 3 ≤ x →
      |(∑ p ∈ Nat.primesLE x, (1 : ℝ) / p) - Real.log (Real.log (x : ℝ))| ≤ C := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := primeRecips_sub_loglog_bound
  refine ⟨C₀ + 21, by linarith, ?_⟩
  intro x hx3
  by_cases hx11 : 11 ≤ x
  · have hfl : ⌊(x : ℝ)⌋₊ = x := Nat.floor_natCast x
    have h := hC₀ (x : ℝ) (by exact_mod_cast hx11)
    rw [hfl] at h
    linarith
  · have hxle : x ≤ 11 := by omega
    have hSnonneg : 0 ≤ ∑ p ∈ Nat.primesLE x, (1 : ℝ) / p :=
      Finset.sum_nonneg (fun p _ => by positivity)
    have h1 : |(∑ p ∈ Nat.primesLE x, (1 : ℝ) / p)| ≤ 12 := by
      rw [abs_of_nonneg hSnonneg]
      exact primesLE_sum_le_twelve x hxle
    have h2 := abs_loglog_le_nine hx3 hxle
    have h3 : |(∑ p ∈ Nat.primesLE x, (1 : ℝ) / p) - Real.log (Real.log (x : ℝ))| ≤ 21 := by
      have h := abs_sub_le (∑ p ∈ Nat.primesLE x, (1 : ℝ) / p) 0 (Real.log (Real.log (x : ℝ)))
      simp only [sub_zero, zero_sub, abs_neg] at h
      linarith
    linarith

end Commons.NumberTheory.Mertens
