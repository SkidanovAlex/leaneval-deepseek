import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.NumberTheory.Robin

noncomputable section

open scoped BigOperators

/-- `log((p^{k+1}−1)/p^{k+1}) < 0` for `p ≥ 2` and any exponent `k`: the correction factor
`log(1 − p^{−(k+1)})` is a negative logarithm.  (Inlined port of `caCorrLog_neg`.) -/
private lemma caCorrLog_neg_local (p k : ℕ) (hp : 2 ≤ p) :
    Real.log ((((p : ℝ) ^ (k + 1 : ℕ)) - 1) / ((p : ℝ) ^ (k + 1 : ℕ))) < 0 := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hnum : 0 < ((p : ℝ) ^ (k + 1 : ℕ)) - 1 := by
    have hpowgt : 1 < (p : ℝ) ^ (k + 1 : ℕ) :=
      one_lt_pow₀ (by exact_mod_cast (by omega : 1 < p) : (1 : ℝ) < (p : ℝ))
        (by omega : k + 1 ≠ 0)
    linarith
  have hden : 0 < (p : ℝ) ^ (k + 1 : ℕ) := pow_pos hp0 (k + 1)
  have hratio : ((p : ℝ) ^ (k + 1 : ℕ)) - 1 < (p : ℝ) ^ (k + 1 : ℕ) := by linarith
  have hlt : (((p : ℝ) ^ (k + 1 : ℕ)) - 1) / ((p : ℝ) ^ (k + 1 : ℕ)) < 1 := by
    rw [div_lt_one hden]; exact hratio
  have hpos : 0 < (((p : ℝ) ^ (k + 1 : ℕ)) - 1) / ((p : ℝ) ^ (k + 1 : ℕ)) := div_pos hnum hden
  exact Real.log_neg hpos hlt

theorem caCorrSum_nonpos (ε : ℝ) : (Finset.sum (((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime).filter (fun p : ℕ => 1 ≤ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊)) (fun p : ℕ => Real.log ((((p : ℝ) ^ (⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊ + 1)) - 1) / ((p : ℝ) ^ (⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊ + 1))))) ≤ 0 := by
  refine Finset.sum_nonpos ?_
  intro p hp
  have hpS : p ∈ ((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime) :=
    (Finset.mem_filter.mp hp).1
  have hprime : Nat.Prime p := (Finset.mem_filter.mp hpS).2
  exact le_of_lt (caCorrLog_neg_local p _ hprime.two_le)

end

end Commons.NumberTheory.Robin