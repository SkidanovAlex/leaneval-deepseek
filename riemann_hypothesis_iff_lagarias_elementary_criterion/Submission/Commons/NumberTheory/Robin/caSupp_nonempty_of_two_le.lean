import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.NumberTheory.Robin

-- PORT HINT: see Work caCore.lean (`Nε_ge_two_pow_caExp`, `caSupp`) and caU.lean; keep inlined helpers PRIVATE.
theorem caSupp_nonempty_of_two_le {ε : ℝ} (hε : 0 < ε) (h : 2 ≤ (Finset.prod ((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime) (fun p : ℕ => p ^ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊))) : (((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime).filter (fun p : ℕ => 1 ≤ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊)).Nonempty := by
  have _ : (0 : ℝ) < ε := hε
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  have hprod :
      (Finset.prod ((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime)
        (fun p : ℕ => p ^ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊)) = 1 := by
    apply Finset.prod_eq_one
    intro p hp
    have hnot : ¬ (1 ≤ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊) := by
      intro hge
      have hmem : p ∈ (((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime).filter
          (fun p : ℕ => 1 ≤ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊)) :=
        Finset.mem_filter.mpr ⟨hp, hge⟩
      rw [hempty] at hmem
      simp at hmem
    have he : ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊ = 0 := by omega
    rw [he, pow_zero]
  omega

end Commons.NumberTheory.Robin