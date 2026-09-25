import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.NumberTheory.Robin

-- PORT HINT: see Work caCore.lean / caU.lean (`caSupp`, `mem_caSupp`, `caXiOf`); keep inlined helpers PRIVATE.
theorem caXi_prime {ε : ℝ} (hs : (((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime).filter (fun p : ℕ => 1 ≤ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊)).Nonempty) : Nat.Prime ((((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime).filter (fun p : ℕ => 1 ≤ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊)).max' hs) := by
  have hmem := Finset.max'_mem _ hs
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp hmem).1).2

end Commons.NumberTheory.Robin