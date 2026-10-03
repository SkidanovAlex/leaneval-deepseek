import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Field.GeomSum

set_option autoImplicit false

namespace Commons.Analysis.Asymptotics

open scoped BigOperators

/-- For a ratio `0 ≤ r < 1`, every finite set of powers `r^m` sums to at most the
full geometric-series value `1 / (1 - r)`.  Proof: extend `s` to a full initial
segment `{0,…,N}` (possible since all terms are nonnegative), then use the closed
form of the finite geometric sum. -/
theorem geom_finset_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (s : Finset ℕ) :
    (∑ m ∈ s, r ^ m) ≤ 1 / (1 - r) := by
  let N : ℕ := s.sup (fun m : ℕ => m) + 1
  have hsN : s ⊆ Finset.range N := by
    intro m hm
    simp only [Finset.mem_range]
    have hle : m ≤ s.sup (fun m : ℕ => m) := Finset.le_sup (f := fun m : ℕ => m) hm
    dsimp [N]
    omega
  have hnonneg : ∀ a ∈ Finset.range N, a ∉ s → 0 ≤ r ^ a := by
    intro a ha ha'
    exact pow_nonneg hr0 a
  have hle1 : (∑ m ∈ s, r ^ m) ≤ (∑ m ∈ Finset.range N, r ^ m) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsN hnonneg
  have hrne : r ≠ 1 := by
    intro h
    linarith
  have hsum : (∑ m ∈ Finset.range N, r ^ m) = (1 - r ^ N) / (1 - r) := by
    rw [geom_sum_eq hrne N]
    field_simp [hrne]
    ring
  have hrange_le : (∑ m ∈ Finset.range N, r ^ m) ≤ 1 / (1 - r) := by
    rw [hsum]
    have hden : 0 < 1 - r := by linarith
    have hrn : 0 ≤ r ^ N := pow_nonneg hr0 N
    have hle : 1 - r ^ N ≤ 1 := by linarith
    exact div_le_div_of_nonneg_right hle (le_of_lt hden)
  exact le_trans hle1 hrange_le

end Commons.Analysis.Asymptotics
