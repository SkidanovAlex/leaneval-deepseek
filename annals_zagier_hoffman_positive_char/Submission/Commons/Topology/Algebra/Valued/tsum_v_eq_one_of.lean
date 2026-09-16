import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

open scoped WithZero Topology

namespace Commons.Topology.Algebra.Valued

/-- If `f : ℕ → K` is summable in a valued field `K` (with `ℤᵐ⁰`-valued valuation `v`),
`f 0 = 1` and every other term has valuation `< 1`, then the sum has valuation exactly `1`
(hence is nonzero). The lower bound `1 ≤ v (∑' f)` uses that `{x | 1 ≤ v x}` is closed (it is
the complement of the open ball `{x | v x < 1}`, `Valued.isOpen_ball`); the upper bound
`v (∑' f) ≤ 1` uses that the closed unit ball `{x | v x ≤ 1}` is closed
(`Valued.isClosed_closedBall`); both applied to the partial sums via
`IsClosed.mem_of_tendsto` and `Summable.hasSum.tendsto_sum_nat`, whose valuation is exactly `1`
by `Valuation.map_sum_lt` + `Valuation.map_add_eq_of_lt_left`. -/
theorem tsum_v_eq_one_of {K : Type*} [Field K] [Valued K ℤᵐ⁰] (f : ℕ → K)
    (hf0 : f 0 = 1) (hsumm : Summable f)
    (hlt : ∀ n : ℕ, 1 ≤ n → Valued.v (f n) < (1 : ℤᵐ⁰)) :
    Valued.v (∑' n, f n) = (1 : ℤᵐ⁰) := by
  -- The valuation of every partial sum of length `≥ 1` is `1`: the term `f 0 = 1` dominates all
  -- the other (smaller) terms.
  have hS : ∀ n : ℕ, 1 ≤ n → Valued.v (∑ i ∈ Finset.range n, f i) = (1 : ℤᵐ⁰) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Finset.sum_range_succ']
    have hT : Valued.v (∑ k ∈ Finset.range m, f (k + 1)) < (1 : ℤᵐ⁰) :=
      Valuation.map_sum_lt Valued.v one_ne_zero (fun k _ => hlt (k + 1) (by omega))
    have hlt' : Valued.v (∑ k ∈ Finset.range m, f (k + 1)) < Valued.v (f 0) := by
      rw [hf0, map_one]; exact hT
    rw [Valuation.map_add_eq_of_lt_right Valued.v hlt', hf0, map_one]
  have htend : Filter.Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, f i) Filter.atTop
      (𝓝 (∑' n, f n)) :=
    hsumm.hasSum.tendsto_sum_nat
  -- The closed unit ball `{x | v x ≤ 1}` is closed.
  have hcl_le : IsClosed {x : K | Valued.v x ≤ (1 : ℤᵐ⁰)} := by
    have h := Valued.isClosed_closedBall K (1 : _)
    convert h using 1
    ext x
    simp
  -- `{x | 1 ≤ v x}` is the complement of the open unit ball `{x | v x < 1}`, hence closed.
  have hcl_ge : IsClosed {x : K | (1 : ℤᵐ⁰) ≤ Valued.v x} := by
    have hopen : IsOpen {x : K | Valued.v x < (1 : ℤᵐ⁰)} := by
      have h := Valued.isOpen_ball K (1 : _)
      convert h using 1
      ext x
      simp
    convert hopen.isClosed_compl using 1
    ext x
    simp [not_lt]
  have h1 : Valued.v (∑' n, f n) ≤ (1 : ℤᵐ⁰) := by
    have := IsClosed.mem_of_tendsto (s := {x : K | Valued.v x ≤ (1 : ℤᵐ⁰)})
      (x := ∑' n, f n) (f := fun n : ℕ => ∑ i ∈ Finset.range n, f i) hcl_le htend ?_
    · exact this
    rw [Filter.eventually_atTop]
    exact ⟨1, fun n hn => le_of_eq (hS n hn)⟩
  have h2 : (1 : ℤᵐ⁰) ≤ Valued.v (∑' n, f n) := by
    have := IsClosed.mem_of_tendsto (s := {x : K | (1 : ℤᵐ⁰) ≤ Valued.v x})
      (x := ∑' n, f n) (f := fun n : ℕ => ∑ i ∈ Finset.range n, f i) hcl_ge htend ?_
    · exact this
    rw [Filter.eventually_atTop]
    exact ⟨1, fun n hn => le_of_eq (hS n hn).symm⟩
  exact le_antisymm h1 h2

end Commons.Topology.Algebra.Valued
