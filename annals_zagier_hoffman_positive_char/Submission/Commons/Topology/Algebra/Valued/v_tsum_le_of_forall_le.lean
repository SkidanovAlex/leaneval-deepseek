import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.Valued.ValuationTopology

open scoped Topology WithZero

namespace Commons.Topology.Algebra.Valued

/-- In a complete non-archimedean valued field, the valuation of an absolutely convergent sum
is at most the supremum of the valuations of the summands: if `v (f i) ≤ γ` for all `i` then
`v (∑' i, f i) ≤ γ`.  (The closed ball `{x | v x ≤ γ}` is closed and closed under finite sums.) -/
theorem v_tsum_le_of_forall_le {K : Type*} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
    [CompleteSpace K] [T2Space K] [NonarchimedeanAddGroup K]
    {α : Type*} {f : α → K} (hf : Summable f) {γ : WithZero (Multiplicative ℤ)}
    (h : ∀ i, Valued.v (f i) ≤ γ) : Valued.v (∑' i, f i) ≤ γ := by
  -- The set `{x | v x ≤ γ}` is closed: it is the intersection of the closed sets
  -- `{x | v.restrict x < g}` over all `g` in the value group with `embedding g > γ`.
  have hclosed : IsClosed {x : K | Valued.v x ≤ γ} := by
    have hkey : {x : K | Valued.v x ≤ γ}
        = ⋂ (g : MonoidWithZeroHom.ValueGroup₀
              (.ofClass (Valued.v : Valuation K (WithZero (Multiplicative ℤ)))))
            (_ : γ < MonoidWithZeroHom.ValueGroup₀.embedding g),
            {x : K | Valued.v.restrict x < g} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      constructor
      · intro hx g hg
        rw [Valuation.restrict_lt_iff_lt_embedding]
        exact lt_of_le_of_lt hx hg
      · intro hx
        by_contra hlt
        rw [not_le] at hlt
        exact absurd
          (hx (Valued.v.restrict x)
            (by rw [Valuation.embedding_restrict]; exact hlt))
          (lt_irrefl _)
    rw [hkey]
    exact isClosed_iInter fun g => isClosed_iInter fun _ => Valued.isClosed_ball K g
  -- Every finite partial sum lies in this closed set.
  have hmem : ∀ s : Finset α, Valued.v (∑ i ∈ s, f i) ≤ γ :=
    fun s => Valued.v.map_sum_le (fun i _ => h i)
  -- Hence so does the sum.
  exact hclosed.mem_of_tendsto hf.hasSum (Filter.Eventually.of_forall hmem)

end Commons.Topology.Algebra.Valued