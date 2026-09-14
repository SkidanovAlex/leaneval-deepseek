import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

/-!
# A countable dense sequence in a nonempty subset of a second-countable pseudometric space

In a second-countable (pseudo)metric space, every nonempty subset `K` admits a sequence with values
in `K` whose range is dense in `K`.  This is the countable-density statement used to extract a
countable "dense net" out of a compact (or merely separable) set.
-/

set_option linter.style.haveILetI false

namespace Commons.Topology

/-- In a nonempty subset `K` of a second-countable pseudometric space there is a sequence taking
values in `K` which is dense in `K`: for every `z ∈ K` and every `ε > 0` some term of the sequence
is at distance `< ε` from `z`. -/
theorem exists_seq_denseRange_of_isCompact {E : Type*} [PseudoMetricSpace E] [SecondCountableTopology E]
    (K : Set E) (hK : K.Nonempty) :
    ∃ ψ : ℕ → E, (∀ n, ψ n ∈ K) ∧ ∀ z ∈ K, ∀ ε > 0, ∃ n, dist (ψ n) z < ε := by
  haveI : Nonempty K := hK.to_subtype
  -- `K` with the induced topology is second countable (hence separable) as a subspace of `E`.
  refine ⟨fun n => (TopologicalSpace.denseSeq K n : E), fun n => (TopologicalSpace.denseSeq K n).2, ?_⟩
  intro z hz ε hε
  -- the range of `denseSeq K` is dense in `K`, so it meets every ball around `⟨z, hz⟩`
  obtain ⟨n, hn⟩ :=
    (TopologicalSpace.denseRange_denseSeq K).exists_dist_lt (⟨z, hz⟩ : K) hε
  refine ⟨n, ?_⟩
  have h2 : dist z (↑(TopologicalSpace.denseSeq K n) : E) < ε := by
    rwa [Subtype.dist_eq] at hn
  rwa [dist_comm]

end Commons.Topology