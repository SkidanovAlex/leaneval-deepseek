import Submission.Work.RelatorRank.Instance.abstractRelatorHalfOf_elementaryAbelian
import Submission.Work.RelatorRank.Instance.abstractRelatorHalfOf_commutative

/-!
# `Work.RelatorRank` -- the discrete topology: the abstract core as a special case

**Namespace** `Work.RelatorRank`; module `Submission.Work.RelatorRank.Discrete`.

On a discrete topological group every subgroup is closed, so a family densely generates iff it
generates; consequently the abstract (topology-free) presentation bounds of this chapter imply the
topological ones.  The main corollary is the topological form of the unconditional instance
`Work.RelatorRank.Instance.abstractRelatorHalfOf_elementaryAbelian`: **every** generating `d`-family
of `(ℤ/2)^d` is presented by at most `d + d(d-1)/2` relators, in the sense of
`RelatorHalfOf`, i.e. an unconditional instance of the conclusion of the bridge.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace Work.RelatorRank

/-- On a discrete topological group, dense generation is generation. -/
theorem denseGenerating_iff_generating_of_discrete {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    [DiscreteTopology Γ] {ι : Type*} (gen : ι → Γ) :
    DenseGenerating gen ↔ Generating gen := by
  have h : ∀ s : Subgroup Γ, s.topologicalClosure = s := by
    intro s
    refine le_antisymm (Subgroup.topologicalClosure_minimal _ le_rfl (isClosed_discrete _))
      (Subgroup.le_topologicalClosure s)
  rw [denseGenerating_iff, generating_iff, h]

/-- The abstract presentation-independent bound implies the topological one on a discrete
topological group. -/
theorem relatorHalfOf_of_abstractRelatorHalfOf_of_discrete {Γ : Type*} [Group Γ]
    [TopologicalSpace Γ] [DiscreteTopology Γ] {d r : ℕ} (h : AbstractRelatorHalfOf Γ d r) :
    RelatorHalfOf Γ d r := by
  intro gen hgen
  exact h gen ((denseGenerating_iff_generating_of_discrete gen).mp hgen)

/-- **An unconditional instance of the bridge's conclusion.**  Every dense generating `d`-family
of the elementary abelian `2`-group `(ℤ/2)^d` (with the discrete topology, as a compact pro-`2`
group) is presented by at most `d + d(d-1)/2` relators -- namely the squares and the commutators,
which is `dim_{𝔽₂} H²((ℤ/2)^d, 𝔽₂)`. -/
theorem relatorHalfOf_elementaryAbelian (d : ℕ) :
    RelatorHalfOf (Fin d → Multiplicative (ZMod 2)) d (d + d * (d - 1) / 2) :=
  relatorHalfOf_of_abstractRelatorHalfOf_of_discrete
    (Work.RelatorRank.Instance.abstractRelatorHalfOf_elementaryAbelian d)

/-- **The `∀`-form holds for every commutative group** (discrete topology): every generating
`d`-family of a commutative topological group with the discrete topology is presented by at most
`d + d(d-1)/2` relators. -/
theorem relatorHalfOf_commutative_of_discrete (G : Type*) [CommGroup G] [TopologicalSpace G]
    [DiscreteTopology G] (d : ℕ) : RelatorHalfOf G d (d + d * (d - 1) / 2) :=
  relatorHalfOf_of_abstractRelatorHalfOf_of_discrete
    (Work.RelatorRank.Instance.abstractRelatorHalfOf_commutative d)

end Work.RelatorRank

