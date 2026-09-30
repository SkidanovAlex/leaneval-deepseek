import Submission.Work.Cohomology.pd_plumbing
import Submission.Work.Cohomology.localHomology

/-!
# The exact sequence of a triple

For `C ⊆ A ⊆ X` the relative chain complexes fit into the short exact sequence

  `0 ⟶ C_*(A,C) ⟶ C_*(X,C) ⟶ C_*(X,A) ⟶ 0`,

whose long exact sequence in homology is the **exact sequence of the triple** `(X,A,C)`.  This is
the tool used by the cell-attachment step of the Serre exact sequence in the stable range
(`Submission/Work/StemsB/SERRE_PLAN.md`, addendum): the induction is over the skeleta of the base,
and the five lemma is applied to the map of triple sequences
`(E|_W, E|_{W'}, F) → (W, W', {b₀})`.

The short complex is the one whose components are the map `C_*(A,C) → C_*(X,C)` induced by the
inclusion of pairs (the workspace's `Work.Cohomology.relChainsMap`) and the map `C_*(X,C) → C_*(X,A)`
induced by the inclusion `C ⊆ A` (the workspace's `Work.Cohomology.relChainsSubMap`).
-/

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

namespace Work.StemsB

noncomputable section

/-- The relative complex of the pair `(A, C)`, regarded inside the ambient space `X`. -/
abbrev tripleRelChains (X : TopCat) (C A : Set X) : ChainComplex (ModuleCat ℤ) ℕ :=
  Work.Cohomology.relChains (TopCat.of A) {y : ↥A | (y : X) ∈ C}

/-- The first map of the triple sequence: `C_*(A,C) ⟶ C_*(X,C)`. -/
abbrev tripleIncl (X : TopCat) (C A : Set X) : tripleRelChains X C A ⟶ Work.Cohomology.relChains X C :=
  Work.Cohomology.relChainsMap X A C

/-- **The short complex of a triple** `C ⊆ A ⊆ X`:
`0 ⟶ C_*(A,C) ⟶ C_*(X,C) ⟶ C_*(X,A) ⟶ 0`. -/
theorem triple_comp_zero (X : TopCat) (C A : Set X) (hCA : C ⊆ A) :
    tripleIncl X C A ≫ Work.Cohomology.relChainsSubMap X C A hCA = 0 := by
  have hπ : cokernel.π (Work.Cohomology.inclChains (TopCat.of A) {y : ↥A | (y : X) ∈ C})
      ≫ (tripleIncl X C A ≫ Work.Cohomology.relChainsSubMap X C A hCA) = 0 := by
    rw [← Category.assoc]
    dsimp only [tripleIncl]
    rw [Work.Cohomology.cokernel_π_relChainsMap, Category.assoc,
      Work.Cohomology.relChainsSubMap_comp]
    rw [show Work.Cohomology.chainMap ℤ (TopCat.of A) X (Work.Cohomology.subtypeIncl X A)
        = Work.Cohomology.inclChains X A from rfl, cokernel.condition]
  exact (cancel_epi (cokernel.π (Work.Cohomology.inclChains (TopCat.of A)
    {y : ↥A | (y : X) ∈ C}))).1 (by rw [hπ, comp_zero])

/-- **The short complex of a triple** `C ⊆ A ⊆ X`:
`0 ⟶ C_*(A,C) ⟶ C_*(X,C) ⟶ C_*(X,A) ⟶ 0`. -/
def tripleShort (X : TopCat) (C A : Set X) (hCA : C ⊆ A) :
    ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (tripleIncl X C A) (Work.Cohomology.relChainsSubMap X C A hCA)
    (triple_comp_zero X C A hCA)

end

end Work.StemsB
