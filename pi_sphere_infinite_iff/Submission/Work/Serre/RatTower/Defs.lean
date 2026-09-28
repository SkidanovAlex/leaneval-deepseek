import Mathlib
import Submission.Work.StemsB.RelChainsR
import Submission.Work.StemsB.tripleShort_shortExact
import Submission.Work.Cohomology.localCohomology
import Submission.Work.Serre.csrDefs
import Submission.Work.Serre.csrGlue

/-!
# The rational triple sequence, and the vocabulary of the tower comparison

Over `ℚ`, the relative chains of a pair `(X,A)` are `Work.StemsB.relChainsR ℚ X A = C_*(X)/C_*(A)`.
For `A ⊆ B ⊆ X` the natural sequence

`0 ⟶ C_*(B, A; ℚ) ⟶ C_*(X, A; ℚ) ⟶ C_*(X, B; ℚ) ⟶ 0`

is short exact (`tripleShortR_shortExact`); here the first term is the "subspace-in-B" model
`relChainsR ℚ (TopCat.of ↥B) {x : ↥B | (x : X) ∈ A}`.  This is the rational counterpart of
`Work.Cohomology.tripleShort`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Serre.RatTower

noncomputable section

/-! ## Functoriality of the rational chain map -/

lemma chainMapQ_comp {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Work.Cohomology.chainMap ℚ X Z (f ≫ g)
      = Work.Cohomology.chainMap ℚ X Y f ≫ Work.Cohomology.chainMap ℚ Y Z g :=
  CategoryTheory.Functor.map_comp _ _ _

lemma chainMapQ_id (X : TopCat) :
    Work.Cohomology.chainMap ℚ X X (𝟙 X) = 𝟙 _ :=
  CategoryTheory.Functor.map_id _ _

/-- **`csrRelMapOf` depends only on the underlying continuous maps.** -/
theorem csrRelMapOf_congr {X Y : TopCat} {A : Set X} {B : Set Y} {f f' : X ⟶ Y} (hf : f = f')
    {g g' : TopCat.of ↥A ⟶ TopCat.of ↥B} (hg : g = g')
    (w : Work.Cohomology.subtypeIncl X A ≫ f = g ≫ Work.Cohomology.subtypeIncl Y B)
    (w' : Work.Cohomology.subtypeIncl X A ≫ f' = g' ≫ Work.Cohomology.subtypeIncl Y B) :
    Work.Serre.csrRelMapOf X Y A B f g w = Work.Serre.csrRelMapOf X Y A B f' g' w' := by
  subst hf
  subst hg
  exact congrArg _ (Subsingleton.elim _ _)

/-- The inclusion `A ⊆ B` of subsets as a map of topological spaces. -/
def inclTop (X : TopCat) (A B : Set X) (hAB : A ⊆ B) : TopCat.of ↥A ⟶ TopCat.of ↥B :=
  TopCat.ofHom ⟨fun x => ⟨x.1, hAB x.2⟩,
    Continuous.subtype_mk continuous_subtype_val (fun x => hAB x.2)⟩

lemma inclTop_subtypeIncl (X : TopCat) (A B : Set X) (hAB : A ⊆ B) :
    inclTop X A B hAB ≫ Work.Cohomology.subtypeIncl X B = Work.Cohomology.subtypeIncl X A := by
  ext x
  rfl

lemma subtypeIncl_interInclInterA (X : TopCat) (A B : Set X) (hAB : A ⊆ B) :
    Work.Cohomology.subtypeIncl (TopCat.of ↥B) {x : ↥B | (x : X) ∈ A}
        ≫ Work.Cohomology.subtypeIncl X B
      = Work.Cohomology.inclInterA X B A ≫ Work.Cohomology.subtypeIncl X A := by
  ext x
  rfl

/-! ## The short complex of a triple -/

set_option maxHeartbeats 4000000 in
/-- **The short complex of the triple `A ⊆ B ⊆ X`**, over `ℚ`:
`0 ⟶ C_*(B,A;ℚ) ⟶ C_*(X,A;ℚ) ⟶ C_*(X,B;ℚ) ⟶ 0`. -/
noncomputable def tripleShortR (X : TopCat) (A B : Set X) (hAB : A ⊆ B) :
    ShortComplex (ChainComplex (ModuleCat ℚ) ℕ) :=
  ShortComplex.mk
    (cokernel.map
      (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥B) {x : ↥B | (x : X) ∈ A})
      (Work.StemsB.relChainsRIncl ℚ X A)
      (Work.Cohomology.chainMap ℚ (TopCat.of {x : ↥B | (x : X) ∈ A}) (TopCat.of ↥A)
        (Work.Cohomology.inclInterA X B A))
      (Work.StemsB.relChainsRIncl ℚ X B)
      (by
        show Work.Cohomology.chainMap ℚ (TopCat.of {x : ↥B | (x : X) ∈ A}) (TopCat.of ↥B)
              (Work.Cohomology.subtypeIncl (TopCat.of ↥B) {x : ↥B | (x : X) ∈ A})
              ≫ Work.Cohomology.chainMap ℚ (TopCat.of ↥B) X (Work.Cohomology.subtypeIncl X B)
            = Work.Cohomology.chainMap ℚ (TopCat.of {x : ↥B | (x : X) ∈ A}) (TopCat.of ↥A)
                (Work.Cohomology.inclInterA X B A)
              ≫ Work.Cohomology.chainMap ℚ (TopCat.of ↥A) X (Work.Cohomology.subtypeIncl X A)
        rw [← chainMapQ_comp, ← chainMapQ_comp, subtypeIncl_interInclInterA X A B hAB]))
    (cokernel.desc (Work.StemsB.relChainsRIncl ℚ X A)
      (cokernel.π (Work.StemsB.relChainsRIncl ℚ X B))
      (by
        show Work.Cohomology.chainMap ℚ (TopCat.of ↥A) X (Work.Cohomology.subtypeIncl X A)
              ≫ cokernel.π (Work.Cohomology.chainMap ℚ (TopCat.of ↥B) X
                  (Work.Cohomology.subtypeIncl X B)) = 0
        rw [← inclTop_subtypeIncl X A B hAB, chainMapQ_comp, Category.assoc, cokernel.condition,
          comp_zero]))
    (by
      apply (cancel_epi (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥B)
        {x : ↥B | (x : X) ∈ A}))).mp
      rw [← Category.assoc, cokernel.map, cokernel.π_desc, Category.assoc, cokernel.π_desc,
        cokernel.condition, comp_zero])

/-- **The triple sequence is short exact.** -/
theorem tripleShortR_shortExact (X : TopCat) (A B : Set X) (hAB : A ⊆ B) :
    (tripleShortR X A B hAB).ShortExact := by
  haveI hiso : IsIso (Work.Cohomology.inclInterA X B A) :=
    Work.StemsB.isIso_inclInterA X A B hAB
  haveI hisoc : IsIso (Work.Cohomology.chainMap ℚ (TopCat.of {x : ↥B | (x : X) ∈ A})
      (TopCat.of ↥A) (Work.Cohomology.inclInterA X B A)) := inferInstance
  haveI hmono : Mono (Work.StemsB.relChainsRIncl ℚ X B) :=
    Work.StemsB.mono_chainMap_subtypeIncl_ring ℚ X B
  unfold tripleShortR
  refine Work.StemsB.shortExact_of_cokernelMap
    (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥B) {x : ↥B | (x : X) ∈ A})
    (Work.Cohomology.chainMap ℚ (TopCat.of {x : ↥B | (x : X) ∈ A}) (TopCat.of ↥A)
      (Work.Cohomology.inclInterA X B A))
    (Work.StemsB.relChainsRIncl ℚ X B)
    (Work.StemsB.relChainsRIncl ℚ X A) ?_ ?_

end

end Work.Serre.RatTower
