import Mathlib
import Submission.Work.Cohomology.Ovl.chartU_vanishing
import Submission.Work.Cohomology.Ovl.chartV_vanishing
import Submission.Work.Cohomology.Endgame.relCohMV_elim

/-!
# `H⁵(Vk(-2), (U ∩ V) ∪ collar(-2)) = 0`

The relative cohomology of the pair consisting of the two-chart disc bundle `Vk(-2)` and
`W = (U ∩ V) ∪ collar(-2)` vanishes in degree `5`.  This is the vanishing hypothesis which makes
the restriction `H⁴(Vk(-2), collar(-2)) → H⁴(W, W ∩ collar(-2))` surjective (via the long exact
sequence of the triple), and hence the restriction of `H⁴(Vk(-2), Mk(-2))` to the overlap.

The proof is the relative Mayer–Vietoris elimination lemma `relCohMV_elim` applied to the cover
`Vk(-2) = U ∪ V`: the intersection term vanishes because `(U ∩ V) ∩ W = U ∩ V` (the relative
cohomology of a space modulo itself), and the two chart terms are
`Work.Cohomology.Ovl.chartU_vanishing` and `Work.Cohomology.Ovl.chartV_vanishing`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Topology

namespace Work.Cohomology.Ovl

noncomputable section

/-! ## The relative cohomology of a space modulo itself -/

/-- The canonical map from a space to its one-point `Set.univ` subtype. -/
def univIncl (X : TopCat) : X ⟶ TopCat.of (Set.univ : Set X) :=
  TopCat.ofHom ⟨fun x => ⟨x, Set.mem_univ x⟩,
    continuous_id.subtype_mk (fun x => Set.mem_univ x)⟩

/-- `univIncl` is a section of the inclusion of `Set.univ`. -/
theorem univIncl_comp_subtypeIncl (X : TopCat) :
    univIncl X ≫ subtypeIncl X (Set.univ : Set X) = 𝟙 X := by
  apply TopCat.hom_ext
  ext x
  rfl

/-- `univIncl` is a retraction of the inclusion of `Set.univ`. -/
theorem subtypeIncl_comp_univIncl (X : TopCat) :
    subtypeIncl X (Set.univ : Set X) ≫ univIncl X = 𝟙 (TopCat.of (Set.univ : Set X)) := by
  apply TopCat.hom_ext
  ext x
  rfl

/-- A relative `n`-cochain of the pair `(Y, Y)` is zero. -/
theorem relKern_univ_eq_zero (Y : TopCat) (n : ℕ) (a : relKern ℤ Y (Set.univ : Set Y) n) :
    (a : (singularCochainComplex ℤ Y).X n) = 0 := by
  have hcomp : restr ℤ Y (Set.univ : Set Y) ≫
      dualChainMap ℤ Y (TopCat.of (Set.univ : Set Y)) (univIncl Y) =
      𝟙 (singularCochainComplex ℤ Y) := by
    rw [restr, ← dualChainMap_comp (R := ℤ) (f := univIncl Y)
      (g := subtypeIncl Y (Set.univ : Set Y)), univIncl_comp_subtypeIncl, dualChainMap_id]
  have hcomp' := congrArg (fun (φ : singularCochainComplex ℤ Y ⟶ singularCochainComplex ℤ Y) =>
    (φ.f n).hom) hcomp
  rw [HomologicalComplex.comp_f, ModuleCat.hom_comp, HomologicalComplex.id_f,
    ModuleCat.hom_id] at hcomp'
  have h2 : ((dualChainMap ℤ Y (TopCat.of (Set.univ : Set Y)) (univIncl Y)).f n).hom
      (((restr ℤ Y (Set.univ : Set Y)).f n).hom a.1) = a.1 :=
    LinearMap.congr_fun hcomp' a.1
  rw [← h2, a.2, map_zero]

/-- The relative `n`-cochains of the pair `(Y, Y)` are a subsingleton. -/
theorem relKern_univ_subsingleton (Y : TopCat) (n : ℕ) :
    Subsingleton ↥(relKern ℤ Y (Set.univ : Set Y) n) :=
  ⟨fun a b => Subtype.ext (by rw [relKern_univ_eq_zero Y n a, relKern_univ_eq_zero Y n b])⟩

/-- **The relative cohomology of a space modulo itself vanishes**: `H^n(Y, Y) = 0`. -/
theorem relCohomology_univ_vanishing (Y : TopCat) (n : ℕ) :
    Subsingleton (relCohomology ℤ Y Set.univ n) := by
  have hex : (relComplex ℤ Y (Set.univ : Set Y)).ExactAt n :=
    HomologicalComplex.ExactAt.of_isZero (K := relComplex ℤ Y (Set.univ : Set Y)) (i := n)
      (ModuleCat.isZero_iff_subsingleton.mpr (relKern_univ_subsingleton Y n))
  exact ModuleCat.isZero_iff_subsingleton.mp hex.isZero_homology

/-! ## The vanishing for the union of the overlap and the collar -/

/-- The trace of `W = (U ∩ V) ∪ collar(-2)` on the overlap is the whole overlap. -/
theorem ovlW_trace_overlap :
    (Subtype.val : ↥(Work.Cohomology.Crux.vkU ∩ Work.Cohomology.Crux.vkV) →
      Work.Cohomology.vkPairX) ⁻¹' Work.Cohomology.Endgame.ovlW = Set.univ := by
  ext y
  simp only [Set.mem_preimage, Set.mem_univ, iff_true]
  exact Or.inl y.2

/-- **`H⁵(Vk(-2), (U ∩ V) ∪ collar(-2)) = 0`.** -/
theorem ovlUnionCollar_vanishing :
    Subsingleton (relCohomology ℤ vkPairX Work.Cohomology.Endgame.ovlW 5) := by
  have h0 : Subsingleton (relCohomology ℤ
      (TopCat.of ↥(Work.Cohomology.Crux.vkU ∩ Work.Cohomology.Crux.vkV))
      ((Subtype.val : ↥(Work.Cohomology.Crux.vkU ∩ Work.Cohomology.Crux.vkV) →
        Work.Cohomology.vkPairX) ⁻¹' Work.Cohomology.Endgame.ovlW) 4) := by
    rw [ovlW_trace_overlap]
    exact relCohomology_univ_vanishing _ 4
  exact Work.Cohomology.Endgame.relCohMV_elim Work.Cohomology.vkPairX
    Work.Cohomology.Endgame.ovlW Work.Cohomology.Crux.vkU Work.Cohomology.Crux.vkV
    Work.Cohomology.Crux.vkU_isOpen Work.Cohomology.Crux.vkV_isOpen
    Work.Cohomology.Crux.vkU_union_vkV 4 h0 chartU_vanishing chartV_vanishing

end

end Work.Cohomology.Ovl
