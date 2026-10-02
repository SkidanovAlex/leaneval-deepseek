import Mathlib
import Submission.Work.Thom.Glue
import Submission.Work.Thom.pdCoh_empty_iso
import Submission.Work.Cohomology.relCohMV_honest_les

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# The transgression square: the single remaining gap of the Thom chapter

With the five lemma in long exact sequence form (`Work.Thom.five_lemma_LES`,
`Submission/Work/Thom/Ladder.lean`), the Thom isomorphism theorem for a general oriented bundle over
a two-piece cover `B = U ∪ V` reduces to three squares of the Mayer--Vietoris ladder.  Two of them
are proved (`Work.Thom.thomMap_restrict` is the `F`-square; the `G`-square is the same statement for
the difference of the two restrictions).  This file states the third — the **transgression square**
— as a `Prop`, so that the remaining gap has an exact Lean signature.

The mathematical content: for every `y ∈ H^k(U ∩ V;ℤ)`,

`δ_E (π_{U∩V}^*(y) ⌣ τ|_{U∩V}) = π^*(δ_B y) ⌣ τ`

where `δ_B` and `δ_E` are the honest Mayer--Vietoris connecting maps
(`Work.Cohomology.honestDelta`) of the base `B` and of the Thom pair `(E, E∖0)`, `τ` is the global
class of the Thom pair, and the Thom maps are `Work.Thom.thomMap` and `Work.Thom.localThomMap`.
-/

open Work.TangentClasses

namespace Work.Thom

open Bundle CategoryTheory CategoryTheory.Limits

open scoped Topology

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-- **The canonical identification** of the absolute relative cohomology `H^k(B,∅;ℤ)` with the
singular cohomology `H^k(B;ℤ)` of the chapter: the map induced by the inclusion
`C^*(B,∅) ⟶ C^*(B)`, which is an isomorphism because the restriction to the empty set is zero
(`Work.Cohomology.relComplex_empty_homology_iso`).  This is the *canonical* choice — `pdCoh_empty_iso`
only provides the existence of some isomorphism. -/
noncomputable def pdCohIso (B : Type) [TopologicalSpace B] (k : ℕ) :
    Work.Cohomology.pdCoh (TopCat.of B) (∅ : Set B) k ≅ Coh ℤ k B :=
  @asIso _ _ _ _ (HomologicalComplex.homologyMap
      (Work.Cohomology.relIncl ℤ (TopCat.of B) (∅ : Set B)) k)
    (Work.Cohomology.relComplex_empty_homology_iso (TopCat.of B) k)

/-- The preimage of the pieces of a cover is a cover of the total space. -/
theorem preimage_union_univ (Z : RealBundle B F ι) {U V : Set B} (hcov : U ∪ V = Set.univ) :
    Z.proj ⁻¹' U ∪ Z.proj ⁻¹' V = Set.univ := by
  rw [← Set.preimage_union, hcov, Set.preimage_univ]

/-- **The transgression square** of the Mayer--Vietoris ladder of the Thom isomorphism theorem:
the compatibility of the Mayer--Vietoris connecting map with the Thom map.

This is the *only* remaining mathematical input of the general Thom isomorphism theorem in the
Mayer--Vietoris route; see `Submission/Work/Thom/README.md`, ADDENDUM 9. -/
def TransgressionSquare (Z : RealBundle B F ι) (n : ℕ) {U V : Set B} (hU : IsOpen U)
    (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (τ : OpenThom Z n) : Prop :=
  ∀ (k : ℕ) (y : Coh ℤ k ↥(U ∩ V)),
    (thomMap Z n τ (k + 1))
        ((pdCohIso B (k + 1)).hom
          ((Work.Cohomology.honestDelta (TopCat.of B) (∅ : Set B) U V hU hV hcov k).hom
            ((pdCohIso ↥(U ∩ V) k).symm.hom y)))
      = (eqToHom (congrArg (fun m => OpenThom Z m) (by omega : (k + n) + 1 = (k + 1) + n))).hom
          ((Work.Cohomology.honestDelta (TopCat.of Z.TotalSpace) (zeroComplement Z)
              (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) (hU.preimage Z.continuous_proj)
              (hV.preimage Z.continuous_proj) (preimage_union_univ Z hcov)
              (k + n)).hom
            ((localThomMap Z n (U ∩ V) ((PieceRes Z (U ∩ V) n) τ) k) y))

end

end Work.Thom
