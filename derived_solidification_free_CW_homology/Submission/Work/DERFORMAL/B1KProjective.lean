/-
AREA DERFORMAL — B1 of REFS/02 §1: degreewise solidification of a solid-cofibrant complex is
K-projective.

The point of the whole area is that `LightCondAb` has too few projectives, so the blueprint
replaces "K-projective" by the relative notion `SolidCofibrant` (`Cofibrant` below): homotopy
classes of maps from `K` into the degreewise inclusion of a complex of solid objects are the
same as morphisms in the derived category.  B1 says that after solidifying, this relative
notion *is* the absolute one, in the category of solid objects:

* if `A` is an acyclic complex of solid objects, then `incC.obj A` is acyclic (the inclusion of
  solid objects is exact), so `Q (incC A)` is a zero object of `D(LightCondAb)` (an acyclic
  complex is zero in the derived category, phrased here with the canonical t-structure);
* hence every morphism in `D(LightCondAb)` into `Q (incC A)` is zero, and since `K` is
  solid-cofibrant, so is every element of `Hom_K(K, incC A)`;
* the adjunction `solK ⊣ incK` of `Setup.lean` identifies `Hom_K(solC K, A)` with
  `Hom_K(K, incC A)`, hence every morphism `solC K ⟶ A` is null-homotopic.

This is exactly the K-projectivity of `solC K` (`CochainComplex.IsKProjective`).
-/
import Mathlib
import Submission.Work.DERFORMAL.Setup

namespace Work.DERFORMAL

open CategoryTheory Limits
open LightCondensed
open Work.DERFORMAL

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

section

variable [isSolid.ι.IsRightAdjoint]

/-! ## The ingredients of B1 -/

/-- Acyclicity is preserved by the degreewise inclusion of complexes of solid objects: the
inclusion `isSolid.ι` is exact, so it commutes with the homology of the short complexes
`K.sc i`, and `K.ExactAt i` is by definition `(K.sc i).Exact`. -/
lemma acyclic_incC {A : SCpx} (hA : A.Acyclic) : (incC.obj A).Acyclic :=
  fun i => (hA i).map isSolid.ι

/-- An acyclic complex of solid objects is a zero object of `D(LightCondAb)` after applying the
degreewise inclusion of solid objects.  (Phrased via the canonical t-structure on the derived
category: an acyclic complex is both `≤ -1` and `≥ 1`.) -/
lemma isZero_Q_obj_incC_of_acyclic (A : SCpx) (hA : A.Acyclic) :
    IsZero (Q.obj (incC.obj A)) := by
  have hA' := acyclic_incC hA
  have hLE : (incC.obj A).IsLE (-1) := by
    rw [CochainComplex.isLE_iff]
    intro i hi
    exact hA' i
  have hGE : (incC.obj A).IsGE 1 := by
    rw [CochainComplex.isGE_iff]
    intro i hi
    exact hA' i
  haveI := hLE
  haveI := hGE
  exact CategoryTheory.Triangulated.TStructure.isZero
    DerivedCategory.TStructure.t _ (-1) 1 (by norm_num)

/-- The adjunction bijection `homKEquiv` (between homotopy classes of maps
`solC K ⟶ N` and maps `K ⟶ incC N`) sends zero to zero. -/
lemma homKEquiv_zero (K : Cpx) (N : SCpx) : homKEquiv K N 0 = 0 := by
  simp [homKEquiv, homEquivK, Equiv.trans_apply, Iso.homCongr_apply]

/-- **B1 (main step).**  If `K` is solid-cofibrant, then every morphism of complexes
`solC K ⟶ A` into an acyclic complex `A` of solid objects is null-homotopic: its image in the
homotopy category `K(Solid)` is zero. -/
lemma qs_map_eq_zero_of_cofibrant (K : Cpx) (hK : Cofibrant K) {A : SCpx}
    (hA : A.Acyclic) (f : solC.obj K ⟶ A) : qs.map f = 0 := by
  have hz := isZero_Q_obj_incC_of_acyclic A hA
  -- `homKEquiv` identifies `qs.map f` with an element of `Hom_K(K, incC A)`
  have hg : homKEquiv K A (qs.map f) = 0 := by
    -- which is zero since it is zero in `D(LightCondAb)` and `K` is solid-cofibrant
    refine (hK A).1 ?_
    change DerivedCategory.Qh.map (homKEquiv K A (qs.map f)) = DerivedCategory.Qh.map 0
    rw [Functor.map_zero]
    exact hz.eq_zero_of_tgt _
  exact (homKEquiv K A).injective (by rw [hg, homKEquiv_zero K A])

end

/-- **B1 of REFS/02 §1.**  Degreewise solidification of a solid-cofibrant complex is
K-projective in the category of solid objects. -/
theorem B1KProjective [isSolid.ι.IsRightAdjoint] (K : Cpx) (hK : Cofibrant K) : CochainComplex.IsKProjective (solC.obj K) := by
  refine ⟨fun {A} f hA => ⟨HomotopyCategory.homotopyOfEq f 0 ?_⟩⟩
  rw [qs_map_eq_zero_of_cofibrant K hK hA f, Functor.map_zero]

end Work.DERFORMAL
