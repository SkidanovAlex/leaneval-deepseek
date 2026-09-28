import Mathlib
import Submission.Work.Thom.CapChain
import Submission.Work.StemsB.ExcisionMapR

/-!
# The chain of isomorphisms proving the cap isomorphism, over an arbitrary coefficient ring

`Submission/Work/Thom/CapChain.lean` proves, over `ℤ`, that the cap map

`(b,w) ↦ (b, capMap n w) : (B × Dⁿ, B × Sⁿ⁻¹) ⟶ (B × Sⁿ, B × {last ≤ 1/2})`

factors as a composite of three maps of pairs whose induced maps on relative cohomology are all
isomorphisms:

* (a) the inclusion `(B × Sⁿ, B × {last < 1/2}) → (B × Sⁿ, B × {last ≤ 1/2})`;
* (b) the excision of the closed south cap `{last ≤ -1/2}`, followed by the canonical
  identification of a product-subtype with the product;
* (c) the cap map `(b,w) ↦ (b, capMap n w)` from `(B × Dⁿ, B × Sⁿ⁻¹)` to
  `(B × {last > -1/2}, B × {-1/2 < last < 1/2})`.

Every ingredient of the three proofs (`Work.Cohomology.homotopyEquiv`,
`Work.Thom.isIso_homologyMap_relComplexMap`,
`Work.CapGlue.isIso_relComplexMap_homeomorph`,
`Work.CapGlue.isIso_homologyMap_dualChainMap_prodMap`) is stated for an arbitrary commutative
ring, the only exception being excision, whose coefficient-generic form
`Work.StemsB.relComplexMapExcision_R` is proved in `Submission/Work/StemsB/ExcisionMapR.lean`.
Hence the same three steps give the isomorphism over any `R`; this file records that form.  The
`ℤ` originals are untouched.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000

open CategoryTheory

namespace Work.Thom

noncomputable section

variable (R : Type) [CommRing R]

variable (B : Type) [TopologicalSpace B] (n : ℕ)
/-- The inclusion of the open band into the closed band induces an isomorphism on the cohomology of
the subtypes (the two are homotopy equivalent by the scaling). -/
theorem isIso_bandIncl_R (m : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap (Work.Cohomology.dualChainMap R
      (TopCat.of ↥(ppLt B n)) (TopCat.of ↥(ppLe B n)) (TopCat.ofHom (bandIncl B n))) m) :=
  Work.Cohomology.homotopyEquiv R (TopCat.of ↥(ppLt B n)) (TopCat.of ↥(ppLe B n))
    (TopCat.ofHom (bandIncl B n)) (TopCat.ofHom (bandScale B n))
    (bandHomotopyLt B n) (bandHomotopyLe B n) m

/-- **Step (a)**: the inclusion of pairs
`(B × Sⁿ, B × {last < 1/2}) → (B × Sⁿ, B × {last ≤ 1/2})` induces an isomorphism on relative
cohomology (the two `A`-parts are homotopy equivalent by the scaling `Φ_{1/2}`). -/
theorem isIso_relCohMap_bandIncl_R (m : ℕ) :
    CategoryTheory.IsIso (relCohMap (ContinuousMap.id (B × MSph (n + 1))) (ppLt B n) (ppLe B n)
      (fun x hx => ppLt_subset_ppLe B n hx) R m) := by
  have hX : ∀ k, CategoryTheory.IsIso (HomologicalComplex.homologyMap (Work.Cohomology.dualChainMap R
      (TopCat.of (B × MSph (n + 1))) (TopCat.of (B × MSph (n + 1)))
      (𝟙 (TopCat.of (B × MSph (n + 1))))) k) := by
    intro k
    rw [Work.Cohomology.dualChainMap_id, HomologicalComplex.homologyMap_id]
    infer_instance
  have hA : ∀ k, CategoryTheory.IsIso (HomologicalComplex.homologyMap (Work.Cohomology.dualChainMap R
      (TopCat.of ↥(ppLt B n)) (TopCat.of ↥(ppLe B n))
      (Work.Cohomology.relMapSub (ppLt B n) (ppLe B n)
        (𝟙 (TopCat.of (B × MSph (n + 1)))) (fun x hx => ppLt_subset_ppLe B n hx))) k) := by
    intro k
    have heq : Work.Cohomology.relMapSub (ppLt B n) (ppLe B n)
        (𝟙 (TopCat.of (B × MSph (n + 1)))) (fun x hx => ppLt_subset_ppLe B n hx)
        = TopCat.ofHom (bandIncl B n) := by
      apply TopCat.ext
      intro a
      rfl
    rw [heq]
    exact isIso_bandIncl_R R B n k
  exact isIso_homologyMap_relComplexMap (X₁ := TopCat.of (B × MSph (n + 1)))
    (X₂ := TopCat.of (B × MSph (n + 1))) (ppLt B n) (ppLe B n)
    (𝟙 (TopCat.of (B × MSph (n + 1)))) (fun x hx => ppLt_subset_ppLe B n hx) R hX hA m


/-! ## Step (b): excising the south cap -/



/-- **Step (b)**: the excision of the south cap, followed by the identification of the
product-subtype with the product, induces an isomorphism on relative cohomology. -/
theorem isIso_relCohMap_excision_R (m : ℕ) :
    CategoryTheory.IsIso (relCohMap (excMap B n) (Qset B n) (ppLt B n)
      (fun x hx => by
        rw [excMap]
        exact ⟨x.2.1.2, hx.2⟩) R m) := by
  let X : TopCat := TopCat.of (B × MSph (n + 1))
  let S : Set X := {p : B × MSph (n + 1) | p ∉ Zcap B n}
  let A : Set X := ppLt B n
  have hZ : closure (Zcap B n) ⊆ interior (ppLt B n) := by
    have hsub : Zcap B n ⊆ ppLt B n := fun p hp => ⟨hp.1, lt_of_le_of_lt hp.2 (by norm_num)⟩
    calc closure (Zcap B n) = Zcap B n := (isClosed_Zcap B n).closure_eq
      _ ⊆ ppLt B n := hsub
      _ = interior (ppLt B n) := (IsOpen.interior_eq (isOpen_ppLt B n)).symm
  -- the excision isomorphism
  haveI h1 : CategoryTheory.IsIso (relCohMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥S, ↑X))
      ((Subtype.val : ↥S → ↑X) ⁻¹' ppLt B n) (ppLt B n)
      (fun x hx => hx) R m) :=
    Work.StemsB.relComplexMapExcision_R R X A (Zcap B n) hZ m
  -- the identification of the product-subtype with the product
  haveI h2 : CategoryTheory.IsIso (relCohMap
      (excHomeo B n : C(B × ↥(flGt n (-(1 / 2))), ↥S)) (Qset B n)
      ((Subtype.val : ↥S → B × MSph (n + 1)) ⁻¹' ppLt B n)
      (fun x hx => by
        have hq : lastC n x.2.1.1 < 1 / 2 := (mem_Qset B n).mp hx
        exact ⟨x.2.1.2, hq⟩) R m) :=
    CapGlue.isIso_relComplexMap_homeomorph (Qset B n)
      ((Subtype.val : ↥S → B × MSph (n + 1)) ⁻¹' ppLt B n) (excHomeo B n)
      (by
        intro x
        constructor
        · intro hx
          have hq : lastC n x.2.1.1 < 1 / 2 := (mem_Qset B n).mp hx
          exact ⟨x.2.1.2, hq⟩
        · intro hx
          exact (mem_Qset B n).mpr hx.2) R m
  -- the composite is the map of pairs of step (b)
  have hcomp := relCohMap_comp' (A := Qset B n)
    (B := (Subtype.val : ↥S → B × MSph (n + 1)) ⁻¹' ppLt B n) (C := ppLt B n)
    (f := (excHomeo B n : C(B × ↥(flGt n (-(1 / 2))), ↥S)))
    (g := (⟨Subtype.val, continuous_subtype_val⟩ : C(↥S, B × MSph (n + 1))))
    (hf := (fun x hx => by
        have hq : lastC n x.2.1.1 < 1 / 2 := (mem_Qset B n).mp hx
        exact ⟨x.2.1.2, hq⟩))
    (hg := (fun x hx => hx))
    (hgf := (fun x hx => by
        have hq : lastC n x.2.1.1 < 1 / 2 := (mem_Qset B n).mp hx
        exact ⟨x.2.1.2, hq⟩)) R m
  have hmap : (⟨Subtype.val, continuous_subtype_val⟩ : C(↥S, B × MSph (n + 1))).comp
      (excHomeo B n : C(B × ↥(flGt n (-(1 / 2))), ↥S)) = excMap B n := by
    apply ContinuousMap.ext
    intro p
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      rfl
  haveI : CategoryTheory.IsIso (relCohMap
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(↥S, B × MSph (n + 1))).comp
        (excHomeo B n : C(B × ↥(flGt n (-(1 / 2))), ↥S)))
      (Qset B n) (ppLt B n)
      (fun x hx => by
        have hq : lastC n x.2.1.1 < 1 / 2 := (mem_Qset B n).mp hx
        exact ⟨x.2.1.2, hq⟩) R m) := by
    rw [← hcomp]
    infer_instance
  rw [relCohMap_congr' (Qset B n) (ppLt B n) hmap _ _ R m] at this
  exact this


/-! ## Step (c): the cap map -/


/-- The ambient component of step (c): the cap map is a homotopy equivalence. -/
theorem isIso_capMapPairC_X_R (k : ℕ) : CategoryTheory.IsIso (HomologicalComplex.homologyMap
    (Work.Cohomology.dualChainMap R (TopCat.of (B × MBall n))
      (TopCat.of (B × ↥(flGt n (-(1 / 2))))) (TopCat.ofHom (capMapPairC B n))) k) := by
  haveI hcontr : ContractibleSpace ↥(flGt n (-(1 / 2))) := CapContract.contractibleSpace_flGt n
  have h1 : ((capBig n).comp (stripBig n)).Homotopic
      (ContinuousMap.id ↥(flGt n (-(1 / 2)))) :=
    homotopic_of_contractible_codomain _ _
  have h2 : ((stripBig n).comp (capBig n)).Homotopic (ContinuousMap.id (MBall n)) :=
    (CapBall.stripBig_comp_capBig n) ▸ ContinuousMap.Homotopic.refl (ContinuousMap.id (MBall n))
  have heq : TopCat.ofHom (capMapPairC B n)
      = TopCat.ofHom ((ContinuousMap.id B).prodMap (capBig n)) := rfl
  rw [heq]
  exact CapGlue.isIso_homologyMap_dualChainMap_prodMap (B := B) (capBig n) (stripBig n)
    h1 h2 R k

/-- The `A`-level component of step (c): the restriction of the cap map to the boundary sphere is a
homotopy equivalence. -/
theorem isIso_capMapPairC_A_R (k : ℕ) : CategoryTheory.IsIso (HomologicalComplex.homologyMap
    (Work.Cohomology.dualChainMap R (TopCat.of ↥(Abound B n)) (TopCat.of ↥(Qset B n))
      (Work.Cohomology.relMapSub (Abound B n) (Qset B n)
        (TopCat.ofHom (capMapPairC B n)) (capQ_mem B n))) k) := by
  have heq : Work.Cohomology.relMapSub (Abound B n) (Qset B n)
      (TopCat.ofHom (capMapPairC B n)) (capQ_mem B n)
      = TopCat.ofHom (capPairRestrict B n) := by
    apply TopCat.ext
    intro x
    rfl
  rw [heq]
  exact Work.Cohomology.homotopyEquiv R (TopCat.of ↥(Abound B n)) (TopCat.of ↥(Qset B n))
    (TopCat.ofHom (capPairRestrict B n)) (TopCat.ofHom (capPairRestrictInv B n))
    (capPairHomotopyInv B n) (capPairHomotopy B n) k

/-- **Step (c)**: the cap map induces an isomorphism on the relative cohomology of the pair
`(B × Dⁿ, B × Sⁿ⁻¹) → (B × {last > -1/2}, B × {-1/2 < last < 1/2})`. -/
theorem isIso_relCohMap_cap_R (m : ℕ) :
    CategoryTheory.IsIso (relCohMap (capMapPairC B n) (Abound B n) (Qset B n)
      (capQ_mem B n) R m) :=
  Work.Thom.isIso_homologyMap_relComplexMap (X₁ := TopCat.of (B × MBall n))
    (X₂ := TopCat.of (B × ↥(flGt n (-(1 / 2))))) (Abound B n) (Qset B n)
    (TopCat.ofHom (capMapPairC B n)) (capQ_mem B n) R
    (fun k => isIso_capMapPairC_X_R R B n k) (fun k => isIso_capMapPairC_A_R R B n k) m


end

end Work.Thom
