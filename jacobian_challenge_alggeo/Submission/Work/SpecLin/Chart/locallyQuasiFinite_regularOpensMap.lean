import Mathlib
import Submission.Work.SpecLin.Chart.Regular
import Submission.Work.SpecLin.Chart.RegularOpensMap
import Submission.Work.SpecLin.Chart.RegularOpensAffineAux
import Submission.Work.CurveBasics.All

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry TopCat TopCat.Presheaf Opposite
open scoped Classical

universe u

namespace Work.SpecLin.Chart

open Work.CurveBasics

variable {K : Type u} [Field K]

/-! ## Preimages of basic opens -/

/-- The preimage of the basic open of a polynomial `r` under the coordinate morphism is the
basic open of the section `r(x)`. -/
theorem preimage_basicOpen_regularOpensMap (C : Curve K) (x : C.functionField) (r : Polynomial K) :
    (regularOpensMap C x) ⁻¹ᵁ (PrimeSpectrum.basicOpen r) =
      (regularOpens C x).toScheme.basicOpen (regularOpensCoeff C x r) := by
  rw [regularOpensMap, Scheme.Hom.comp_preimage]
  rw [AlgebraicGeometry.SpecMap_preimage_basicOpen]
  rw [Scheme.toSpecΓ_preimage_basicOpen]
  rfl

/-! ## The open `regularOpens C x` is an integral Noetherian scheme of dimension at most one -/

theorem isNoetherian_regularOpens_toScheme (C : Curve K) (x : C.functionField) :
    IsNoetherian (regularOpens C x).toScheme := by
  haveI : CompactSpace (regularOpens C x).toScheme := by
    have h : IsCompact ((regularOpens C x) : Set C.left) :=
      TopologicalSpace.NoetherianSpace.isCompact _
    exact isCompact_iff_compactSpace.mp h
  exact ⟨⟩

theorem coheight_le_one_regularOpens_toScheme (C : Curve K) (x : C.functionField)
    (z : (regularOpens C x).toScheme) : Order.coheight z ≤ 1 := by
  rw [← AlgebraicGeometry.coheight_eq_of_isOpenImmersion (regularOpens C x).ι (x := z)]
  exact Curve.coheight_le_one C _

/-- The complement of a basic open of a nonzero section of an integral Noetherian one-dimensional
scheme is finite. -/
theorem finite_compl_basicOpen {X : Scheme} [IsIntegral X] [IsNoetherian X]
    (hco : ∀ z : X, Order.coheight z ≤ 1) (b : Γ(X, ⊤)) (hb : b ≠ 0) :
    ((X.basicOpen b : X.Opens) : Set X)ᶜ.Finite := by
  refine Work.CurveBasics.Order.finite_of_isClosed_of_genericPoint_notMem _ ?_ ?_ hco
  · exact (X.basicOpen b).isOpen.isClosed_compl
  · rw [Set.notMem_compl_iff]
    have hne : X.basicOpen b ≠ ⊥ := fun h => hb ((AlgebraicGeometry.basicOpen_eq_bot_iff b).mp h)
    have hne' : ((X.basicOpen b : X.Opens) : Set X).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h
      exact hne (TopologicalSpace.Opens.ext (by rw [h, TopologicalSpace.Opens.coe_bot]))
    obtain ⟨y, hy⟩ := hne'
    exact (genericPoint_spec X).mem_open_set_iff (X.basicOpen b).isOpen |>.mpr ⟨y, trivial, hy⟩

/-! ## Auxiliary facts about the coordinate morphism -/

/-- The ring homomorphism `Γ(U,⊤) → K(C)` obtained by restricting to `U = regularOpens C x`
and taking the germ at the generic point. -/
noncomputable def germRestrict (C : Curve K) (x : C.functionField) :
    Γ((regularOpens C x).toScheme, ⊤) →+* C.functionField :=
  ((Scheme.Opens.topIso (regularOpens C x)).hom ≫
    C.germToFunctionField (regularOpens C x)).hom

/-- Restricting along the open immersion `regularOpens C x ⊆ C` commutes with the `topIso`. -/
theorem topIso_hom_ι_appTop (C : Curve K) (x : C.functionField) (z : Γ(C.left, ⊤)) :
    (Scheme.Opens.topIso (regularOpens C x)).hom ((regularOpens C x).ι.appTop z) =
      C.left.presheaf.map (homOfLE (le_top : regularOpens C x ≤ ⊤)).op z := by
  simp only [Scheme.Opens.topIso_hom, Scheme.Opens.ι_appTop]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  congr 1

/-- The map `germRestrict C x` sends the section `regularOpensTopSection C x` to `x`. -/
theorem germRestrict_regularOpensTopSection (C : Curve K) (x : C.functionField) :
    germRestrict C x (regularOpensTopSection C x) = x := by
  rw [show germRestrict C x (regularOpensTopSection C x) =
      C.germToFunctionField (regularOpens C x)
        ((Scheme.Opens.topIso (regularOpens C x)).hom
          ((Scheme.Opens.topIso (regularOpens C x)).inv (regularOpensSection C x))) from rfl]
  rw [Iso.inv_hom_id_apply]
  exact germToFunctionField_regularOpensSection C x

/-- The map `germRestrict C x` is compatible with the structure morphisms: it is a morphism of
`K`-algebras. -/
theorem germRestrict_structureRingHom (C : Curve K) (x : C.functionField) (c : K) :
    germRestrict C x (structureRingHom (regularOpens C x).toScheme c) =
      algebraMap K C.functionField c := by
  rw [structureRingHom]
  simp only [ConcreteCategory.comp_apply]
  rw [show ((regularOpens C x).toScheme ↘ Spec (CommRingCat.of K)) =
      (regularOpens C x).ι ≫ C.hom from rfl]
  rw [Scheme.Hom.comp_appTop]
  show (C.germToFunctionField (regularOpens C x)).hom
      ((Scheme.Opens.topIso (regularOpens C x)).hom
        ((regularOpens C x).ι.appTop
          (C.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c)))) = _
  rw [topIso_hom_ι_appTop]
  rw [TopCat.Presheaf.germ_res_apply]
  rfl

/-- The coordinate homomorphism `regularOpensCoeff C x`, followed by the germ at the generic
point, is evaluation of polynomials at `x`. -/
theorem germRestrict_regularOpensCoeff (C : Curve K) (x : C.functionField) (P : Polynomial K) :
    germRestrict C x (regularOpensCoeff C x P) = Polynomial.aeval x P := by
  have hφ : regularOpensCoeff C x P =
      Polynomial.eval₂ (structureRingHom (regularOpens C x).toScheme)
        (regularOpensTopSection C x) P := rfl
  rw [hφ, Polynomial.hom_eval₂, germRestrict_regularOpensTopSection]
  rw [show (germRestrict C x).comp (structureRingHom (regularOpens C x).toScheme) =
      (algebraMap K C.functionField) from
    RingHom.ext (fun c => germRestrict_structureRingHom C x c)]
  rw [Polynomial.aeval_def]

theorem regularOpensCoeff_injective (C : Curve K) (x : C.functionField)
    (hx : Transcendental K x) : Function.Injective (regularOpensCoeff C x) := by
  rw [injective_iff_map_eq_zero]
  intro P hP
  have h1 : germRestrict C x (regularOpensCoeff C x P) = 0 := by rw [hP, map_zero]
  rw [germRestrict_regularOpensCoeff] at h1
  exact (transcendental_iff.mp hx) P h1

theorem asIdeal_ne_bot_regularOpensMap_aux (C : Curve K) (x : C.functionField)
    (w : (regularOpens C x).toScheme)
    (hw : IsClosed ({w} : Set (regularOpens C x).toScheme)) :
    ((regularOpensMap C x) w).asIdeal ≠ ⊥ := by
  haveI : LocallyOfFiniteType (regularOpensMap C x) := locallyOfFiniteType_regularOpensMap C x
  have hclosed : IsClosed ({(regularOpensMap C x) w} :
      Set (Spec (CommRingCat.of (Polynomial K)))) :=
    Scheme.Hom.closePoints_subset_preimage_closedPoints (regularOpensMap C x) hw
  have hmax : ((regularOpensMap C x) w).asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp hclosed
  exact ne_of_gt (Ideal.bot_lt_of_maximal _ (Polynomial.not_isField K))

/-- Every point of `regularOpens C x` other than its generic point is closed: the only
non-closed point of a curve is its generic point, which lies in `regularOpens C x`. -/
theorem isClosed_singleton_of_ne_genericPoint (C : Curve K) (x : C.functionField)
    (w : (regularOpens C x).toScheme) (hw : w ≠ genericPoint (regularOpens C x).toScheme) :
    IsClosed ({w} : Set (regularOpens C x).toScheme) := by
  rcases Curve.eq_genericPoint_or_isClosed C w.val with h | h
  · exfalso
    apply hw
    have hg : (genericPoint (regularOpens C x).toScheme).val = genericPoint C.left :=
      genericPoint_eq_of_isOpenImmersion (regularOpens C x).ι
    exact Subtype.ext (h.trans hg.symm)
  · rw [show ({w} : Set (regularOpens C x).toScheme) =
        Subtype.val ⁻¹' ({w.val} : Set C.left) from by ext z; simp]
    exact h.preimage continuous_subtype_val

/-! ## The main theorem -/

open CategoryTheory AlgebraicGeometry in
theorem locallyQuasiFinite_regularOpensMap {K : Type*} [Field K] (C : Work.CurveBasics.Curve K)
    (x : C.functionField) (hx : Transcendental K x) :
    LocallyQuasiFinite (Work.SpecLin.Chart.regularOpensMap C x) := by
  haveI hfin : LocallyOfFiniteType (regularOpensMap C x) :=
    locallyOfFiniteType_regularOpensMap C x
  refine LocallyQuasiFinite.of_finite_preimage_singleton (f := regularOpensMap C x) fun y => ?_
  by_cases hy : y.asIdeal = ⊥
  · have hsub : (regularOpensMap C x) ⁻¹' {y} ⊆
        {genericPoint (regularOpens C x).toScheme} := by
      intro w hw
      rw [Set.mem_singleton_iff]
      by_contra hne
      have h2 := asIdeal_ne_bot_regularOpensMap_aux C x w
        (isClosed_singleton_of_ne_genericPoint C x w hne)
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hw
      rw [hw, hy] at h2
      exact h2 rfl
    exact Set.Finite.subset (Set.finite_singleton _) hsub
  · obtain ⟨P, hPmem, hPne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hy
    have hφP : regularOpensCoeff C x P ≠ 0 := fun h =>
      hPne (regularOpensCoeff_injective C x hx (by rw [h, map_zero]))
    haveI hN : IsNoetherian (regularOpens C x).toScheme :=
      isNoetherian_regularOpens_toScheme C x
    refine Set.Finite.subset
      (finite_compl_basicOpen (fun z => coheight_le_one_regularOpens_toScheme C x z) _ hφP) ?_
    intro w hw
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hw
    simp only [Set.mem_compl_iff, SetLike.mem_coe]
    rw [← preimage_basicOpen_regularOpensMap C x P, Scheme.Hom.mem_preimage, hw,
      PrimeSpectrum.mem_basicOpen]
    exact fun h => h hPmem

end Work.SpecLin.Chart
