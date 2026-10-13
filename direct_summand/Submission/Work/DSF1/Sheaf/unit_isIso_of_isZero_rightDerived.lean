import Mathlib
import Submission.Work.DSMap.Map
import Submission.Work.DSF1.Sheaf.mapHomologicalComplex_extendUpNat

/-!
# The acyclicity criterion for the right derived functor of a left exact functor

If `F : C ⥤ D` is an additive, left exact functor between abelian categories, `C` has enough
injectives, and `M : C` satisfies `R^q F (M) = 0` for all `q > 0`, then the unit
`F.rightDerivedFunctorPlusUnith` of the right derived functor of `F` on the bounded below
homotopy categories is an isomorphism at the one-term complex `M[0]`.

This is obligation (H1) of `DSF1` of the direct summand project (see `DSF1/DESIGN.md`).

The proof is the classical one. Choose an injective resolution `R` of `M`
(`InjectiveResolution.cochainComplex` is the associated bounded below cochain complex of injective
objects) and let `R.ι' : (single 0).obj M ⟶ R.cochainComplex` be its augmentation, which is a
quasi-isomorphism. Two inputs are used:

* the unit of the right derived functor is an isomorphism at every bounded below complex of
  injective objects (Mathlib's instance for the right derivability structure whose resolutions are
  the bounded below complexes of injectives);
* the augmentation `R.ι'` remains a quasi-isomorphism after applying `F`. Indeed, for `q : ℕ`,
  `H^q (F R.cochainComplex) ≅ H^q (F R.cocomplex) ≅ (F.rightDerived q).obj M` (via
  `HomologicalComplex.extendHomologyIso` and `InjectiveResolution.isoRightDerivedObj`), so the
  hypothesis `h` gives the vanishing of the target in positive degrees, while the source
  `F ((single 0).obj M)` is concentrated in degree `0`; in degree `0` the claim is the statement
  that a left exact functor commutes with `H⁰` on complexes supported in degrees `≥ 0`
  (`isIso_homologyMap_zero_mapHomologicalComplex` below), and in negative degrees both sides
  vanish.

Finally the unit is natural, so the unit at `M[0]` is the composite of the unit at the injective
resolution with two isomorphisms, hence an isomorphism.
-/

namespace Work.DSF1.Sheaf

open CategoryTheory Limits

universe u v w x

set_option linter.style.haveILetI false

/-- The one-term complex `M[0]`, as a bounded below cochain complex. -/
private noncomputable def singlePlusObj (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] (M : C) : CochainComplex.Plus C :=
  ⟨(CochainComplex.singleFunctor C 0).obj M, ⟨0, inferInstance⟩⟩

set_option maxHeartbeats 1600000 in
/-- A left exact additive functor commutes with `H⁰` on complexes concentrated in degrees `≥ 0`:
if `f : K ⟶ L` is a quasi-isomorphism between cochain complexes strictly supported in degrees
`≥ 0`, then `H⁰ (F f)` is an isomorphism.

Indeed, for such a complex `K` the homology in degree `0` is computed by the short complex
`K.sc 0`, whose differential `(K.sc 0).f` vanishes by strict support in degrees `≥ 0`; hence the
left homology data of `K.sc 0` is preserved by `F` (left exactness gives preservation of the
kernel of `(K.sc 0).g`, and the other condition concerns the cokernel of `(K.sc 0).f'`, which
vanishes by the preceding point).  Naturality of `ShortComplex.mapHomologyIso` then identifies
`H⁰ (F f)` with `F (H⁰ f)`, which is an isomorphism because `f` is a quasi-isomorphism. -/
private theorem isIso_homologyMap_zero_mapHomologicalComplex {C : Type u} [Category.{v} C]
    [Abelian C] {D : Type w} [Category.{x} D] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    {K L : CochainComplex C ℤ} [K.IsStrictlyGE 0] [L.IsStrictlyGE 0] (f : K ⟶ L) [QuasiIso f] :
    IsIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f) 0) := by
  -- the incoming differentials vanish because the complexes are strictly supported in degrees `≥ 0`
  have hK : K.d (-1) 0 = 0 :=
    (CochainComplex.isZero_of_isStrictlyGE K 0 (-1) (by norm_num)).eq_of_src _ _
  have hL : L.d (-1) 0 = 0 :=
    (CochainComplex.isZero_of_isStrictlyGE L 0 (-1) (by norm_num)).eq_of_src _ _
  -- the `f` component of the short complexes in degree `0` is this vanishing differential
  have hfK : (K.sc 0).f = 0 := by
    show K.d ((ComplexShape.up ℤ).prev 0) 0 = 0
    rw [show (ComplexShape.up ℤ).prev 0 = (-1 : ℤ) by simp]
    exact hK
  have hfL : (L.sc 0).f = 0 := by
    show L.d ((ComplexShape.up ℤ).prev 0) 0 = 0
    rw [show (ComplexShape.up ℤ).prev 0 = (-1 : ℤ) by simp]
    exact hL
  -- the `.f'` morphism of the canonical left homology data is zero
  have hf'K : (K.sc 0).leftHomologyData.f' = 0 := by
    rw [← cancel_mono (K.sc 0).leftHomologyData.i, ShortComplex.LeftHomologyData.f'_i,
      hfK, zero_comp]
  have hf'L : (L.sc 0).leftHomologyData.f' = 0 := by
    rw [← cancel_mono (L.sc 0).leftHomologyData.i, ShortComplex.LeftHomologyData.f'_i,
      hfL, zero_comp]
  -- so `F` preserves the left homology of the two short complexes
  have iK : (K.sc 0).leftHomologyData.IsPreservedBy F :=
    ⟨inferInstance, by rw [hf'K]; infer_instance⟩
  have iL : (L.sc 0).leftHomologyData.IsPreservedBy F :=
    ⟨inferInstance, by rw [hf'L]; infer_instance⟩
  haveI pK : F.PreservesLeftHomologyOf (K.sc 0) :=
    Functor.PreservesLeftHomologyOf.mk' F (K.sc 0).leftHomologyData
  haveI pL : F.PreservesLeftHomologyOf (L.sc 0) :=
    Functor.PreservesLeftHomologyOf.mk' F (L.sc 0).leftHomologyData
  -- the map of short complexes induced by `f`
  let φ : (K.sc 0) ⟶ (L.sc 0) :=
    (HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) 0).map f
  have hφ : IsIso (ShortComplex.homologyMap φ) := by
    haveI : QuasiIsoAt f 0 := inferInstance
    exact (quasiIsoAt_iff_isIso_homologyMap f 0).mp inferInstance
  have hgoal : IsIso (ShortComplex.homologyMap (F.mapShortComplex.map φ)) := by
    haveI h3 : IsIso (F.map (ShortComplex.homologyMap φ)) := inferInstance
    haveI h1 : IsIso (((K.sc 0).mapHomologyIso F).hom) := inferInstance
    haveI h2 : IsIso (((L.sc 0).mapHomologyIso F).inv) := inferInstance
    have hnat : ShortComplex.homologyMap (F.mapShortComplex.map φ) ≫
        ((L.sc 0).mapHomologyIso F).hom =
        ((K.sc 0).mapHomologyIso F).hom ≫ F.map (ShortComplex.homologyMap φ) :=
      ShortComplex.mapHomologyIso_hom_naturality φ F
    have heq : ShortComplex.homologyMap (F.mapShortComplex.map φ) =
        ((K.sc 0).mapHomologyIso F).hom ≫ F.map (ShortComplex.homologyMap φ) ≫
          ((L.sc 0).mapHomologyIso F).inv := by
      rw [← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [heq]
    infer_instance
  exact hgoal

set_option maxHeartbeats 1600000 in
/-- **The acyclicity criterion.**  If the higher right derived functors of a left exact additive
functor `F` vanish at `M`, then the unit of the right derived functor of `F` is an isomorphism at
`M[0]`. -/
theorem unit_isIso_of_isZero_rightDerived {C : Type u} [CategoryTheory.Category.{v} C]
    [CategoryTheory.Abelian C] [HasDerivedCategory C] [CategoryTheory.EnoughInjectives C]
    {D : Type w} [CategoryTheory.Category.{x} D] [CategoryTheory.Abelian D]
    [HasDerivedCategory D] (F : CategoryTheory.Functor C D) [F.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits F] (M : C)
    (h : ∀ q : ℕ, 0 < q → CategoryTheory.Limits.IsZero ((F.rightDerived q).obj M)) :
    CategoryTheory.IsIso (F.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.singleFunctor C 0).obj M)) := by
  -- a chosen injective resolution of `M`, as a bounded below complex of injective objects
  let R : InjectiveResolution M := injectiveResolution M
  let L₀ : CochainComplex.Plus C := ⟨R.cochainComplex, ⟨0, inferInstance⟩⟩
  let i : singlePlusObj C M ⟶ L₀ := ObjectProperty.homMk R.ι'
  have hi : CochainComplex.Plus.quasiIso C i := by
    rw [CochainComplex.Plus.quasiIso_iff]
    exact inferInstanceAs (QuasiIso R.ι')
  -- the image of the resolution map under `F` is again a quasi-isomorphism
  have hcrux : QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map R.ι') := by
    rw [quasiIso_iff]
    intro q
    rw [quasiIsoAt_iff_isIso_homologyMap]
    -- the source of the map has homology only in degree `0`
    have hsrc : ∀ (j : ℤ), j ≠ 0 → IsZero (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor C 0).obj M)).homology j) := by
      intro j hj
      have e := (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app M
      exact IsZero.of_iso
        (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 (F.obj M) j hj)
        ((HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) j).mapIso e)
    -- the target of the map has vanishing homology in negative degrees
    have htgt_neg : ∀ (j : ℤ), j < 0 → IsZero (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        R.cochainComplex).homology j) := by
      intro j hj
      obtain ⟨e⟩ := mapHomologicalComplex_extendUpNat F R.cocomplex
      refine IsZero.of_iso ?_ ((HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) j).mapIso e)
      exact CochainComplex.isZero_of_isGE (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        R.cocomplex).extend ComplexShape.embeddingUpNat) 0 j hj
    -- the target of the map has vanishing homology in positive degrees, by hypothesis
    have htgt_pos : ∀ (n : ℕ), 0 < n → IsZero (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        R.cochainComplex).homology (n : ℤ)) := by
      intro n hn
      obtain ⟨e⟩ := mapHomologicalComplex_extendUpNat F R.cocomplex
      refine IsZero.of_iso ?_ ((HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ)
        (n : ℤ)).mapIso e)
      refine IsZero.of_iso ?_ (HomologicalComplex.extendHomologyIso
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex) ComplexShape.embeddingUpNat
        (show ComplexShape.embeddingUpNat.f n = (n : ℤ) from rfl))
      exact IsZero.of_iso (h n hn) (R.isoRightDerivedObj F n).symm
    rcases lt_trichotomy q 0 with hq | hq | hq
    · exact IsZero.isIso (hsrc q (by omega)) (htgt_neg q hq) _
    · subst hq
      exact isIso_homologyMap_zero_mapHomologicalComplex F R.ι'
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_lt hq)
      have hn : 0 < n := by omega
      exact IsZero.isIso (hsrc (n : ℤ) (by omega)) (htgt_pos n hn) _
  have hFi : CochainComplex.Plus.quasiIso D (F.mapCochainComplexPlus.map i) := by
    rw [CochainComplex.Plus.quasiIso_iff]
    exact hcrux
  -- the resolution map, seen in the bounded below homotopy category
  let s : (HomotopyCategory.Plus.quotient C).obj (singlePlusObj C M) ⟶
      (HomotopyCategory.Plus.quotient C).obj L₀ := (HomotopyCategory.Plus.quotient C).map i
  have hs : HomotopyCategory.Plus.quasiIso C s := by
    have h' := MorphismProperty.map_mem_map (CochainComplex.Plus.quasiIso C)
      (HomotopyCategory.Plus.quotient C) i hi
    rwa [HomotopyCategory.Plus.quasiIso_map_quotient_eq_quasiIso] at h'
  -- the unit is an isomorphism at the injective resolution
  have hLu : IsIso (F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient C).obj L₀)) :=
    inferInstance
  -- the two maps appearing in the naturality square of the unit are isomorphisms
  have hsQ : IsIso (DerivedCategory.Plus.Qh.map s) := Localization.inverts _ _ _ hs
  have hFsQ : IsIso (DerivedCategory.Plus.Qh.map (F.mapHomotopyCategoryPlus.map s)) := by
    have hQ : IsIso (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map i)) :=
      Localization.inverts _ _ _ hFi
    have hQh : IsIso (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient D).map
        (F.mapCochainComplexPlus.map i))) :=
      (NatIso.isIso_map_iff (DerivedCategory.Plus.quotientCompQhIso D).symm _).mp hQ
    have heq : F.mapHomotopyCategoryPlus.map s =
        (HomotopyCategory.Plus.quotient D).map (F.mapCochainComplexPlus.map i) := by
      have hnat := NatTrans.naturality (F.quotientCompMapHomotopyCategoryPlusIso).hom i
      have h1 : (F.quotientCompMapHomotopyCategoryPlusIso).hom.app (singlePlusObj C M) = 𝟙 _ := rfl
      have h2 : (F.quotientCompMapHomotopyCategoryPlusIso).hom.app L₀ = 𝟙 _ := rfl
      rw [h1, h2] at hnat
      simpa [s] using hnat
    rw [heq]
    exact hQh
  -- naturality of the unit of the right derived functor
  have nat : DerivedCategory.Plus.Qh.map (F.mapHomotopyCategoryPlus.map s) ≫
      F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient C).obj L₀) =
      F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient C).obj (singlePlusObj C M)) ≫
        F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map s) :=
    F.rightDerivedFunctorPlusUnith.naturality s
  have hB : IsIso (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map s)) := inferInstance
  -- conclude: the unit at `M[0]` is a composite of isomorphisms
  have hgoal : IsIso (F.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient C).obj (singlePlusObj C M))) := by
    rw [show F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient C).obj
          (singlePlusObj C M)) =
        (DerivedCategory.Plus.Qh.map (F.mapHomotopyCategoryPlus.map s) ≫
          F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient C).obj L₀)) ≫
          CategoryTheory.inv (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map s)) from by
      rw [nat, Category.assoc, IsIso.hom_inv_id, Category.comp_id]]
    exact inferInstanceAs (IsIso ((DerivedCategory.Plus.Qh.map (F.mapHomotopyCategoryPlus.map s) ≫
          F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient C).obj L₀)) ≫
          CategoryTheory.inv (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map s))))
  exact hgoal

end Work.DSF1.Sheaf
