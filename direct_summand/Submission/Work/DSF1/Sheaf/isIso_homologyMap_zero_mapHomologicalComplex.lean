import Mathlib

namespace Work.DSF1.Sheaf

open CategoryTheory CategoryTheory.Limits

set_option linter.style.haveILetI false

universe u v w x

/-- If `X` is a zero object, then any additive functor preserves the cokernel of a morphism
out of `X` (which is necessarily a zero morphism, so that the cokernel is the identity). -/
lemma preservesColimit_parallelPair_of_isZero {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {D : Type w} [Category.{x} D] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] {X Y : C} (f : X ⟶ Y) (hX : IsZero X) :
    PreservesColimit (parallelPair f 0) F := by
  have h0 : f = 0 := hX.eq_zero_of_src f
  subst h0
  infer_instance

/-- For a cochain complex `K` strictly supported in degrees `≥ 0`, the first object of the
short complex `K.sc 0` (namely `K.X (-1)`) is a zero object. -/
lemma isZero_sc_zero_X₁ {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    (K : CochainComplex C ℤ) [K.IsStrictlyGE 0] : IsZero ((K.sc 0).X₁) := by
  have hprev : (ComplexShape.up ℤ).prev 0 = -1 := by
    apply ComplexShape.prev_eq'
    simp [ComplexShape.up, ComplexShape.up']
  exact IsZero.of_iso (K.isZero_of_isStrictlyGE 0 (-1) (by norm_num)) (K.XIsoOfEq hprev)

/-- A functor preserving finite limits (in particular kernels) preserves the left homology of
the short complex `K.sc 0` when `K` is strictly supported in degrees `≥ 0`: the only cokernel
involved is that of a morphism out of the zero object `K.X (-1)`. -/
lemma preservesLeftHomologyOf_sc_zero {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type w} [Category.{x} D] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex C ℤ) [K.IsStrictlyGE 0] :
    F.PreservesLeftHomologyOf (K.sc 0) := by
  haveI : (K.sc 0).leftHomologyData.IsPreservedBy F :=
    ShortComplex.LeftHomologyData.IsPreservedBy.mk (by infer_instance) (by
      exact preservesColimit_parallelPair_of_isZero F _
        (isZero_sc_zero_X₁ (K := K)))
  exact CategoryTheory.Functor.PreservesLeftHomologyOf.mk' F (K.sc 0).leftHomologyData

/-- A left exact additive functor commutes with `H⁰` on complexes concentrated in degrees `≥ 0`:
if `f : K ⟶ L` is a quasi-isomorphism between cochain complexes strictly supported in degrees
`≥ 0`, then `H⁰ (F f)` is an isomorphism.
Sketch: for `K` strictly supported in degrees `≥ 0`, `H⁰ K` is the kernel of `K.d 0 1` (there are
no boundaries in degree `0`), and `F` preserves kernels; this gives a natural isomorphism
`H⁰ (F K) ≅ F (H⁰ K)` (for all such `K`), under which `H⁰ (F f)` corresponds to `F (H⁰ f)`.
Since `f` is a quasi-isomorphism, `H⁰ f` is an isomorphism, hence so is `F (H⁰ f)`. -/
theorem isIso_homologyMap_zero_mapHomologicalComplex {C : Type u} [CategoryTheory.Category.{v} C]
    [CategoryTheory.Abelian C]
    {D : Type w} [CategoryTheory.Category.{x} D] [CategoryTheory.Abelian D]
    (F : CategoryTheory.Functor C D) [F.Additive] [CategoryTheory.Limits.PreservesFiniteLimits F]
    {K L : CochainComplex C ℤ} [K.IsStrictlyGE 0] [L.IsStrictlyGE 0] (f : K ⟶ L) [QuasiIso f] :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f) 0) := by
  haveI hK : F.PreservesLeftHomologyOf (K.sc 0) := preservesLeftHomologyOf_sc_zero F K
  haveI hL : F.PreservesLeftHomologyOf (L.sc 0) := preservesLeftHomologyOf_sc_zero F L
  -- The degree `0` part of `f` as a morphism of short complexes.
  let Scf : K.sc 0 ⟶ L.sc 0 :=
    (HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) 0).map f
  have hhom : IsIso (ShortComplex.homologyMap Scf) :=
    (quasiIsoAt_iff_isIso_homologyMap f 0).1 (QuasiIso.quasiIsoAt 0)
  let hhomIso := @asIso _ _ _ _ (ShortComplex.homologyMap Scf) hhom
  -- The canonical isomorphism `H⁰ (F K) ≅ F (H⁰ K)`, built from the preservation of homology
  -- of the short complex `K.sc 0` and the isomorphism `H⁰ f`.
  let Φ : ((K.sc 0).map F).homology ≅ F.obj ((L.sc 0).homology) :=
    ((K.sc 0).mapHomologyIso F).trans (F.mapIso hhomIso)
  -- Naturality of `mapHomologyIso` in the short complex.
  have hsq : ShortComplex.homologyMap (F.mapShortComplex.map Scf) ≫
      ((L.sc 0).mapHomologyIso F).hom = Φ.hom :=
    ShortComplex.mapHomologyIso_hom_naturality (F := F) Scf
  have hX : ShortComplex.homologyMap (F.mapShortComplex.map Scf) =
      Φ.hom ≫ ((L.sc 0).mapHomologyIso F).inv := by
    rw [← hsq]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h1 : ShortComplex.homologyMap (F.mapShortComplex.map Scf)
      ≫ (((L.sc 0).mapHomologyIso F).hom ≫ Φ.inv) = 𝟙 _ := by
    rw [← Category.assoc, hsq, Iso.hom_inv_id]
  have h2 : (((L.sc 0).mapHomologyIso F).hom ≫ Φ.inv)
      ≫ ShortComplex.homologyMap (F.mapShortComplex.map Scf) = 𝟙 _ := by
    rw [hX]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id]
  exact IsIso.mk ⟨((L.sc 0).mapHomologyIso F).hom ≫ Φ.inv, h1, h2⟩

end Work.DSF1.Sheaf
