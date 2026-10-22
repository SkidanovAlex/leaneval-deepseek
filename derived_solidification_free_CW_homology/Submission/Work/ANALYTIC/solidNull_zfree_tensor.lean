import Mathlib
import Submission.Blueprint.Interfaces
import Submission.Work.ANALYTIC.Basic
import Submission.Work.ATOM.Defs
import Submission.Work.ATOM.Main
import Submission.Work.RESOL.Main
import Submission.Work.FLAT.Main
import Submission.Work.ANALYTIC.solidComplexLift
import Submission.Work.ATOM.isAtomicSum_tmul_zfree
import Submission.Work.REFL.solid_iff_testMap
import Submission.Work.DERFORMAL.Gen.AdjHomologicalComplex
import Submission.Work.DERFORMAL.Gen.AdjHomotopyCategory

/-!
# `SolidNull` is preserved by tensoring with a free light condensed abelian group

This file proves `Work.ANALYTIC.solidNull_zfree_tensor`: if the single complex on `A` is
solid-null (every morphism from it in `D(LightCondAb)` into the derived inclusion of a complex of
solid objects is zero), then the same holds for `ℤ[S] ⊗ A`.

## Strategy

Rather than the (unavailable) derived tensor–hom adjunction `Hom_D(A ⊗^L M, B) ≅
Hom_D(A, RHom(M, B))` of the paper, the proof uses the *underived* tensor–hom adjunction,
resolved on both sides:

* resolve `single A` by a functorial solid-cofibrant complex `ρ → single A` with atomic terms
  (`Work.RESOL.hasBoundedResolutionZero`), bounded above;
* the complex `X := ℤ[S] ⊗ ρ` (degreewise tensor with the flat `ℤ[S]`) is then bounded above with
  atomic terms, hence *solid-cofibrant* (`Work.RESOL.solidCofibrant_of_boundedAbove_atomic`), so
  `Hom_D(Q X, ι N) = Hom_K(hq X, hq (ι N))` for every complex `N` of solid objects;
* the adjunction `tensorLeft ℤ[S] ⊣ ihom ℤ[S]`, prolonged to complexes and descended to homotopy
  categories (`Work.DERFORMAL.Gen.AdjHomotopyCategory`), identifies `Hom_K(hq X, hq (ι N))` with
  `Hom_K(hq ρ, hq (ihom ℤ[S] (ι N)))`;
* `ihom ℤ[S] (ι N)` is a complex of *solid* objects (solidity is closed under internal homs into a
  solid object), so it lifts to a complex `M` of solid objects and the cofibrancy of `ρ` gives
  `Hom_K(hq ρ, hq (ι M)) = Hom_D(Q ρ, ι M) = Hom_D(single A, ι M)`, which is zero by hypothesis.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

noncomputable section

namespace Work.ANALYTIC

open _root_.LightCondensed _root_.LightCondensed.Solid

/-! ## Two elementary lemmas used in the main proof -/

/-- Conjugation transport for bijectivity of precomposition: if `e.hom ≫ f' = f ≫ e.hom`
then `f` and `f'` have the same precomposition-bijectivity. -/
lemma bijective_precomp_conj {C : Type*} [Category C] {A X Y : C} (e : X ≅ Y) (f : X ⟶ X)
    (f' : Y ⟶ Y) (h : e.hom ≫ f' = f ≫ e.hom) :
    Function.Bijective (fun g : X ⟶ A => f ≫ g) ↔
      Function.Bijective (fun g : Y ⟶ A => f' ≫ g) := by
  have hΨ : Function.Bijective (fun g : Y ⟶ A => e.hom ≫ g) := by
    refine ⟨fun a b hab => ?_, fun b => ⟨e.inv ≫ b, ?_⟩⟩
    · have h2 := congrArg (fun t => e.inv ≫ t) hab
      simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] using h2
    · simp only []
      rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hcomp : (fun g : X ⟶ A => f ≫ g) ∘ (fun g : Y ⟶ A => e.hom ≫ g) =
      (fun g : Y ⟶ A => e.hom ≫ g) ∘ (fun g : Y ⟶ A => f' ≫ g) := by
    funext g
    simp only [Function.comp_apply]
    rw [← Category.assoc, ← h, Category.assoc]
  constructor
  · intro hf
    have h1 : Function.Bijective ((fun g : X ⟶ A => f ≫ g) ∘ (fun g : Y ⟶ A => e.hom ≫ g)) :=
      Function.Bijective.comp hf hΨ
    rw [hcomp] at h1
    exact (Function.Bijective.of_comp_iff' hΨ (fun g : Y ⟶ A => f' ≫ g)).mp h1
  · intro hf
    have h1 : Function.Bijective ((fun g : Y ⟶ A => e.hom ≫ g) ∘ (fun g : Y ⟶ A => f' ≫ g)) :=
      Function.Bijective.comp hΨ hf
    rw [← hcomp] at h1
    exact (Function.Bijective.of_comp_iff (fun g : X ⟶ A => f ≫ g) hΨ).mp h1

/-- **F8 (REFS/01): solidity is stable under internal homs.** -/
lemma isSolid_ihom' (X M : LightCondAb) (hM : LightCondensed.isSolid M) :
    LightCondensed.isSolid ((ihom X).obj M) := by
  classical
  rw [Work.REFL.isSolid_iff_bijective_testMap]
  intro S
  let zf : LightCondAb := (LightCondensed.free (R := ℤ)).obj S.toCondensed
  let Z : LightCondAb := P ⊗ zf
  let f : Z ⟶ Z := oneMinusShift ▷ zf
  have hfs : Work.REFL.testMap S = f := rfl
  -- ## Step A: currying `Hom(Z, X ⟹ M) ≃ Hom(X ⊗ Z, M)`
  let Φ : (X ⊗ Z ⟶ M) ≃ (Z ⟶ (ihom X).obj M) := (ihom.adjunction X).homEquiv Z M
  have hA : Function.Bijective (fun g : Z ⟶ (ihom X).obj M => f ≫ g) ↔
      Function.Bijective (fun g : X ⊗ Z ⟶ M => (X ◁ f) ≫ g) := by
    have hcomp : (fun g : Z ⟶ (ihom X).obj M => f ≫ g) ∘ ⇑Φ =
        ⇑Φ ∘ (fun g : X ⊗ Z ⟶ M => (X ◁ f) ≫ g) := by
      funext g
      simp only [Function.comp_apply]
      exact (Adjunction.homEquiv_naturality_left (ihom.adjunction X) f g).symm
    constructor
    · intro h
      have h1 : Function.Bijective ((fun g : Z ⟶ (ihom X).obj M => f ≫ g) ∘ ⇑Φ) :=
        Function.Bijective.comp h (Equiv.bijective Φ)
      rw [hcomp] at h1
      exact (Function.Bijective.of_comp_iff' (Equiv.bijective Φ)
        (fun g : X ⊗ Z ⟶ M => (X ◁ f) ≫ g)).mp h1
    · intro h
      have h1 : Function.Bijective (⇑Φ ∘ (fun g : X ⊗ Z ⟶ M => (X ◁ f) ≫ g)) :=
        Function.Bijective.comp (Equiv.bijective Φ) h
      rw [← hcomp] at h1
      exact (Function.Bijective.of_comp_iff (fun g : Z ⟶ (ihom X).obj M => f ≫ g)
        (Equiv.bijective Φ)).mp h1
  -- ## Step B: the braiding moves `X` past `Z = P ⊗ zf`
  have hB : Function.Bijective (fun g : X ⊗ Z ⟶ M => (X ◁ f) ≫ g) ↔
      Function.Bijective (fun g : Z ⊗ X ⟶ M => (f ▷ X) ≫ g) := by
    refine bijective_precomp_conj (β_ X Z) (X ◁ f) (f ▷ X) ?_
    have hnat := BraidedCategory.braiding_naturality (𝟙 X) f
    simpa only [id_tensorHom, tensorHom_id] using hnat.symm
  -- ## Step C: associativity `(P ⊗ zf) ⊗ X ≅ P ⊗ (zf ⊗ X)`
  have hC : Function.Bijective (fun g : Z ⊗ X ⟶ M => (f ▷ X) ≫ g) ↔
      Function.Bijective (fun g : P ⊗ (zf ⊗ X) ⟶ M => (oneMinusShift ▷ (zf ⊗ X)) ≫ g) := by
    refine bijective_precomp_conj (α_ P zf X) (f ▷ X) (oneMinusShift ▷ (zf ⊗ X)) ?_
    have hnat := associator_naturality oneMinusShift (𝟙 zf) (𝟙 X)
    have hL : (oneMinusShift ⊗ₘ 𝟙 zf) ⊗ₘ 𝟙 X = (oneMinusShift ▷ zf) ▷ X := by
      rw [tensorHom_id oneMinusShift zf, tensorHom_id (oneMinusShift ▷ zf) X]
    have hR : oneMinusShift ⊗ₘ (𝟙 zf ⊗ₘ 𝟙 X) = oneMinusShift ▷ (zf ⊗ X) := by
      rw [id_tensorHom zf (𝟙 X), whiskerLeft_id, tensorHom_id]
    rw [hL, hR] at hnat
    exact hnat.symm
  -- ## Step D: `hM` through the currying `Hom(P ⊗ W, M) ≃ Hom(W, P ⟹ M)`
  have hD : Function.Bijective
      (fun g : P ⊗ (zf ⊗ X) ⟶ M => (oneMinusShift ▷ (zf ⊗ X)) ≫ g) := by
    haveI : IsIso ((MonoidalClosed.pre oneMinusShift).app M) := hM
    have hpost : Function.Bijective
        (fun k : zf ⊗ X ⟶ (ihom P).obj M => k ≫ (MonoidalClosed.pre oneMinusShift).app M) := by
      refine ⟨fun a b hab => ?_, fun b => ⟨b ≫ inv ((MonoidalClosed.pre oneMinusShift).app M), ?_⟩⟩
      · have h2 := congrArg (fun t => t ≫ inv ((MonoidalClosed.pre oneMinusShift).app M)) hab
        simpa only [Category.assoc, IsIso.hom_inv_id, Category.comp_id] using h2
      · simp only []
        rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    let Φ' : (P ⊗ (zf ⊗ X) ⟶ M) ≃ (zf ⊗ X ⟶ (ihom P).obj M) :=
      (ihom.adjunction P).homEquiv (zf ⊗ X) M
    have hcomp : (fun k : zf ⊗ X ⟶ (ihom P).obj M =>
          k ≫ (MonoidalClosed.pre oneMinusShift).app M) ∘ ⇑Φ' =
        ⇑Φ' ∘ (fun g : P ⊗ (zf ⊗ X) ⟶ M => (oneMinusShift ▷ (zf ⊗ X)) ≫ g) := by
      funext g
      simp only [Function.comp_apply]
      exact MonoidalClosed.curry_pre_app (f := oneMinusShift) (g := g)
    have h1 : Function.Bijective ((fun k : zf ⊗ X ⟶ (ihom P).obj M =>
          k ≫ (MonoidalClosed.pre oneMinusShift).app M) ∘ ⇑Φ') :=
      Function.Bijective.comp hpost (Equiv.bijective Φ')
    rw [hcomp] at h1
    exact (Function.Bijective.of_comp_iff' (Equiv.bijective Φ')
      (fun g : P ⊗ (zf ⊗ X) ⟶ M => (oneMinusShift ▷ (zf ⊗ X)) ≫ g)).mp h1
  exact hA.mpr (hB.mpr (hC.mpr hD))

/-! ## Elementary transport lemmas for `Subsingleton` of morphism sets -/

/-- A subsingleton of morphisms out of `X` transfers to morphisms out of any object isomorphic
to `X`. -/
lemma subsingleton_of_iso_source {C : Type*} [Category C] {X Y Z : C} (e : X ≅ Y)
    (h : Subsingleton (X ⟶ Z)) : Subsingleton (Y ⟶ Z) :=
  ⟨fun f g => by
    have h1 : e.hom ≫ f = e.hom ≫ g := Subsingleton.elim _ _
    calc f = e.inv ≫ (e.hom ≫ f) := (Iso.inv_hom_id_assoc e f).symm
      _ = e.inv ≫ (e.hom ≫ g) := by rw [h1]
      _ = g := Iso.inv_hom_id_assoc e g⟩

/-- A subsingleton of morphisms into `Z` transfers to morphisms into any object isomorphic
to `Z`. -/
lemma subsingleton_of_iso_target {C : Type*} [Category C] {X Z W : C} (e : Z ≅ W)
    (h : Subsingleton (X ⟶ Z)) : Subsingleton (X ⟶ W) :=
  ⟨fun f g => by
    have h1 : (f ≫ e.inv) = (g ≫ e.inv) := Subsingleton.elim _ _
    calc f = (f ≫ e.inv) ≫ e.hom := by
            rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      _ = (g ≫ e.inv) ≫ e.hom := by rw [h1]
      _ = g := by rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]⟩

/-- A bijection transfers subsingleton-ness backwards along it. -/
lemma subsingleton_of_equiv {α β : Sort*} (e : α ≃ β) (h : Subsingleton β) : Subsingleton α :=
  ⟨fun a b => e.injective (Subsingleton.elim (e a) (e b))⟩

/-- A bijection transfers subsingleton-ness forwards along it. -/
lemma subsingleton_of_equiv' {α β : Sort*} (e : α ≃ β) (h : Subsingleton α) : Subsingleton β :=
  ⟨fun a b => e.symm.injective (Subsingleton.elim (e.symm a) (e.symm b))⟩

theorem solidNull_zfree_tensor (S : LightProfinite.{0}) {A : LightCondAb}
    (h : Work.ANALYTIC.SolidNull
      (CategoryTheory.Functor.obj (DerivedCategory.singleFunctor LightCondAb 0) A)) :
    Work.ANALYTIC.SolidNull
      (CategoryTheory.Functor.obj (DerivedCategory.singleFunctor LightCondAb 0)
        (Work.ATOM.tmul ((LightCondensed.free (R := ℤ)).obj S.toCondensed) A)) := by
  classical
  -- ## Notation
  -- the free object `ℤ[S]`
  let B : LightCondAb := (LightCondensed.free (R := ℤ)).obj S.toCondensed
  -- the complex `single A` concentrated in degree `0`
  let K : Work.RESOL.Cpx := (HomologicalComplex.single LightCondAb (ComplexShape.up ℤ) 0).obj A
  -- ## A functorial solid-cofibrant resolution of `K` with atomic terms, bounded above
  obtain ⟨F, π, hF0, hπ, hFat⟩ := Work.RESOL.hasAtomicCoverZero
  haveI : F.PreservesZeroMorphisms := hF0
  let Kres : Work.RESOL.Cpx := (Work.RESOL.Zero.R F π hπ).obj K
  have hKbd : Work.RESOL.IsBoundedAbove K :=
    ⟨0, fun n hn => HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 A n (by omega)⟩
  have hKresbd : Work.RESOL.IsBoundedAbove Kres :=
    Work.RESOL.zIsBoundedAboveTotFull F π hπ K hKbd
  have hKresat : Work.RESOL.HasAtomicTerms Kres :=
    Work.RESOL.zHasAtomicTermsTotFull F π hπ hFat K
  have hKrescof : Submission.Blueprint.SolidCofibrant Kres :=
    Work.RESOL.boundedAbove_atomic_solidCofibrant Work.ATOM.atom_prop Kres hKresbd hKresat
  have hKresqi : QuasiIso ((Work.RESOL.Zero.eps F π hπ).app K) :=
    Work.RESOL.Zero.quasiIso_eps_of_boundedAbove F π hπ K hKbd
  -- ## The tensor with `ℤ[S]` of the resolution
  haveI hbl : CategoryTheory.Limits.PreservesFiniteLimits (tensorLeft B) := Work.FLAT.flat_prop S.toCondensed
  haveI hAddB : (tensorLeft B).Additive := by
    have hc : PreservesColimitsOfSize.{0, 0} (tensorLeft B) :=
      (ihom.adjunction B).leftAdjoint_preservesColimits
    have h₂ : PreservesColimitsOfShape (Discrete WalkingPair) (tensorLeft B) :=
      hc.preservesColimitsOfShape
    have h₃ : PreservesBinaryBiproducts (tensorLeft B) :=
      preservesBinaryBiproducts_of_preservesBinaryCoproducts _
    exact Functor.additive_of_preservesBinaryBiproducts _
  haveI hAddIhomB : (ihom B).Additive := by
    have hc : PreservesColimitsOfSize.{0, 0} (tensorLeft B) :=
      (ihom.adjunction B).leftAdjoint_preservesColimits
    have h₂ : PreservesColimitsOfShape (Discrete WalkingPair) (tensorLeft B) :=
      hc.preservesColimitsOfShape
    have h₃ : PreservesBinaryBiproducts (tensorLeft B) :=
      preservesBinaryBiproducts_of_preservesBinaryCoproducts _
    have h₄ : (tensorLeft B).Additive := Functor.additive_of_preservesBinaryBiproducts _
    exact (ihom.adjunction B).right_adjoint_additive
  haveI hbc : PreservesFiniteColimits (tensorLeft B) := by
    have hc : PreservesColimitsOfSize.{0, 0} (tensorLeft B) :=
      (ihom.adjunction B).leftAdjoint_preservesColimits
    exact PreservesColimitsOfSize.preservesFiniteColimits (tensorLeft B)
  let X : Work.RESOL.Cpx := ((tensorLeft B).mapHomologicalComplex (ComplexShape.up ℤ)).obj Kres
  have hXbd : Work.RESOL.IsBoundedAbove X := by
    obtain ⟨n₀, hn₀⟩ := hKresbd
    refine ⟨n₀, fun n hn => ?_⟩
    dsimp only [X]
    rw [Functor.mapHomologicalComplex_obj_X (tensorLeft B) (ComplexShape.up ℤ) Kres n]
    exact (tensorLeft B).map_isZero (hn₀ n hn)
  have hXat : Work.RESOL.HasAtomicTerms X := by
    intro n
    dsimp only [X]
    rw [Functor.mapHomologicalComplex_obj_X (tensorLeft B) (ComplexShape.up ℤ) Kres n]
    exact Work.ATOM.isAtomicSum_tmul_zfree S (hKresat n)
  have hXcof : Submission.Blueprint.SolidCofibrant X :=
    Work.RESOL.boundedAbove_atomic_solidCofibrant Work.ATOM.atom_prop X hXbd hXat
  -- ## The isomorphism `Q X ≅ single (ℤ[S] ⊗ A)`
  haveI hεiso : IsIso (DerivedCategory.Q.map ((Work.RESOL.Zero.eps F π hπ).app K)) :=
    (Localization.inverts DerivedCategory.Q
      (HomologicalComplex.quasiIso LightCondAb (ComplexShape.up ℤ)))
      _ hKresqi
  have hA1 : DerivedCategory.Q.obj X ≅
      (DerivedCategory.singleFunctor LightCondAb 0).obj (B ⊗ A) :=
    (((tensorLeft B).mapDerivedCategoryFactors).symm.app Kres) ≪≫
      (tensorLeft B).mapDerivedCategory.mapIso
        (asIso (DerivedCategory.Q.map ((Work.RESOL.Zero.eps F π hπ).app K)) ≪≫
          ((DerivedCategory.singleFunctorIsoCompQ LightCondAb 0).app A).symm) ≪≫
      ((tensorLeft B).mapDerivedCategorySingleFunctor 0).app A
  -- ## The main argument
  intro N
  -- represent the object of `D(Solid)`
  haveI hQ : (DerivedCategory.Q (C := Solid)).EssSurj :=
    Localization.essSurj (L := DerivedCategory.Q (C := Solid))
      (HomologicalComplex.quasiIso Solid (ComplexShape.up ℤ))
  obtain ⟨M₀, ⟨eN⟩⟩ := Functor.EssSurj.mem_essImage (DerivedCategory.Q (C := Solid)) N
  have eNiso : derivedInclusion.obj N ≅
      DerivedCategory.Q.obj (Submission.Blueprint.ιC.obj M₀) :=
    (derivedInclusion.mapIso eN).symm ≪≫ (isSolid.ι.mapDerivedCategoryFactors.app M₀)
  -- the complex `ihom ℤ[S] (ι M₀)` of internal homs, which is a complex of solid objects
  let RC : Work.RESOL.Cpx ⥤ Work.RESOL.Cpx := (ihom B).mapHomologicalComplex (ComplexShape.up ℤ)
  have hRCsolid : ∀ q : ℤ,
      LightCondensed.isSolid ((RC.obj (Submission.Blueprint.ιC.obj M₀)).X q) := by
    intro q
    dsimp only [RC]
    rw [Functor.mapHomologicalComplex_obj_X (ihom B) (ComplexShape.up ℤ)
      (Submission.Blueprint.ιC.obj M₀) q]
    exact isSolid_ihom' B ((Submission.Blueprint.ιC.obj M₀).X q) ((M₀.X q).property)
  obtain ⟨M₁, ⟨eM₁⟩⟩ := solidComplexLift (RC.obj (Submission.Blueprint.ιC.obj M₀)) hRCsolid
  -- ## The chain of identifications, starting from the hypothesis
  have sH : Subsingleton ((DerivedCategory.singleFunctor LightCondAb 0).obj A ⟶
      derivedInclusion.obj (DerivedCategory.Q.obj M₁)) := h (DerivedCategory.Q.obj M₁)
  -- `single A ≅ Q K`
  have eG₁ : (DerivedCategory.singleFunctor LightCondAb 0).obj A ≅ DerivedCategory.Q.obj K :=
    (DerivedCategory.singleFunctorIsoCompQ LightCondAb 0).app A
  -- `ι (Q M₁) ≅ Q (ι M₁)`
  have eG₂ : derivedInclusion.obj (DerivedCategory.Q.obj M₁) ≅
      DerivedCategory.Q.obj (Submission.Blueprint.ιC.obj M₁) :=
    isSolid.ι.mapDerivedCategoryFactors.app M₁
  have sG : Subsingleton (DerivedCategory.Q.obj K ⟶
      DerivedCategory.Q.obj (Submission.Blueprint.ιC.obj M₁)) :=
    subsingleton_of_iso_source eG₁ (subsingleton_of_iso_target eG₂ sH)
  -- `Q K ≅ Q Kres`
  haveI hεisoK : IsIso (DerivedCategory.Q.map ((Work.RESOL.Zero.eps F π hπ).app K)) := hεiso
  have eF : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj Kres :=
    (asIso (DerivedCategory.Q.map ((Work.RESOL.Zero.eps F π hπ).app K))).symm
  have sF : Subsingleton (DerivedCategory.Q.obj Kres ⟶
      DerivedCategory.Q.obj (Submission.Blueprint.ιC.obj M₁)) :=
    subsingleton_of_iso_source eF sG
  -- cofibrancy of the resolution
  have sE : Subsingleton (Submission.Blueprint.hq Kres ⟶
      Submission.Blueprint.hq (Submission.Blueprint.ιC.obj M₁)) :=
    subsingleton_of_equiv
      (Equiv.ofBijective
        (fun f : Submission.Blueprint.hq Kres ⟶
          Submission.Blueprint.hq (Submission.Blueprint.ιC.obj M₁) => DerivedCategory.Qh.map f)
        (hKrescof M₁)) sF
  -- replace the target by the complex `RC.obj (ι M₀)` of internal homs
  have sD : Subsingleton (Submission.Blueprint.hq Kres ⟶
      Submission.Blueprint.hq (RC.obj (Submission.Blueprint.ιC.obj M₀))) :=
    subsingleton_of_iso_target
      ((HomotopyCategory.quotient LightCondAb (ComplexShape.up ℤ)).mapIso eM₁) sE
  -- the adjunction `tensorLeft ℤ[S] ⊣ ihom ℤ[S]` on homotopy categories
  obtain ⟨adjHK⟩ :=
    Work.DERFORMAL.Gen.AdjHomotopyCategory (ihom.adjunction B) (ComplexShape.up ℤ)
  have sD' : Subsingleton (Submission.Blueprint.hq Kres ⟶
      ((ihom B).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        (Submission.Blueprint.hq (Submission.Blueprint.ιC.obj M₀))) := sD
  have sC : Subsingleton (((tensorLeft B).mapHomotopyCategory (ComplexShape.up ℤ)).obj
      (Submission.Blueprint.hq Kres) ⟶
      Submission.Blueprint.hq (Submission.Blueprint.ιC.obj M₀)) :=
    subsingleton_of_equiv'
      (adjHK.homEquiv (Submission.Blueprint.hq Kres)
        (Submission.Blueprint.hq (Submission.Blueprint.ιC.obj M₀))).symm sD'
  have sC' : Subsingleton (Submission.Blueprint.hq X ⟶
      Submission.Blueprint.hq (Submission.Blueprint.ιC.obj M₀)) := sC
  -- cofibrancy of `X`
  have sB : Subsingleton (DerivedCategory.Q.obj X ⟶
      DerivedCategory.Q.obj (Submission.Blueprint.ιC.obj M₀)) :=
    subsingleton_of_equiv'
      (Equiv.ofBijective
        (fun f : Submission.Blueprint.hq X ⟶
          Submission.Blueprint.hq (Submission.Blueprint.ιC.obj M₀) => DerivedCategory.Qh.map f)
        (hXcof M₀)) sC'
  -- descend to the statement
  have s₀ : Subsingleton ((DerivedCategory.singleFunctor LightCondAb 0).obj (B ⊗ A) ⟶
      DerivedCategory.Q.obj (Submission.Blueprint.ιC.obj M₀)) :=
    subsingleton_of_iso_source hA1 sB
  have s₁ : Subsingleton ((DerivedCategory.singleFunctor LightCondAb 0).obj (B ⊗ A) ⟶
      derivedInclusion.obj N) :=
    subsingleton_of_iso_target eNiso.symm s₀
  exact s₁

end Work.ANALYTIC
