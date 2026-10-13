import Mathlib
import Submission.Work.DSMap.Mix
import Submission.Work.DSG4a.Criterion
import Submission.Work.DSG4a.F1Interface
import Submission.Work.DSG4a.isSplitMono_Q_map_iff_chainSplit
import Submission.Work.DSG4a.isSplitMono_rgUnit_iff_chainSplit

/-!
# DSMX0bU, part 1: the chain-level bridge from a finite free model of the Čech complex to
`DSplit`

Subproject DSMX0bU of the `direct_summand` project (area owner for the node `MX0bU` of the
MIX2 route, `sources/dsmap/direct_summand_mix2.md`, Task 2).  The node is

```
DSMap.Mix2.area_MX0bU :
  (P, ε) a finite free model of the Čech complex of a finite affine cover `U` of `X`
  (with the coaugmentation `ε` compatible with `coaug0`) and
  `h : ModSplit P ε (RingHom.id A) ⊥ 1`  ⟹  `DSplit A X f` .
```

This file contains the *chain-level* half of the bridge — everything that does not use the
area `F1` (`DSMap.area_F1_cech`, the Čech model of `RΓ(X,𝒪_X)`, owned by subproject DSF1):

* `singleZ A` — `A` as a cochain complex concentrated in degree `0` (the source of the
  coaugmentation);
* `coaugFromEps P ε hε : singleZ A ⟶ P` — the cochain map whose degree-`0` component is `ε`
  (`HomologicalComplex.mkHomFromSingle`), with its two defining properties
  (`coaugFromEps_f_zero`, `coaugElem_coaugFromEps`);
* `chainSplit_of_modSplit` — the *honest* splitting `ModSplit P ε (RingHom.id A) ⊥ 1` of the
  model is a chain-level splitting `ChainSplit P (coaugFromEps P ε hε)`;
* `isKProjective_of_isBddFinFree` — a bounded-above complex of finite free modules is
  K-projective (`CochainComplex.isKProjective_of_projective`);
* `quasiCompact_of_isProper` — proper morphisms are quasi-compact (needed to apply `F1`);
* `isSplitMono_of_model` — **the bridge**: given the Čech model data of `F1` for the cover
  `U`, a quasi-isomorphism `P ⟶ Č(U)` and a chain-level splitting of `P`, the challenge unit
  `rgUnit` is a split monomorphism in `D⁺(A)`.

The derived-category comparison itself (`F1`) is consumed in `Main.lean`; the mathematics of
the present file is purely about the cochain complex `P` and the functional
`TensorProduct A A (P.X 0) →ₗ[A] A ⧸ ⊥` produced by `ModSplit`.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry Limits

namespace Work.DSMX0bU

universe a b c

/-- `A` as a cochain complex concentrated in degree `0`.  This is the source of the frozen
Čech coaugmentation `cc` of `DSMap.area_F1_cech` and of the coaugmentation of a model. -/
noncomputable abbrev singleZ (A : Type a) [CommRing A] : CochainComplex (ModuleCat.{a} A) ℤ :=
  (HomologicalComplex.single (ModuleCat.{a} A) (ComplexShape.up ℤ) 0).obj (ModuleCat.of A A)

/-! ## The coaugmentation of a model -/

/-- The cochain map `A[0] ⟶ P` whose degree-`0` component is `ε`, defined whenever `ε`
composes to zero with all the differentials of `P` out of degree `0` (in particular whenever
`ε ≫ P.d 0 k = 0` for all `k`, which is what a coaugmentation of a model provides). -/
noncomputable def coaugFromEps {A : Type a} [CommRing A] {P : CochainComplex (ModuleCat.{a} A) ℤ}
    (ε : ModuleCat.of A A ⟶ P.X 0) (hε : ∀ k, ε ≫ P.d 0 k = 0) : singleZ A ⟶ P :=
  HomologicalComplex.mkHomFromSingle (c := ComplexShape.up ℤ) (j := (0 : ℤ)) (K := P) ε
    (fun k _hk => hε k)

/-- The degree-`0` component of the coaugmentation built from `ε`. -/
lemma coaugFromEps_f_zero {A : Type a} [CommRing A] {P : CochainComplex (ModuleCat.{a} A) ℤ}
    (ε : ModuleCat.of A A ⟶ P.X 0) (hε : ∀ k, ε ≫ P.d 0 k = 0) :
    (coaugFromEps (P := P) ε hε).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).hom ≫ ε :=
  HomologicalComplex.mkHomFromSingle_f _ _

/-- The class of the unit under the coaugmentation built from `ε` is `ε 1`: this is the form
in which the chain-level splitting condition `ChainSplit` sees `ε`. -/
lemma coaugElem_coaugFromEps {A : Type a} [CommRing A] {P : CochainComplex (ModuleCat.{a} A) ℤ}
    (ε : ModuleCat.of A A ⟶ P.X 0) (hε : ∀ k, ε ≫ P.d 0 k = 0) :
    DSG4a.Criterion.coaugElem P (coaugFromEps (P := P) ε hε) = ε.hom 1 := by
  rw [DSG4a.Criterion.coaugElem, coaugFromEps_f_zero]
  simp only [Iso.inv_hom_id_assoc]

/-! ## From the honest splitting of a model to a chain-level splitting -/

/-- **The honest splitting of a model splits its coaugmentation at the chain level.**
`ModSplit P ε (RingHom.id A) ⊥ 1` provides a functional
`s : A ⊗[A] P⁰ ⟶ A ⧸ ⊥` killing the differential `d⁻¹` and with `s (1 ⊗ ε 1) = 1`; the
Tensor-Hom adjunction and the identification `A ⧸ ⊥ ≅ A` turn it into
`s' : P⁰ ⟶ A` with `s' ∘ d⁻¹ = 0` and `s' (ε 1) = 1`, i.e. `ChainSplit P (coaugFromEps …)`.
No finiteness, projectivity or boundedness is used. -/
theorem chainSplit_of_modSplit {A : Type a} [CommRing A]
    {P : CochainComplex (ModuleCat.{a} A) ℤ}
    (ε : ModuleCat.of A A ⟶ P.X 0) (hε : ∀ k, ε ≫ P.d 0 k = 0)
    (h : DSMap.Mix.ModSplit P ε (RingHom.id A) ⊥ 1) :
    DSG4a.Criterion.ChainSplit P (coaugFromEps (P := P) ε hε) := by
  letI : Algebra A A := (RingHom.id A).toAlgebra
  obtain ⟨s, hs1, hs2⟩ := h
  let ιt : P.X 0 →ₗ[A] TensorProduct A A (P.X 0) := (TensorProduct.mk A A (P.X 0)) (1 : A)
  let e : (A ⧸ (⊥ : Ideal A)) →ₗ[A] A := (AlgEquiv.quotientBot (R := A) (S := A)).toLinearMap
  let s' : P.X 0 →ₗ[A] A := e.comp (s.comp ιt)
  refine ⟨s', ?_, ?_⟩
  · ext x
    change e (s (ιt ((P.d (-1) 0).hom x))) = 0
    have hx : ιt ((P.d (-1) 0).hom x) =
        (LinearMap.baseChange A (P.d (-1) 0).hom) ((1 : A) ⊗ₜ[A] x) := by
      rw [TensorProduct.mk_apply, LinearMap.baseChange_tmul]
    rw [hx, hs1 ((1 : A) ⊗ₜ[A] x), map_zero]
  · rw [coaugElem_coaugFromEps]
    change e (s (ιt (ε.hom 1))) = 1
    rw [show ιt (ε.hom 1) = (1 : A) ⊗ₜ[A] ε.hom 1 by rw [TensorProduct.mk_apply]]
    rw [hs2]
    exact AlgEquiv.quotientBot_mk (R := A) (S := A) 1

/-! ## K-projectivity of a bounded-above complex of finite free modules -/

/-- A bounded-above complex of finite free `A`-modules is K-projective (Spaltenstein;
Mathlib's `CochainComplex.isKProjective_of_projective`). -/
theorem isKProjective_of_isBddFinFree {A : Type a} [CommRing A]
    {P : CochainComplex (ModuleCat.{a} A) ℤ} (hP : DSMap.Mix.IsBddFinFree P) :
    P.IsKProjective := by
  obtain ⟨h1, N, hN⟩ := hP
  haveI : ∀ n : ℤ, Projective (P.X n) := fun n => by
    haveI : Module.Free A (P.X n) := (h1 n).1
    exact ModuleCat.projective_of_categoryTheory_projective (P.X n)
  haveI : P.IsStrictlyLE N := (CochainComplex.isStrictlyLE_iff P N).mpr fun i hi => hN i hi
  exact CochainComplex.isKProjective_of_projective P N

/-! ## A geometric input needed to invoke the area `F1` -/

/-- Proper morphisms are quasi-compact.  This is *not* part of Mathlib's `IsProper` class
(which only extends `IsSeparated`, `UniversallyClosed` and `LocallyOfFiniteType`), but it
follows from the valuative criterion for properness
(`IsProper.eq_valuativeCriterion`, Stacks 0BX5), which exhibits `IsProper` as
`ValuativeCriterion ⊓ QuasiCompact ⊓ QuasiSeparated ⊓ LocallyOfFiniteType`. -/
theorem quasiCompact_of_isProper {X Y : Scheme.{a}} (f : X ⟶ Y) [h : IsProper f] :
    QuasiCompact f := by
  rw [IsProper.eq_valuativeCriterion] at h
  exact h.1.1.2

/-! ## The derived-category bridge -/

/-- **MX0bU, chain half.**  Let `U` be a finite family of opens of `X`, `P` a bounded-above
complex of finite free `A`-modules with a quasi-isomorphism `q : P ⟶ Č(U; 𝒪)` whose
degree-`0` part intertwines the coaugmentation `ε` of `P` with the Čech coaugmentation
`coaug0`, and let `cc`, `e` be the output of the area `F1` for this cover: a chain map
`cc : A[0] ⟶ Č(U;𝒪)` and an isomorphism `e : ι (RΓ(X,𝒪)) ≅ Q (Č(U;𝒪))` compatible with the
units.  If the coaugmentation of `P` splits at the chain level, then the challenge unit
`rgUnit A X f` is a split monomorphism in `D⁺(A)`.

The proof identifies the Čech coaugmentation with the coaugmentation of the model (using
`q` and both compatibility clauses), transports the `F1` compatibility along the resulting
isomorphism `e ≪≫ (Q q)⁻¹`, and applies the `K`-projective descent of subproject DSG4a
(`Work.DSG4a.isSplitMono_rgUnit_iff_chainSplit`). -/
theorem isSplitMono_of_model {A : Type a} [CommRing A]
    [HasDerivedCategory.{b} (ModuleCat.{a} A)] (X : Scheme.{a}) (f : X ⟶ Spec (.of A))
    [HasDerivedCategory.{c} (SheafOfModules X.ringCatSheaf)]
    [EnoughInjectives (SheafOfModules X.ringCatSheaf)]
    {ι : Type a} (U : ι → X.Opens)
    (P : CochainComplex (ModuleCat.{a} A) ℤ) [P.IsKProjective]
    (q : P ⟶ DSMap.cechZ A X f U) (hq : QuasiIso q)
    (ε : ModuleCat.of A A ⟶ P.X 0) (hε : ∀ k, ε ≫ P.d 0 k = 0)
    (cc : singleZ A ⟶ DSMap.cechZ A X f U)
    (e : DerivedCategory.Plus.ι.obj (DSMap.RG A X f) ≅
      DerivedCategory.Q.obj (DSMap.cechZ A X f U))
    (he : DerivedCategory.Plus.ι.map (DSMap.rgUnit A X f) ≫ e.hom =
      DSG4a.Criterion.unitComparison A (DSMap.cechZ A X f U) cc)
    (hcc : cc.f 0 ≫ ((DSMap.cech A X f U).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).hom =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).hom ≫
        DSMap.coaug0 A X f U)
    (hqε : ε ≫ q.f 0 ≫ ((DSMap.cech A X f U).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).hom =
      DSMap.coaug0 A X f U)
    (hchain : DSG4a.Criterion.ChainSplit P (coaugFromEps (P := P) ε hε)) :
    IsSplitMono (DSMap.rgUnit A X f) := by
  haveI : IsIso (DerivedCategory.Q.map q) := inferInstance
  set E := (DSMap.cech A X f U).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl
  have hcc' : cc = coaugFromEps (P := P) ε hε ≫ q := by
    refine HomologicalComplex.from_single_hom_ext (j := (0 : ℤ)) ?_
    refine (cancel_mono E.hom).mp ?_
    rw [HomologicalComplex.comp_f, coaugFromEps_f_zero]
    simp only [Category.assoc]
    rw [hqε]
    exact hcc
  have he' : DSG4a.Criterion.F1UnitCompatible P (coaugFromEps (P := P) ε hε)
      (e ≪≫ (asIso (DerivedCategory.Q.map q)).symm) := by
    show DerivedCategory.Plus.ι.map (DSMap.rgUnit A X f) ≫
      (e.hom ≫ (asIso (DerivedCategory.Q.map q)).inv) =
        DSG4a.Criterion.unitComparison A P (coaugFromEps (P := P) ε hε)
    rw [← Category.assoc, he, asIso_inv]
    rw [DSG4a.Criterion.unitComparison, DSG4a.Criterion.unitComparison, hcc']
    simp only [Functor.map_comp, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  exact (DSG4a.isSplitMono_rgUnit_iff_chainSplit X f P
    (coaugFromEps (P := P) ε hε) _ he').mpr hchain

/-! ## Two small pieces of the interface -/

/-- A chain-level retraction of the coaugmentation is a chain splitting: this is the form in
which consumers such as area `EQ0` (`Work.DSEQ0.PerfectModel`) provide their retraction
`cc ≫ φ = 𝟙`.  (Immediate from `DSG4a.chainSplit_iff_exists_chainRetraction`.) -/
theorem chainSplit_of_retraction {A : Type a} [CommRing A]
    (P : CochainComplex (ModuleCat.{a} A) ℤ)
    (cc : (HomologicalComplex.single (ModuleCat.{a} A) (ComplexShape.up ℤ) 0).obj
      (ModuleCat.of A A) ⟶ P)
    (φ : P ⟶ (HomologicalComplex.single (ModuleCat.{a} A) (ComplexShape.up ℤ) 0).obj
      (ModuleCat.of A A))
    (h : cc ≫ φ = 𝟙 _) : DSG4a.Criterion.ChainSplit P cc :=
  (DSG4a.chainSplit_iff_exists_chainRetraction P cc).mpr ⟨φ, h⟩

/-- Degenerate case: modulo the whole ring every class splits (`D ⧸ ⊤` is a subsingleton), so
`ModSplit` holds with any value.  Recorded to make the interface's degenerate behaviour
explicit. -/
theorem modSplit_top {A : Type a} [CommRing A] (P : CochainComplex (ModuleCat.{a} A) ℤ)
    (ε : ModuleCat.of A A ⟶ P.X 0) {D : Type a} [CommRing D] (ψ : A →+* D) (c : D) :
    DSMap.Mix.ModSplit P ε ψ ⊤ c := by
  letI : Algebra A D := ψ.toAlgebra
  haveI : Subsingleton (D ⧸ (⊤ : Ideal D)) := Ideal.Quotient.subsingleton_iff.mpr rfl
  exact ⟨0, fun y => rfl, Subsingleton.elim _ _⟩

end Work.DSMX0bU
