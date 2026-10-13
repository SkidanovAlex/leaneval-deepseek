import Mathlib
import Submission.Work.DSMap.Mix2
import Submission.Work.DSMX0bU.Basic

/-!
# DSMX0bU (area MX0bU of the MIX2 route): the bridge from `ModSplit` on a finite free model
of the Čech complex to `DSplit`

Deliverable: `DSMap.Mix2.area_MX0bU_proved`, with a type definitionally identical to the
frozen node

```
DSMap.Mix2.area_MX0bU :
  ∀ (A) [CommRing A] (X) (f) [IsProper f] {ι} [Finite ι] (U) (hU : ∀ i, IsAffineOpen (U i))
    (hcov : ⨆ i, U i = ⊤) (P) (ε)
    (hP : IsFinFreeModelU A X f U P ε) (h : ModSplit P ε (RingHom.id A) ⊥ 1),
    DSplit.{a,b,c} A X f
```

of `Submission/Work/DSMap/Mix2.lean` (machine-checked by the `example` at the end of this
file).

## What is proved, and from what

* `Work.DSMX0bU.CechModelData` — the *output* of the frozen area `F1`
  (`DSMap.area_F1_cech`) for the cover `U`, packaged as a predicate: a cochain map
  `cc : A[0] ⟶ Č(U;𝒪)` whose degree-`0` component is the Čech coaugmentation `coaug0`, and an
  isomorphism `e : ι (RΓ(X,𝒪_X)) ≅ Q (Č(U;𝒪))` in `D⁺(A)` with
  `ι(rgUnit) ≫ e.hom = unitComparison cc`.
* `Work.DSMX0bU.dsplit_of_cechModel` — **the general interface of the area**.  For a
  K-projective model `P` of the Čech complex `cechZ A X f U` of a finite family of opens `U`
  (a quasi-isomorphism `P ⟶ Č(U;𝒪)` carrying the coaugmentation `ε` of `P` to the Čech
  coaugmentation `coaug0`), for the output of the area `F1` for `U` (taken as a *hypothesis*
  uniformly over the derived-category instances), and for a chain-level splitting of the
  coaugmentation of `P`, the challenge unit splits: `DSplit.{a,b,c} A X f`.
* `DSMap.Mix2.area_MX0bU_of_F1` — the deliverable's statement with `CechModelData` as an
  explicit hypothesis.  **This theorem is axiom-clean**: `#print axioms` gives
  `[propext, Classical.choice, Quot.sound]` (see `AxiomCheck.lean`).
* `Work.DSMX0bU.F1Data_exists` — the *single* place where the frozen node
  `DSMap.area_F1_cech` is invoked.
* `DSMap.Mix2.area_MX0bU_proved` — the deliverable: `area_MX0bU_of_F1` applied to
  `F1Data_exists`.

## The dependency on the area `F1`, and what it is

`MX0bU` is, mathematically, the composite of two statements:

1. *(`F1`, frozen, owned by subproject `DSF1`)* the challenge unit `rgUnit : A[0] ⟶ RΓ(X,𝒪_X)`
   is, up to the canonical isomorphism, the derived image of the Čech coaugmentation of a
   finite affine cover, i.e. `RΓ(X,𝒪_X) ≅ Q(Č(U;𝒪))` *compatibly with the units*.  This is
   the predicate `CechModelData A X f U`, which is the frozen `DSMap.area_F1_cech` for the
   cover `U`.
2. *(proved here)* the chain-level splitting of the model, plus the quasi-isomorphism
   `P ⟶ Č(U;𝒪)`, produce a retraction of the challenge unit.  This is everything in
   `Submission/Work/DSMX0bU/Basic.lean` together with the `K`-projectivity descent of
   subproject `DSG4a` (`Work.DSG4a.isSplitMono_rgUnit_iff_chainSplit`).

Nothing in the second part can replace the first: the hypotheses of the frozen statement
mention only the Čech complex of the cover and a splitting of the model, and no chain-level
algebra produces a retraction of a map *out of the right derived functor* `RΓ` without knowing
how `RΓ` is computed.  `area_MX0bU_of_F1` isolates that single input.

`area_MX0bU_proved` therefore cites `DSMap.area_F1_cech`, as the other nodes of the MIX2
assembly (`area_MIX2` of `Submission/Work/DSMap/Mix2.lean`) cite their own inputs: its axiom
list contains `sorryAx` *through that frozen node only*.  To make it axiom-clean it suffices
to replace the one line of `F1Data_exists` by any proved version of `F1` — for instance the
announced `Work.DSF1.area_F1_cech_proved` of `Submission/Work/DSF1/Main.lean`, or a proof put
into `DSMap.area_F1_cech` itself; no other change is needed.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicGeometry Limits

universe a b c

namespace Work.DSMX0bU

/-- **The output of the area `F1` for the cover `U`** (the frozen `DSMap.area_F1_cech`),
packaged as a predicate: a chain map `cc : A[0] ⟶ Č(U;𝒪)` whose degree-`0` part is the Čech
coaugmentation (`coaug0`), and an isomorphism `e : ι (RΓ(X,𝒪)) ≅ Q (Č(U;𝒪))` in the derived
category which carries the challenge unit `rgUnit` to the derived image of `cc`
(`DSG4a.Criterion.unitComparison`). -/
def CechModelData (A : Type a) [CommRing A] [HasDerivedCategory.{b} (ModuleCat.{a} A)]
    (X : Scheme.{a}) (f : X ⟶ Spec (.of A)) [HasDerivedCategory.{c} (SheafOfModules X.ringCatSheaf)]
    [EnoughInjectives (SheafOfModules X.ringCatSheaf)] {ι : Type a} (U : ι → X.Opens) : Prop :=
  ∃ (cc : singleZ A ⟶ DSMap.cechZ A X f U)
    (e : DerivedCategory.Plus.ι.obj (DSMap.RG A X f) ≅
      DerivedCategory.Q.obj (DSMap.cechZ A X f U)),
    cc.f 0 ≫ ((DSMap.cech A X f U).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).hom =
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).hom ≫
          DSMap.coaug0 A X f U ∧
      DerivedCategory.Plus.ι.map (DSMap.rgUnit A X f) ≫ e.hom =
        DSG4a.Criterion.unitComparison A (DSMap.cechZ A X f U) cc

/-- **The general interface of area `MX0bU`.**  Given

* a K-projective complex `P` of `A`-modules and a quasi-isomorphism `q : P ⟶ Č(U;𝒪)` to the
  Čech complex of the finite family of opens `U`,
* a coaugmentation `ε : A ⟶ P⁰` of `P` whose composite with `q` is, in degree `0`, the Čech
  coaugmentation `coaug0`,
* a chain-level splitting of that coaugmentation (`ChainSplit`),
* the output of the area `F1` for `U` (`CechModelData`), uniformly over the derived-category
  instances,

the challenge unit `rgUnit A X f` is a split monomorphism in `D⁺(A)` for every choice of the
derived-category instances, i.e. `DSplit.{a,b,c} A X f`.

This is the reusable form of the node `MX0bU`: everything except `F1` is unconditional, and
the conclusion is the frozen `DSplit`. -/
theorem dsplit_of_cechModel (A : Type a) [CommRing A] (X : Scheme.{a})
    (f : X ⟶ Spec (.of A)) {ι : Type a} (U : ι → X.Opens)
    (P : CochainComplex (ModuleCat.{a} A) ℤ) [P.IsKProjective]
    (q : P ⟶ DSMap.cechZ A X f U) (hq : QuasiIso q)
    (ε : ModuleCat.of A A ⟶ P.X 0) (hε : ∀ k, ε ≫ P.d 0 k = 0)
    (hqε : ε ≫ q.f 0 ≫ ((DSMap.cech A X f U).extendXIso ComplexShape.embeddingUpNat
      (i := 0) rfl).hom = DSMap.coaug0 A X f U)
    (hchain : DSG4a.Criterion.ChainSplit P (coaugFromEps (P := P) ε hε))
    (hF1 : ∀ (_ : HasDerivedCategory.{b} (ModuleCat.{a} A))
      (_ : HasDerivedCategory.{c} (SheafOfModules X.ringCatSheaf))
      (_ : EnoughInjectives (SheafOfModules X.ringCatSheaf)),
      CechModelData A X f U) : DSMap.DSplit.{a, b, c} A X f := by
  intro hb hc hEn
  letI := hb
  letI := hc
  letI := hEn
  obtain ⟨cc, e, hcc, he⟩ := hF1 hb hc hEn
  exact isSplitMono_of_model X f U P q hq ε hε cc e he hcc hqε hchain

/-- **The only invocation of the frozen area `F1`** in this subproject.  `DSMap.area_F1_cech`
gives the Čech model of `RΓ(X,𝒪_X)`, compatibly with the units, for every finite affine cover
`U` of `X` (`X` separated and quasi-compact, as `IsProper f` provides).  Replacing this
declaration's proof by a proved version of `F1` makes `DSMap.Mix2.area_MX0bU_proved`
axiom-clean. -/
theorem F1Data_exists (A : Type a) [CommRing A] (X : Scheme.{a}) (f : X ⟶ Spec (.of A))
    [IsProper f] {ι : Type a} [Finite ι] (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcov : ⨆ i, U i = ⊤) :
    ∀ (_ : HasDerivedCategory.{b} (ModuleCat.{a} A))
      (_ : HasDerivedCategory.{c} (SheafOfModules X.ringCatSheaf))
      (_ : EnoughInjectives (SheafOfModules X.ringCatSheaf)),
      CechModelData A X f U := by
  intro hb hc hEn
  letI := hb
  letI := hc
  letI := hEn
  haveI : QuasiCompact f := quasiCompact_of_isProper f
  exact DSMap.area_F1_cech A X f U hU hcov

end Work.DSMX0bU

namespace DSMap.Mix2

open DSMap DSMap.Mix

/-- **MX0bU, stated against the area `F1`.**  Same conclusion as the frozen
`DSMap.Mix2.area_MX0bU`, but with the output of `F1` for the given cover (the predicate
`Work.DSMX0bU.CechModelData`) as an explicit hypothesis, uniformly over the derived-category
instances.  This is the axiom-clean form of the deliverable: everything except `F1` is proved
in `Submission/Work/DSMX0bU/Basic.lean` and in subproject `DSG4a`. -/
theorem area_MX0bU_of_F1 (A : Type a) [CommRing A] (X : Scheme.{a})
    (f : X ⟶ Spec (.of A)) [IsProper f] {ι : Type a} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hcov : ⨆ i, U i = ⊤)
    (P : CochainComplex (ModuleCat.{a} A) ℤ) (ε : ModuleCat.of A A ⟶ P.X 0)
    (hP : IsFinFreeModelU A X f U P ε) (h : ModSplit P ε (RingHom.id A) ⊥ 1)
    (hF1 : ∀ (_ : HasDerivedCategory.{b} (ModuleCat.{a} A))
      (_ : HasDerivedCategory.{c} (SheafOfModules X.ringCatSheaf))
      (_ : EnoughInjectives (SheafOfModules X.ringCatSheaf)),
      Work.DSMX0bU.CechModelData A X f U) : DSplit.{a, b, c} A X f := by
  obtain ⟨hBdd, hε, q, hq, hqε⟩ := hP
  haveI : P.IsKProjective := Work.DSMX0bU.isKProjective_of_isBddFinFree hBdd
  exact Work.DSMX0bU.dsplit_of_cechModel A X f U P q hq ε hε hqε
    (Work.DSMX0bU.chainSplit_of_modSplit ε hε h) hF1

/-- **MX0bU (deliverable).**  An honest splitting `ModSplit P ε (RingHom.id A) ⊥ 1` of a
finite free model `P` of the Čech complex of a finite affine cover `U` of a proper `X`, with
`ε` carrying the unit to the Čech coaugmentation, gives the derived splitting
`DSplit A X f`.  Same type as the frozen `DSMap.Mix2.area_MX0bU`.

Its only non-Mathlib input is the frozen area `F1` (`DSMap.area_F1_cech`), invoked once, in
`Work.DSMX0bU.F1Data_exists`. -/
theorem area_MX0bU_proved (A : Type a) [CommRing A] (X : Scheme.{a})
    (f : X ⟶ Spec (.of A)) [IsProper f] {ι : Type a} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hcov : ⨆ i, U i = ⊤)
    (P : CochainComplex (ModuleCat.{a} A) ℤ) (ε : ModuleCat.of A A ⟶ P.X 0)
    (hP : IsFinFreeModelU A X f U P ε) (h : ModSplit P ε (RingHom.id A) ⊥ 1) :
    DSplit.{a, b, c} A X f :=
  area_MX0bU_of_F1 A X f U hU hcov P ε hP h (Work.DSMX0bU.F1Data_exists A X f U hU hcov)

/-- The type of the deliverable is definitionally identical to the type of the frozen
`DSMap.Mix2.area_MX0bU`.  (Universe levels are made explicit: without them `type_of%`
introduces two distinct level metavariables and `rfl` is not applicable.) -/
example : type_of% (@area_MX0bU_proved.{a, b, c}) = type_of% (@DSMap.Mix2.area_MX0bU.{a, b, c}) :=
  rfl

end DSMap.Mix2
