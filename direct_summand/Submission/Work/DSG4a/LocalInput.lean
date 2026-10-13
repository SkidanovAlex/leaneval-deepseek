import Mathlib
import Submission.Work.DSMap.Map
import Submission.Work.DSG4a.isUnimodular_of_forall_maximal
import Submission.Work.DSG4a.Data
import Submission.Work.DSG4a.ModelCriterionFull
import Submission.Work.DSG4a.CriterionPresent
import Submission.Work.DSG4a.chainSplit_baseChange_iff
import Submission.Work.DSG4a.cechZ_baseChange
import Submission.Work.DSG4a.isKProjective_baseChangeComplexFunctor
import Submission.Work.DSG4a.isAffineOpen_baseChangeOpen
import Submission.Work.DSG4a.iSup_baseChangeOpen
import Submission.Work.DSG4a.freePres_modelModule
import Submission.Work.DSEQ0.exists_lift_of_quasiIso
import Submission.Work.DSEQ0.exists_finite_affineCover
import Submission.Work.DSEQP.EqpCechSetup
import Submission.Work.DSG1.enoughInjectives_sheafOfModules
import Submission.Work.DSMX0bU.Basic
import Submission.Work.DSG4a.nonempty_index_of_isCovering

/-!
# DSG4a — the local-to-global area `G4a`, in the form in which it is provable

The frozen statement of the area (`DSMap.area_G4a_localGlobal`, `Submission/Work/DSMap/Map.lean`)
has the conclusion `DSMap.DSplit.{a,b,c} A X f` and the hypothesis

```
h : ∀ m maximal, ∃ (A' : Type a) [CommRing A'] [IsLocalRing A'] (ψ : A →+* A'),
      ψ.Flat ∧ (maximalIdeal A').comap ψ = m ∧ DSplit.{a, d, e} A' X' f'
```

with `d`, `e` *arbitrary universe parameters of the theorem*.  That hypothesis cannot be used:
`DSplit.{a,d,e} A' X' f'` is `∀ (_ : HasDerivedCategory.{d} (ModuleCat.{a} A')) ..., IsSplitMono`,
so extracting the splitting over `A'` requires a term of `HasDerivedCategory.{d} (ModuleCat.{a} A')`,
and Mathlib has exactly two ways to build one (`HasDerivedCategory.standard`, at the standard
universe `a+1`, and `MorphismProperty.hasLocalizationOfLocallySmall`, which needs
`LocallySmall.{d}` of the derived category — Hovey's smallness theorem, a documented TODO in
Mathlib).  For arbitrary `d` there is no instance, and `h` carries no information.  The same
defect was found for `area_G1_pullback` and repaired by the lead in
`Submission/Work/DSMap/Fix.lean` (`area_G1_pullbackU`: `DSplit.{a,b,d}` replaced by
`DSplit.{a,b,a+1}`); this file performs the analogous repair for `G4a`, in the same style.

## What is proved here

* `Work.DSG4a.isUnimodular_tmul_of_splitMono_baseChange` — **the base change half of the area**
  (the hypothesis `hbc` of `area_G4a_localGlobal_of_models`): given the model `P` of
  `RΓ(X,𝒪_X)` produced by `F1 + COH` for the finite affine cover `U`, a flat `A`-algebra `A'`,
  and the output of `F1` for the pulled-back cover of `X_{A'} = X ×_{Spec A} Spec A'`, a
  splitting of the challenge unit over `A'` makes `1 ⊗ e` unimodular over `A'`, where `e` is the
  model element over `A`.
* `Work.DSG4a.area_G4a_localGlobal_of_instances` — the frozen conclusion from
  `F1 + COH` (taken as hypotheses, at the universes of the conclusion and, for the base change,
  at the standard universes `a+1`) and the *repaired* local hypothesis
  (`DSplit.{a, a+1, a+1} A' X' f'`, whose instances are supplied by
  `HasDerivedCategory.standard`).

The repaired hypothesis is exactly the frozen one with `d = e = a + 1`, which is the
instantiation used by `DSMap.main_dsplit` (`area_G4a_localGlobal.{u, w₁, u+1, u+1, u+1}`).
-/

open CategoryTheory AlgebraicGeometry Limits
open scoped ChangeOfRings TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.DSG4a

universe u

/-- A bounded-above complex of finite free `A`-modules is K-projective after base change to any
`A`-algebra.  (`Work.DSG4a.isKProjective_baseChangeComplexFunctor` needs the boundedness and
projectivity instances separately; this packages them.) -/
theorem isKProjective_baseChangeComplex_of_isFreeModel {A : Type u} [CommRing A] {A' : Type u}
    [CommRing A'] [Algebra A A'] {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (h : IsFreeModel A P) :
    CochainComplex.IsKProjective (baseChangeComplex (A := A) (A' := A') P) := by
  obtain ⟨hfin, hfree, b, hb⟩ := h
  haveI : P.IsStrictlyLE b := hb
  haveI : ∀ n, Projective (P.X n) := fun n => by
    haveI := hfree n
    infer_instance
  exact isKProjective_baseChangeComplexFunctor (A := A) (A' := A') P b

/-- The diagonal of `X` over the terminal scheme is affine as soon as `f : X ⟶ Spec A` is
separated; in particular when `f` is proper.  (This is the instance required by
`Work.DSG4a.cechZ_baseChange`.) -/
theorem isAffineHom_diagonal_of_isProper {A : Type u} [CommRing A] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of A)} [IsProper f] :
    IsAffineHom (pullback.diagonal (terminal.from X)) :=
  Work.DSEQP.isAffineHom_diagonal_of_isSeparated (A := A) (X := X) (f := f) inferInstance

/-- **The base-change half of area `G4a`** (the hypothesis `hbc` of
`Work.DSG4a.area_G4a_localGlobal_of_models`), in the form in which the base-changed model is a
lift of the Čech coaugmentation.

Data: a complex `P` of `A`-modules which is a finite free model (`IsFreeModel`), a
quasi-isomorphism `q : P ⟶ cechZ A X f U` and a coaugmentation `cc : A[0] ⟶ P` lifting the Čech
coaugmentation `ccAn` of the area `F1` along `q`, the output `F1Data` of the area `F1` for the
*pulled-back* cover of `X_{A'}` over a flat `A`-algebra `A'`, and a splitting of the challenge
unit over `A'`.

Conclusion: the base change `1 ⊗ modelElem P cc` of the model element is unimodular over `A'`. -/
theorem isUnimodular_tmul_of_splitMono_baseChange {A : Type u} [CommRing A] {A' : Type u}
    [CommRing A'] [Algebra A A'] {X : Scheme.{u}} {f : X ⟶ Spec (.of A)} [IsProper f]
    {ι : Type u} [Finite ι] [Nonempty ι] (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    [HasDerivedCategory (ModuleCat.{u} A)] [HasDerivedCategory (SheafOfModules X.ringCatSheaf)]
    [EnoughInjectives (SheafOfModules X.ringCatSheaf)]
    [HasDerivedCategory (ModuleCat.{u} A')]
    [HasDerivedCategory (SheafOfModules (baseChangeScheme (A := A) (A' := A') X f).ringCatSheaf)]
    [EnoughInjectives (SheafOfModules (baseChangeScheme (A := A) (A' := A') X f).ringCatSheaf)]
    (hflat : Module.Flat A A')
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : IsFreeModel A P)
    (q : P ⟶ DSMap.cechZ A X f U) (hq : QuasiIso q)
    (cc : singleZ A ⟶ P) (ccAn : singleZ A ⟶ DSMap.cechZ A X f U)
    (hccAn : coaugClause X f U ccAn)
    (hlift : DerivedCategory.Q.map ccAn = DerivedCategory.Q.map cc ≫ DerivedCategory.Q.map q)
    (hF1' : F1Data A' (baseChangeScheme (A := A) (A' := A') X f)
      (baseChangeSnd (A := A) (A' := A') X f) (fun i => baseChangeOpen (A := A) (A' := A') X f (U i)))
    (hsplit : IsSplitMono (DSMap.rgUnit A' (baseChangeScheme (A := A) (A' := A') X f)
      (baseChangeSnd (A := A) (A' := A') X f))) :
    Module.IsUnimodular A' (TensorProduct.mk A A' (Criterion.modelModule P) 1
      (Criterion.modelElem P cc)) := by
  haveI : IsAffineHom (pullback.diagonal (terminal.from X)) :=
    isAffineHom_diagonal_of_isProper (A := A) (X := X) (f := f)
  haveI : CochainComplex.IsKProjective P := hP.isKProjective
  obtain ⟨ccAn', e', hccAn', he'⟩ := hF1'
  obtain ⟨Φ, hΦq, hΦ⟩ := cechZ_baseChange (A := A) (A' := A') X f U hU
  let qb : baseChangeComplex (A := A) (A' := A') P ⟶
      DSMap.cechZ A' (baseChangeScheme (A := A) (A' := A') X f)
        (baseChangeSnd (A := A) (A' := A') X f)
        (fun i => baseChangeOpen (A := A) (A' := A') X f (U i)) :=
    (baseChangeComplexFunctor (A := A) (A' := A')).map q ≫ Φ
  have hqb : QuasiIso qb := by
    haveI : QuasiIso ((baseChangeComplexFunctor (A := A) (A' := A')).map q) :=
      quasiIso_baseChangeComplexFunctor (A := A) (A' := A') hflat q hq
    exact inferInstance
  haveI : CochainComplex.IsKProjective (baseChangeComplex (A := A) (A' := A') P) :=
    isKProjective_baseChangeComplex_of_isFreeModel (A := A) (A' := A') hP
  obtain ⟨cc', hcc'⟩ := Work.DSEQ0.exists_lift_of_quasiIso
    (baseChangeComplex (A := A) (A' := A') P)
    (DSMap.cechZ A' (baseChangeScheme (A := A) (A' := A') X f) (baseChangeSnd (A := A) (A' := A') X f)
      (fun i => baseChangeOpen (A := A) (A' := A') X f (U i)))
    qb hqb ccAn'
  have k1 : IsSplitMono (DSMap.rgUnit A' (baseChangeScheme (A := A) (A' := A') X f)
      (baseChangeSnd (A := A) (A' := A') X f)) ↔
      Module.IsUnimodular A' (Criterion.modelElem (baseChangeComplex (A := A) (A' := A') P) cc') :=
    isSplitMono_iff_isUnimodular_of_lift (A := A') (X := baseChangeScheme (A := A) (A' := A') X f)
      (f := baseChangeSnd (A := A) (A' := A') X f)
      (U := fun i => baseChangeOpen (A := A) (A' := A') X f (U i))
      (baseChangeComplex (A := A) (A' := A') P) qb hqb ccAn' e' he' cc' hcc'
  exact (chainSplit_baseChange_iff (A := A) (A' := A') X f U hU hflat P q hq cc ccAn hccAn hlift
    ccAn' hccAn' Φ hΦq hΦ cc' hcc').mp
    ((chainSplit_iff_isUnimodular (baseChangeComplex (A := A) (A' := A') P) cc').mpr
      (k1.mp hsplit))

/-- **Area `G4a`, in the form in which it is provable.**

The conclusion is the frozen conclusion `DSMap.DSplit.{a,b,c} A X f`.  The hypotheses are:

* a finite nonempty family `U` of affine opens covering `X` (the frozen statement derives one
  from `hp : IsProjOver A f`; `Work.DSG4a.area_G4a_localGlobal_of_areas` does that for every `X`,
  using for `X = ∅` the trivial cover `⊤`, which is affine because `X.Opens` is then a
  subsingleton and Mathlib's `AlgebraicGeometry.isAffineOpen_bot` applies);
* the output of the area `F1` for `U` (`F1Data A X f U`) and of the area `COH`
  (`CohData A X f`), uniformly over the derived-category instances at the universes `b`, `c` of
  the conclusion — this is the frozen `DSMap.area_F1_cech` and `DSMap.area_COH` (which are
  `sorry` stubs in the lead file, hence used here as explicit hypotheses);
* the output of the area `F1` for the pulled-back cover of `X_{A'} = X ×_{Spec A} Spec A'`, for
  every `A`-algebra `A'`, at the standard universes `a+1`, `a+1`;
* the local input: for every maximal ideal `m` a flat local `A`-algebra `A'` lying over `m` in
  which the challenge unit splits (`DSplit.{a, a+1, a+1} A' X' f'`).

The last hypothesis is the frozen one with `DSplit.{a, d, e}` replaced by
`DSplit.{a, a+1, a+1}`: with `d`, `e` arbitrary universe variables the hypothesis cannot be
used at all (see the module documentation and `Submission/Work/DSMap/Fix.lean` for the same
repair in `area_G1_pullback`). -/
theorem area_G4a_localGlobal_of_instances.{a, b, c} (A : Type a) [CommRing A] [IsNoetherianRing A]
    (X : Scheme.{a}) (f : X ⟶ Spec (.of A)) [IsProper f] (hp : DSMap.IsProjOver A f)
    {ι : Type a} [Finite ι] [Nonempty ι] (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcov : ⨆ i, U i = ⊤)
    (hF1 : ∀ (i : HasDerivedCategory.{b} (ModuleCat.{a} A))
      (j : HasDerivedCategory.{c} (SheafOfModules.{a} X.ringCatSheaf))
      (k : EnoughInjectives (SheafOfModules.{a} X.ringCatSheaf)), F1Data A X f U)
    (hCoh : ∀ (i : HasDerivedCategory.{b} (ModuleCat.{a} A))
      (j : HasDerivedCategory.{c} (SheafOfModules.{a} X.ringCatSheaf))
      (k : EnoughInjectives (SheafOfModules.{a} X.ringCatSheaf)), CohData A X f)
    (hF1' : ∀ (A' : Type a) [CommRing A'] (ψ : A →+* A') [Algebra A A']
      (i : HasDerivedCategory.{a + 1} (ModuleCat.{a} A'))
      (j : HasDerivedCategory.{a + 1}
        (SheafOfModules.{a} (baseChangeScheme (A := A) (A' := A') X f).ringCatSheaf))
      (k : EnoughInjectives
        (SheafOfModules.{a} (baseChangeScheme (A := A) (A' := A') X f).ringCatSheaf)),
      F1Data A' (baseChangeScheme (A := A) (A' := A') X f)
        (baseChangeSnd (A := A) (A' := A') X f)
        (fun i => baseChangeOpen (A := A) (A' := A') X f (U i)))
    (h : ∀ (m : Ideal A) (hm : m.IsMaximal),
      ∃ (A' : Type a) (_ : CommRing A') (_ : IsLocalRing A') (ψ : A →+* A'),
        ψ.Flat ∧ (IsLocalRing.maximalIdeal A').comap ψ = m ∧
        DSMap.DSplit.{a, a + 1, a + 1} A' (pullback f (Spec.map (CommRingCat.ofHom ψ)))
          (pullback.snd f (Spec.map (CommRingCat.ofHom ψ)))) :
    DSMap.DSplit.{a, b, c} A X f := by
  intro hb hc hEn
  letI := hb
  letI := hc
  letI := hEn
  obtain ⟨P, cc, q, ccAn, e₀, hP, hq, hccAn, he₀, hlift, hcrit⟩ :=
    exists_model_criterion_full (A := A) X f U (hF1 hb hc hEn) (hCoh hb hc hEn)
  haveI : CochainComplex.IsKProjective P := hP.isKProjective
  rw [hcrit]
  refine isUnimodular_of_forall_maximal (freePres_modelModule hP).some (Criterion.modelElem P cc) ?_
  intro m hm
  obtain ⟨A'', hcr, hlr, ψ, hψflat, hcomap, hsplit⟩ := h m hm
  letI : Algebra A A'' := ψ.toAlgebra
  have hflat : Module.Flat A A'' := hψflat
  refine ⟨A'', hcr, hlr, ψ, hψflat, hcomap, ?_⟩
  haveI : HasDerivedCategory.{a + 1} (ModuleCat.{a} A'') := HasDerivedCategory.standard _
  haveI : HasDerivedCategory.{a + 1}
      (SheafOfModules.{a} (baseChangeScheme (A := A) (A' := A'') X f).ringCatSheaf) :=
    HasDerivedCategory.standard _
  haveI : EnoughInjectives
      (SheafOfModules.{a} (baseChangeScheme (A := A) (A' := A'') X f).ringCatSheaf) :=
    Work.DSG1.enoughInjectives_sheafOfModules _
  have hsplit' : IsSplitMono (DSMap.rgUnit A'' (baseChangeScheme (A := A) (A' := A'') X f)
      (baseChangeSnd (A := A) (A' := A'') X f)) := hsplit _ _ _
  exact isUnimodular_tmul_of_splitMono_baseChange (A := A) (A' := A'') U hU hflat P hP q hq
    cc ccAn hccAn hlift (hF1' A'' ψ _ _ _) hsplit'

/-- **Area `G4a`, with the areas `F1` and `COH` as hypotheses in their full generality and no
cover in the statement.**

This is `Work.DSG4a.area_G4a_localGlobal_of_instances` with the finite affine cover *derived*
from `hp : IsProjOver A f` (`Work.DSEQ0.exists_finite_affineCover`), so that the hypotheses
mention no cover.  It is the frozen statement of the area up to exactly two things: the local
hypothesis `h` uses `DSplit.{a, a+1, a+1}` (the repair of §1(a) of `STATUS.md`, `d = e = a + 1`),
and the areas `F1`/`COH` occur as explicit hypotheses.

For nonempty `X` the cover is produced by `exists_finite_affineCover` together with
`Work.DSG4a.nonempty_index_of_isCovering`; for `X = ∅` the *trivial* cover `⊤` of `X` is used —
`X.Opens` is then a subsingleton, so `⊤ = ⊥` and `AlgebraicGeometry.isAffineOpen_bot` gives the
affineness of the cover, and the cover is nonempty by construction (`ι = PUnit`), which is
exactly what `F1` and the base change comparison require.  (For `X = ∅` the conclusion holds only
when `A` is the zero ring, and the proof derives that from `h`; but no separate argument is
needed: the machinery of `_of_instances` applies verbatim to the trivial cover.) -/
theorem area_G4a_localGlobal_of_areas.{a, b, c} (A : Type a) [CommRing A] [IsNoetherianRing A]
    (X : Scheme.{a}) (f : X ⟶ Spec (.of A)) [IsProper f] (hp : DSMap.IsProjOver A f)
    (hF1 : ∀ (B : Type a) [CommRing B] {Y : Scheme.{a}} (g : Y ⟶ Spec (.of B)) [IsProper g]
      {κ : Type a} [Finite κ] [Nonempty κ] (W : κ → Y.Opens) (hW : ∀ i, IsAffineOpen (W i))
      (hcov : ⨆ i, W i = ⊤)
      (i : HasDerivedCategory.{b} (ModuleCat.{a} B))
      (j : HasDerivedCategory.{c} (SheafOfModules.{a} Y.ringCatSheaf))
      (k : EnoughInjectives (SheafOfModules.{a} Y.ringCatSheaf)), F1Data B Y g W)
    (hCoh : ∀ (B : Type a) [CommRing B] [IsNoetherianRing B] {Y : Scheme.{a}}
      (g : Y ⟶ Spec (.of B)) [IsProper g] (hp : DSMap.IsProjOver B g)
      (i : HasDerivedCategory.{b} (ModuleCat.{a} B))
      (j : HasDerivedCategory.{c} (SheafOfModules.{a} Y.ringCatSheaf))
      (k : EnoughInjectives (SheafOfModules.{a} Y.ringCatSheaf)), CohData B Y g)
    (hF1' : ∀ (A' : Type a) [CommRing A'] (ψ : A →+* A') [Algebra A A'] {κ : Type a}
      [Finite κ] [Nonempty κ] (W : κ → (baseChangeScheme (A := A) (A' := A') X f).Opens)
      (hW : ∀ i, IsAffineOpen (W i)) (hcov : ⨆ i, W i = ⊤)
      (i : HasDerivedCategory.{a + 1} (ModuleCat.{a} A'))
      (j : HasDerivedCategory.{a + 1}
        (SheafOfModules.{a} (baseChangeScheme (A := A) (A' := A') X f).ringCatSheaf))
      (k : EnoughInjectives
        (SheafOfModules.{a} (baseChangeScheme (A := A) (A' := A') X f).ringCatSheaf)),
      F1Data A' (baseChangeScheme (A := A) (A' := A') X f)
        (baseChangeSnd (A := A) (A' := A') X f) W)
    (h : ∀ (m : Ideal A) (hm : m.IsMaximal),
      ∃ (A' : Type a) (_ : CommRing A') (_ : IsLocalRing A') (ψ : A →+* A'),
        ψ.Flat ∧ (IsLocalRing.maximalIdeal A').comap ψ = m ∧
        DSMap.DSplit.{a, a + 1, a + 1} A' (pullback f (Spec.map (CommRingCat.ofHom ψ)))
          (pullback.snd f (Spec.map (CommRingCat.ofHom ψ)))) :
    DSMap.DSplit.{a, b, c} A X f := by
  obtain ⟨ι, hιfin, hιne, U, hU, hcov⟩ :
      ∃ (ι : Type a) (_ : Finite ι) (_ : Nonempty ι) (U : ι → X.Opens),
        (∀ i, IsAffineOpen (U i)) ∧ ⨆ i, U i = ⊤ := by
    by_cases hX : Nonempty X
    · obtain ⟨J, hJ, U, hU, hcov⟩ := Work.DSEQ0.exists_finite_affineCover (A := A) f
      exact ⟨J, hJ, nonempty_index_of_isCovering U hcov, U, hU, hcov⟩
    · -- `X` is empty: `X.Opens` is a subsingleton, so `⊤ = ⊥` and the *trivial* cover works.
      haveI : IsEmpty X := not_nonempty_iff.mp hX
      have htop : (⊤ : X.Opens) = ⊥ := by
        ext x
        exact iff_of_true trivial (IsEmpty.false x)
      exact ⟨PUnit.{a + 1}, inferInstance, inferInstance, fun _ => ⊤,
        fun _ => htop ▸ AlgebraicGeometry.isAffineOpen_bot X,
        (iSup_const : (⨆ _ : PUnit.{a + 1}, (⊤ : X.Opens)) = ⊤)⟩
  haveI : Finite ι := hιfin
  haveI : Nonempty ι := hιne
  refine area_G4a_localGlobal_of_instances A X f hp U hU hcov ?_ ?_ ?_ h
  · intro i j k
    exact hF1 A (g := f) (W := U) hU hcov i j k
  · intro i j k
    exact hCoh A (g := f) hp i j k
  · intro A' hA'cr ψ hA'alg i j k
    haveI : IsProper (baseChangeSnd (A := A) (A' := A') X f) := inferInstance
    exact hF1' A' ψ (fun i => baseChangeOpen (A := A) (A' := A') X f (U i))
      (fun i => isAffineOpen_baseChangeOpen (A := A) (A' := A') X f U hU i)
      (iSup_baseChangeOpen (A := A) (A' := A') X f U hcov) i j k

/-- **Area `G4a` with the *other* minimal repair of the frozen hypothesis: the instances are
carried by `h`.**

`Work.DSG4a.area_G4a_localGlobal_of_instances` repairs the frozen hypothesis by fixing its
universes to `a+1` (the universes at which `HasDerivedCategory.standard` provides the
instances), exactly as the lead did for `area_G1_pullback` in `Submission/Work/DSMap/Fix.lean`.
Here instead the local hypothesis carries the three instances and the output of the area `F1` for
the pulled-back cover, so that no universes have to be fixed:

```
h : ∀ m maximal, ∃ (A' : Type a) [CommRing A'] [IsLocalRing A'] (ψ : A →+* A'),
      ψ.Flat ∧ (maximalIdeal A').comap ψ = m ∧
      ∃ (i : HasDerivedCategory (ModuleCat.{a} A')) (j : HasDerivedCategory (SheafOfModules X'.ringCatSheaf))
        (k : EnoughInjectives (SheafOfModules X'.ringCatSheaf)),
        F1Data A' X' f' U' ∧ IsSplitMono (rgUnit A' X' f')
```

The conclusion is again the frozen conclusion `DSMap.DSplit.{a,b,c} A X f`; `F1` and `COH` for
the chosen cover are hypotheses, as above. -/
theorem area_G4a_localGlobal_of_localData.{a, b, c} (A : Type a) [CommRing A]
    [IsNoetherianRing A] (X : Scheme.{a}) (f : X ⟶ Spec (.of A)) [IsProper f]
    (hp : DSMap.IsProjOver A f) {ι : Type a} [Finite ι] [Nonempty ι] (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hcov : ⨆ i, U i = ⊤)
    (hF1 : ∀ (i : HasDerivedCategory.{b} (ModuleCat.{a} A))
      (j : HasDerivedCategory.{c} (SheafOfModules.{a} X.ringCatSheaf))
      (k : EnoughInjectives (SheafOfModules.{a} X.ringCatSheaf)), F1Data A X f U)
    (hCoh : ∀ (i : HasDerivedCategory.{b} (ModuleCat.{a} A))
      (j : HasDerivedCategory.{c} (SheafOfModules.{a} X.ringCatSheaf))
      (k : EnoughInjectives (SheafOfModules.{a} X.ringCatSheaf)), CohData A X f)
    (h : ∀ (m : Ideal A) (hm : m.IsMaximal),
      ∃ (A' : Type a) (_ : CommRing A') (_ : IsLocalRing A') (ψ : A →+* A'),
        ∃ (i : HasDerivedCategory.{a + 1} (ModuleCat.{a} A'))
          (j : HasDerivedCategory.{a + 1}
            (SheafOfModules.{a} (pullback f (Spec.map (CommRingCat.ofHom ψ))).ringCatSheaf))
          (k : EnoughInjectives
            (SheafOfModules.{a} (pullback f (Spec.map (CommRingCat.ofHom ψ))).ringCatSheaf)),
          (letI : Algebra A A' := ψ.toAlgebra
           ψ.Flat ∧ (IsLocalRing.maximalIdeal A').comap ψ = m ∧
           F1Data A' (baseChangeScheme (A := A) (A' := A') X f)
              (baseChangeSnd (A := A) (A' := A') X f)
              (fun i => baseChangeOpen (A := A) (A' := A') X f (U i)) ∧
           IsSplitMono (DSMap.rgUnit A' (pullback f (Spec.map (CommRingCat.ofHom ψ)))
              (pullback.snd f (Spec.map (CommRingCat.ofHom ψ)))))) :
    DSMap.DSplit.{a, b, c} A X f := by
  intro hb hc hEn
  letI := hb
  letI := hc
  letI := hEn
  obtain ⟨P, cc, q, ccAn, e₀, hP, hq, hccAn, he₀, hlift, hcrit⟩ :=
    exists_model_criterion_full (A := A) X f U (hF1 hb hc hEn) (hCoh hb hc hEn)
  haveI : CochainComplex.IsKProjective P := hP.isKProjective
  rw [hcrit]
  refine isUnimodular_of_forall_maximal (freePres_modelModule hP).some (Criterion.modelElem P cc) ?_
  intro m hm
  obtain ⟨A'', hcr, hlr, ψ, i, j, k, hψflat, hcomap, hF1'', hsplit''⟩ := h m hm
  letI : Algebra A A'' := ψ.toAlgebra
  have hflat : Module.Flat A A'' := hψflat
  refine ⟨A'', hcr, hlr, ψ, hψflat, hcomap, ?_⟩
  letI := i
  letI := j
  letI := k
  exact isUnimodular_tmul_of_splitMono_baseChange (A := A) (A' := A'') U hU hflat P hP q hq
    cc ccAn hccAn hlift hF1'' hsplit''

end Work.DSG4a
