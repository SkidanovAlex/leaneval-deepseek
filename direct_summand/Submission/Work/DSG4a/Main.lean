import Mathlib
import Submission.Work.DSMap.Map
import Submission.Work.DSG4a.Split
import Submission.Work.DSG4a.LocalGlobal
import Submission.Work.DSG4a.FreePres
import Submission.Work.DSG4a.isUnimodular_of_forall_maximal
import Submission.Work.DSG4a.isUnimodular_presentMk_of_forall_maximal
import Submission.Work.DSG4a.LocalInput
import Submission.Work.DSMap.Fix2
import Submission.Work.DSMX0bU.Basic

/-!
# DSG4a — local-to-global for the derived direct summand theorem (area `G4a`)

This file is the assembly point of subproject **DSG4a**, the area `G4a` of the frozen proof
map (`Submission/Work/DSMap/Map.lean`).  It proves the local-to-global step of the derived
direct summand theorem *modulo the model interface*, and documents exactly what is missing.

## The statement of the area

`DSMap.area_G4a_localGlobal` (frozen) says: if `DSplit A' (X_{A'}) (f_{A'})` holds for a flat
local `A'` over every maximal ideal of `A` (with `A` Noetherian, `f : X ⟶ Spec A` proper and
projective), then `DSplit A X f`.  The mathematically used part of the hypothesis is
**flatness together with the lying-over condition on maximal ideals**; only those two are
needed by the algebra below.

## What is proved here, unconditionally

The algebraic engine, all of it reduced to Mathlib:

* `splitIdeal A e` and `Module.IsUnimodular A e` (`Split.lean`): the splitting condition is
  that `e` is unimodular, equivalently that the trace ideal `splitIdeal A e` is the unit
  ideal; a splitting over `A` base changes to one over any `A`-algebra.
* flat base change of the trace ideal for finitely presented modules
  (`one_mem_map_splitIdeal_of_isUnimodular_tmul`, `one_mem_splitIdeal_map_present`,
  `solSet_span_eq_baseChange`): `IsUnimodular A' (1 ⊗ e)` implies `1 ∈ (splitIdeal A e)·A'`.
* local-to-global for ideals (`one_mem_ideal_of_forall_maximal`): `1 ∈ I·A'` for a flat local
  `A'` over every maximal ideal implies `1 ∈ I`.
* **`isUnimodular_of_forall_maximal`**: if `M` is finitely presented, `e : M`, and `1 ⊗ e`
  is unimodular over a flat local `A'` over every maximal ideal of `A`, then `e` is
  unimodular over `A`.
* the criterion `isSplitMono_Q_map_iff_chainSplit`: for a K-projective model `P` of
  `RΓ(X, 𝒪)` with coaugmentation `cc`, `IsSplitMono (Q.map cc)` is equivalent to the
  chain-level splitting condition `ChainSplit P cc`, hence to `Module.IsUnimodular A`
  of `modelElem P cc` (`chainSplit_iff_isUnimodular`).

## What is *not* available in this workspace, and is assumed in the assembly below

The areas `F1` (Čech model of `RΓ(X, 𝒪)` in the challenge's `rightDerivedFunctorPlus` API)
and `COH` (finiteness and boundedness of `Hⁱ(X, 𝒪_X)` for `X` projective over Noetherian
`A`) are frozen as unproved stubs in `Submission/Work/DSMap/Map.lean`.  They are exactly what is
needed to produce, for every choice of derived category instances:

* a K-projective finite free model `P` of `RΓ(X, 𝒪)`, a coaugmentation
  `cc : A[0] ⟶ P` whose image in the derived category is the challenge unit, and hence (by
  `isSplitMono_Q_map_iff_chainSplit`) an element `e = modelElem P cc` of the finitely
  presented module `modelModule P = coker (P.d (-1) 0)` with

  `DSplit A X f ↔ Module.IsUnimodular A e`   (the hypothesis `hcrit` below);

* the compatibility of this model with flat base change `A → A'`: the model of
  `X_{A'} = pullback f (Spec A')` is `A' ⊗_A M` and the base-changed element is `1 ⊗ e`
  (the hypothesis `hbc` below).  This is the statement that the Čech complex of an affine
  cover base changes termwise, which is a `F1`-level result.

Given those two hypotheses, the frozen statement's conclusion follows, and the proof uses
only the flatness and lying-over conditions from the frozen hypothesis — in particular no
faithful flatness, no completeness, and no algebraically closed residue field is needed at
this stage (those are used inside the areas that supply `hcrit`/`hbc`).
-/

open CategoryTheory AlgebraicGeometry IsLocalRing Limits

set_option linter.unusedVariables false

namespace Work.DSG4a

universe u v w₁ w₂ w₃ w₄

/-- **The local-to-global area `G4a`, modulo the model interface.**

This is `DSMap.area_G4a_localGlobal` with two additional hypotheses, both of which are the
output of the areas `F1` and `COH` (see the module documentation):

* `hcrit` : the derived splitting condition `DSplit` is equivalent to the unimodularity of
  the element `e` of the finitely presented module `M`;
* `hbc` : the base change `A' ⊗_A M` with element `1 ⊗ e` is the model of the base-changed
  scheme, so that a splitting over `A'` gives unimodularity of `1 ⊗ e`.

The proof is the algebraic local-to-global theorem `isUnimodular_of_forall_maximal`: if `e`
becomes unimodular after the flat local base change at every maximal ideal, it already was
unimodular. -/
theorem area_G4a_localGlobal_of_models.{a, b, c, d, e} (A : Type a) [CommRing A]
    [IsNoetherianRing A] (X : Scheme.{a}) (f : X ⟶ Spec (.of A)) [IsProper f]
    (hp : DSMap.IsProjOver A f)
    (M : Type a) [AddCommGroup M] [Module A M] (e : M) (hpres : FreePres A M)
    (hcrit : DSMap.DSplit.{a, b, c} A X f ↔ Module.IsUnimodular A e)
    (hbc : ∀ (m : Ideal A) (hm : m.IsMaximal) (A' : Type a) (_ : CommRing A')
      (_ : IsLocalRing A') (ψ : A →+* A') (hflat : ψ.Flat)
      (hcomap : (IsLocalRing.maximalIdeal A').comap ψ = m),
      (letI : Algebra A A' := ψ.toAlgebra
       DSMap.DSplit.{a, d, e} A' (pullback f (Spec.map (CommRingCat.ofHom ψ)))
         (pullback.snd f (Spec.map (CommRingCat.ofHom ψ))) →
       Module.IsUnimodular A' (TensorProduct.mk A A' M (1 : A') e)))
    (h : ∀ m : Ideal A, m.IsMaximal → ∃ (A' : Type a) (_ : CommRing A') (_ : IsLocalRing A')
      (ψ : A →+* A'), ψ.Flat ∧ (IsLocalRing.maximalIdeal A').comap ψ = m ∧
      DSMap.DSplit.{a, d, e} A' (pullback f (Spec.map (CommRingCat.ofHom ψ)))
        (pullback.snd f (Spec.map (CommRingCat.ofHom ψ)))) :
    DSMap.DSplit.{a, b, c} A X f := by
  rw [hcrit]
  refine isUnimodular_of_forall_maximal hpres e ?_
  intro m hm
  obtain ⟨A', hA'cr, hA'lr, ψ, hflat, hcomap, hsplit⟩ := h m hm
  exact ⟨A', hA'cr, hA'lr, ψ, hflat, hcomap, hbc m hm A' hA'cr hA'lr ψ hflat hcomap hsplit⟩

#print axioms area_G4a_localGlobal_of_models

-- The frozen statement of the area, for comparison.  Its proof is not available in this
-- workspace: it needs the areas `F1` and `COH` (see the module documentation and `NOTES.md`).
#check @DSMap.area_G4a_localGlobal

/-- **The same local-to-global step, in the explicit presentation form.**

Instead of a `FreePres`, the caller supplies a matrix `D` and a vector `e` with the property
that `DSplit A X f` is equivalent to the unimodularity of the class of `e` in
`A^m ⧸ im D` (the form in which the model of `RΓ(X, 𝒪)` presents itself after choosing
bases), and the base change of the model correspondingly.  The conclusion is again the
frozen conclusion. -/
theorem area_G4a_localGlobal_of_presentation.{a, b, c, d, e} (A : Type a) [CommRing A]
    [IsNoetherianRing A] (X : Scheme.{a}) (f : X ⟶ Spec (.of A)) [IsProper f]
    (hp : DSMap.IsProjOver A f) {m n : ℕ} (D : Fin m → Fin n → A) (e : Fin m → A)
    (hcrit : DSMap.DSplit.{a, b, c} A X f ↔ Module.IsUnimodular A (presentMk D e))
    (hbc : ∀ (p : Ideal A) (hpm : p.IsMaximal) (A' : Type a) (_ : CommRing A')
      (_ : IsLocalRing A') (ψ : A →+* A') (hflat : ψ.Flat)
      (hcomap : (IsLocalRing.maximalIdeal A').comap ψ = p),
      (letI : Algebra A A' := ψ.toAlgebra
       DSMap.DSplit.{a, d, e} A' (pullback f (Spec.map (CommRingCat.ofHom ψ)))
         (pullback.snd f (Spec.map (CommRingCat.ofHom ψ))) →
       Module.IsUnimodular A' (presentMk (fun i j => algebraMap A A' (D i j))
         (fun i => algebraMap A A' (e i)))))
    (h : ∀ p : Ideal A, p.IsMaximal → ∃ (A' : Type a) (_ : CommRing A') (_ : IsLocalRing A')
      (ψ : A →+* A'), ψ.Flat ∧ (IsLocalRing.maximalIdeal A').comap ψ = p ∧
      DSMap.DSplit.{a, d, e} A' (pullback f (Spec.map (CommRingCat.ofHom ψ)))
        (pullback.snd f (Spec.map (CommRingCat.ofHom ψ)))) :
    DSMap.DSplit.{a, b, c} A X f := by
  rw [hcrit]
  refine isUnimodular_presentMk_of_forall_maximal D e ?_
  intro p hp_max
  obtain ⟨A', hA'cr, hA'lr, ψ, hflat, hcomap, hsplit⟩ := h p hp_max
  exact ⟨A', hA'cr, hA'lr, ψ, hflat, hcomap, hbc p hp_max A' hA'cr hA'lr ψ hflat hcomap hsplit⟩

#print axioms area_G4a_localGlobal_of_presentation

end Work.DSG4a

/-! ## The repaired frozen node of the lead's `Submission/Work/DSMap/Fix2.lean`

`DSMap.Fix2.area_G4a_localGlobalU` replaces the frozen node `DSMap.area_G4a_localGlobal` (whose
hypothesis `DSplit.{a, d, e} A' X' f'` quantifies over derived-category instances at arbitrary
universe levels `d`, `e`, whence it is unusable — see `Submission/Work/DSG4a/STATUS.md` §1(a) and
`Submission/Work/DSG4a/Obstruction.lean`) by the same node with `d = e = a + 1`, the universes at
which `HasDerivedCategory.standard` provides the instances.  The theorem below has a type
definitionally identical to that node (checked by the `example` at the end) and is proved by the
area's machinery `Work.DSG4a.area_G4a_localGlobal_of_areas`, citing the two still frozen areas
`DSMap.area_F1_cech` and `DSMap.area_COH`: its axiom list therefore contains `sorryAx` *through
those two nodes only*, which is what the lead's final wiring replaces (the area theorems
`Work.DSG4a.area_G4a_localGlobal_of_areas` and `…_of_instances` are the same statement with the
conclusions of `F1`/`COH` as explicit hypotheses, and are axiom-clean). -/

open CategoryTheory AlgebraicGeometry IsLocalRing Limits

namespace DSMap.Fix2

/-- **Area `G4aU` of the lead's `Fix2`, proved.** -/
theorem area_G4a_localGlobalU_proved.{a, b, c} (A : Type a) [CommRing A] [IsNoetherianRing A]
    (X : Scheme.{a}) (f : X ⟶ Spec (.of A)) [IsProper f] (hp : IsProjOver A f)
    (h : ∀ m : Ideal A, m.IsMaximal → ∃ (A' : Type a) (_ : CommRing A') (_ : IsLocalRing A')
      (ψ : A →+* A'), ψ.Flat ∧ (maximalIdeal A').comap ψ = m ∧
      DSplit.{a, a + 1, a + 1} A' (pullback f (Spec.map (CommRingCat.ofHom ψ)))
        (pullback.snd f (Spec.map (CommRingCat.ofHom ψ)))) :
    DSplit.{a, b, c} A X f :=
  Work.DSG4a.area_G4a_localGlobal_of_areas.{a, b, c} A X f hp
    (fun (B : Type a) [CommRing B] {Y : Scheme.{a}} (g : Y ⟶ Spec (.of B)) [IsProper g]
      {κ : Type a} [Finite κ] [Nonempty κ] (W : κ → Y.Opens) (hW : ∀ i, IsAffineOpen (W i))
      (hcov : ⨆ i, W i = ⊤) (i : HasDerivedCategory.{b} (ModuleCat.{a} B))
      (j : HasDerivedCategory.{c} (SheafOfModules.{a} Y.ringCatSheaf))
      (k : EnoughInjectives (SheafOfModules.{a} Y.ringCatSheaf)) => by
        letI := i
        letI := j
        letI := k
        haveI : QuasiCompact g := Work.DSMX0bU.quasiCompact_of_isProper g
        exact DSMap.area_F1_cech.{a, b, c} B Y g W hW hcov)
    (fun (B : Type a) [CommRing B] [IsNoetherianRing B] {Y : Scheme.{a}}
      (g : Y ⟶ Spec (.of B)) [IsProper g] (hp : IsProjOver B g)
      (i : HasDerivedCategory.{b} (ModuleCat.{a} B))
      (j : HasDerivedCategory.{c} (SheafOfModules.{a} Y.ringCatSheaf))
      (k : EnoughInjectives (SheafOfModules.{a} Y.ringCatSheaf)) => by
        letI := i
        letI := j
        letI := k
        exact DSMap.area_COH.{a, b, c} B Y g hp)
    (fun (A' : Type a) [CommRing A'] (ψ : A →+* A') [Algebra A A'] {κ : Type a}
      [Finite κ] [Nonempty κ]
      (W : κ → (Work.DSG4a.baseChangeScheme (A := A) (A' := A') X f).Opens)
      (hW : ∀ i, IsAffineOpen (W i)) (hcov : ⨆ i, W i = ⊤)
      (i : HasDerivedCategory.{a + 1} (ModuleCat.{a} A'))
      (j : HasDerivedCategory.{a + 1}
        (SheafOfModules.{a} (Work.DSG4a.baseChangeScheme (A := A) (A' := A') X f).ringCatSheaf))
      (k : EnoughInjectives
        (SheafOfModules.{a} (Work.DSG4a.baseChangeScheme (A := A) (A' := A') X f).ringCatSheaf)) => by
        letI := i
        letI := j
        letI := k
        haveI : IsProper (Work.DSG4a.baseChangeSnd (A := A) (A' := A') X f) := inferInstance
        haveI : QuasiCompact (Work.DSG4a.baseChangeSnd (A := A) (A' := A') X f) :=
          Work.DSMX0bU.quasiCompact_of_isProper _
        exact DSMap.area_F1_cech.{a, a + 1, a + 1} A'
          (Work.DSG4a.baseChangeScheme (A := A) (A' := A') X f)
          (Work.DSG4a.baseChangeSnd (A := A) (A' := A') X f) W hW hcov)
    h

-- The type of the delivered theorem is definitionally identical to the type of the frozen
-- repaired node `DSMap.Fix2.area_G4a_localGlobalU`.
universe a b c

example : type_of% (@area_G4a_localGlobalU_proved.{a, b, c}) =
    type_of% (@DSMap.Fix2.area_G4a_localGlobalU.{a, b, c}) := rfl

end DSMap.Fix2
