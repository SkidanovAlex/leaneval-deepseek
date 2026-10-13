/-
# `Work.DSEQP.cechZ_homology_chartCover_proved`

Finiteness and high-degree vanishing of the cohomology of the (unnormalised) Čech complex of the
structure sheaf of a closed subscheme `i : X ⟶ ℙᴺ_A` over a Noetherian ring `A`, with respect to
the standard chart cover `DSMap.Mix2.chartCover i`.

Everything except the *normalisation comparison* is already available and axiom-clean:

* the **vanishing** half is `Work.DSEQ0.cechZ_homology_isZero_of_card_le` (pure combinatorics:
  image-size filtration + `Work.DSEQ0.surjCech_vanishing`);
* the **finiteness** half is Serre finiteness for the *chart* Čech complex of a finitely generated
  graded module (`Work.DSCOH.chartCech_finite_vanishing`, area DSCOH) together with the chartwise
  bridge `Work.DSEQP.chartCechTerm_iso`;
* the two are wired together, given the normalisation comparison

  `h1c : ∀ q, H^q(cech A X f U) ≅ H^q(altCech (cechPresheaf A X f) U)`,

  by `Work.DSEQP.cechZ_homology_finite_chartCover` (`Submission/Work/DSEQP/CechCoherence.lean`).

This file supplies `h1c`.  Mathlib's `cechComplexFunctor U P` is the *unnormalised* Čech complex
(indexed by all tuples `Fin (n+1) → ι`).  It is compared with the alternating Čech complex through
the semi-ordered complex (`Work.DSCOH.Norm.semiT`, nondecreasing tuples):

* `semiProj : allT ⟶ semiT` has the signed sorting section `semiLift` (`semiLift_semiProj`), which
  is a chain map (`semiLift_chain`);
* the "degenerate simplices" argument lower down the chain (`Work.DSCOH.Norm.SemiRaw.semiHom_homotopy`
  and `Work.DSCOH.Norm.ordIncl_ordProj`) and the reindexing `Work.DSCOH.Norm.ordT_iso_altCech`
  compare `semiT` with the alternating complex `Work.DSCOH.altCech`, both proved and axiom-clean;
* the missing ingredient is Stacks 20.23.6 (tag `01FG`, the "first homotopy"): `semiProj ≫ semiLift`
  is homotopic to the identity of the unnormalised complex, i.e. there is `h` with
  `d 0 1 ≫ h 0 + semiProj 0 ≫ semiLift 0 = 𝟙` and
  `h n ≫ d n (n+1) + d (n+1) (n+2) ≫ h (n+1) + semiProj (n+1) ≫ semiLift (n+1) = 𝟙` in every degree.

The assembly below (`normPsiC`, `normHomotopyEquivAllTSemiT`, `normHomotopyEquivSemiTOrdT`,
`normIsoOrdTAltCech`, `cechHomologyIsoAltCech_of_homotopy`) is self-contained: it only imports the
proved, axiom-clean pieces of `Submission.Work.DSCOH.Norm` (it does *not* import the modules whose
`cechComplexFunctor_homology_iso` rests on the still-open `semiLift_homotopy`).
-/
import Mathlib
import Submission.Work.DSMap.Gaps
import Submission.Work.DSEQP.CechCoherence
import Submission.Work.DSCOH.Norm.SortSection
import Submission.Work.DSCOH.Norm.Complexes
import Submission.Work.DSCOH.Norm.semiLift_chain
import Submission.Work.DSCOH.Norm.ordT_iso_altCech
import Submission.Work.DSCOH.Norm.ordIncl_ordProj
import Submission.Work.DSCOH.Norm.SemiHomRaw
import Submission.Work.DSCOH.AltCechComplex
import Submission.Work.DSCOH.Norm.semiLift_homotopy
import Submission.Work.DSEQ0.cechZ_homology_isZero_of_card_le

namespace Work.DSEQP

open CategoryTheory AlgebraicGeometry IsLocalRing Limits Opposite DSMap DSMap.Mix DSMap.Mix2
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

universe u v w

variable {X : Type u} [TopologicalSpace X] {A : Type v} [CommRing A]
variable {ι : Type w} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
  [CategoryTheory.Limits.HasProducts (ModuleCat A)]
variable {P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ ModuleCat A} {U : ι → TopologicalSpace.Opens X}

/-! ## The comparison `allT ⟶ semiT ⟶ ordT ≅ altCech`, from the raw homotopy data -/

/-- The chain map `semiT ⟶ allT` attached to a degreewise family which is a chain map. -/
noncomputable def normPsiC
    (psi : ∀ n : ℕ, Work.DSCOH.Norm.semiTerm P U n ⟶ ((cechComplexFunctor U).obj P).X n)
    (hchain : ∀ n : ℕ, psi n ≫ ((cechComplexFunctor U).obj P).d n (n + 1) =
      Work.DSCOH.Norm.semiD P U n ≫ psi (n + 1)) :
    Work.DSCOH.Norm.semiT P U ⟶ (cechComplexFunctor U).obj P :=
  CochainComplex.ofHom (X := Work.DSCOH.Norm.semiT P U) (Y := (cechComplexFunctor U).obj P)
    (fun n => psi n) (fun n => by rw [Work.DSCOH.Norm.semiT_d]; exact hchain n)

@[simp]
lemma normPsiC_f
    (psi : ∀ n : ℕ, Work.DSCOH.Norm.semiTerm P U n ⟶ ((cechComplexFunctor U).obj P).X n)
    (hchain : ∀ n : ℕ, psi n ≫ ((cechComplexFunctor U).obj P).d n (n + 1) =
      Work.DSCOH.Norm.semiD P U n ≫ psi (n + 1)) (n : ℕ) :
    (normPsiC psi hchain).f n = psi n := rfl

/-- **The sorting deformation retraction** (Stacks 20.23.6, the "first homotopy"): a section `psi`
of `semiProj` which is a chain map, together with a homotopy witnessing that `semiProj ≫ psi` is
homotopic to the identity, exhibits `allT` as a deformation retract of `semiT`. -/
noncomputable def normHomotopyEquivAllTSemiT
    (psi : ∀ n : ℕ, Work.DSCOH.Norm.semiTerm P U n ⟶ ((cechComplexFunctor U).obj P).X n)
    (hsec : ∀ n : ℕ, psi n ≫ Work.DSCOH.Norm.semiProj P U n = 𝟙 (Work.DSCOH.Norm.semiTerm P U n))
    (hchain : ∀ n : ℕ, psi n ≫ ((cechComplexFunctor U).obj P).d n (n + 1) =
      Work.DSCOH.Norm.semiD P U n ≫ psi (n + 1))
    (h : ∀ n : ℕ, ((cechComplexFunctor U).obj P).X (n + 1) ⟶ ((cechComplexFunctor U).obj P).X n)
    (h0 : ((cechComplexFunctor U).obj P).d 0 1 ≫ h 0 + Work.DSCOH.Norm.semiProj P U 0 ≫ psi 0 =
      𝟙 (((cechComplexFunctor U).obj P).X 0))
    (hs : ∀ n : ℕ, h n ≫ ((cechComplexFunctor U).obj P).d n (n + 1) +
        ((cechComplexFunctor U).obj P).d (n + 1) (n + 2) ≫ h (n + 1) +
        Work.DSCOH.Norm.semiProj P U (n + 1) ≫ psi (n + 1) =
      𝟙 (((cechComplexFunctor U).obj P).X (n + 1))) :
    HomotopyEquiv (Work.DSCOH.Norm.semiT P U) ((cechComplexFunctor U).obj P) := by
  refine HomotopyEquiv.mk (normPsiC psi hchain) (Work.DSCOH.Norm.semiProjC P U) ?_ ?_
  · apply Homotopy.ofEq
    apply HomologicalComplex.hom_ext
    intro n
    rw [HomologicalComplex.comp_f, HomologicalComplex.id_f, Work.DSCOH.Norm.semiProjC_f]
    exact hsec n
  · refine (Work.DSCOH.Norm.homotopyOfRaw (C := (cechComplexFunctor U).obj P)
      (D := (cechComplexFunctor U).obj P) (f := 𝟙 ((cechComplexFunctor U).obj P))
      (g := Work.DSCOH.Norm.semiProjC P U ≫ normPsiC psi hchain) (fun n => h n) ?_ ?_).symm
    · rw [HomologicalComplex.id_f, HomologicalComplex.comp_f, Work.DSCOH.Norm.semiProjC_f]
      rw [normPsiC_f]
      exact h0.symm
    · intro n
      rw [HomologicalComplex.id_f, HomologicalComplex.comp_f, Work.DSCOH.Norm.semiProjC_f,
        ← hs n]
      abel

/-- **Ordered versus semi-ordered**, from the "degenerate simplices" homotopy and the section
identity `ordIncl ≫ ordProj = 𝟙`. -/
noncomputable def normHomotopyEquivSemiTOrdT
    (hord : Work.DSCOH.Norm.ordInclC P U ≫ Work.DSCOH.Norm.ordProjC P U =
      𝟙 (Work.DSCOH.Norm.ordT P U))
    (hsemi : Nonempty (Homotopy (Work.DSCOH.Norm.ordProjC P U ≫ Work.DSCOH.Norm.ordInclC P U)
      (𝟙 (Work.DSCOH.Norm.semiT P U)))) :
    HomotopyEquiv (Work.DSCOH.Norm.ordT P U) (Work.DSCOH.Norm.semiT P U) :=
  HomotopyEquiv.mk (Work.DSCOH.Norm.ordInclC P U) (Work.DSCOH.Norm.ordProjC P U)
    (Homotopy.ofEq hord) hsemi.some

/-- **Ordered versus the alternating complex**: the reindexing of strictly increasing tuples by
subsets of `ι`. -/
noncomputable def normIsoOrdTAltCech :
    Work.DSCOH.Norm.ordT P U ≅ Work.DSCOH.altCech P U :=
  HomologicalComplex.Hom.isoOfComponents (C₁ := Work.DSCOH.Norm.ordT P U)
    (C₂ := Work.DSCOH.altCech P U)
    (Classical.choose (Work.DSCOH.Norm.ordT_iso_altCech P U))
    (fun i j hij => by
      rw [ComplexShape.up_Rel] at hij
      subst hij
      rw [Work.DSCOH.Norm.ordT_d]
      exact (Classical.choose_spec (Work.DSCOH.Norm.ordT_iso_altCech P U)) i)

/-- **The normalisation comparison at the level of cohomology**, from the raw homotopy data: the
homology of Mathlib's unnormalised Čech complex is the homology of the alternating Čech complex. -/
theorem cechHomologyIsoAltCech_of_homotopy
    (psi : ∀ n : ℕ, Work.DSCOH.Norm.semiTerm P U n ⟶ ((cechComplexFunctor U).obj P).X n)
    (hsec : ∀ n : ℕ, psi n ≫ Work.DSCOH.Norm.semiProj P U n = 𝟙 (Work.DSCOH.Norm.semiTerm P U n))
    (hchain : ∀ n : ℕ, psi n ≫ ((cechComplexFunctor U).obj P).d n (n + 1) =
      Work.DSCOH.Norm.semiD P U n ≫ psi (n + 1))
    (h : ∀ n : ℕ, ((cechComplexFunctor U).obj P).X (n + 1) ⟶ ((cechComplexFunctor U).obj P).X n)
    (h0 : ((cechComplexFunctor U).obj P).d 0 1 ≫ h 0 + Work.DSCOH.Norm.semiProj P U 0 ≫ psi 0 =
      𝟙 (((cechComplexFunctor U).obj P).X 0))
    (hs : ∀ n : ℕ, h n ≫ ((cechComplexFunctor U).obj P).d n (n + 1) +
        ((cechComplexFunctor U).obj P).d (n + 1) (n + 2) ≫ h (n + 1) +
        Work.DSCOH.Norm.semiProj P U (n + 1) ≫ psi (n + 1) =
      𝟙 (((cechComplexFunctor U).obj P).X (n + 1))) :
    ∀ q : ℕ, Nonempty (((cechComplexFunctor U).obj P).homology q ≅
      (Work.DSCOH.altCech P U).homology q) := by
  intro q
  exact ⟨((normHomotopyEquivAllTSemiT psi hsec hchain h h0 hs).toHomologyIso q).symm.trans
    (((normHomotopyEquivSemiTOrdT (Work.DSCOH.Norm.ordIncl_ordProj P U)
        (Work.DSCOH.Norm.SemiRaw.semiHom_homotopy P U)).toHomologyIso q).symm.trans
      ((HomologicalComplex.homologyFunctor (ModuleCat A) (ComplexShape.up ℕ) q).mapIso
        (normIsoOrdTAltCech (P := P) (U := U))))⟩

/-! ## The Stacks first homotopy (the input furnished by area DSCOH)

`Work.DSCOH.Norm.semiLift_homotopy` (Stacks 20.23.6, tag `01FG`, Equation 20.23.6.1) is proved
and axiom-clean in `Submission/Work/DSCOH/Norm/semiLift_homotopy.lean`: there is a homotopy `h`
between `semiProj ≫ semiLift` and the identity of the unnormalised Čech complex.  It is the single
input that `Submission/Work/DSEQP/CechCoherence.lean` leaves open. -/

/-! ## The target theorem -/

theorem cechZ_homology_chartCover_proved (A : Type u) [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} (N : ℕ) (i : X ⟶ PSpace A N) (hi : IsClosedImmersion i)
    (f : X ⟶ Spec (.of A)) (hif : i ≫ PSpace.toSpec A N = f) :
    ∃ N' : ℤ, ∀ j : ℤ,
      Module.Finite A ((cechZ A X f (chartCover i)).homology j) ∧
      (N' < j → CategoryTheory.Limits.IsZero ((cechZ A X f (chartCover i)).homology j)) := by
  -- The normalisation comparison (Stacks 01FG, the first homotopy) for the chart cover of `X`.
  obtain ⟨h, h0, hs⟩ := Work.DSCOH.Norm.semiLift_homotopy (DSMap.cechPresheaf A X f)
    (chartCover i)
  have h1c : ∀ q : ℕ, Nonempty ((DSMap.cech A X f (chartCover i)).homology q ≅
      (Work.DSCOH.altCech (DSMap.cechPresheaf A X f) (chartCover i)).homology q) := fun q =>
    cechHomologyIsoAltCech_of_homotopy (Work.DSCOH.Norm.semiLift (DSMap.cechPresheaf A X f)
        (chartCover i))
      (Work.DSCOH.Norm.semiLift_semiProj (DSMap.cechPresheaf A X f) (chartCover i))
      (Work.DSCOH.Norm.semiLift_chain (DSMap.cechPresheaf A X f) (chartCover i)) h h0 hs q
  exact cechZ_homology_finite_chartCover A N i hi f hif h1c

end Work.DSEQP
