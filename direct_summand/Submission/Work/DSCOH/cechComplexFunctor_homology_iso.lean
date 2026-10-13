/-
Area DSCOH (curric-46) — the comparison between Mathlib's unnormalized Čech complex and the
(geometric) alternating Čech complex, at the level of cohomology.

The unnormalized Čech complex `(cechComplexFunctor U).obj P` (all tuples `Fin (n+1) → ι`,
repetitions allowed) is compared with the alternating complex `Work.DSCOH.altCech P U` (subsets
`S` of `ι` with `|S| = n+1`) through the chain

`allT = (cechComplexFunctor U).obj P  →  semiT  →  ordT  ≅  altCech`

where

* `semiT` is the semi-ordered complex (nondecreasing tuples), `Work.DSCOH.Norm.semiT`;
* `ordT` is the ordered complex (strictly increasing tuples), `Work.DSCOH.Norm.ordT`.

Each step is a homotopy equivalence (hence a quasi-isomorphism):

* `allT ≃ semiT` is the classical sorting/degeneracy homotopy (Stacks Tag 01FG, §20.23): the
  section `psi` of the projection `semiProj` is the signed sorting extension
  `psi(s)_x = sign(σ^x) · s_{sorted x}`; the homotopy components and the degreewise identities are
  the raw data supplied by `Work.DSCOH.Norm.allT_homotopy_semiT`.
* `semiT ≃ ordT` is the "degenerate simplices" argument: `ordIncl ≫ ordProj = 𝟙`
  (`Work.DSCOH.Norm.ordIncl_ordProj`) and `ordProj ≫ ordIncl ~ 𝟙`
  (`Work.DSCOH.Norm.semiHom_homotopy`, via the homotopy `Work.DSCOH.Norm.semiHom`).
* `ordT ≅ altCech` is the reindexing of strictly increasing tuples by subsets
  (`Work.DSCOH.Norm.ordT_iso_altCech`).

Since each step is a homotopy equivalence of cochain complexes, the homology in every degree is
isomorphic, which is the statement of `cechComplexFunctor_homology_iso` below.
-/
import Mathlib
import Submission.Work.DSCOH.AltCechComplex
import Submission.Work.DSCOH.Norm.Complexes
import Submission.Work.DSCOH.Norm.ordT_iso_altCech
import Submission.Work.DSCOH.Norm.ordIncl_ordProj
import Submission.Work.DSCOH.Norm.SemiHomRaw
import Submission.Work.DSCOH.Norm.allT_homotopy_semiT

open CategoryTheory Limits Opposite TopologicalSpace
open scoped BigOperators

namespace Work.DSCOH

noncomputable section

set_option linter.unusedVariables false

universe u v w

variable {X : Type u} [TopologicalSpace X] {A : Type v} [CommRing A]
variable {ι : Type w} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
  [CategoryTheory.Limits.HasProducts (ModuleCat A)]
variable {P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ ModuleCat A} {U : ι → TopologicalSpace.Opens X}

/-- The chain map `semiT ⟶ allT` attached to a degreewise family which is a chain map. -/
def Norm.psiC (psi : ∀ n : ℕ, Norm.semiTerm P U n ⟶ ((cechComplexFunctor U).obj P).X n)
    (hchain : ∀ n : ℕ, psi n ≫ ((cechComplexFunctor U).obj P).d n (n + 1) =
      Norm.semiD P U n ≫ psi (n + 1)) :
    Norm.semiT P U ⟶ (cechComplexFunctor U).obj P :=
  CochainComplex.ofHom (X := Norm.semiT P U) (Y := (cechComplexFunctor U).obj P)
    (fun n => psi n) (fun n => by rw [Norm.semiT_d]; exact hchain n)

@[simp]
lemma Norm.psiC_f (psi : ∀ n : ℕ, Norm.semiTerm P U n ⟶ ((cechComplexFunctor U).obj P).X n)
    (hchain : ∀ n : ℕ, psi n ≫ ((cechComplexFunctor U).obj P).d n (n + 1) =
      Norm.semiD P U n ≫ psi (n + 1)) (n : ℕ) :
    (Norm.psiC psi hchain).f n = psi n := rfl

/-- **Semi-ordered versus all tuples.**  The raw data of the sorting homotopy of Stacks Tag 01FG,
§20.23: a section `psi` of the projection `semiProj` which is a chain map, together with the
degreewise components `h` of the homotopy `semiProj ≫ psi ~ 𝟙` (the degree `0` identity is listed
separately, since it does not follow from the higher ones). -/
def homotopyEquiv_allT_semiT
    (psi : ∀ n : ℕ, Norm.semiTerm P U n ⟶ ((cechComplexFunctor U).obj P).X n)
    (hsec : ∀ n : ℕ, psi n ≫ Norm.semiProj P U n = 𝟙 (Norm.semiTerm P U n))
    (hchain : ∀ n : ℕ, psi n ≫ ((cechComplexFunctor U).obj P).d n (n + 1) =
      Norm.semiD P U n ≫ psi (n + 1))
    (h : ∀ n : ℕ, ((cechComplexFunctor U).obj P).X (n + 1) ⟶ ((cechComplexFunctor U).obj P).X n)
    (h0 : ((cechComplexFunctor U).obj P).d 0 1 ≫ h 0 + Norm.semiProj P U 0 ≫ psi 0 =
      𝟙 (((cechComplexFunctor U).obj P).X 0))
    (hs : ∀ n : ℕ, h n ≫ ((cechComplexFunctor U).obj P).d n (n + 1) +
        ((cechComplexFunctor U).obj P).d (n + 1) (n + 2) ≫ h (n + 1) +
        Norm.semiProj P U (n + 1) ≫ psi (n + 1) =
      𝟙 (((cechComplexFunctor U).obj P).X (n + 1))) :
    HomotopyEquiv (Norm.semiT P U) ((cechComplexFunctor U).obj P) := by
  refine HomotopyEquiv.mk (Norm.psiC psi hchain) (Norm.semiProjC P U) ?_ ?_
  · apply Homotopy.ofEq
    apply HomologicalComplex.hom_ext
    intro n
    rw [HomologicalComplex.comp_f, HomologicalComplex.id_f, Norm.psiC_f, Norm.semiProjC_f]
    exact hsec n
  · refine (Norm.homotopyOfRaw (C := (cechComplexFunctor U).obj P)
      (D := (cechComplexFunctor U).obj P) (f := 𝟙 ((cechComplexFunctor U).obj P))
      (g := Norm.semiProjC P U ≫ Norm.psiC psi hchain) (fun n => h n) ?_ ?_).symm
    · rw [HomologicalComplex.id_f, HomologicalComplex.comp_f, Norm.semiProjC_f,
        Norm.psiC_f]
      exact h0.symm
    · intro n
      rw [HomologicalComplex.id_f, HomologicalComplex.comp_f, Norm.semiProjC_f, Norm.psiC_f,
        ← hs n]
      abel

/-- **Semi-ordered versus ordered**, from the "degenerate simplices" homotopy and the section
identity `ordIncl ≫ ordProj = 𝟙`. -/
def homotopyEquiv_semiT_ordT
    (hord : Norm.ordInclC P U ≫ Norm.ordProjC P U = 𝟙 (Norm.ordT P U))
    (hsemi : Nonempty (Homotopy (Norm.ordProjC P U ≫ Norm.ordInclC P U) (𝟙 (Norm.semiT P U)))) :
    HomotopyEquiv (Norm.ordT P U) (Norm.semiT P U) :=
  HomotopyEquiv.mk (Norm.ordInclC P U) (Norm.ordProjC P U) (Homotopy.ofEq hord) hsemi.some

/-- **Ordered versus the alternating complex**: the reindexing of strictly increasing tuples by
subsets of `ι`. -/
def iso_ordT_altCech :
    Norm.ordT P U ≅ altCech P U :=
  HomologicalComplex.Hom.isoOfComponents (C₁ := Norm.ordT P U) (C₂ := altCech P U)
    (Classical.choose (Norm.ordT_iso_altCech P U))
    (fun i j hij => by
      rw [ComplexShape.up_Rel] at hij
      subst hij
      rw [Norm.ordT_d]
      exact (Classical.choose_spec (Norm.ordT_iso_altCech P U)) i)

end

theorem cechComplexFunctor_homology_iso (A : Type*) [CommRing A] (X : AlgebraicGeometry.Scheme)
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    [CategoryTheory.Limits.HasProducts (ModuleCat A)]
    (P : CategoryTheory.Functor (Opposite (TopologicalSpace.Opens X)) (ModuleCat A))
    (U : ι → TopologicalSpace.Opens X) (q : ℕ) :
    Nonempty (((CategoryTheory.cechComplexFunctor U).obj P).homology q ≅
      (Work.DSCOH.altCech P U).homology q) := by
  classical
  obtain ⟨psi, hsec, hchain, h, h0, hs⟩ := Norm.allT_homotopy_semiT P U
  exact ⟨((homotopyEquiv_allT_semiT psi hsec hchain h h0 hs).toHomologyIso q).symm.trans
    (((homotopyEquiv_semiT_ordT (Norm.ordIncl_ordProj P U)
        (Norm.SemiRaw.semiHom_homotopy P U)).toHomologyIso q).symm.trans
      ((HomologicalComplex.homologyFunctor (ModuleCat A) (ComplexShape.up ℕ) q).mapIso
        iso_ordT_altCech))⟩

end Work.DSCOH
