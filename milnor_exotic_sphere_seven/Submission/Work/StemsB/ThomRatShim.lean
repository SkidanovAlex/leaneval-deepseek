import Mathlib
import Submission.Work.Thom.Cohomology
import Submission.Work.Thom.Pair
import Submission.Work.Thom.MixedCup
import Submission.Work.StemsB.MixedCupR

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Coefficient-generic shims for the port of the Thom chapter

The `Submission/Work/Thom/` chapter mixes two conventions: some lemmas are coefficient-generic
(`Work.Thom.Coh`, `Work.Thom.RelCoh`, `Work.Thom.CohMap`, `Work.Thom.mixedCupC R`,
`Work.Thom.relToAbs R`, `Work.Cohomology.mixedCupR R`, `Work.Cohomology.pairδ R`,
`Work.Cohomology.pair_exact₁/₂/₃ R`), while a few are pinned to `ℤ`
(`Work.Thom.pairδC`, `Work.Thom.pairExact₁/₂/₃`, `Work.Thom.mixedCup_relToAbs`,
`Work.Thom.relToAbs_relClassOf`).

This file supplies the missing coefficient-generic forms, so that the proofs of the chapter can be
carried over to an arbitrary coefficient ring `R` (in particular to `ℚ`, which is what the rational
Wang transgression needs) with the *same* text, only the coefficient ring changing.  Nothing here
is new mathematics: each statement is the `R`-instance of an existing one.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.StemsB

open CategoryTheory

noncomputable section

/-- The connecting homomorphism `H^n(A;R) → H^{n+1}(X,A;R)` of the pair `(X,A)`. -/
abbrev pairδCR (R : Type) [CommRing R] {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    Work.Thom.Coh R n A ⟶ Work.Thom.RelCoh R (n + 1) X A :=
  Work.Cohomology.pairδ R (TopCat.of X) A n

/-- The exactness of the pair sequence at `H^{n+1}(X,A;R)`, in the `range`/`ker` form. -/
theorem pairKer₁R (R : Type) [CommRing R] {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    LinearMap.range (pairδCR R A n).hom
      = LinearMap.ker (Work.Thom.relToAbs R A (n + 1)).hom := by
  have h := ShortComplex.Exact.moduleCat_range_eq_ker
    (Work.Cohomology.pair_exact₁ R (TopCat.of X) A n)
  exact h

/-- The exactness of the pair sequence at `H^n(X;R)`, in the `range`/`ker` form. -/
theorem pairKer₂R (R : Type) [CommRing R] {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    LinearMap.range (Work.Thom.relToAbs R A n).hom
      = LinearMap.ker (Work.Thom.CohMap (Work.Thom.subtypeMap A) R n).hom := by
  have h := ShortComplex.Exact.moduleCat_range_eq_ker
    (Work.Cohomology.pair_exact₂ R (TopCat.of X) A n)
  exact h

/-- The exactness of the pair sequence at `H^n(A;R)`, in the `range`/`ker` form. -/
theorem pairKer₃R (R : Type) [CommRing R] {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    LinearMap.ker (pairδCR R A n).hom
      = LinearMap.range (Work.Thom.CohMap (Work.Thom.subtypeMap A) R n).hom := by
  have h := ShortComplex.Exact.moduleCat_range_eq_ker
    (Work.Cohomology.pair_exact₃ R (TopCat.of X) A n)
  exact h.symm

/-- The `R`-valued mixed cup product of the chapter is the generic one. -/
theorem mixedCupC_eq_mixedCupR (R : Type) [CommRing R] {X : Type} [TopologicalSpace X]
    (A : Set X) (m n : ℕ) :
    Work.Thom.mixedCupC R A m n = Work.Cohomology.mixedCupR R (TopCat.of X) A m n := rfl

/-- The forgetful map on the class of a relative cocycle, over `R`. -/
theorem relToAbs_relClassOf_R (R : Type) [CommRing R] {X : Type} [TopologicalSpace X] (A : Set X)
    {n : ℕ} (a : Work.Cohomology.relKern R (TopCat.of X) A n)
    (ha : Work.Cohomology.relDiffLM R (TopCat.of X) A n a = 0) :
    (Work.Thom.relToAbs R A n).hom (Work.Cohomology.relClassOf R (TopCat.of X) A a ha) =
      Work.Cohomology.cohomologyClassOf R (TopCat.toSSet.obj (TopCat.of X)) a.1
        (Work.Cohomology.relClassOf_cochainDiff R (TopCat.of X) A a ha) :=
  Work.Cohomology.relIncl_homologyMap_relClassOf R (TopCat.of X) A a ha

/-- **The mixed cup product is compatible with the forgetful map**, over `R`. -/
theorem mixedCup_relToAbs_R (R : Type) [CommRing R] {X : Type} [TopologicalSpace X] (A : Set X)
    (m n : ℕ) (x : Work.Thom.Coh R m X) (y : Work.Thom.RelCoh R n X A) :
    (Work.Thom.relToAbs R A (m + n)).hom ((Work.Thom.mixedCupC R A m n) x y) =
      Work.Cohomology.cupH' R (TopCat.toSSet.obj (TopCat.of X)) m n x
        ((Work.Thom.relToAbs R A n).hom y) := by
  obtain ⟨a, ha, rfl⟩ := Work.Cohomology.exists_cohomologyClassOf R
    (TopCat.toSSet.obj (TopCat.of X)) m x
  obtain ⟨b, hb, rfl⟩ := Work.Cohomology.exists_relClassOf R (TopCat.of X) A n y
  obtain ⟨hmem, hd, hcup⟩ := Work.Cohomology.mixedCupR_apply R (TopCat.of X) A m n a b ha hb
  rw [mixedCupC_eq_mixedCupR, hcup]
  rw [relToAbs_relClassOf_R R A ⟨_, hmem⟩ hd]
  rw [relToAbs_relClassOf_R R A b hb]
  rw [Work.Cohomology.cupH'_apply' R (TopCat.toSSet.obj (TopCat.of X)) a b.1 ha
      (Work.Cohomology.relClassOf_cochainDiff R (TopCat.of X) A b hb)]

end

end Work.StemsB
