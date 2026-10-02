import Mathlib
import Submission.Work.Cohomology.mixedRelCupH
import Submission.Work.Cohomology.RelCupTransfer
import Submission.Work.Cohomology.RelCup

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The mixed cup product over an arbitrary commutative ring

`Submission/Work/Cohomology/mixedRelCupH.lean` proves the existence of the mixed cup product

  `H^m(X;R) × H^n(X,A;R) ⟶ H^{m+n}(X,A;R)`

as an unexplicit `∃`, for a **general commutative ring** `R`.
`Submission/Work/Cohomology/sph3DiscMixedDefs.lean` then pins it down for `R = ℤ` (`mixedCup`).

This file does the same for an arbitrary `R` (`mixedCupR` with its computation rule
`mixedCupR_apply`).  This is the first step of the `ℚ`-coefficient rerun of the E4 chapter
(`RERUN_PLAN.md` §1): the whole derivation chapter is stated here over `ℤ`, while subproject SERRE's
engine is over `ℚ`, so the coefficient-general forms are needed.
-/

namespace Work.Cohomology

noncomputable section

/-- **The mixed cup product over a commutative ring `R`.**
`H^m(X;R) × H^n(X,A;R) ⟶ H^{m+n}(X,A;R)`, a choice of the pairing whose existence is
`Work.Cohomology.mixedRelCupH`. -/
noncomputable def mixedCupR (R : Type) [CommRing R] (X : TopCat) (A : Set X) (m n : ℕ) :=
  (Classical.choose (mixedRelCupH (R := R) X A)) m n

/-- **The computation rule for `mixedCupR`**: on the classes of an absolute cocycle `a` and a
relative cocycle `b` it is the class of the Alexander–Whitney product `a ⌣ b`. -/
theorem mixedCupR_apply (R : Type) [CommRing R] (X : TopCat) (A : Set X) (m n : ℕ)
    (a : Cochain R (TopCat.toSSet.obj X) m) (b : relKern R X A n)
    (ha : cochainDiff R (TopCat.toSSet.obj X) a = 0) (hb : relDiffLM R X A n b = 0) :
    ∃ (hmem : cup R (TopCat.toSSet.obj X) a (b.1 : Cochain R (TopCat.toSSet.obj X) n) ∈
        relKern R X A (m + n)),
      ∃ (h : relDiffLM R X A (m + n)
            ⟨cup R (TopCat.toSSet.obj X) a (b.1 : Cochain R (TopCat.toSSet.obj X) n), hmem⟩ = 0),
        mixedCupR R X A m n (cohomologyClassOf R (TopCat.toSSet.obj X) a ha)
            (relClassOf R X A b hb) =
          relClassOf R X A
            ⟨cup R (TopCat.toSSet.obj X) a (b.1 : Cochain R (TopCat.toSSet.obj X) n), hmem⟩ h :=
  (Classical.choose_spec (mixedRelCupH (R := R) X A)) m n a b ha hb

end

end Work.Cohomology
