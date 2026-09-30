import Mathlib
import Submission.Work.Cohomology.mixedRelCupH
import Submission.Work.Cohomology.RelCupTransfer
import Submission.Work.Cohomology.RelCup

/-!
# The mixed cup product (absolute x relative) for the pair `(S³ × D⁴, S³ × S³)`

`Submission/Work/Cohomology/mixedRelCupH.lean` proves the existence of the mixed cup product

  `H^m(X) × H^n(X,A) ⟶ H^{m+n}(X,A)`

(the module structure of the relative cohomology over the absolute one) as an unexplicit `∃`.
This file pins that pairing once and for all (`mixedCup`), in the style of
`Submission/Work/Cohomology/RelCupTransfer.lean`, and records its computation rule on the classes
of cocycles.
-/

namespace Work.Cohomology

noncomputable section

/-- **The mixed cup product** `H^m(X) × H^n(X,A) ⟶ H^{m+n}(X,A)`, a choice of the pairing whose
existence is `Work.Cohomology.mixedRelCupH`. -/
noncomputable def mixedCup (X : TopCat) (A : Set X) (m n : ℕ) :=
  (Classical.choose (mixedRelCupH (R := ℤ) X A)) m n

/-- **The computation rule for `mixedCup`**: on the classes of an absolute cocycle `a` and a
relative cocycle `b` it is the class of the Alexander–Whitney product `a ⌣ b` (which is
automatically relative). -/
theorem mixedCup_apply (X : TopCat) (A : Set X) (m n : ℕ)
    (a : Cochain ℤ (TopCat.toSSet.obj X) m) (b : relKern ℤ X A n)
    (ha : cochainDiff ℤ (TopCat.toSSet.obj X) a = 0) (hb : relDiffLM ℤ X A n b = 0) :
    ∃ (hmem : cup ℤ (TopCat.toSSet.obj X) a (b.1 : Cochain ℤ (TopCat.toSSet.obj X) n) ∈
        relKern ℤ X A (m + n)),
      ∃ (h : relDiffLM ℤ X A (m + n)
            ⟨cup ℤ (TopCat.toSSet.obj X) a (b.1 : Cochain ℤ (TopCat.toSSet.obj X) n), hmem⟩ = 0),
        mixedCup X A m n (cohomologyClassOf ℤ (TopCat.toSSet.obj X) a ha)
            (relClassOf ℤ X A b hb) =
          relClassOf ℤ X A
            ⟨cup ℤ (TopCat.toSSet.obj X) a (b.1 : Cochain ℤ (TopCat.toSSet.obj X) n), hmem⟩ h :=
  (Classical.choose_spec (mixedRelCupH (R := ℤ) X A)) m n a b ha hb

end

end Work.Cohomology
