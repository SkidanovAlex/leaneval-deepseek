import Mathlib
import Submission.Work.ORLyndon.foxWord_occurrences
import Submission.Work.ORLyndon.annAtDefs
import Submission.Work.OROneRel.wordOfDefs

/-!
# The root Fox vector as a sum over occurrences of a letter

The Fox vector of the *root* `u` pushed into `K[G]`, `G = ⟨X | r⟩`, is
`(rootVec K r u) x = presentAlg K r (∂u/∂x)`.  Combining the occurrence expansion of the Fox
derivative of a *word* (`Work.ORLyndon.foxWord_occurrences`, applied to the reduced word
`Work.OROneRel.wordOf u` of `u`) with the fact that `presentAlg` is a ring homomorphism carrying
`MonoidAlgebra.of K (FreeGroup X) w` to `MonoidAlgebra.of K (OneRelatorGroup r) (presentRho r w)`
gives the same expansion with every prefix element pushed into the group algebra of `G`:

`(rootVec K r u) x = ∑ i, (if (wordOf u).get i = (x,true) then of (presentRho (take i))
                                else if (wordOf u).get i = (x,false) then - of (presentRho (take (i+1)))
                                else 0)`.

This is the shape in which the occurrence expansion is consumed by the coefficient computations of
the Cohen--Lyndon induction (`Work.ORLyndon.ann_rootVec_of_level`,
`Work.ORLyndon.levelPart_rootVec_eq_base`, ...).
-/

set_option autoImplicit false

namespace Work.ORLyndon

open MonoidAlgebra

/-- The Fox derivative `∂u/∂x` of a group element is the Fox derivative of its reduced word. -/
theorem foxD_eq_foxWord_wordOf {X : Type*} [DecidableEq X] {K : Type*} [Field K] (x : X)
    (u : FreeGroup X) :
    foxD (K := K) x u = foxWord (K := K) x (Work.OROneRel.wordOf u) := by
  conv_lhs => rw [← Work.OROneRel.mk_wordOf u]
  rw [foxD_mk]

/-- The algebra map `presentAlg` carries the `i`-th summand of the occurrence expansion of the Fox
derivative of a word to the corresponding summand for the presented group: the prefix group element
`FreeGroup.mk (take i)` becomes `presentRho r (FreeGroup.mk (take i))`, while the three cases
(`(x,true)`, `(x,false)`, neither) are preserved because `presentAlg` is a ring homomorphism. -/
theorem presentAlg_occSummand {X : Type*} [DecidableEq X] {K : Type*} [Field K]
    (r : FreeGroup X) (x : X) (L : List (X × Bool)) (i : Fin L.length) :
    presentAlg K r
        (if L.get i = (x, true) then
            MonoidAlgebra.of K (FreeGroup X) (FreeGroup.mk (L.take i.1))
          else if L.get i = (x, false) then
            - MonoidAlgebra.of K (FreeGroup X) (FreeGroup.mk (L.take (i.1 + 1)))
          else 0) =
      (if L.get i = (x, true) then
          MonoidAlgebra.of K (OneRelatorGroup r) (presentRho r (FreeGroup.mk (L.take i.1)))
        else if L.get i = (x, false) then
          - MonoidAlgebra.of K (OneRelatorGroup r)
              (presentRho r (FreeGroup.mk (L.take (i.1 + 1))))
        else 0) := by
  split_ifs with h1 h2
  · rw [presentAlg_of]
  · rw [map_neg, presentAlg_of]
  · rfl

theorem rootVec_occurrences {K : Type*} [Field K] {α : Type*} [DecidableEq α]
    (r u : FreeGroup α) (x : α) :
    rootVec K r u x =
      ∑ i : Fin (Work.OROneRel.wordOf u).length,
        (if (Work.OROneRel.wordOf u).get i = (x, true) then
            MonoidAlgebra.of K (OneRelatorGroup r)
              (presentRho r (FreeGroup.mk ((Work.OROneRel.wordOf u).take i.1)))
          else if (Work.OROneRel.wordOf u).get i = (x, false) then
            - MonoidAlgebra.of K (OneRelatorGroup r)
              (presentRho r (FreeGroup.mk ((Work.OROneRel.wordOf u).take (i.1 + 1))))
          else 0) := by
  rw [rootVec_apply, foxD_eq_foxWord_wordOf, foxWord_occurrences, map_sum]
  exact Finset.sum_congr rfl fun i _ => presentAlg_occSummand r x _ i

end Work.ORLyndon
