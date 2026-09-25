/-
Copyright: the martinet_totally_real_towers team.

# `invFun` is a two-sided inverse of `f` on the image

`CoeffSES.invFun` is the set-theoretic inverse of `f`, defined by `Classical.choose` on the
image of `f` and `0` elsewhere.  This module records the elementary consequence that
`invFun` inverts `f` on every element of the image: if `S.f a = b` then `S.invFun b = a`.
-/

import Mathlib
import Submission.Work.ConCohomology.Setup

namespace Work.ConCohomology

lemma invFun_eq_of {G : Type*} [Group G] {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
    (S : CoeffSES G A B C) {a : A} {b : B} (h : S.f a = b) : S.invFun b = a := by
  have hb : ∃ a' : A, S.f a' = b := ⟨a, h⟩
  simp only [CoeffSES.invFun_eq, hb, dite_true]
  exact S.injective_f (by rw [Classical.choose_spec hb, h])

end Work.ConCohomology
