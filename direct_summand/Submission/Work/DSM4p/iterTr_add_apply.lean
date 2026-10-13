import Mathlib
import Submission.Work.DSM4p.Basic

namespace Work.DSM4p

open DSMap DSMap.Mix

universe a

/-- Transport-compatibility of the transition maps: transporting the result of `tr b` along
`h : b = a` is the same as applying `tr a` to the transported argument.  This is the
"coherence" of the tower transitions with respect to the `Nat.add` re-associations that make
the index `n + c + d` of `D` unambiguous; it is proved by `cases h` (any dependent function is
automatically a section for the transport). -/
private lemma tr_eqRec_apply {B : Type a} [CommRing B] {D : ℕ → Type a}
    [∀ n, CommRing (D n)] [∀ n, Algebra B (D n)] (tr : ∀ n, D (n + 1) →ₐ[B] D n)
    {b a : ℕ} (h : b = a) (y : D (b + 1)) :
    tr a (congrArg (fun k => k + 1) h ▸ y) = h ▸ tr b y := by
  cases h
  rfl

theorem iterTr_add_apply {B : Type a} [CommRing B] {D : ℕ → Type a} [∀ n, CommRing (D n)]
    [∀ n, Algebra B (D n)] (tr : ∀ n, D (n + 1) →ₐ[B] D n) (n c d : ℕ) (y : D ((n + c) + d)) :
    DSMap.Mix.iterTr tr n (c + d) ((Nat.add_assoc n c d) ▸ y) =
      DSMap.Mix.iterTr tr n c (DSMap.Mix.iterTr tr (n + c) d y) := by
  induction d with
  | zero =>
      rw [iterTr_zero_apply]
      change (iterTr tr n c) ((Nat.add_assoc n c 0) ▸ y) = (iterTr tr n c) y
      rw [show Nat.add_assoc n c 0 = (rfl : ((n + c) + 0) = (n + (c + 0))) from
        Subsingleton.elim _ _]
  | succ d ih =>
      rw [iterTr_succ_apply]
      change (iterTr tr n (c + d + 1)) ((Nat.add_assoc n c (d + 1)) ▸ y) =
        (iterTr tr n c) ((iterTr tr (n + c) d) (tr (n + c + d) y))
      rw [iterTr_succ_apply]
      rw [← ih (tr (n + c + d) y)]
      refine congrArg (iterTr tr n (c + d)) ?_
      convert tr_eqRec_apply tr (Nat.add_assoc n c d) y using 2

end Work.DSM4p
