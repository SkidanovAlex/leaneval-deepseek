/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

The norm of the Magnus rewriting `magRewRel t w` of a cyclically reduced relator `w` is invariant
under cyclic rotation of the underlying word.

The point is that `magRewRel t w = mk (rewrite t w.toWord)` and that for a *reduced* word `W` the
norm of `mk (rewrite t W)` is just `(rewrite t W).length`: the Magnus rewriting of a reduced word is
again reduced (`Work.OROneRel.rewrite_isReduced`), and a rotation of a cyclically reduced word is
reduced.  The length of the rewriting is the number of letters different from `t`, which a rotation
obviously preserves.

* `relatorNorm_magRewRel_mk_of_isReduced` -- `relatorNorm (magRewRel t (mk W)) = (rewrite t W).length`
  for reduced `W`;
* `isReduced_rotate_of_cyc` -- a rotation of a cyclically reduced word is reduced;
* `rewrite_rotate_length` -- `rewrite t` preserves the length of a word under rotation.
-/
import Mathlib
import Submission.Work.OROneRel.HNNStep
import Submission.Work.OROneRel.rewrite_isReduced

namespace Work.OROneRel

universe u

/-- For a *reduced* word `W`, the norm of `magRewRel t (mk W)` is the length of the Magnus
rewriting `rewrite t W` (which is reduced, so it computes the norm of `mk (rewrite t W)`).

The `DecidableEq` instances are written out explicitly because `relatorNorm` unfolds to
`FreeGroup.norm` at the type `{a // a ≠ t} × ℤ` using `Classical.decEq`; writing them by hand keeps
the `rewrite` steps on the nose. -/
private lemma relatorNorm_magRewRel_mk_of_isReduced {α : Type u} (t : α) {W : List (α × Bool)}
    (hW : FreeGroup.IsReduced W) :
    relatorNorm (magRewRel t (FreeGroup.mk W)) = (rewrite t W).length := by
  classical
  unfold relatorNorm magRewRel
  have h1 : @FreeGroup.toWord α (fun a b => Classical.propDecidable (a = b)) (FreeGroup.mk W) = W := by
    rw [FreeGroup.toWord_mk, hW.reduce_eq]
  rw [h1]
  show (@FreeGroup.reduce ({a : α // a ≠ t} × ℤ) (fun a b => Classical.propDecidable (a = b))
      (rewrite t W)).length = (rewrite t W).length
  exact congrArg List.length
    (@FreeGroup.IsReduced.reduce_eq ({a : α // a ≠ t} × ℤ) (rewrite t W)
      (fun a b => Classical.propDecidable (a = b)) (rewrite_isReduced t hW))

/-- A rotation of a cyclically reduced word is reduced.  Indeed `L ++ L` is cyclically reduced
(hence reduced, `FreeGroup.IsCyclicallyReduced.flatten_replicate`), and `L.rotate k`, being
`L.drop m ++ L.take m` with `m = k % L.length`, is a contiguous block of `L ++ L`. -/
private lemma isReduced_rotate_of_cyc {α : Type u} {L : List (α × Bool)}
    (h : FreeGroup.IsCyclicallyReduced L) (k : ℕ) : FreeGroup.IsReduced (L.rotate k) := by
  have hLL : FreeGroup.IsReduced (L ++ L) := by
    have h' := h.flatten_replicate 2
    rw [show (List.replicate 2 L).flatten = L ++ L by simp] at h'
    exact h'.isReduced
  rw [List.rotate_eq_drop_append_take_mod]
  refine hLL.infix ⟨L.take (k % L.length), L.drop (k % L.length), ?_⟩
  calc (L.take (k % L.length) ++ (L.drop (k % L.length) ++ L.take (k % L.length)))
          ++ L.drop (k % L.length)
      = (L.take (k % L.length) ++ L.drop (k % L.length)) ++
        (L.take (k % L.length) ++ L.drop (k % L.length)) := by simp only [List.append_assoc]
    _ = L ++ L := by rw [List.take_append_drop]

/-- The length of the Magnus rewriting is the number of letters different from `t`, computed with
any starting exponent sum `i`. -/
private lemma rewriteAux_length {α : Type u} [DecidableEq α] (t : α) (i : ℤ)
    (L : List (α × Bool)) :
    (rewriteAux t i L).length = (L.filter (fun p => decide (p.1 ≠ t))).length := by
  induction L generalizing i with
  | nil => rw [rewriteAux_nil]; simp
  | cons p L ih =>
    by_cases hp : p.1 = t
    · rw [rewriteAux_cons_of_eq t i L hp, ih, List.filter_cons_of_neg (by simp [hp])]
    · rw [rewriteAux_cons_of_ne t i L hp, List.length_cons, ih,
        List.filter_cons_of_pos (by simp [hp]), List.length_cons]

/-- The length of the Magnus rewriting `rewrite t` is invariant under rotation: both `W` and
`W.rotate k` have the same set of letters (as a multiset), hence the same number of letters
different from `t`. -/
private lemma rewrite_rotate_length {α : Type u} [DecidableEq α] (t : α) (L : List (α × Bool))
    (k : ℕ) : (rewrite t (L.rotate k)).length = (rewrite t L).length := by
  rw [rewrite, rewrite, rewriteAux_length, rewriteAux_length]
  exact (List.Perm.filter _ (List.rotate_perm L k)).length_eq

theorem relatorNorm_magRewRel_rotate {α : Type u} (t : α) {L : List (α × Bool)}
    (hcyc : FreeGroup.IsCyclicallyReduced L) (k : ℕ) :
    Work.OROneRel.relatorNorm (Work.OROneRel.magRewRel t (FreeGroup.mk (L.rotate k))) =
      Work.OROneRel.relatorNorm (Work.OROneRel.magRewRel t (FreeGroup.mk L)) := by
  classical
  rw [relatorNorm_magRewRel_mk_of_isReduced t (isReduced_rotate_of_cyc hcyc k),
      relatorNorm_magRewRel_mk_of_isReduced t hcyc.1,
      rewrite_rotate_length t L k]

end Work.OROneRel
