import Mathlib
import Submission.Work.OROneRel.Basic

/-!
# The relator length of a non-trivial power

For a non-trivial element `u` of a free group `F(α)` and every `l : ℕ`, the reduced length of
`u ^ l` is at least `l`:

`l ≤ relatorNorm (u ^ l)`.

The proof is the standard cyclic-reduction argument.  Writing `w = u.toWord` for the reduced word
of `u` (which is non-empty because `u ≠ 1`), Mathlib's
`reduceCyclically.reduce_flatten_replicate_succ` gives

`toWord (u ^ (m+1)) = conjugator w ++ (reduceCyclically w)^(m+1) ++ invRev (conjugator w)`,

so that the length of `u ^ (m+1)` is `2 * |conjugator w| + (m+1) * |reduceCyclically w|`.  Since a
reduced non-empty word has non-empty cyclic reduction, the second summand is at least `m+1`, which
is the claim.

## Main declarations

* `Work.OROneRel.reduceCyclically_ne_nil_of_isReduced`: the cyclic reduction of a reduced non-empty
  word is non-empty;
* `Work.OROneRel.toWord_pow_succ_length`: the length formula for a positive power;
* `Work.OROneRel.le_relatorNorm_pow`: `l ≤ relatorNorm (u ^ l)` for `u ≠ 1`.
-/

namespace Work.OROneRel

universe u

open FreeGroup

/-- The cyclic reduction of a reduced, non-empty word is non-empty.  (Without reducedness this is
false: `reduceCyclically [x, !x] = []`.) -/
theorem reduceCyclically_ne_nil_of_isReduced {α : Type u} [DecidableEq α] {L : List (α × Bool)}
    (h : FreeGroup.IsReduced L) (hL : L ≠ []) : FreeGroup.reduceCyclically L ≠ [] := by
  induction L using List.bidirectionalRec with
  | nil => exact absurd rfl hL
  | singleton a => simp
  | cons_append a l b ih =>
    rw [FreeGroup.reduceCyclically.cons_append]
    split
    · -- the outer letters cancel, so the cyclic reduction is that of the inner word
      rename_i hc
      cases l with
      | nil =>
        -- the word would be `[a, b]` with `b = a⁻¹`, contradicting reducedness
        rw [List.nil_append] at h
        rw [FreeGroup.isReduced_cons_cons] at h
        obtain ⟨h1, -⟩ := h
        exact absurd (hc.2.trans (h1 hc.1.symm)) (by cases b.2 <;> simp)
      | cons c l' => exact ih (h.infix ⟨[a], [b], rfl⟩) (by simp)
    · simp

/-- The length of the reduced word of a positive power, in terms of the cyclic reduction of the
reduced word of the base. -/
theorem toWord_pow_succ_length {α : Type u} [DecidableEq α] (x : FreeGroup α) (n : ℕ) :
    (x ^ (n + 1)).toWord.length =
      2 * (FreeGroup.reduceCyclically.conjugator x.toWord).length
        + (n + 1) * (FreeGroup.reduceCyclically x.toWord).length := by
  rw [FreeGroup.toWord_pow,
    FreeGroup.reduceCyclically.reduce_flatten_replicate_succ FreeGroup.isReduced_toWord n]
  simp [List.length_append, FreeGroup.invRev_length, List.length_flatten, List.map_replicate,
    List.sum_replicate]
  ring

theorem le_relatorNorm_pow {α : Type u} (u : FreeGroup α) (l : ℕ) (hu : u ≠ 1) :
    l ≤ Work.OROneRel.relatorNorm (u ^ l) := by
  classical
  match l with
  | 0 => simp [Work.OROneRel.relatorNorm, FreeGroup.norm]
  | (m + 1) =>
    have hu' : u.toWord ≠ [] := by simpa [FreeGroup.toWord_eq_nil_iff] using hu
    have hrc : 1 ≤ (FreeGroup.reduceCyclically u.toWord).length :=
      List.length_pos_iff.mpr
        (reduceCyclically_ne_nil_of_isReduced FreeGroup.isReduced_toWord hu')
    have hlen := toWord_pow_succ_length u m
    simp only [Work.OROneRel.relatorNorm, FreeGroup.norm]
    rw [hlen]
    have := Nat.mul_le_mul_left (m + 1) hrc
    omega

end Work.OROneRel
