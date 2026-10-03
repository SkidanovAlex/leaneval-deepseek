import Mathlib
import Submission.Work.OROneRel.ntDefs
import Submission.Work.OROneRel.Basic

/-!
# A letter of a relator is not counted by `nt`

For a relator `r` on the generators `α` (whose reduced word is `r.toWord`) and a generator `t`
occurring in `r`, the number `nt t r.toWord` of letters of `r.toWord` different from `t` is
strictly smaller than the length `relatorNorm r = r.toWord.length` of the relator: at least one
letter of `r.toWord` has underlying generator `t`, and that letter is not counted by `nt`.

No hypothesis of reducedness or cyclical reduction is needed: `nt` only sees the letters of the
word, not the group element it represents.
-/

namespace Work.OROneRel

universe u

/-- `FreeGroup.toWord` does not depend on which `DecidableEq` instance is used.  This lets one pass
between the `DecidableEq` instance supplied by `Classical.decEq` (which the definitions
`relatorLetters`, `relatorNorm` and `IsCyclicallyReducedRelator` use internally) and a local
instance. -/
private theorem toWord_decEq_congr {α : Type u} (i j : DecidableEq α) (x : FreeGroup α) :
    @FreeGroup.toWord α i x = @FreeGroup.toWord α j x := by
  have h : i = j := Subsingleton.elim i j
  rw [h]

/-- If a word contains a letter with underlying generator `t`, then strictly fewer of its letters
are different from `t` than it has letters in total. -/
private theorem nt_lt_length_of_mem {α : Type u} {t : α} {b : Bool} {L : List (α × Bool)}
    (h : (t, b) ∈ L) : nt t L < L.length := by
  rw [nt_eq_countP]
  exact List.countP_lt_length_iff.mpr ⟨(t, b), h, by simp⟩

/-- The target statement with the `DecidableEq` instance appearing in `toWord` fixed to be the
classical one, which is the instance used internally by `relatorLetters` and `relatorNorm`. -/
private theorem nt_lt_relatorNorm_classical {α : Type u} (t : α) (r : FreeGroup α)
    (ht : t ∈ relatorLetters r) :
    nt t (@FreeGroup.toWord α (Classical.decEq α) r) < relatorNorm r := by
  classical
  -- `ht` says that the reduced word of `r` contains a letter with generator `t`.
  obtain ⟨b, hb⟩ : ∃ b : Bool, (t, b) ∈ @FreeGroup.toWord α (Classical.decEq α) r := by
    simpa [relatorLetters] using ht
  rw [relatorNorm, FreeGroup.norm]
  exact nt_lt_length_of_mem hb

theorem nt_lt_relatorNorm {α : Type u} [DecidableEq α] {t : α} {r : FreeGroup α} (ht : t ∈ relatorLetters r) :
    nt t r.toWord < relatorNorm r := by
  -- Replace the `toWord` occurring in the goal by the classical-instance one.
  rw [toWord_decEq_congr (j := Classical.decEq α)]
  exact nt_lt_relatorNorm_classical t r ht

end Work.OROneRel
