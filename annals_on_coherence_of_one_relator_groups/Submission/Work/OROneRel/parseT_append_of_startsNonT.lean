import Mathlib
import Submission.Work.OROneRel.npsubstDefs

namespace Work.OROneRel

/-! ### Appending a word that starts with a non-`t` letter

The run decomposition `parseT t` is compatible with concatenation on the right, provided the
appended word starts with a letter different from `t` (or is empty).  The only obstruction is the
merging of a trailing `t`-run: if `B` started with `t`, the last run of `A` would absorb the leading
`t`-letters of `B`. -/

private theorem startsNonT_takeWhile_isT_eq_nil {β : Type*} [DecidableEq β] {t : β}
    {B : List (β × Bool)} (hB : StartsNonT t B) : B.takeWhile (isT t) = [] := by
  rcases startsNonT_iff.mp hB with rfl | ⟨c, rest, rfl, hc⟩
  · simp
  · simp [isT, hc]

private theorem startsNonT_dropWhile_isT_eq_self {β : Type*} [DecidableEq β] {t : β}
    {B : List (β × Bool)} (hB : StartsNonT t B) : B.dropWhile (isT t) = B := by
  rcases startsNonT_iff.mp hB with rfl | ⟨c, rest, rfl, hc⟩
  · simp
  · simp [isT, hc]

private theorem takeWhile_isT_append_of_startsNonT {β : Type*} [DecidableEq β] {t : β}
    {L B : List (β × Bool)} (hB : StartsNonT t B) :
    (L ++ B).takeWhile (isT t) = L.takeWhile (isT t) := by
  rw [List.takeWhile_append]
  by_cases h : (L.takeWhile (isT t)).length = L.length
  · rw [if_pos h, startsNonT_takeWhile_isT_eq_nil hB, List.append_nil]
    exact ((List.takeWhile_prefix (isT t)).eq_of_length h).symm
  · rw [if_neg h]

private theorem dropWhile_isT_append_of_startsNonT {β : Type*} [DecidableEq β] {t : β}
    {L B : List (β × Bool)} (hB : StartsNonT t B) :
    (L ++ B).dropWhile (isT t) = L.dropWhile (isT t) ++ B := by
  rw [List.dropWhile_append]
  by_cases h : (L.dropWhile (isT t)).isEmpty = true
  · rw [if_pos h, startsNonT_dropWhile_isT_eq_self hB, List.isEmpty_iff.mp h, List.nil_append]
  · rw [if_neg h]

theorem parseT_append_of_startsNonT {β : Type*} [DecidableEq β] {t : β} {A B : List (β × Bool)}
    (hB : Work.OROneRel.StartsNonT t B) :
    Work.OROneRel.parseT t (A ++ B) = Work.OROneRel.parseT t A ++ Work.OROneRel.parseT t B := by
  have key : ∀ A : List (β × Bool),
      (∀ B : List (β × Bool), StartsNonT t B →
          parseT t (A ++ B) = parseT t A ++ parseT t B) ∧
      (∀ B : List (β × Bool), StartsNonT t B →
          parseT t (A.dropWhile (isT t) ++ B) =
            parseT t (A.dropWhile (isT t)) ++ parseT t B) := by
    intro A
    induction A with
    | nil =>
      constructor
      · intro B hB; simp
      · intro B hB; simp
    | cons c rest ih =>
      obtain ⟨ihT, ihU⟩ := ih
      have hTc : ∀ B : List (β × Bool), StartsNonT t B →
          parseT t ((c :: rest) ++ B) = parseT t (c :: rest) ++ parseT t B := by
        intro B hB
        by_cases hc : c.1 = t
        · rw [List.cons_append, parseT_cons_of_eq hc, parseT_cons_of_eq hc]
          exact ihT B hB
        · rw [List.cons_append, parseT_cons_of_ne hc, parseT_cons_of_ne hc,
            takeWhile_isT_append_of_startsNonT hB, dropWhile_isT_append_of_startsNonT hB,
            List.cons_append]
          rw [ihU B hB]
      constructor
      · exact hTc
      · intro B hB
        by_cases hc : c.1 = t
        · rw [List.dropWhile_cons_of_pos (p := isT t) (a := c) (l := rest) (by simp [isT, hc])]
          exact ihU B hB
        · rw [List.dropWhile_cons_of_neg (p := isT t) (a := c) (l := rest) (by simp [isT, hc])]
          exact hTc B hB
  exact (key A).1 B hB

end Work.OROneRel
