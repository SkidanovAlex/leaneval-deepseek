import Mathlib
import Submission.Work.OROneRel.npsubstDefs

namespace Work.OROneRel

/-! ### Auxiliary facts about `takeWhile`/`dropWhile` with the test `isT t` -/

theorem pbk_takeWhile_nil_of_startsNonT {β : Type*} [DecidableEq β] {t : β} {X : List (β × Bool)}
    (hX : Work.OROneRel.StartsNonT t X) : X.takeWhile (isT t) = [] := by
  cases X with
  | nil => simp
  | cons c rest =>
    exact List.takeWhile_cons_of_neg (by have h := hX c rest rfl; simp [isT, h])

theorem pbk_dropWhile_self_of_startsNonT {β : Type*} [DecidableEq β] {t : β} {X : List (β × Bool)}
    (hX : Work.OROneRel.StartsNonT t X) : X.dropWhile (isT t) = X := by
  cases X with
  | nil => simp
  | cons c rest =>
    exact List.dropWhile_cons_of_neg (by have h := hX c rest rfl; simp [isT, h])

theorem pbk_takeWhile_append_eq_left {β : Type*} [DecidableEq β] {t : β} {X Y : List (β × Bool)}
    (hX : ∀ d ∈ X, isT t d = true) (hY : Work.OROneRel.StartsNonT t Y) :
    (X ++ Y).takeWhile (isT t) = X := by
  rw [List.takeWhile_append, List.takeWhile_eq_self_iff.mpr hX, if_pos rfl,
    pbk_takeWhile_nil_of_startsNonT hY, List.append_nil]

theorem pbk_dropWhile_append_eq_right {β : Type*} [DecidableEq β] {t : β} {X Y : List (β × Bool)}
    (hX : ∀ d ∈ X, isT t d = true) (hY : Work.OROneRel.StartsNonT t Y) :
    (X ++ Y).dropWhile (isT t) = Y := by
  rw [List.dropWhile_append, List.dropWhile_eq_nil_iff.mpr hX, if_pos (by simp),
    pbk_dropWhile_self_of_startsNonT hY]

/-! ### The substitution preserves the "starts with a non-`t` letter" condition -/

theorem pbk_startsNonT_blkT {β : Type*} [DecidableEq β] {t : β} {p : ℤ} {X : List (β × Bool)}
    (hX : Work.OROneRel.StartsNonT t X) : Work.OROneRel.StartsNonT t (blkT t p X) := by
  cases X with
  | nil => exact StartsNonT.nil t
  | cons c rest =>
    have hc : c.1 ≠ t := hX c rest rfl
    rw [blkT_cons, blk_of_ne hc, List.singleton_append]
    exact StartsNonT.cons hc

/-! ### The key "peeling" step

`parseT t (c :: (X ++ Y))` for `c` a non-`t` letter, `X` a run of `t`-letters and `Y` a word starting
with a non-`t` letter is `(c, X) :: parseT t Y`.  This is the shape in which `parseT t (blkT t p L)`
appears after splitting off the block of the first letter. -/

theorem pbk_parseT_cons_append {β : Type*} [DecidableEq β] {t : β} {c : β × Bool}
    {X Y : List (β × Bool)}
    (hc : c.1 ≠ t) (hX : ∀ d ∈ X, isT t d = true) (hY : Work.OROneRel.StartsNonT t Y) :
    parseT t (c :: (X ++ Y)) = (c, X) :: parseT t Y := by
  rw [parseT_cons_of_ne hc, pbk_takeWhile_append_eq_left hX hY,
    pbk_dropWhile_append_eq_right hX hY]

/-! ### The main result -/

theorem parseT_blkT {β : Type*} [DecidableEq β] {t : β} (p : ℤ) {L : List (β × Bool)}
    (hL : Work.OROneRel.StartsNonT t L) :
    Work.OROneRel.parseT t (Work.OROneRel.blkT t p L) =
      (Work.OROneRel.parseT t L).map (fun q => (q.1, Work.OROneRel.blkT t p q.2)) := by
  have key : ∀ (n : ℕ) (L : List (β × Bool)), L.length = n → StartsNonT t L →
      parseT t (blkT t p L) = (parseT t L).map (fun q => (q.1, blkT t p q.2)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro L hlen hL
      cases L with
      | nil => simp [blkT]
      | cons c rest =>
        have hc : c.1 ≠ t := hL c rest rfl
        have hlen' : (rest.dropWhile (isT t)).length < n := by
          have h1 : (c :: rest).length = n := hlen
          simp only [List.length_cons] at h1
          have h2 := List.length_dropWhile_le (isT t) rest
          omega
        have hrest : blkT t p rest =
            blkT t p (rest.takeWhile (isT t)) ++ blkT t p (rest.dropWhile (isT t)) :=
          (congrArg (blkT t p)
            (List.takeWhile_append_dropWhile (p := isT t) (l := rest)).symm).trans
            (blkT_append p _ _)
        have hblk : blkT t p (c :: rest) =
            c :: (blkT t p (rest.takeWhile (isT t)) ++ blkT t p (rest.dropWhile (isT t))) := by
          rw [blkT_cons, blk_of_ne hc, hrest, List.singleton_append]
        have hstep : parseT t (blkT t p (c :: rest)) =
            (c, blkT t p (rest.takeWhile (isT t))) ::
              parseT t (blkT t p (rest.dropWhile (isT t))) := by
          rw [hblk]
          exact pbk_parseT_cons_append hc
            (fun d hd => (isT_eq_true_iff).mpr
              (blkT_fst_of_all_fst_eq p (startsNonT_takeWhile_all t rest) d hd))
            (pbk_startsNonT_blkT (startsNonT_dropWhile t rest))
        rw [hstep, parseT_cons_of_ne hc]
        simp only [List.map_cons]
        congr 1
        exact ih _ hlen' _ rfl (startsNonT_dropWhile t rest)
  exact key L.length L rfl hL

end Work.OROneRel
