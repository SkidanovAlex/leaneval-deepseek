import Submission.Work.NielsenAlign
import Submission.Work.NielsenPeel

open Submission.Nielsen
set_option autoImplicit false

/-!
# `|x·x| ≥ |x|`: squaring never shortens a free-group element

A free-group element's word, squared, can cancel only across the seam: the
reduced word of `x·x` is `reduce (X ++ X)` with `X := toWord x` reduced, and
the quantitative alignment identity (`NielsenAlign.reduce_append_align`) gives
`|x·x| = 2·|X| − 2·align X X`.  This module proves that this is never below
`|X|`: the self-alignment `align X X` is at most half the word
(`align_self_le_half` — a reduced word cannot match its own inverse-reverse
beyond the middle, else it would contain an adjacent inverse pair or a
self-inverse middle letter), hence

    norm_mul_self_ge : |x| ≤ |x·x|

This elementary fact is the *same-sign* degeneracy selector of the strict
phase: a strict inequality `|es[j-1] · es[j]| < |es[j-1]|` with
`es[j-1] = es[j] = ±w_p` (the two aggregate factors being the same basis
image up to sign) is impossible, so the two factor coordinates `p`, `q` of a
strictly-shortening junction pair must differ.

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`
(omega arithmetic over the alignment identity; no new axioms).
-/

namespace Commons.GroupTheory.FreeGroup

private lemma getElem_index_congr {α : Type*} {l : List α} {i j : ℕ} (h : i = j)
    (hi : i < l.length) (hj : j < l.length) : l[i]'(hi) = l[j]'(hj) := by
  subst j
  rfl

/-- Entries of the two words at a common position below the taken prefix are
equal, when the taken prefixes are equal. -/
private lemma getElem_eq_of_take_eq {α : Type*} {L M : List α} {r i : ℕ}
    (h : L.take r = M.take r) (hi : i < r) (hiL : i < L.length) (hiM : i < M.length) :
    L[i]'(hiL) = M[i]'(hiM) := by
  have hbL : i < (L.take r).length := by
    rw [List.length_take]
    exact Nat.lt_min.mpr ⟨hi, hiL⟩
  have hbM : i < (M.take r).length := by
    rw [List.length_take]
    exact Nat.lt_min.mpr ⟨hi, hiM⟩
  have hgtL : (L.take r)[i]'(hbL) = L[i]'(hiL) := by
    exact List.getElem_take (xs := L) (j := r) (i := i) (h := hbL)
  have hgtM : (M.take r)[i]'(hbM) = M[i]'(hiM) := by
    exact List.getElem_take (xs := M) (j := r) (i := i) (h := hbM)
  have hc : (L.take r)[i]'(hbL) = (M.take r)[i]'(hbM) := by
    exact List.getElem_of_eq (l := L.take r) (l' := M.take r) h hbL
  calc
    L[i]'(hiL) = (L.take r)[i]'(hbL) := hgtL.symm
    _ = (M.take r)[i]'(hbM) := hc
    _ = M[i]'(hiM) := hgtM

/-- **Self-alignment bound.**  For a reduced word `X`, aligning `X` against
itself cancels at most half of it: `2 · align X X ≤ X.length`.  (If more
than half of `X` matched its own inverse-reverse, the middle of the word
would be an adjacent inverse pair — even length — or a self-inverse middle
letter — odd length — contradicting reducedness.) -/
lemma align_self_le_half {α : Type*} [DecidableEq α] (X : List (α × Bool))
    (hred : FreeGroup.IsReduced X) : align X X * 2 ≤ X.length := by
  by_contra h
  have hgt : X.length < 2 * align X X := by omega
  let A : List (α × Bool) := X.reverse.map letterInv
  have htake : A.take (align X X) = X.take (align X X) := by
    have hc : align X X ≤ commonPrefixLen A X := by
      dsimp [A]
      unfold align
      exact le_rfl
    exact (commonPrefixLen_ge_iff_take A X (align X X) (align_le_length_right X X)).mp hc
  have hrmid : X.length / 2 < align X X := by omega
  have hlenA : A.length = X.length := by
    dsimp [A]
    rw [List.length_map, List.length_reverse]
  rcases Nat.mod_two_eq_zero_or_one X.length with hmod | hmod
  · -- even: X.length = 2m, m := X.length/2 ≥ 1; positions m-1, m adjacent
    let m : ℕ := X.length / 2
    have hm : X.length = 2 * m := by unfold m; omega
    have hmpos : 0 < m := by
      by_contra hn
      have hm0 : m = 0 := by exact Nat.eq_zero_of_not_pos hn
      have hzero : X.length = 0 := by omega
      have hXnil : X = [] := (List.eq_nil_iff_length_eq_zero).mpr hzero
      subst X
      simp [align, commonPrefixLen] at hgt
    have hmltX : m < X.length := by unfold m; omega
    have hmltA : m < A.length := by rw [hlenA]; exact hmltX
    have hmltm1X : m - 1 < X.length := by omega
    have hAm : A[m]'(hmltA) = X[m]'(hmltX) :=
      getElem_eq_of_take_eq htake hrmid hmltA hmltX
    have hrevb : m < X.reverse.length := by rw [List.length_reverse]; exact hmltX
    have hmapm : A[m]'(hmltA) = letterInv (X.reverse[m]'(hrevb)) := by
      exact List.getElem_map letterInv (l := X.reverse) (i := m) (h := hmltA)
    have h2 : X.length - 1 - m < X.length := by omega
    have hrev : X.reverse[m]'(hrevb) = X[X.length - 1 - m]'(h2) := by
      exact List.getElem_reverse (l := X) (i := m) (h := hrevb)
    have hcong : X[X.length - 1 - m]'(h2) = X[m - 1]'(hmltm1X) := by
      exact getElem_index_congr (l := X) (i := X.length - 1 - m) (j := m - 1)
        (by omega) h2 hmltm1X
    have htarget : letterInv (X[m - 1]'(hmltm1X)) = X[m]'(hmltX) := by
      calc
        letterInv (X[m - 1]'(hmltm1X))
            = letterInv (X[X.length - 1 - m]'(h2)) := by exact congrArg letterInv hcong.symm
        _ = letterInv (X.reverse[m]'(hrevb)) := by exact congrArg letterInv hrev.symm
        _ = A[m]'(hmltA) := hmapm.symm
        _ = X[m]'(hmltX) := hAm
    have hi : (m - 1) + 1 < X.length := by omega
    have hR0 : (fun a b : α × Bool => a.1 = b.1 → a.2 = b.2) (X[m - 1]'(hmltm1X)) (X[(m - 1) + 1]'(hi)) :=
      List.IsChain.getElem (l := X) hred (m - 1) hi
    have hcongm : X[(m - 1) + 1]'(hi) = X[m]'(hmltX) := by
      exact getElem_index_congr (l := X) (i := (m - 1) + 1) (j := m) (by omega) hi hmltX
    have hR : (fun a b : α × Bool => a.1 = b.1 → a.2 = b.2) (X[m - 1]'(hmltm1X)) (X[m]'(hmltX)) := by
      simpa [hcongm] using hR0
    have hfirst : (X[m - 1]'(hmltm1X)).1 = (X[m]'(hmltX)).1 := by
      have hf := congrArg Prod.fst htarget
      simpa [letterInv] using hf
    have hsecond : ¬ (X[m - 1]'(hmltm1X)).2 = (X[m]'(hmltX)).2 := by
      intro hs
      have hf := congrArg Prod.snd htarget
      rw [← hs] at hf
      cases (X[m - 1]'(hmltm1X)).2 with
      | true => simp [letterInv] at hf
      | false => simp [letterInv] at hf
    exact hsecond (hR hfirst)
  · -- odd: X.length = 2m+1, m := X.length/2; position m is the centre
    let m : ℕ := X.length / 2
    have hm : X.length = 2 * m + 1 := by unfold m; omega
    have hmltX : m < X.length := by unfold m; omega
    have hmltA : m < A.length := by rw [hlenA]; exact hmltX
    have hAm : A[m]'(hmltA) = X[m]'(hmltX) :=
      getElem_eq_of_take_eq htake hrmid hmltA hmltX
    have hrevb : m < X.reverse.length := by rw [List.length_reverse]; exact hmltX
    have hmapm : A[m]'(hmltA) = letterInv (X.reverse[m]'(hrevb)) := by
      exact List.getElem_map letterInv (l := X.reverse) (i := m) (h := hmltA)
    have h2 : X.length - 1 - m < X.length := by omega
    have hrev : X.reverse[m]'(hrevb) = X[X.length - 1 - m]'(h2) := by
      exact List.getElem_reverse (l := X) (i := m) (h := hrevb)
    have hcong : X[X.length - 1 - m]'(h2) = X[m]'(hmltX) := by
      exact getElem_index_congr (l := X) (i := X.length - 1 - m) (j := m)
        (by omega) h2 hmltX
    have htarget : letterInv (X[m]'(hmltX)) = X[m]'(hmltX) := by
      calc
        letterInv (X[m]'(hmltX))
            = letterInv (X[X.length - 1 - m]'(h2)) := by exact congrArg letterInv hcong.symm
        _ = letterInv (X.reverse[m]'(hrevb)) := by exact congrArg letterInv hrev.symm
        _ = A[m]'(hmltA) := hmapm.symm
        _ = X[m]'(hmltX) := hAm
    exact (letterInv_ne_self (X[m]'(hmltX))) htarget

/-- **Squaring never shortens.**  For every element of a free group,
`|x| ≤ |x·x|` (the reduced word of `x·x` is the two copies of the reduced
word of `x` with at most half of the second copy cancelling against the tail
of the first). -/
theorem norm_mul_self_ge {α : Type*} [DecidableEq α] (x : FreeGroup α) :
    FreeGroup.norm x ≤ FreeGroup.norm (x * x) := by
  have hx : FreeGroup.norm x = (FreeGroup.toWord x).length := rfl
  have hxx : FreeGroup.norm (x * x) =
      (FreeGroup.reduce (FreeGroup.toWord x ++ FreeGroup.toWord x)).length := by
    unfold FreeGroup.norm
    rw [FreeGroup.toWord_mul]
  have hid := reduce_append_align (FreeGroup.toWord x) (FreeGroup.toWord x)
    (FreeGroup.isReduced_toWord) (FreeGroup.isReduced_toWord)
  have hself := align_self_le_half (FreeGroup.toWord x) FreeGroup.isReduced_toWord
  rw [hx, hxx, hid]
  omega

end Commons.GroupTheory.FreeGroup
