/-
# The occurrence terms of the Fox expansion are pairwise distinct — import-hygiene version

`Work.ORLyndon.occTerm_distinct_clean`: for a cyclically reduced relator `u` which is not a proper
power, and a letter `x`, the classes in `⟨α | u⟩` of the occurrence prefixes of `∂u/∂x` are pairwise
distinct.

The mathematics is the same as in `Work.ORLyndon.occTerm_distinct`
(`Submission/Work/ORLyndon/occTerm_distinct.lean`): a reduction to **Weinbaum's theorem** — a
nontrivial subword `v` of a power of `u` with `relatorNorm v < relatorNorm u` is nontrivial in
`⟨α | u⟩` — applied to the block of `wordOf u` between two distinct occurrences of `x^{±1}`.

What is *new* here is only the import hygiene, which is why this file exists at all.  The original
`Submission/Work/ORLyndon/occTerm_distinct.lean` imports `Submission.Work.OROneRel.weinbaum_at`,
whose dependency `Submission.Work.OROneRel.mrslAux` *redeclares* the public theorem
`Work.OROneRel.toWord_pow_of_isCyclicallyReduced`, which is already declared by
`Submission.Work.OROneRel.magnus_step_root`; the latter lies in the import cone of
`Submission.Work.ORLyndon.epsNeZeroDescent` (`… → magnus_step_root`).  Any module importing both
cones therefore fails with

`import …mrslAux failed, environment already contains
'Work.OROneRel.toWord_pow_of_isCyclicallyReduced' from …magnus_step_root`,

and in particular the `annChain` cone cannot use `occTerm_distinct` — which is exactly the
"distinctness of the support" input that the leading-term arguments for `annAt` need.

The resolution used here is the one already applied in this chapter (`foxD_zeta_of_ne_clean.lean`,
`relatorLetters_pow_clean.lean`): the eight Weinbaum-chain modules above the offending declaration
are copied verbatim into the fresh nested namespace `Work.OROneRel.WBClean` (see
`Submission/Work/ORLyndon/WBClean/`), with the single duplicated declaration renamed to
`Work.OROneRel.WBClean.toWord_pow_of_isCyclicallyReduced_wbc`.  The copies keep the namespace
`Work.OROneRel` *nested inside* a fresh subnamespace, so every unqualified reference inside them
still resolves through the parent namespace to the untouched `Work.OROneRel` development, and only
the imports among the eight copied modules had to be redirected.  Consequently the present module may
import `Submission.Work.ORLyndon.epsNeZeroDescent` *and* Weinbaum's theorem simultaneously, so that
it can be imported from inside the `annChain` cone.

Both the copies (`Submission/Work/ORLyndon/WBClean/*.lean`) and this file can be deleted as soon as
the duplicate declaration `Work.OROneRel.toWord_pow_of_isCyclicallyReduced` is removed from one of
its two homes `mrslAux` / `magnus_step_root`.

## Main declaration

* `Work.ORLyndon.occTerm_distinct_clean`
-/
import Mathlib
import Submission.Work.ORLyndon.epsNeZeroDescent
import Submission.Work.ORLyndon.occDefs
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.Subword
import Submission.Work.OROneRel.wordOfDefs
import Submission.Work.ORLyndon.WBClean.weinbaum_at

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u

namespace Work.ORLyndon

namespace WB

variable {α : Type u} [DecidableEq α]

/-! ## The bridge between `wordOf` (the `Classical` instance) and the ambient `toWord` -/

theorem wordOf_eq_toWord (u : FreeGroup α) : Work.OROneRel.wordOf u = FreeGroup.toWord u := by
  rw [show Work.OROneRel.wordOf u = @FreeGroup.toWord α (Classical.decEq α) u from rfl]
  rw [Subsingleton.elim (Classical.decEq α) ‹DecidableEq α›]

/-- `toWord` at the `Classical` instance agrees with `toWord` at the ambient instance. -/
theorem classicalToWord_eq (w : FreeGroup α) :
    @FreeGroup.toWord α (Classical.decEq α) w = FreeGroup.toWord w := by
  rw [Subsingleton.elim (Classical.decEq α) ‹DecidableEq α›]

/-- `toWord` of a reduced word, at the `Classical` instance. -/
theorem toWord_mk_of_reduced {M : List (α × Bool)} (hM : FreeGroup.IsReduced M) :
    @FreeGroup.toWord α (Classical.decEq α) (FreeGroup.mk M) = M := by
  rw [classicalToWord_eq, FreeGroup.toWord_mk, FreeGroup.IsReduced.reduce_eq hM]

/-- `toWord` of the trivial element, at the `Classical` instance. -/
theorem classicalToWord_one : @FreeGroup.toWord α (Classical.decEq α) (1 : FreeGroup α) = [] := by
  rw [classicalToWord_eq, FreeGroup.toWord_one]

/-! ## The prefix length attached to an occurrence -/

/-- The length of the prefix of `L` attached to the position `i` in the Fox expansion of `∂·/∂x`:
`L` cut just *before* the `i`-th letter when that letter is `x`, and just *after* it when the letter
is `x⁻¹`. -/
noncomputable def occLen (x : α) (L : List (α × Bool)) (i : Fin L.length) : ℕ :=
  i.1 + if L.get i = (x, true) then 0 else 1

theorem occTerm_eq_take_occLen (x : α) (L : List (α × Bool)) (i : Fin L.length) :
    occTerm x L i = FreeGroup.mk (L.take (occLen x L i)) := rfl

theorem occLen_of_pos {x : α} {L : List (α × Bool)} {i : Fin L.length} (h : L.get i = (x, true)) :
    occLen x L i = i.1 := by
  unfold occLen; rw [if_pos h, add_zero]

theorem occLen_of_ne_pos {x : α} {L : List (α × Bool)} {i : Fin L.length}
    (h : ¬ L.get i = (x, true)) : occLen x L i = i.1 + 1 := by
  unfold occLen; rw [if_neg h]

theorem occLen_le (x : α) (L : List (α × Bool)) (i : Fin L.length) : occLen x L i ≤ L.length := by
  rw [occLen]; split_ifs <;> omega

/-- The prefix length vanishes only at a positive occurrence of `x` in the very first position. -/
theorem occLen_eq_zero {x : α} {L : List (α × Bool)} {i : Fin L.length}
    (h : occLen x L i = 0) : L.get i = (x, true) := by
  by_contra h'
  rw [occLen_of_ne_pos h'] at h
  omega

/-- The prefix length equals the length of the word only at a negative occurrence of `x` in the very
last position. -/
theorem occLen_eq_length {x : α} {L : List (α × Bool)} {i : Fin L.length}
    (hi : occSign x L i ≠ 0) (h : occLen x L i = L.length) :
    L.get i = (x, false) ∧ i.1 + 1 = L.length := by
  by_cases h' : L.get i = (x, true)
  · rw [occLen_of_pos h'] at h; omega
  · refine ⟨?_, ?_⟩
    · rcases (occSign_ne_zero_iff x L i).mp hi with h'' | h''
      · exact absurd h'' h'
      · exact h''
    · rw [occLen_of_ne_pos h'] at h; omega

/-! ## Two consecutive letters of a reduced word are not mutually inverse -/

theorem not_isReduced_of_adjacent {L : List (α × Bool)} {k : ℕ} {y : α} {b : Bool}
    (h₁ : L[k]? = some (y, b)) (h₂ : L[k + 1]? = some (y, !b)) : ¬ FreeGroup.IsReduced L := by
  revert h₁ h₂
  induction L generalizing k with
  | nil => intro h₁; simp at h₁
  | cons c L ih =>
    intro h₁ h₂
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h₁
      subst h₁
      rw [List.getElem?_cons_succ] at h₂
      cases L with
      | nil => simp at h₂
      | cons d L =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h₂
        subst h₂
        intro hred
        have hrel : (y, b).1 = (y, !b).1 → (y, b).2 = (y, !b).2 := hred.rel
        exact absurd (hrel rfl) (by cases b <;> simp)
    | succ k =>
      simp only [List.getElem?_cons_succ] at h₁ h₂
      intro hred
      exact ih h₁ h₂ hred.tail

/-! ## Injectivity of the prefix length on occurrences -/

theorem occLen_ne {L : List (α × Bool)} (hred : FreeGroup.IsReduced L) {x : α}
    {i j : Fin L.length} (hi : occSign x L i ≠ 0) (hj : occSign x L j ≠ 0) (hij : i ≠ j) :
    occLen x L i ≠ occLen x L j := by
  intro h
  have hii : i.1 ≠ j.1 := fun h1 => hij (Fin.ext h1)
  rcases (occSign_ne_zero_iff x L i).mp hi with hi' | hi' <;>
    rcases (occSign_ne_zero_iff x L j).mp hj with hj' | hj'
  · rw [occLen_of_pos hi', occLen_of_pos hj'] at h
    exact hii h
  · have hne : ¬ L.get j = (x, true) := by
      rw [hj']; intro hh; exact Bool.false_ne_true (congrArg Prod.snd hh)
    rw [occLen_of_pos hi', occLen_of_ne_pos hne] at h
    refine not_isReduced_of_adjacent (k := j.1) (y := x) (b := false) ?_ ?_ hred
    · rw [List.getElem?_eq_getElem (h := j.2), ← List.get_eq_getElem]
      exact congrArg some hj'
    · have hthis : L[i.1]? = some (x, true) := by
        rw [List.getElem?_eq_getElem (h := i.2), ← List.get_eq_getElem]
        exact congrArg some hi'
      rw [show i.1 = j.1 + 1 from h] at hthis
      simpa using hthis
  · have hne : ¬ L.get i = (x, true) := by
      rw [hi']; intro hh; exact Bool.false_ne_true (congrArg Prod.snd hh)
    rw [occLen_of_ne_pos hne, occLen_of_pos hj'] at h
    refine not_isReduced_of_adjacent (k := i.1) (y := x) (b := false) ?_ ?_ hred
    · rw [List.getElem?_eq_getElem (h := i.2), ← List.get_eq_getElem]
      exact congrArg some hi'
    · have hthis : L[j.1]? = some (x, true) := by
        rw [List.getElem?_eq_getElem (h := j.2), ← List.get_eq_getElem]
        exact congrArg some hj'
      rw [show j.1 = i.1 + 1 from by omega] at hthis
      simpa using hthis
  · have hnei : ¬ L.get i = (x, true) := by
      rw [hi']; intro hh; exact Bool.false_ne_true (congrArg Prod.snd hh)
    have hnej : ¬ L.get j = (x, true) := by
      rw [hj']; intro hh; exact Bool.false_ne_true (congrArg Prod.snd hh)
    rw [occLen_of_ne_pos hnei, occLen_of_ne_pos hnej] at h
    exact hii (by omega)

/-! ## The middle block is shorter than the relator -/

theorem occLen_sub_lt {L : List (α × Bool)} (hcyc : FreeGroup.IsCyclicallyReduced L) {x : α}
    {i j : Fin L.length} (hi : occSign x L i ≠ 0) (hj : occSign x L j ≠ 0)
    (hlt : occLen x L i < occLen x L j) :
    occLen x L j - occLen x L i < L.length := by
  have hb : occLen x L j ≤ L.length := occLen_le x L j
  by_contra hc
  rw [Nat.not_lt] at hc
  have hbe : occLen x L j = L.length := by omega
  have hae : occLen x L i = 0 := by omega
  obtain ⟨hjl, hjlen⟩ := occLen_eq_length hj hbe
  have hil : L.get i = (x, true) := occLen_eq_zero hae
  have hi0 : i.1 = 0 := by rw [occLen_of_pos hil] at hae; omega
  have hi?_ : L[i.1]? = some (x, true) := by
    rw [List.getElem?_eq_getElem (h := i.2), ← List.get_eq_getElem]
    exact congrArg some hil
  have hj?_ : L[j.1]? = some (x, false) := by
    rw [List.getElem?_eq_getElem (h := j.2), ← List.get_eq_getElem]
    exact congrArg some hjl
  have hhead : L.head? = some (x, true) := by
    rw [List.head?_eq_getElem?, ← hi0]
    exact hi?_
  have hlast : L.getLast? = some (x, false) := by
    rw [List.getLast?_eq_getElem?, show L.length - 1 = j.1 from by omega]
    exact hj?_
  have hbad : (x, false).2 = (x, true).2 :=
    hcyc.2 (x, false) (by rw [Option.mem_def, hlast]) (x, true)
      (by rw [Option.mem_def, hhead]) rfl
  exact Bool.false_ne_true hbad

/-! ## The main lemma -/

/-- **The occurrence terms of `∂u/∂x` are pairwise distinct in `⟨α | u⟩`.**  Here `u` is represented
by the reduced word `L` (`hu : mk L = u`), which is cyclically reduced and not a proper power. -/
theorem occTerm_distinct_aux {L : List (α × Bool)} {u : FreeGroup α}
    (hu : FreeGroup.mk L = u) (hcyc : FreeGroup.IsCyclicallyReduced L)
    (hpp : ¬ Work.OROneRel.IsProperPower u) {x : α}
    {i j : Fin L.length} (hi : occSign x L i ≠ 0) (hj : occSign x L j ≠ 0) (hij : i ≠ j) :
    PresentedGroup.mk ({u} : Set (FreeGroup α)) (occTerm x L i) ≠
      PresentedGroup.mk ({u} : Set (FreeGroup α)) (occTerm x L j) := by
  have hred : FreeGroup.IsReduced L := hcyc.1
  have hu' : @FreeGroup.toWord α (Classical.decEq α) u = L := by
    rw [← hu]
    exact toWord_mk_of_reduced hred
  have hcyc_u : Work.OROneRel.IsCyclicallyReducedRelator u := by
    show FreeGroup.IsCyclicallyReduced (@FreeGroup.toWord α (Classical.decEq α) u)
    rw [hu']
    exact hcyc
  have key : ∀ {i j : Fin L.length}, occSign x L i ≠ 0 → occSign x L j ≠ 0 →
      occLen x L i < occLen x L j →
      PresentedGroup.mk ({u} : Set (FreeGroup α)) (occTerm x L i) ≠
        PresentedGroup.mk ({u} : Set (FreeGroup α)) (occTerm x L j) := by
    intro i j hi hj hlt hcon
    set m := (L.take (occLen x L j)).drop (occLen x L i) with hm
    have hle : occLen x L i ≤ occLen x L j := le_of_lt hlt
    have htake : L.take (occLen x L i) ++ m = L.take (occLen x L j) := by
      have h1 : L.take (occLen x L i)
          = List.take (occLen x L i) (L.take (occLen x L j)) := by
        rw [List.take_take, min_eq_left hle]
      rw [hm, h1]
      exact List.take_append_drop (occLen x L i) (L.take (occLen x L j))
    have hmred : FreeGroup.IsReduced m := by
      rw [hm, List.drop_take]
      exact List.IsChain.take (List.IsChain.drop hred (occLen x L i))
        (occLen x L j - occLen x L i)
    have hmlen : m.length = occLen x L j - occLen x L i := by
      rw [hm, List.length_drop, List.length_take, min_eq_left (occLen_le x L j)]
    have hmne : m ≠ [] := by
      rw [← List.length_pos_iff, hmlen]
      omega
    have hmk : FreeGroup.mk (L.take (occLen x L j))
        = FreeGroup.mk (L.take (occLen x L i)) * FreeGroup.mk m := by
      rw [FreeGroup.mul_mk, htake]
    have hsub : Work.OROneRel.IsSubwordOf (FreeGroup.mk m) u := by
      refine ⟨L.take (occLen x L i), L.drop (occLen x L j), ?_⟩
      show @FreeGroup.toWord α (Classical.decEq α) u
        = L.take (occLen x L i) ++ @FreeGroup.toWord α (Classical.decEq α) (FreeGroup.mk m)
          ++ L.drop (occLen x L j)
      rw [hu', toWord_mk_of_reduced hmred, htake]
      exact (List.take_append_drop (occLen x L j) L).symm
    have hlen : Work.OROneRel.relatorNorm (FreeGroup.mk m) < Work.OROneRel.relatorNorm u := by
      have h1 : Work.OROneRel.relatorNorm (FreeGroup.mk m) = m.length := by
        show (@FreeGroup.toWord α (Classical.decEq α) (FreeGroup.mk m)).length = m.length
        rw [toWord_mk_of_reduced hmred]
      have h2 : Work.OROneRel.relatorNorm u = L.length := by
        show (@FreeGroup.toWord α (Classical.decEq α) u).length = L.length
        rw [hu']
      rw [h1, h2, hmlen]
      exact occLen_sub_lt hcyc hi hj hlt
    have hv1 : FreeGroup.mk m ≠ 1 := by
      intro h1
      have h2 : @FreeGroup.toWord α (Classical.decEq α) (FreeGroup.mk m)
          = @FreeGroup.toWord α (Classical.decEq α) (1 : FreeGroup α) := congrArg _ h1
      rw [toWord_mk_of_reduced hmred, classicalToWord_one] at h2
      exact hmne h2
    have hw := Work.OROneRel.WBClean.weinbaum_at u hcyc_u hpp 1 (FreeGroup.mk m)
      (by simpa using hsub) hlen hv1
    apply hw
    have hcon' : PresentedGroup.mk ({u} : Set (FreeGroup α)) (FreeGroup.mk (L.take (occLen x L i)))
        = PresentedGroup.mk ({u} : Set (FreeGroup α)) (FreeGroup.mk (L.take (occLen x L j))) := by
      simpa only [occTerm_eq_take_occLen] using hcon
    have hcomp : PresentedGroup.mk ({u} : Set (FreeGroup α)) (FreeGroup.mk (L.take (occLen x L i)))
          * PresentedGroup.mk ({u} : Set (FreeGroup α)) (FreeGroup.mk m)
        = PresentedGroup.mk ({u} : Set (FreeGroup α)) (FreeGroup.mk (L.take (occLen x L i))) * 1 := by
      rw [mul_one, ← map_mul, ← hmk, hcon']
    exact mul_left_cancel hcomp
  rcases lt_or_gt_of_ne (occLen_ne hred hi hj hij) with h | h
  · exact key hi hj h
  · exact fun hcon => key hj hi h hcon.symm

end WB

/-- **The occurrence terms of `∂u/∂x` are pairwise distinct in `⟨α | u⟩`** (import-hygiene form:
this module is importable inside the `annChain` cone, see the file header). -/
theorem occTerm_distinct_clean {α : Type u} [DecidableEq α] (u : FreeGroup α) {x : α}
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (hpp : ¬ Work.OROneRel.IsProperPower u)
    {i j : Fin (Work.OROneRel.wordOf u).length}
    (hi : Work.ORLyndon.occSign x (Work.OROneRel.wordOf u) i ≠ 0)
    (hj : Work.ORLyndon.occSign x (Work.OROneRel.wordOf u) j ≠ 0) (hij : i ≠ j) :
    PresentedGroup.mk ({u} : Set (FreeGroup α))
        (Work.ORLyndon.occTerm x (Work.OROneRel.wordOf u) i) ≠
      PresentedGroup.mk ({u} : Set (FreeGroup α))
        (Work.ORLyndon.occTerm x (Work.OROneRel.wordOf u) j) :=
  WB.occTerm_distinct_aux (Work.OROneRel.mk_wordOf u) hcyc hpp hi hj hij

end Work.ORLyndon
