/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The doubled word of a cyclically reduced relator is cyclically reduced

For a list of letters `L : List (α × Bool)` write `dbl L = (L.map (fun p => [p, p])).flatten` for
the word obtained from `L` by repeating every letter twice.  The main result of this file,

`isCyclicallyReduced_doubledWord_of_relator`: if `r` is a cyclically reduced relator then `dbl`
applied to the reduced word of `r` is cyclically reduced.

The mathematical content is entirely elementary.  Two consecutive repeated letters `p, p` of a
doubled word never cancel (a cancellation needs the second letter to be `(p.1, !p.2) ≠ p`), and two
letters at the junction of two consecutive blocks are the last letter `p` of one block and the
first letter `q` of the next, which are *consecutive* letters of the original word `L`; since `L`
is reduced they do not cancel either.  Hence `dbl L` is reduced whenever `L` is.  The only
remaining point is that the first and the last letter of `dbl L` are those of `L`
(`head?_flatten_doubled`, `getLast?_flatten_doubled`), so the cyclic condition transfers as well.

The reducedness part (`isReduced_flatten_doubled`) is the special case `f p = [p, p]`,
`φ = id` of the general flattening statement `Work.OROneRel.isReduced_flatten_map`; it is proved
here directly so that this file only depends on `Mathlib` and `Submission.Work.OROneRel.Basic`.
-/
import Mathlib
import Submission.Work.OROneRel.Basic

namespace Work.OROneRel

universe u

/-- The doubled word starts with the first letter of the original word.  (Every block `[p, p]` is
nonempty, so the head of a concatenation of blocks is the head of the first block.) -/
lemma head?_flatten_doubled {α : Type u} (L : List (α × Bool)) :
    ((L.map (fun p : α × Bool => [p, p])).flatten).head? = L.head? := by
  induction L with
  | nil => rfl
  | cons p L ih => simp

/-- The doubled word ends with the last letter of the original word.  (The blocks to the right of
the first one are nonempty, so the last letter of the concatenation is the last letter of the last
block, which is the last letter of `L`.) -/
lemma getLast?_flatten_doubled {α : Type u} (L : List (α × Bool)) :
    ((L.map (fun p : α × Bool => [p, p])).flatten).getLast? = L.getLast? := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    cases L with
    | nil => rfl
    | cons q L' =>
      have hne : (List.map (fun p : α × Bool => [p, p]) (q :: L')).flatten ≠ [] := by
        cases L' with
        | nil => simp
        | cons r L'' => simp
      rw [List.map_cons, List.flatten_cons, List.getLast?_append_of_ne_nil _ hne, ih,
        List.getLast?_cons_cons]

/-- The doubling of a reduced word is reduced: within a block the two letters are equal (so they
cannot be inverse to each other), and between two blocks the junction letters are consecutive
letters of the original reduced word. -/
lemma isReduced_flatten_doubled {α : Type u} {L : List (α × Bool)}
    (h : FreeGroup.IsReduced L) :
    FreeGroup.IsReduced ((L.map (fun p : α × Bool => [p, p])).flatten) := by
  rw [FreeGroup.IsReduced]
  have hne : [] ∉ L.map (fun p : α × Bool => [p, p]) := by
    intro hl
    rcases List.mem_map.mp hl with ⟨p, _, hp⟩
    exact List.cons_ne_nil p [p] hp
  refine (List.isChain_flatten hne).2 ⟨?_, ?_⟩
  · -- each block `[p, p]` is reduced
    intro l hl
    rcases List.mem_map.mp hl with ⟨p, _, rfl⟩
    show FreeGroup.IsReduced ([p, p] : List (α × Bool))
    rw [FreeGroup.isReduced_cons_cons]
    exact ⟨fun _ => rfl, FreeGroup.IsReduced.singleton⟩
  · -- consecutive blocks are joined by consecutive letters of `L`
    exact List.isChain_map_of_isChain (fun p : α × Bool => [p, p])
      (fun a b hab => by
        intro x hx y hy
        simp only [Option.mem_def] at hx hy
        have hx' : a = x := by simpa using hx
        have hy' : b = y := by simpa using hy
        rw [← hx', ← hy']
        exact hab) h

/-- `FreeGroup.toWord` does not depend on which `DecidableEq` instance is used: any two instances
of `DecidableEq α` are equal (`Subsingleton (DecidableEq α)`), since `Decidable p` is a
subsingleton for every proposition `p`.  This is needed because `IsCyclicallyReducedRelator` is
defined using `Classical.decEq`, whereas the statement below uses the ambient instance. -/
lemma toWord_decEq_eq {α : Type u} (d₁ d₂ : DecidableEq α) (r : FreeGroup α) :
    @FreeGroup.toWord α d₁ r = @FreeGroup.toWord α d₂ r := by
  rw [Subsingleton.elim d₁ d₂]

theorem isCyclicallyReduced_doubledWord_of_relator {α : Type u} [DecidableEq α] {r : FreeGroup α}
    (h : Work.OROneRel.IsCyclicallyReducedRelator r) :
    FreeGroup.IsCyclicallyReduced
      ((FreeGroup.toWord r).map (fun p : α × Bool => [p, p])).flatten := by
  have h' : FreeGroup.IsCyclicallyReduced
      (@FreeGroup.toWord α (inferInstance : DecidableEq α) r) := by
    have hc : FreeGroup.IsCyclicallyReduced
        (@FreeGroup.toWord α (Classical.decEq α) r) := by
      simpa only [IsCyclicallyReducedRelator] using h
    exact (toWord_decEq_eq (Classical.decEq α) (inferInstance : DecidableEq α) r) ▸ hc
  refine ⟨isReduced_flatten_doubled h'.1, fun a ha b hb hab => ?_⟩
  rw [head?_flatten_doubled] at hb
  rw [getLast?_flatten_doubled] at ha
  exact h'.2 a ha b hb hab

end Work.OROneRel
