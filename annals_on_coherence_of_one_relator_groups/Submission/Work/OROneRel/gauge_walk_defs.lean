import Mathlib
import Submission.Work.OROneRel.GaugeDefs

/-!
# The walk of a decorated word, and the first-arrival gauge

Definitions and basic lemmas used by `Work.OROneRel.gauge_nontrivial_bound_vertices`.

Let `c : α → ℤ` be a weight function and `L` a word.  Reading the letters of `L` from the left and
keeping track of the running weight gives the list of *levels* `running c i L` (of length
`L.length + 1`); the decorated word `decor c i L` is the list of *steps* of the walk, the `j`-th
letter running from level `(running c i L)[j]` to level `(running c i L)[j+1]`.  The two lemmas
`decor_map_coverSrc` and `decor_map_coverTgt` record this: the sources of the decorated letters are
the levels with the last one deleted, the targets are the levels with the first one deleted.

Given a walk (a list of steps `WalkStep β`) and a gauge `W : ℤ → FreeGroup β`, the step
`(v, l, v')` is *trivial* if `W v * l * (W v')⁻¹ = 1`.  `walkGauge vs lbl` is the **first-arrival
gauge** of a walk with levels `vs` and labels `lbl`: it is built by the state machine `stepUpd` /
`runSteps` below.  Running through the steps in order, whenever a step arrives at a level that is
not yet assigned, that level is assigned the product of the source level's word with the label of
the step.  Every *discovering* step is then trivial, so at most `N - (V - 1)` of the `N` steps can
fail to be trivial, where `V` is the number of distinct levels visited.
-/

namespace Work.OROneRel

universe u v

variable {α : Type u} {β : Type v}

/-- The weight of a single letter. -/
def letterW (c : α → ℤ) (l : α × Bool) : ℤ := if l.2 then c l.1 else -c l.1

/-- **The levels visited by a word.**  The `j`-th entry is the running weight after reading the
first `j` letters, so the list has length `L.length + 1`; its first entry is `i`. -/
def running (c : α → ℤ) : ℤ → List (α × Bool) → List ℤ
  | i, [] => [i]
  | i, (a, true) :: L => i :: running c (i + c a) L
  | i, (a, false) :: L => i :: running c (i - c a) L

/-- A step of a walk: a label read at a source level, arriving at a target level. -/
structure WalkStep (β : Type v) where
  src : ℤ
  lbl : FreeGroup β
  tgt : ℤ

/-- The state update of the first-arrival gauge: a step whose target is not yet assigned assigns
to that target the product of the source's word with the label of the step. -/
noncomputable def stepUpd (acc : ℤ → Option (FreeGroup β)) (s : WalkStep β) :
    ℤ → Option (FreeGroup β) :=
  fun x => if x = s.tgt ∧ acc s.tgt = none then some ((acc s.src).getD 1 * s.lbl) else acc x

/-- Running the state machine over a list of steps. -/
noncomputable def runSteps (acc : ℤ → Option (FreeGroup β)) (steps : List (WalkStep β)) :
    ℤ → Option (FreeGroup β) :=
  steps.foldl stepUpd acc

/-- The initial state of the machine: the starting level carries the empty word. -/
noncomputable def initState (v : ℤ) : ℤ → Option (FreeGroup β) :=
  fun x => if x = v then some 1 else none

/-- The steps of a walk from its levels and its labels: the `j`-th step runs from the `j`-th level
to the `(j+1)`-st level and carries the `j`-th label.  The two lists are to have the same
length. -/
def mkSteps : List ℤ → List (FreeGroup β) → List (WalkStep β)
  | v :: v' :: vs, l :: ls => ⟨v, l, v'⟩ :: mkSteps (v' :: vs) ls
  | _, _ => []

/-- **The first-arrival gauge** of the walk with levels `vs` and labels `lbl`: a level carries the
product of the labels along the chain of levels that first discovered it. -/
noncomputable def walkGauge (vs : List ℤ) (lbl : List (FreeGroup β)) : ℤ → FreeGroup β :=
  fun x => (runSteps (initState (vs.headD 0)) (mkSteps vs lbl) x).getD 1

/-! ### The running weights -/

theorem running_ne_nil (c : α → ℤ) (i : ℤ) (L : List (α × Bool)) : running c i L ≠ [] := by
  induction L generalizing i with
  | nil => simp [running]
  | cons p L ih =>
    obtain ⟨a, b⟩ := p
    cases b <;> simp [running]

theorem running_length (c : α → ℤ) (i : ℤ) (L : List (α × Bool)) :
    (running c i L).length = L.length + 1 := by
  induction L generalizing i with
  | nil => simp [running]
  | cons p L ih =>
    obtain ⟨a, b⟩ := p
    cases b <;> simp [running, ih]

theorem running_eq_cons_tail (c : α → ℤ) (i : ℤ) (L : List (α × Bool)) :
    i :: (running c i L).tail = running c i L := by
  induction L generalizing i with
  | nil => rfl
  | cons p L ih =>
    obtain ⟨a, b⟩ := p
    cases b <;> simp only [running, List.tail_cons]

theorem running_head (c : α → ℤ) (i : ℤ) (L : List (α × Bool)) : (running c i L).headD i = i := by
  have h := running_eq_cons_tail c i L
  cases hL : running c i L with
  | nil => exact absurd hL (running_ne_nil c i L)
  | cons x xs =>
    rw [hL] at h
    simp only [List.tail_cons] at h
    rw [List.headD_cons, ← (List.cons.inj h).1]

/-! ### The decorated walk -/

theorem decor_map_coverSrc (c : α → ℤ) (i : ℤ) (L : List (α × Bool)) :
    (decor c i L).map (coverSrc c) = (running c i L).dropLast := by
  induction L generalizing i with
  | nil => simp [decor, running]
  | cons p L ih =>
    obtain ⟨a, b⟩ := p
    cases b
    · simp only [decor, running, List.map_cons, coverSrc, Bool.false_eq_true, if_false]
      rw [ih (i - c a), List.dropLast_cons_of_ne_nil (running_ne_nil c (i - c a) L)]
      congr 1
      ring
    · simp only [decor, running, List.map_cons, coverSrc, if_true]
      rw [ih (i + c a), List.dropLast_cons_of_ne_nil (running_ne_nil c (i + c a) L)]

theorem decor_map_coverTgt (c : α → ℤ) (i : ℤ) (L : List (α × Bool)) :
    (decor c i L).map (coverTgt c) = (running c i L).tail := by
  induction L generalizing i with
  | nil => simp [decor, running]
  | cons p L ih =>
    obtain ⟨a, b⟩ := p
    cases b
    · simp only [decor, running, List.map_cons, coverTgt, Bool.false_eq_true, if_false,
        List.tail_cons]
      rw [ih (i - c a), running_eq_cons_tail]
    · simp only [decor, running, List.map_cons, coverTgt, if_true, List.tail_cons]
      rw [ih (i + c a), running_eq_cons_tail]

/-! ### The steps of a walk -/

theorem mkSteps_length (vs : List ℤ) (lbl : List (FreeGroup β))
    (hlen : vs.length = lbl.length + 1) : (mkSteps vs lbl).length = lbl.length := by
  induction lbl generalizing vs with
  | nil =>
    match vs with
    | [] => simp at hlen
    | [_] => simp [mkSteps]
    | _ :: _ :: _ => simp at hlen
  | cons l ls ih =>
    match vs with
    | [] => simp at hlen
    | [_] => simp at hlen
    | v :: v' :: vs' =>
      simp only [mkSteps, List.length_cons]
      rw [ih (v' :: vs') (by simp only [List.length_cons] at hlen ⊢; omega)]

theorem mkSteps_map_lbl (vs : List ℤ) (lbl : List (FreeGroup β))
    (hlen : vs.length = lbl.length + 1) :
    (mkSteps vs lbl).map (fun s => s.lbl) = lbl := by
  induction lbl generalizing vs with
  | nil =>
    match vs with
    | [] => simp [mkSteps]
    | [_] => simp [mkSteps]
    | _ :: _ :: _ => simp at hlen
  | cons l ls ih =>
    match vs with
    | [] => simp at hlen
    | [_] => simp at hlen
    | v :: v' :: vs' =>
      simp only [mkSteps, List.map_cons]
      rw [ih (v' :: vs') (by simp only [List.length_cons] at hlen ⊢; omega)]

theorem mkSteps_map_tgt (vs : List ℤ) (lbl : List (FreeGroup β))
    (hlen : vs.length = lbl.length + 1) :
    (mkSteps vs lbl).map (fun s => s.tgt) = vs.tail := by
  induction lbl generalizing vs with
  | nil =>
    match vs with
    | [] => simp [mkSteps]
    | [_] => simp [mkSteps]
    | _ :: _ :: _ => simp at hlen
  | cons l ls ih =>
    match vs with
    | [] => simp at hlen
    | [_] => simp at hlen
    | v :: v' :: vs' =>
      simp only [mkSteps, List.map_cons, List.tail_cons]
      rw [ih (v' :: vs') (by simp only [List.length_cons] at hlen ⊢; omega)]
      simp only [List.tail_cons]

theorem mkSteps_map_src (vs : List ℤ) (lbl : List (FreeGroup β))
    (hlen : vs.length = lbl.length + 1) :
    (mkSteps vs lbl).map (fun s => s.src) = vs.dropLast := by
  induction lbl generalizing vs with
  | nil =>
    match vs with
    | [] => simp [mkSteps]
    | [_] => simp [mkSteps]
    | _ :: _ :: _ => simp at hlen
  | cons l ls ih =>
    match vs with
    | [] => simp at hlen
    | [_] => simp at hlen
    | v :: v' :: vs' =>
      simp only [mkSteps, List.map_cons]
      rw [ih (v' :: vs') (by simp only [List.length_cons] at hlen ⊢; omega)]
      conv_rhs => rw [List.dropLast_cons_of_ne_nil (show (v' :: vs') ≠ [] by simp)]

end Work.OROneRel
