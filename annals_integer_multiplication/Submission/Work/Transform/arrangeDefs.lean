import Mathlib
import Submission.Work.Transform.Defs
import Submission.Work.Kernel.Raw

/-!
# `arrangeWord`: the value-shuffling vocabulary

`HvdH.WordR` shuffling words act on the stack of *values* on stack 0, and the library operations
`pick k` (copy the `k`-th value to the top) and `roll k` (move it there) index that stack by
position.  A word that only rearranges (and duplicates) the values of a fixed pool of 8 values is
conveniently described by

* `I8 = Fin 8`: an index of a pool value,
* `valAt pool i`: the value of the pool at index `i`,
* `stateOf pool l`: the value stack whose top-to-bottom list of pool indices is `l`,
* `stepL l s`: the new index list after the shuffle step `s = (copy?, k)` (`true` = `pick`,
  `false` = `roll`),
* `progOf mkCmd plan`: the word obtained by running the plan's steps consecutively.

The point of the index description is that every value of `stateOf pool l` is *one of the eight*
values of the pool; hence any prefix of the value stack has total encoding size `≤ (k+1) * S` for
`S = Σ vsz pool` (`stateOf_take_sum_le`).  That is what turns the library cost
`K (k+1) (Σ vsz + 1)` of one `pick`/`roll` into the *linear* bound of `arrangeWord`
(`pickStep`, `rollStep`, `runPlan`, `planCost_le`).
-/

set_option autoImplicit false

namespace Work.Transform

open HvdH

/-- Indices of the eight working values. -/
abbrev I8 := Fin 8

/-- The value of a pool of eight values at index `i`. -/
def valAt (pool : List Val) (i : I8) : Val := pool.getD (i : ℕ) .nil

/-- The value stack (top first) whose pool indices are `l`. -/
def stateOf (pool : List Val) (l : List I8) : List Val := l.map (valAt pool)

/-- One shuffle step on index lists: `(true, k)` copies the `k`-th value to the top (`pick`),
`(false, k)` moves it there and removes the original (`roll`). -/
def stepL (l : List I8) (s : Bool × ℕ) : List I8 :=
  l.getD s.2 0 :: (if s.1 then l else l.eraseIdx s.2)

/-- The word implementing a plan, given a word for each single step. -/
def progOf (mkCmd : Bool × ℕ → Cmd) : List (Bool × ℕ) → Cmd
  | [] => .skip
  | s :: t => Cmd.seq (mkCmd s) (progOf mkCmd t)

/-- Uniform-in-the-state cost bound of the step `s`, for a pool of total size `S` and a library
constant `Kmax`. -/
def stepCost (Kmax S : ℕ) (s : Bool × ℕ) : ℕ := Kmax * (s.2 + 1) * ((s.2 + 1) * S + 1)

/-- Cost bound of a whole plan (including the cost `1` of the final `skip`). -/
def planCost (Kmax S : ℕ) : List (Bool × ℕ) → ℕ
  | [] => 1
  | s :: t => stepCost Kmax S s + planCost Kmax S t

/-! ## Basic facts about the pool indices -/

@[simp] theorem stepL_true (l : List I8) (k : ℕ) : stepL l (true, k) = l.getD k 0 :: l := by
  simp [stepL]

@[simp] theorem stepL_false (l : List I8) (k : ℕ) :
    stepL l (false, k) = l.getD k 0 :: l.eraseIdx k := by
  simp [stepL]

@[simp] theorem stateOf_length (pool : List Val) (l : List I8) :
    (stateOf pool l).length = l.length := List.length_map ..

theorem valAt_mem {pool : List Val} (hpool : pool.length = 8) (i : I8) : valAt pool i ∈ pool := by
  have hi : (i : ℕ) < pool.length := by have := i.isLt; omega
  simp only [valAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact List.getElem_mem hi

theorem vsz_valAt_le {pool : List Val} (hpool : pool.length = 8) (i : I8) :
    vsz (valAt pool i) ≤ (pool.map vsz).sum :=
  List.le_sum_of_mem (List.mem_map_of_mem (valAt_mem hpool i))

theorem mem_pool_le_sum {pool : List Val} {v : Val} {S : ℕ} (hS : ∀ w ∈ pool, vsz w ≤ S)
    (hv : v ∈ pool) : vsz v ≤ S := hS v hv

/-- `getD` is independent of the default as long as the index is in range. -/
theorem getD_default {α : Type*} (l : List α) {k : ℕ} (hk : k < l.length) (d d' : α) :
    l.getD k d = l.getD k d' := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

/-- A prefix of a mapped list has sum at most `length * S` when every image is `≤ S`. -/
theorem sum_map_take_le {α : Type*} (f : α → ℕ) (S : ℕ) :
    ∀ (l : List α), (∀ x ∈ l, f x ≤ S) → ∀ i : ℕ, ((l.take i).map f).sum ≤ i * S := by
  intro l
  induction l with
  | nil => intro _ i; simp
  | cons x t ih =>
    intro h i
    cases i with
    | zero => simp
    | succ j =>
      rw [List.take_succ_cons, List.map_cons, List.sum_cons]
      have hx : f x ≤ S := h x (by simp)
      have ht : ∀ y ∈ t, f y ≤ S := fun y hy => h y (List.mem_cons_of_mem x hy)
      calc f x + ((List.take j t).map f).sum ≤ S + j * S := Nat.add_le_add hx (ih ht j)
        _ = (j + 1) * S := by ring

/-- Every prefix of a state built from a pool of total size `S` has encoding size `≤ (k+1) * S`,
as long as the prefix does not run past the end of the state. -/
theorem stateOf_take_sum_le {pool : List Val} (hpool : pool.length = 8) {S : ℕ}
    (hS : ∀ v ∈ pool, vsz v ≤ S) (l : List I8) (tail : List Val) {k : ℕ} (hk : k < l.length) :
    (((stateOf pool l ++ tail).take (k + 1)).map vsz).sum ≤ (k + 1) * S := by
  have hlen : k + 1 ≤ (stateOf pool l).length := by rw [stateOf_length]; omega
  rw [List.take_append_of_le_length hlen]
  have h1 : (stateOf pool l).take (k + 1) = (l.take (k + 1)).map (valAt pool) := by
    rw [stateOf, ← List.map_take]
  rw [h1, List.map_map]
  exact sum_map_take_le (fun i => vsz (valAt pool i)) S l (fun i _ => hS _ (valAt_mem hpool i))
    (k + 1)

theorem stateOf_getD {pool : List Val} (l : List I8) {k : ℕ} (hk : k < l.length) :
    (stateOf pool l).getD k .nil = valAt pool (l.getD k 0) := by
  have hlen : k < (stateOf pool l).length := by rw [stateOf_length]; exact hk
  have h1 : (stateOf pool l).getD k .nil = (stateOf pool l).getD k (valAt pool 0) :=
    getD_default (l := stateOf pool l) hlen .nil (valAt pool 0)
  rw [h1, stateOf, List.getD_map]

theorem stateOf_eraseIdx {pool : List Val} (l : List I8) (k : ℕ) :
    (stateOf pool l).eraseIdx k = stateOf pool (l.eraseIdx k) := by
  rw [stateOf, List.eraseIdx_map, stateOf]

/-! ## One `pick` / `roll` step -/

/-- A `pick k` word, transported to the index description of a state. -/
theorem pickStep {main p : Cmd} {K Kmax S k : ℕ} (hK : K ≤ Kmax)
    (h : WordR main p (fun vs => k < vs.length) (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    {pool : List Val} (hpool : pool.length = 8) (hS : ∀ v ∈ pool, vsz v ≤ S)
    (tail : List Val) (l : List I8) (hk : k < l.length) :
    WordR main p (fun vs => vs = stateOf pool l ++ tail)
      (fun _ out => out = stateOf pool (stepL l (true, k)) ++ tail)
      (fun _ => stepCost Kmax S (true, k)) := by
  refine Work.Kernel.WordR_conseq h ?_ ?_ ?_
  · intro vs hvs
    rw [hvs]
    simp only [stateOf, List.length_append, List.length_map]
    omega
  · intro vs out hvs hout
    rw [hvs] at hout
    have hget : (stateOf pool l ++ tail).getD k .nil = valAt pool (l.getD k 0) := by
      rw [List.getD_append (stateOf pool l) tail .nil k
        (by rw [stateOf, List.length_map]; exact hk)]
      exact stateOf_getD l hk
    rw [hout, hget]
    simp only [stepL, ite_true, stateOf, List.map_cons, List.cons_append]
  · intro vs hvs
    rw [hvs]
    have h1 := stateOf_take_sum_le hpool hS l tail hk
    have h3 : ((((stateOf pool l ++ tail).take (k + 1)).map vsz).sum + 1) ≤ (k + 1) * S + 1 :=
      Nat.add_le_add_right h1 1
    have h4 : K * (k + 1) ≤ Kmax * (k + 1) := Nat.mul_le_mul_right _ hK
    simp only [stepCost]
    exact Nat.mul_le_mul h4 h3

/-- A `roll k` word, transported to the index description of a state. -/
theorem rollStep {main p : Cmd} {K Kmax S k : ℕ} (hK : K ≤ Kmax)
    (h : WordR main p (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    {pool : List Val} (hpool : pool.length = 8) (hS : ∀ v ∈ pool, vsz v ≤ S)
    (tail : List Val) (l : List I8) (hk : k < l.length) :
    WordR main p (fun vs => vs = stateOf pool l ++ tail)
      (fun _ out => out = stateOf pool (stepL l (false, k)) ++ tail)
      (fun _ => stepCost Kmax S (false, k)) := by
  refine Work.Kernel.WordR_conseq h ?_ ?_ ?_
  · intro vs hvs
    rw [hvs]
    simp only [stateOf, List.length_append, List.length_map]
    omega
  · intro vs out hvs hout
    rw [hvs] at hout
    have hget : (stateOf pool l ++ tail).getD k .nil = valAt pool (l.getD k 0) := by
      rw [List.getD_append (stateOf pool l) tail .nil k
        (by rw [stateOf, List.length_map]; exact hk)]
      exact stateOf_getD l hk
    have herase : (stateOf pool l ++ tail).eraseIdx k = stateOf pool (l.eraseIdx k) ++ tail := by
      rw [List.eraseIdx_append, ite_eq_left (by rw [stateOf_length]; exact hk), stateOf_eraseIdx]
    rw [hout, hget, herase]
    simp only [stepL, Bool.false_eq_true, ite_false, stateOf, List.map_cons, List.cons_append]
  · intro vs hvs
    rw [hvs]
    have h1 := stateOf_take_sum_le hpool hS l tail hk
    have h3 : ((((stateOf pool l ++ tail).take (k + 1)).map vsz).sum + 1) ≤ (k + 1) * S + 1 :=
      Nat.add_le_add_right h1 1
    have h4 : K * (k + 1) ≤ Kmax * (k + 1) := Nat.mul_le_mul_right _ hK
    simp only [stepCost]
    exact Nat.mul_le_mul h4 h3

/-! ## Running a whole plan -/

/-- Running a plan of shuffle steps: if every step `s` of `plan` is implemented by `mkCmd s`, and
every step's index is in range for the state it is applied to, then `progOf mkCmd plan` transforms
the state `stateOf pool l ++ tail` into `stateOf pool (plan.foldl stepL l) ++ tail`, at cost
`planCost Kmax S plan`. -/
theorem runPlan {main : Cmd} {pool : List Val} (mkCmd : Bool × ℕ → Cmd)
    (tail : List Val) (Kmax S : ℕ)
    (hstep : ∀ (m : Bool) (k : ℕ) (l : List I8), k < l.length →
      WordR main (mkCmd (m, k)) (fun vs => vs = stateOf pool l ++ tail)
        (fun _ out => out = stateOf pool (stepL l (m, k)) ++ tail)
        (fun _ => stepCost Kmax S (m, k))) :
    ∀ (plan : List (Bool × ℕ)) (l : List I8),
      (∀ j, j < plan.length → (plan.getD j (true,0)).2 < ((plan.take j).foldl stepL l).length) →
      WordR main (progOf mkCmd plan) (fun vs => vs = stateOf pool l ++ tail)
        (fun _ out => out = stateOf pool (plan.foldl stepL l) ++ tail)
        (fun _ => planCost Kmax S plan) := by
  intro plan
  induction plan with
  | nil =>
    intro l _
    refine Work.Kernel.WordR_conseq (Work.Kernel.WordR_skip main) (fun _ _ => trivial) ?_ ?_
    · intro vs out hvs hout
      rw [hout, hvs]
      simp
    · intro vs _
      simp [planCost]
  | cons s t ih =>
    intro l hinv
    have h0 : s.2 < l.length := by
      have h := hinv 0 (by simp)
      simpa using h
    have h1 : WordR main (mkCmd s) (fun vs => vs = stateOf pool l ++ tail)
        (fun _ out => out = stateOf pool (stepL l s) ++ tail) (fun _ => stepCost Kmax S s) :=
      hstep s.1 s.2 l h0
    have h2 : WordR main (progOf mkCmd t) (fun vs => vs = stateOf pool (stepL l s) ++ tail)
        (fun _ out => out = stateOf pool (t.foldl stepL (stepL l s)) ++ tail)
        (fun _ => planCost Kmax S t) := by
      refine ih (stepL l s) (fun j hj => ?_)
      have h := hinv (j + 1) (by simpa using hj)
      simpa using h
    refine Work.Kernel.WordR_conseq
      (Work.Kernel.WordR_seq (B := fun _ => planCost Kmax S t) h1 h2 ?_) ?_ ?_ ?_
    · intro vs mid h1' h2'
      exact ⟨h2', le_of_eq rfl⟩
    · intro vs hvs; exact hvs
    · intro vs out hvs hpost
      obtain ⟨mid, hm, ho⟩ := hpost
      rw [ho]
      simp only [List.foldl_cons]
    · intro vs _
      exact le_of_eq rfl

/-- The cost of a plan is at most its length times the uniform single-step bound. -/
theorem planCost_le {Kmax S Bnd : ℕ} (plan : List (Bool × ℕ)) (h : ∀ s ∈ plan, s.2 < Bnd) :
    planCost Kmax S plan ≤ plan.length * (Kmax * Bnd * (Bnd * S + 1)) + 1 := by
  induction plan with
  | nil => simp [planCost]
  | cons s t ih =>
    have hs : s.2 < Bnd := h s (by simp)
    have ht : ∀ u ∈ t, u.2 < Bnd := fun u hu => h u (List.mem_cons_of_mem s hu)
    have h1 : stepCost Kmax S s ≤ Kmax * Bnd * (Bnd * S + 1) := by
      have h2 : s.2 + 1 ≤ Bnd := by omega
      have h3 : (s.2 + 1) * S + 1 ≤ Bnd * S + 1 := by
        exact Nat.add_le_add_right (Nat.mul_le_mul_right S h2) 1
      simp only [stepCost]
      exact Nat.mul_le_mul (Nat.mul_le_mul_left Kmax h2) h3
    calc planCost Kmax S (s :: t)
        = stepCost Kmax S s + planCost Kmax S t := rfl
      _ ≤ Kmax * Bnd * (Bnd * S + 1) + (t.length * (Kmax * Bnd * (Bnd * S + 1)) + 1) :=
          Nat.add_le_add h1 (ih ht)
      _ = (s :: t).length * (Kmax * Bnd * (Bnd * S + 1)) + 1 := by
          rw [List.length_cons]; ring

/-! ## The concrete plan -/

/-- The concrete plan of `arrangeWord`: 17 shuffle steps taking the pool
`[a, ab, zst, zstie, p, r, ts', zs]` (indices `0..7`) to the layout the transform pipeline
consumes. -/
def plan : List (Bool × ℕ) :=
  [(false, 6), (true, 6), (true, 6), (true, 4), (true, 9), (false, 8), (true, 9), (true, 10),
   (true, 12), (true, 11), (false, 10), (true, 13), (false, 15), (false, 14), (false, 16),
   (false, 15), (false, 16)]

/-- The pool index list of the initial working stack. -/
def L0 : List I8 := [0, 1, 2, 3, 4, 5, 6, 7]

/-- The pool index list of the stack the pipeline consumes. -/
def planFinal : List I8 := [4, 1, 7, 2, 5, 4, 0, 2, 5, 4, 4, 3, 5, 1, 4, 5, 6]

theorem plan_length : plan.length = 17 := rfl

theorem plan_foldl : plan.foldl stepL L0 = planFinal := rfl

theorem plan_getD_lt (j : ℕ) (hj : j < plan.length) :
    (plan.getD j (true,0)).2 < 17 := by
  rw [plan_length] at hj
  interval_cases j <;> decide

theorem plan_all_lt : plan.all (fun s => decide (s.2 < 17)) = true := rfl

theorem plan_mem_lt : ∀ s ∈ plan, s.2 < 17 := by
  intro s hs
  have h := List.all_eq_true.mp plan_all_lt s hs
  simpa using h

theorem plan_indices :
    ∀ j, j < plan.length → (plan.getD j (true,0)).2 < ((plan.take j).foldl stepL L0).length := by
  intro j hj
  rw [plan_length] at hj
  interval_cases j <;> decide

end Work.Transform
