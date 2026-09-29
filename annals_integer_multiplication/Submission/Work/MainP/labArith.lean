import Mathlib
import Submission.Work.MainP.crtLabDefs

/-!
# `crtLabTab`: the arithmetic and list identities behind the initial-state word

`crtLabTab` must produce `canon ss 0` from `int S :: intList ss`, where `S = ss.prod`.  The word
walks the list `ss` from a pile (stack `7`), keeping a *running suffix product* `P` on the value
stack and prepending the entries `triple 0 (suf (j+1)) (suf j)` to an accumulator.

* `suf ss j = (ss.drop j).prod` — the product of the entries from position `j` on;
* `suf_succ` — `suf j = ss[j] * suf (j+1)`;
* `canon_zero` — `canon ss 0 = (List.range ss.length).map (entry ss)`;
* `take_canon_succ` — `(canon ss 0).take (i+1) = (canon ss 0).take i ++ [entry ss i]`.
-/

set_option autoImplicit false

namespace Work.MainP

open HvdH

/-- The suffix product `suf ss j = ss[j] * ss[j+1] * … `. -/
def suf (ss : List ℕ) (j : ℕ) : ℕ := (ss.drop j).prod

/-- The `j`-th entry of `canon ss 0`: `triple 0 (suf (j+1)) (suf j)`. -/
def entry (ss : List ℕ) (j : ℕ) : Val :=
  triple 0 ((suf ss (j+1) : ℕ) : ℤ) ((suf ss j : ℕ) : ℤ)

@[simp] theorem suf_zero (ss : List ℕ) : suf ss 0 = ss.prod := rfl

@[simp] theorem suf_length (ss : List ℕ) : suf ss ss.length = 1 := by
  simp [suf]

theorem suf_succ {ss : List ℕ} {j : ℕ} (h : j < ss.length) :
    suf ss j = ss[j] * suf ss (j+1) := by
  rw [suf, List.drop_eq_getElem_cons h, List.prod_cons, suf]

theorem suf_cons (s : ℕ) (ss : List ℕ) (j : ℕ) : suf (s :: ss) (j+1) = suf ss j := by
  rw [suf, suf, List.drop_succ_cons]

theorem range_map_cons {α : Type*} (f : ℕ → α) (n : ℕ) :
    (List.range (n+1)).map f = f 0 :: (List.range n).map (fun j => f (j+1)) := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  rfl

theorem range_map_snoc {α : Type*} (f : ℕ → α) (n : ℕ) :
    (List.range (n+1)).map f = (List.range n).map f ++ [f n] := by
  rw [List.range_succ, List.map_append, List.map_singleton]

theorem entry_cons (s : ℕ) (ss : List ℕ) (j : ℕ) : entry (s :: ss) (j+1) = entry ss j := by
  simp only [entry, suf_cons]

theorem entry_zero_cons (s : ℕ) (ss : List ℕ) :
    entry (s :: ss) 0 = triple 0 ((ss.prod : ℕ) : ℤ) (((s * ss.prod : ℕ)) : ℤ) := by
  simp only [suf, entry]
  rfl

/-- The main identity: `canon ss 0` is the list of entries `triple 0 (suf (j+1)) (suf j)`. -/
theorem canon_zero (ss : List ℕ) :
    canon ss 0 = (List.range ss.length).map (entry ss) := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
      have hc : canon (s :: ss) 0 =
          triple 0 ((ss.prod : ℕ) : ℤ) (((s * ss.prod : ℕ)) : ℤ) :: canon ss 0 := by
        simp only [canon, List.map_cons, crtTab, Nat.zero_mod, Nat.zero_mul, Nat.cast_zero]
      rw [hc, ih, List.length_cons, range_map_cons]
      congr 1

theorem take_canon_zero (ss : List ℕ) {i : ℕ} (h : i ≤ ss.length) :
    (canon ss 0).take i = (List.range i).map (entry ss) := by
  rw [canon_zero, ← List.map_take, List.take_range, min_eq_left h]

theorem take_canon_succ (ss : List ℕ) {i : ℕ} (h : i < ss.length) :
    (canon ss 0).take (i+1) = (canon ss 0).take i ++ [entry ss i] := by
  rw [take_canon_zero ss (by omega), take_canon_zero ss (by omega), range_map_snoc]

end Work.MainP
