import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-!
# Structural list lookups for the `J`-side certificate tables

The final numeric evaluation of the `J`-form reads its tables by *index*, and the kernel's
`List.getD` (which goes through `List.get?`/`getElem`) is far too slow for tens of millions of
lookups.  We use plain structural recursions instead, which the kernel reduces
straight-forwardly.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- Structural lookup in a list of naturals. -/
def nthD : List ℕ → ℕ → ℕ → ℕ
  | [], _, d => d
  | a :: _, 0, _ => a
  | _ :: t, n+1, d => nthD t n d

/-- Structural lookup in a list of lists of naturals. -/
def nthDl : List (List ℕ) → ℕ → List ℕ → List ℕ
  | [], _, d => d
  | a :: _, 0, _ => a
  | _ :: t, n+1, d => nthDl t n d

/-- Structural lookup in a list of pairs of naturals. -/
def nthDp : List (ℕ × ℕ) → ℕ → ℕ × ℕ → ℕ × ℕ
  | [], _, d => d
  | a :: _, 0, _ => a
  | _ :: t, n+1, d => nthDp t n d

@[simp] theorem nthD_nil (n d : ℕ) : nthD [] n d = d := by cases n <;> rfl

theorem nthD_cons_zero (a : ℕ) (t : List ℕ) (d : ℕ) : nthD (a :: t) 0 d = a := rfl

theorem nthD_cons_succ (a : ℕ) (t : List ℕ) (n d : ℕ) : nthD (a :: t) (n+1) d = nthD t n d := rfl

theorem nthD_cons_lt {a : ℕ} {t : List ℕ} {n d : ℕ} (h : 0 < n) :
    nthD (a :: t) n d = nthD t (n-1) d := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp h)
  rfl

theorem nthDl_cons_zero (a : List ℕ) (t : List (List ℕ)) (d : List ℕ) : nthDl (a :: t) 0 d = a := rfl

theorem nthDl_cons_succ (a : List ℕ) (t : List (List ℕ)) (n : ℕ) (d : List ℕ) :
    nthDl (a :: t) (n+1) d = nthDl t n d := rfl

theorem nthDl_eq_getD (l : List (List ℕ)) (n : ℕ) (d : List ℕ) : nthDl l n d = l.getD n d := by
  induction l generalizing n with
  | nil => cases n <;> rfl
  | cons a t ih =>
      cases n with
      | zero => rfl
      | succ m => rw [nthDl_cons_succ, List.getD_cons_succ, ih]

theorem nthDp_cons_zero (a : ℕ × ℕ) (t : List (ℕ × ℕ)) (d : ℕ × ℕ) : nthDp (a :: t) 0 d = a := rfl

theorem nthDp_cons_succ (a : ℕ × ℕ) (t : List (ℕ × ℕ)) (n : ℕ) (d : ℕ × ℕ) :
    nthDp (a :: t) (n+1) d = nthDp t n d := rfl

theorem nthDp_eq_getD (l : List (ℕ × ℕ)) (n : ℕ) (d : ℕ × ℕ) : nthDp l n d = l.getD n d := by
  induction l generalizing n with
  | nil => cases n <;> rfl
  | cons a t ih =>
      cases n with
      | zero => rfl
      | succ m => rw [nthDp_cons_succ, List.getD_cons_succ, ih]

/-- `nthD` agrees with `List.getD`. -/
theorem nthD_eq_getD (l : List ℕ) (n d : ℕ) : nthD l n d = l.getD n d := by
  induction l generalizing n with
  | nil => cases n <;> rfl
  | cons a t ih =>
      cases n with
      | zero => rfl
      | succ m => rw [nthD_cons_succ, List.getD_cons_succ, ih]

/-- `nthD` on a mapped range. -/
theorem nthD_map_range (f : ℕ → ℕ) (N n : ℕ) (hN : N < n) :
    nthD ((List.range n).map f) N 0 = f N := by
  rw [nthD_eq_getD, List.getD_eq_getElem _ _
      (by rw [List.length_map, List.length_range]; exact hN),
    List.getElem_map, List.getElem_range (by rwa [List.length_range])]

theorem nthDl_map_range (f : ℕ → List ℕ) (N n : ℕ) (hN : N < n) :
    nthDl ((List.range n).map f) N [] = f N := by
  rw [nthDl_eq_getD, List.getD_eq_getElem _ _
      (by rw [List.length_map, List.length_range]; exact hN),
    List.getElem_map, List.getElem_range (by rwa [List.length_range])]

theorem nthDp_map_range (f : ℕ → ℕ × ℕ) (N n : ℕ) (hN : N < n) :
    nthDp ((List.range n).map f) N (0, 0) = f N := by
  rw [nthDp_eq_getD, List.getD_eq_getElem _ _
      (by rw [List.length_map, List.length_range]; exact hN),
    List.getElem_map, List.getElem_range (by rwa [List.length_range])]

end Commons.NumberTheory.MaynardSieve
