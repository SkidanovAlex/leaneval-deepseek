import Mathlib
import Submission.Work.OROneRel.letterCountHalfAux

/-!
# The exponent sum of a letter is bounded by its letter count

For a word `L : List (α × Bool)` and a generator `t : α`, each letter contributes
at most `1` in absolute value to the exponent sum `ssum t L`, and contributes
nothing unless its generator is `t`.  Hence

* `abs_ssum_le_tcount` : `|ssum t L| ≤ tcount t L`.

The auxiliary facts recorded here are

* `gfun_abs_le_one` : a single letter contributes at most `1` in absolute value;
* `gfun_eq_zero_of_tp_false` : a letter whose generator is not `t` contributes `0`;
* `tcount_cons_cast` : the integer cast of `tcount` on a cons, split off the head.

-/

namespace Work.OROneRel

universe u

/-- A single letter contributes at most `1` in absolute value to any exponent sum. -/
theorem gfun_abs_le_one {α : Type u} (t : α) (p : α × Bool) : |gfun t p| ≤ 1 := by
  classical
  obtain ⟨a, b⟩ := p
  cases b <;> simp [gfun] <;> split_ifs <;> simp

/-- A letter whose generator is not `t` contributes `0` to the exponent sum of `t`. -/
theorem gfun_eq_zero_of_tp_false {α : Type u} (t : α) (p : α × Bool)
    (h : tp t p = false) : gfun t p = 0 := by
  classical
  have hne : p.1 ≠ t := fun hc => by
    have h1 : tp t p = true := (tp_eq_true_iff t p).mpr hc
    rw [h1] at h
    exact Bool.noConfusion h
  obtain ⟨a, b⟩ := p
  simp only at hne
  simp [gfun, hne]

/-- `tcount` on a cons, with the head split off, at the level of integers. -/
theorem tcount_cons_cast {α : Type u} (t : α) (a : α × Bool) (L : List (α × Bool)) :
    ((tcount t (a :: L) : ℕ) : ℤ) = (if tp t a then (1 : ℤ) else 0) + ((tcount t L : ℕ) : ℤ) := by
  have h : tcount t (a :: L) = tcount t L + (if tp t a = true then 1 else 0) := by
    simp only [tcount, List.countP_cons]
  rw [h, Nat.cast_add]
  by_cases hc : tp t a = true
  · rw [if_pos hc, if_pos hc]; push_cast; ring
  · rw [if_neg hc, if_neg hc]; push_cast; ring

theorem abs_ssum_le_tcount {α : Type u} (t : α) (L : List (α × Bool)) :
    |Work.OROneRel.ssum t L| ≤ ((Work.OROneRel.tcount t L : ℕ) : ℤ) := by
  classical
  induction L with
  | nil => simp [ssum, tcount]
  | cons a L ih =>
    have hsum : ssum t (a :: L) = gfun t a + ssum t L := by simp [ssum]
    have hgi : |gfun t a| ≤ (if tp t a then (1 : ℤ) else 0) := by
      by_cases hc : tp t a = true
      · rw [if_pos hc]; exact gfun_abs_le_one t a
      · rw [if_neg hc]
        have hf : tp t a = false := by cases h' : tp t a <;> simp_all
        rw [gfun_eq_zero_of_tp_false t a hf]; simp
    calc |ssum t (a :: L)| = |gfun t a + ssum t L| := by rw [hsum]
      _ ≤ |gfun t a| + |ssum t L| := abs_add_le _ _
      _ ≤ (if tp t a then (1 : ℤ) else 0) + ((tcount t L : ℕ) : ℤ) := add_le_add hgi ih
      _ = ((tcount t (a :: L) : ℕ) : ℤ) := by rw [tcount_cons_cast]

end Work.OROneRel
