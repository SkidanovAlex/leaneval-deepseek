import Mathlib
import Submission.Work.ThomBordism.TwoSet.exists_cellHomeo

/-!
# The owner of a point, and the cells containing it

Structural facts about the grid of the cube that every cell-by-cell induction on it needs:

* `cOf_sub_of_mem_cellSet`: the owner `cOf N x` (defined in `TwoSet/Cells.lean`) of a point `x` is
  coordinatewise contained in every cell containing `x`;
* `lo_hi_eq_cOf_of_mem_cellSet_of_not_mem_cellRelbd`: if `x` is a point of the cell `c` which is
  *not* in the relative boundary of `c`, then `c` has the owner's coordinates;
* `mem_cellRelbd_of_cOf_ne`: hence every cell containing `x` whose coordinates differ from the
  owner's contains `x` in its **relative boundary**.

Since a treatment of a cell is relative to its relative boundary, the last fact says that the value
at `x` can be changed only by the treatment of the owner of `x`.
-/

open scoped Topology unitInterval

namespace Work.ThomBordism.TwoSet

variable {j N : ℕ}

/-- **The owner of a point is contained in every cell containing it.** -/
theorem cOf_sub_of_mem_cellSet {c : CellIdx j N} {x : IC j} (hx : x ∈ cellSet c) :
    (∀ i, c.lo i ≤ (cOf N x).lo i) ∧ (∀ i, (cOf N x).hi i ≤ c.hi i) := by
  constructor
  · intro i
    have h := (mem_cellSet.mp hx i).1
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      have h1 : c.lo i = 0 := by have hle := c.hle i; have hhi := c.hhi i; omega
      have h2 : (cOf 0 x).lo i = 0 := by rw [cOf_lo]; simp
      omega
    · have hNpos : (0:ℝ) < N := by exact_mod_cast hN
      rw [cOf_lo]
      refine Nat.le_floor ?_
      rw [div_le_iff₀ hNpos] at h
      linarith
  · intro i
    have h := (mem_cellSet.mp hx i).2
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      have h1 : c.hi i = 0 := by have := c.hhi i; omega
      have h2 : (cOf 0 x).hi i = 0 := by rw [cOf_hi]; simp
      omega
    · have hNpos : (0:ℝ) < N := by exact_mod_cast hN
      rw [cOf_hi]
      refine (Nat.ceil_le).mpr ?_
      rw [le_div_iff₀ hNpos] at h
      linarith

/-- **A point of a cell off its relative boundary has the owner's coordinates.** -/
theorem lo_hi_eq_cOf_of_mem_cellSet_of_not_mem_cellRelbd {c : CellIdx j N} {x : IC j}
    (hx : x ∈ cellSet c) (hcon : x ∉ cellRelbd c) :
    (∀ i, c.lo i = (cOf N x).lo i) ∧ (∀ i, c.hi i = (cOf N x).hi i) := by
  obtain ⟨hlo, hhi⟩ := cOf_sub_of_mem_cellSet hx
  have key : ∀ i, c.lo i = (cOf N x).lo i ∧ c.hi i = (cOf N x).hi i := by
    intro i
    have hx1 := (mem_cellSet.mp hx i).1
    have hx2 := (mem_cellSet.mp hx i).2
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      have hzero : c.hi i = 0 := by have := c.hhi i; omega
      have hzero' : c.lo i = 0 := by have hle := c.hle i; have hhi := c.hhi i; omega
      rw [cOf_lo, cOf_hi, hzero', hzero]
      simp
    · have hNpos : (0:ℝ) < N := by exact_mod_cast hN
      have hb1 : (c.lo i : ℝ) ≤ (N:ℝ) * (x i : ℝ) := by
        rw [div_le_iff₀ hNpos] at hx1; linarith
      have hb2 : (N:ℝ) * (x i : ℝ) ≤ (c.hi i : ℝ) := by
        rw [le_div_iff₀ hNpos] at hx2; linarith
      rcases eq_or_lt_of_le (c.hle i) with heq | hlt
      · -- the direction is a node: then `N x i` is forced to be that node
        have hEq : (N:ℝ) * (x i : ℝ) = (c.lo i : ℝ) := by
          rw [← heq] at hb2; linarith
        rw [cOf_lo, cOf_hi, hEq, Nat.floor_natCast, Nat.ceil_natCast]
        exact ⟨rfl, heq.symm⟩
      · -- the direction is an interval: `x i` lies strictly inside it
        have hstep : c.hi i = c.lo i + 1 := by have := c.hstep i; omega
        have hlt1 : (c.lo i : ℝ) < (N:ℝ) * (x i : ℝ) := by
          rcases lt_or_eq_of_le hb1 with h | h
          · exact h
          · exfalso
            apply hcon
            refine ⟨i, hlt, Or.inl ?_⟩
            rw [eq_div_iff (ne_of_gt hNpos)]
            linarith
        have hlt2 : (N:ℝ) * (x i : ℝ) < (c.hi i : ℝ) := by
          rcases lt_or_eq_of_le hb2 with h | h
          · exact h
          · exfalso
            apply hcon
            refine ⟨i, hlt, Or.inr ?_⟩
            rw [eq_div_iff (ne_of_gt hNpos)]
            linarith
        have e1 : ⌊(N:ℝ) * (x i : ℝ)⌋₊ = c.lo i := by
          refine le_antisymm ?_ (Nat.le_floor (le_of_lt hlt1))
          have h := (Nat.floor_lt (le_trans (by positivity) (le_of_lt hlt1))).mpr
            (by push_cast; linarith [hlt2, hstep])
          omega
        have e2 : ⌈(N:ℝ) * (x i : ℝ)⌉₊ = c.hi i := by
          refine le_antisymm ((Nat.ceil_le).mpr (le_of_lt hlt2)) ?_
          have h : c.lo i < ⌈(N:ℝ) * (x i : ℝ)⌉₊ :=
            Nat.lt_ceil.mpr (by push_cast; linarith)
          omega
        rw [cOf_lo, cOf_hi, e1, e2]
        exact ⟨rfl, rfl⟩
  exact ⟨fun i => (key i).1, fun i => (key i).2⟩

/-- **Every cell containing `x` whose coordinates differ from the owner's contains `x` in its
relative boundary.** -/
theorem mem_cellRelbd_of_cOf_ne {c : CellIdx j N} {x : IC j} (hx : x ∈ cellSet c)
    (hne : ∃ i, c.lo i ≠ (cOf N x).lo i ∨ c.hi i ≠ (cOf N x).hi i) : x ∈ cellRelbd c := by
  by_contra hcon
  obtain ⟨h1, h2⟩ := lo_hi_eq_cOf_of_mem_cellSet_of_not_mem_cellRelbd hx hcon
  obtain ⟨i, hi⟩ := hne
  rcases hi with h | h
  · exact h (h1 i)
  · exact h (h2 i)

end Work.ThomBordism.TwoSet
