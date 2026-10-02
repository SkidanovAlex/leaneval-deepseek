import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Grid cells of the cube, and the vocabulary of the "two-set connectivity" argument

This file sets up the elementary combinatorial-topological vocabulary used by
`Work.ThomBordism.Grassmann.twoSetConnected`: the `N`-grid of the cube `I^j`, its cells (the
fibres of `cellIdx`), their closures (the closed boxes `ccl`), and the basic relations between
them.
-/

namespace Work.ThomBordism.TwoSet

open scoped Topology unitInterval

/-- The standard `n`-cube. -/
abbrev IC (n : ℕ) : Type := Fin n → unitInterval

/-- **The index of the `N`-grid cell containing `x`**: the pair `(lo, hi)` with `lo i / N ≤ x i ≤
hi i / N`, chosen so that the fibres of `cellIdx` are the cells of the standard `N`-subdivision. -/
noncomputable def cellIdx {j : ℕ} (N : ℕ) (x : IC j) : (Fin j → ℕ) × (Fin j → ℕ) :=
  (fun i => ⌊(N : ℝ) * (x i : ℝ)⌋₊, fun i => ⌈(N : ℝ) * (x i : ℝ)⌉₊)

theorem cellIdx_fst_le_snd {j N : ℕ} (x : IC j) (i : Fin j) :
    (cellIdx N x).1 i ≤ (cellIdx N x).2 i :=
  Nat.floor_le_ceil ((N : ℝ) * (x i : ℝ))

theorem cellIdx_snd_le {j N : ℕ} (x : IC j) (i : Fin j) : (cellIdx N x).2 i ≤ N := by
  show ⌈(N : ℝ) * (x i : ℝ)⌉₊ ≤ N
  refine Nat.ceil_le.mpr ?_
  have hx1 : (x i : ℝ) ≤ 1 := (x i).2.2
  have hle : (N : ℝ) * (x i : ℝ) ≤ (N : ℝ) :=
    mul_le_of_le_one_right (Nat.cast_nonneg N) hx1
  exact_mod_cast hle

theorem cellIdx_lo_le {j N : ℕ} (x : IC j) (i : Fin j) :
    ((cellIdx N x).1 i : ℝ) ≤ (N : ℝ) * (x i : ℝ) :=
  Nat.floor_le (mul_nonneg (Nat.cast_nonneg N) (x i).2.1)

theorem cellIdx_le_hi {j N : ℕ} (x : IC j) (i : Fin j) :
    (N : ℝ) * (x i : ℝ) ≤ ((cellIdx N x).2 i : ℝ) :=
  Nat.le_ceil _

/-- The **cell** with index `c` (a fibre of `cellIdx`). -/
def cell {j N : ℕ} (c : (Fin j → ℕ) × (Fin j → ℕ)) : Set (IC j) :=
  {x | cellIdx N x = c}

/-- The **closed box** with index `c`. -/
def ccl {j N : ℕ} (c : (Fin j → ℕ) × (Fin j → ℕ)) : Set (IC j) :=
  {x | ∀ i, ((c.1 i : ℝ) ≤ (N : ℝ) * (x i : ℝ) ∧ (N : ℝ) * (x i : ℝ) ≤ (c.2 i : ℝ))}

theorem cell_subset_ccl {j N : ℕ} (c : (Fin j → ℕ) × (Fin j → ℕ)) :
    cell (N := N) c ⊆ ccl (N := N) c := by
  intro x hx i
  have h1 : cellIdx N x = c := hx
  constructor
  · rw [← h1]; simpa using cellIdx_lo_le (N := N) x i
  · rw [← h1]; simpa using cellIdx_le_hi (N := N) x i

theorem mem_ccl_self {j N : ℕ} (x : IC j) : x ∈ ccl (N := N) (cellIdx N x) := by
  intro i; exact ⟨cellIdx_lo_le x i, cellIdx_le_hi x i⟩

theorem cellIdx_ge_of_mem {j N : ℕ} {c : (Fin j → ℕ) × (Fin j → ℕ)} {x : IC j}
    (hx : x ∈ ccl (N := N) c) :
    c.1 ≤ (cellIdx N x).1 ∧ (cellIdx N x).2 ≤ c.2 := by
  have h1 : ∀ i, ((c.1 i : ℝ) ≤ (N : ℝ) * (x i : ℝ)) := fun i => (hx i).1
  have h2 : ∀ i, ((N : ℝ) * (x i : ℝ) ≤ (c.2 i : ℝ)) := fun i => (hx i).2
  constructor
  · intro i
    have h := h1 i
    have hle : c.1 i ≤ ⌊(N : ℝ) * (x i : ℝ)⌋₊ := by
      simpa using Nat.floor_mono h
    simpa [cellIdx] using hle
  · intro i
    have h := h2 i
    have hle : ⌈(N : ℝ) * (x i : ℝ)⌉₊ ≤ c.2 i := by
      simpa using Nat.ceil_mono h
    simpa [cellIdx] using hle

/-- The boundary of the cube `I^n` is closed. -/
theorem isClosed_cubeBoundary (n : ℕ) : IsClosed (Cube.boundary (Fin n)) := by
  have h : Cube.boundary (Fin n) =
      ⋃ i : Fin n, ({x : Fin n → unitInterval | x i = 0} ∪ {x : Fin n → unitInterval | x i = 1}) := by
    ext x; simp [Cube.boundary]
  rw [h]
  exact isClosed_iUnion_of_finite (fun i =>
    (isClosed_eq (continuous_apply i) continuous_const).union
      (isClosed_eq (continuous_apply i) continuous_const))

end Work.ThomBordism.TwoSet
