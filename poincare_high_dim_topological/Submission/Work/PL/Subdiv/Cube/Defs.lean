import Mathlib
import Submission.Work.PL.Subdiv.Defs
import Submission.Work.PL.Generic.Basic

/-!
# The Freudenthal (Kuhn) triangulation of a cube: definitions

Definitions and elementary API for the grid ("Freudenthal"/"Kuhn") triangulation of the cube
`[0,m]^n`, on which `exists_cube_triangulation` builds a mesh-`δ` triangulation of
`PL.closedCube β`.

* `wvec π k` -- the `k`-th vertex of the Freudenthal simplex of the unit cube attached to the
  ordering `π`: the `{0,1}`-vector that is `1` exactly on the positions `≥ k` of `π`.
* `unitVerts π` -- the vertex set `{wvec π k | k ∈ {0,…,n}}` of that simplex (a `Finset`).
* `unitSimp π` -- the region `{y | 0 ≤ y ≤ 1, y monotone along π}`; it is
  `convexHull ℝ (unitVerts π)`.
* `cellPt c` -- the point of `E n` with coordinates `c i`.
* `cellVerts c π` -- `cellVerts c π = cellPt c + unitVerts π`, the vertex set of the Freudenthal
  simplex in the grid cell `c`.
-/

open Set Metric
open scoped BigOperators
open PL

namespace Work.PL.Subdiv.Cube

noncomputable section

variable {n : ℕ}

/-- The `k`-th vertex `w_k` of the Freudenthal simplex of the unit cube for the ordering `π`:
the `{0,1}`-vector which is `1` exactly on the coordinates occupying positions `≥ k` in the
order `π`. -/
def wvec (π : Equiv.Perm (Fin n)) (k : ℕ) : PL.E n :=
  WithLp.toLp 2 (fun i => if k ≤ (π.symm i : ℕ) then (1 : ℝ) else 0)

@[simp] lemma wvec_apply (π : Equiv.Perm (Fin n)) (k : ℕ) (i : Fin n) :
    wvec π k i = if k ≤ (π.symm i : ℕ) then (1 : ℝ) else 0 := by
  simp [wvec]

/-- The value of `wvec π k` at the coordinate sitting at position `a` of `π`. -/
lemma wvec_at (π : Equiv.Perm (Fin n)) (k : ℕ) (a : Fin n) :
    wvec π k (π a) = if k ≤ (a : ℕ) then (1 : ℝ) else 0 := by
  rw [wvec_apply]
  simp

/-- `wvec π k` is a `{0,1}`-vector, hence monotone for the order `π`. -/
lemma wvec_monotone (π : Equiv.Perm (Fin n)) (k : ℕ) :
    ∀ a b : Fin n, a ≤ b → wvec π k (π a) ≤ wvec π k (π b) := by
  intro a b hab
  rw [wvec_at, wvec_at]
  by_cases h : k ≤ (a : ℕ)
  · have h' : k ≤ (b : ℕ) := le_trans h (by exact_mod_cast hab)
    simp [h, h']
  · have hb : ¬ k ≤ (a : ℕ) := h
    by_cases h' : k ≤ (b : ℕ)
    · simp [h, h']
    · simp [h, h']

/-- The last vertex `w_n` is the origin. -/
lemma wvec_last (π : Equiv.Perm (Fin n)) : wvec π n = 0 := by
  ext i
  rw [wvec_apply]
  have h : ¬ (n ≤ (π.symm i : ℕ)) := Nat.not_le.mpr (π.symm i).isLt
  simp [h]

/-- The vertex set of the Freudenthal simplex of the unit cube for the ordering `π`. -/
def unitVerts (π : Equiv.Perm (Fin n)) : Finset (PL.E n) :=
  (Finset.range (n + 1)).image (wvec π)

lemma mem_unitVerts {π : Equiv.Perm (Fin n)} {k : ℕ} (hk : k ≤ n) : wvec π k ∈ unitVerts π :=
  Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk), rfl⟩

/-- The (closed) Freudenthal simplex of the unit cube for the ordering `π`: the points of the
unit cube whose coordinates are non-decreasing along `π`. -/
def unitSimp (π : Equiv.Perm (Fin n)) : Set (PL.E n) :=
  {y | (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ ∀ a b : Fin n, a ≤ b → y (π a) ≤ y (π b)}

lemma wvec_mem_unitSimp (π : Equiv.Perm (Fin n)) (k : ℕ) : wvec π k ∈ unitSimp π := by
  refine ⟨?_, wvec_monotone π k⟩
  intro i
  rw [wvec_apply]
  split <;> norm_num

lemma unitVerts_subset_unitSimp (π : Equiv.Perm (Fin n)) :
    (unitVerts π : Set (PL.E n)) ⊆ unitSimp π := by
  intro v hv
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hv
  exact wvec_mem_unitSimp π k

/-- The point of `E n` with coordinates `c i`. -/
def cellPt (c : Fin n → ℕ) : PL.E n := WithLp.toLp 2 (fun i => (c i : ℝ))

@[simp] lemma cellPt_apply (c : Fin n → ℕ) (i : Fin n) : cellPt c i = (c i : ℝ) := by
  simp [cellPt]

/-- The vertex set of the Freudenthal simplex in the grid cell `c` with ordering `π`. -/
def cellVerts (c : Fin n → ℕ) (π : Equiv.Perm (Fin n)) : Finset (PL.E n) :=
  (unitVerts π).image (fun v => cellPt c + v)

lemma cellVerts_eq (c : Fin n → ℕ) (π : Equiv.Perm (Fin n)) :
    cellVerts c π = (Finset.range (n + 1)).image (fun k => cellPt c + wvec π k) := by
  rw [cellVerts, unitVerts, Finset.image_image]
  rfl

lemma mem_cellVerts {c : Fin n → ℕ} {π : Equiv.Perm (Fin n)} {k : ℕ} (hk : k ≤ n) :
    cellPt c + wvec π k ∈ cellVerts c π :=
  Finset.mem_image.mpr ⟨wvec π k, mem_unitVerts hk, rfl⟩

end

end Work.PL.Subdiv.Cube
