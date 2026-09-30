import Mathlib
import Submission.Work.RatHurewicz.fillingFamilyConst
import Submission.Work.RatHurewicz.CubicalDefs

/-!
# Faces of degenerate cubes (the `Fin` bookkeeping)

`D_k χ := χ ∘ delG k` is the cube `χ` pulled back along the projection dropping the coordinate `k`.
This file records the combinatorial infrastructure for its faces:

* `delIdx i j hij` — the index of `j` after deleting the coordinate `i` (`j ≠ i`), characterised by
  `i.succAbove (delIdx i j hij) = j` (`succAbove_delIdx`) and `delIdx i (i.succAbove k) _ = k`;
* `degenOp_comp_faceCM_self` — the face in the *degeneracy* direction is `χ` itself;
* `delG_faceCM_apply` / `degenOp_comp_faceCM` — in any other direction the face is `D_κ` of the
  corresponding face of `χ`, with the explicit indices `κ = delIdx j i` and `j' = delIdx i j`.
-/

open scoped unitInterval Topology
open Work.Stems.Cubical

namespace Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- The degeneracy of a cube: `D_k χ := χ ∘ delG k`. -/
def degenOp {n : ℕ} (k : Fin (n + 1)) (χ : C(IC n, X)) : C(IC (n + 1), X) :=
  χ.comp (delG n k)

@[simp] theorem degenOp_apply {n : ℕ} (k : Fin (n + 1)) (χ : C(IC n, X)) (z : IC (n + 1)) :
    degenOp k χ z = χ (delG n k z) := rfl

/-- Delete the coordinate `i` from an index `j ≠ i`. -/
def delIdx {n : ℕ} (i j : Fin (n + 1)) (hij : j ≠ i) : Fin n :=
  if h : (j : ℕ) < (i : ℕ) then ⟨(j : ℕ), by omega⟩
  else ⟨(j : ℕ) - 1, by
    have hne : (j : ℕ) ≠ (i : ℕ) := fun hh => hij (Fin.ext hh)
    have := j.isLt
    omega⟩

theorem delIdx_val {n : ℕ} (i j : Fin (n + 1)) (hij : j ≠ i) :
    ((delIdx i j hij : Fin n) : ℕ) = if (j : ℕ) < (i : ℕ) then (j : ℕ) else (j : ℕ) - 1 := by
  rw [delIdx]
  split_ifs with h
  · rfl
  · rfl

/-- The value of `Fin.succAbove` as a natural number. -/
theorem succAbove_val {n : ℕ} (p : Fin (n + 1)) (k : Fin n) :
    ((p.succAbove k : Fin (n + 1)) : ℕ)
      = if (k : ℕ) < (p : ℕ) then (k : ℕ) else (k : ℕ) + 1 := by
  rw [Fin.succAbove]
  split_ifs with h1 h2 <;>
    simp_all [Fin.val_castSucc, Fin.val_succ, Fin.lt_def]

/-- **Round trip**: deleting the coordinate `i` from `j ≠ i` and re-inserting gives back `j`. -/
theorem succAbove_delIdx {n : ℕ} (i j : Fin (n + 1)) (hij : j ≠ i) :
    i.succAbove (delIdx i j hij) = j := by
  apply Fin.ext
  by_cases h : (j : ℕ) < (i : ℕ)
  · have hv : ((delIdx i j hij : Fin n) : ℕ) = (j : ℕ) := by rw [delIdx_val, if_pos h]
    rw [succAbove_val, if_pos (by rw [hv]; exact h), hv]
  · have hv : ((delIdx i j hij : Fin n) : ℕ) = (j : ℕ) - 1 := by rw [delIdx_val, if_neg h]
    have hne : (j : ℕ) ≠ (i : ℕ) := fun hh => hij (Fin.ext hh)
    rw [succAbove_val, if_neg (by rw [hv]; omega), hv]
    omega

/-- **Round trip**: deleting the coordinate `i` from `i.succAbove k` gives back `k`. -/
theorem delIdx_succAbove {n : ℕ} (i : Fin (n + 1)) (k : Fin n)
    (h : i.succAbove k ≠ i) : delIdx i (i.succAbove k) h = k := by
  apply Fin.ext
  by_cases hk : (k : ℕ) < (i : ℕ)
  · have hv : ((i.succAbove k : Fin (n + 1)) : ℕ) = (k : ℕ) := by rw [succAbove_val, if_pos hk]
    rw [delIdx_val, if_pos (by rw [hv]; exact hk), hv]
  · have hv : ((i.succAbove k : Fin (n + 1)) : ℕ) = (k : ℕ) + 1 := by rw [succAbove_val, if_neg hk]
    rw [delIdx_val, if_neg (by rw [hv]; omega), hv]
    omega

/-- Monotonicity of `succAbove` in terms of `delIdx`. -/
theorem succAbove_lt_iff {n : ℕ} (i j : Fin (n + 1)) (hij : j ≠ i) (k : Fin n) :
    i.succAbove k < j ↔ k < delIdx i j hij := by
  have hne : (j : ℕ) ≠ (i : ℕ) := fun hh => hij (Fin.ext hh)
  have hi := i.isLt
  have hj := j.isLt
  have hk := k.isLt
  rw [Fin.lt_def, Fin.lt_def]
  simp only [succAbove_val, delIdx_val]
  split_ifs <;> omega

/-- Equality version. -/
theorem succAbove_eq_iff {n : ℕ} (i j : Fin (n + 1)) (hij : j ≠ i) (k : Fin n) :
    i.succAbove k = j ↔ k = delIdx i j hij := by
  have hne : (j : ℕ) ≠ (i : ℕ) := fun hh => hij (Fin.ext hh)
  have hi := i.isLt
  have hj := j.isLt
  have hk := k.isLt
  rw [Fin.ext_iff, Fin.ext_iff]
  simp only [succAbove_val, delIdx_val]
  split_ifs <;> omega

/-- The face of a degeneracy in the degeneracy direction is the original cube. -/
theorem degenOp_comp_faceCM_self {n : ℕ} (k : Fin (n + 1)) (χ : C(IC n, X))
    (b : unitInterval) :
    (degenOp k χ).comp (faceCM k b) = χ := by
  ext u
  simp only [ContinuousMap.comp_apply, degenOp_apply]
  rw [faceCM_delG]


/-- The value of `faceCM` on its own face direction. -/
theorem faceCM_apply_self' {n : ℕ} (i : Fin (n + 1)) (b : unitInterval) (w : IC n) :
    faceCM i b w i = b := by
  rw [faceCM_eq_insertNth]
  exact Fin.insertNth_apply_same (α := fun _ : Fin (n + 1) => unitInterval) i b w

/-- The value of `faceCM` on a `succAbove`-index. -/
theorem faceCM_apply_succAbove {n : ℕ} (i : Fin (n + 1)) (b : unitInterval) (w : IC n)
    (k : Fin n) : faceCM i b w (i.succAbove k) = w k := by
  rw [faceCM_eq_insertNth]
  exact Fin.insertNth_apply_succAbove (α := fun _ : Fin (n + 1) => unitInterval) i b w k

/-- The `Fin` identity comparing the index obtained by deleting `j` from `i.succAbove k` with the
index obtained by deleting `j'` from `k` (where `j' := delIdx i j hij`). -/
theorem delIdx_succAbove_comm {m : ℕ} (i j : Fin (m + 2)) (hij : j ≠ i) {k : Fin (m + 1)}
    (hk : k ≠ delIdx i j hij) :
    delIdx j (i.succAbove k) (fun h => hk ((succAbove_eq_iff i j hij k).mp h))
      = (delIdx j i hij.symm).succAbove (delIdx (delIdx i j hij) k hk) := by
  apply Fin.ext
  have hne : (j : ℕ) ≠ (i : ℕ) := fun h => hij (Fin.ext h)
  have hkb : (k : ℕ) ≠ ((delIdx i j hij : Fin (m + 1)) : ℕ) := fun h => hk (Fin.ext h)
  have hi := i.isLt
  have hj := j.isLt
  have hkk := k.isLt
  simp only [delIdx_val, succAbove_val] at hkb ⊢
  split_ifs at hkb ⊢ <;> omega

/-- **The face of a degenerate cube**, pointwise: for `j ≠ i`,
`delG i (faceCM j b u) = faceCM j' b (delG κ u)`, where `j' = delIdx i j hij` is the index of `j`
after deleting the coordinate `i` and `κ = delIdx j i hij.symm` is the index of `i` after deleting
the coordinate `j`. -/
theorem delG_faceCM_apply {m : ℕ} (i j : Fin (m + 2)) (hij : j ≠ i) (b : unitInterval)
    (u : IC (m + 1)) :
    delG (m + 1) i (faceCM j b u)
      = faceCM (delIdx i j hij) b (delG m (delIdx j i hij.symm) u) := by
  funext k
  rw [delG_apply]
  by_cases hk : k = delIdx i j hij
  · rw [hk, succAbove_delIdx i j hij, faceCM_apply_self', faceCM_apply_self']
  · have hq : i.succAbove k ≠ j := fun h => hk ((succAbove_eq_iff i j hij k).mp h)
    have hL : faceCM j b u (i.succAbove k) = u (delIdx j (i.succAbove k) hq) := by
      conv_lhs => rw [← succAbove_delIdx j (i.succAbove k) hq]
      exact faceCM_apply_succAbove j b u _
    have hR : faceCM (delIdx i j hij) b (delG m (delIdx j i hij.symm) u) k
        = (delG m (delIdx j i hij.symm) u) (delIdx (delIdx i j hij) k hk) := by
      conv_lhs => rw [← succAbove_delIdx (delIdx i j hij) k hk]
      exact faceCM_apply_succAbove (delIdx i j hij) b _ _
    rw [hL, hR, delG_apply]
    exact congrArg u (delIdx_succAbove_comm i j hij hk)

/-- **The face of a degenerate cube**: in a direction other than the degeneracy direction, the face
of `D_i χ` is `D_κ` of the corresponding face of `χ`. -/
theorem degenOp_comp_faceCM {m : ℕ} (i j : Fin (m + 2)) (hij : j ≠ i)
    (χ : C(IC (m + 1), X)) (b : unitInterval) :
    (degenOp i χ).comp (faceCM j b)
      = degenOp (delIdx j i hij.symm) (χ.comp (faceCM (delIdx i j hij) b)) := by
  ext u
  simp only [ContinuousMap.comp_apply, degenOp_apply]
  rw [delG_faceCM_apply i j hij b u]

end

end Work.RatHurewicz
