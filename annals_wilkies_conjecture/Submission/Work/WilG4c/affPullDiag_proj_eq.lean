/-
  WilG4c — the diagonal `affPullDiag` is exactly the "graph" of `affPullMap`, so projecting
  `liftNM N N X ∩ affPullDiag N c M` onto the first `N` coordinates returns the pullback
  `{x | affPullMap c M x ∈ X}` of `X`.

  The proof is a direct computation with the glueing map `snocIt`: a point of `ℝ^{N+N}` glued
  from `x` (first block) and `w` (last block) lies in `liftNM N N X` iff `w ∈ X`, and lies in
  `affPullDiag N c M` iff `w = affPullMap c M x`.  Hence the existential projection of the
  intersection is the pullback.
-/
import Mathlib
import Submission.Work.WilG4c.AffPullDefs
import Submission.Work.WilG0.projLastIter_eq
import Submission.Work.WilG0.snocIt_natAdd
import Submission.Work.WilG0.snocIt_castAdd
import Submission.Work.WilG0.liftNM_mem

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG4c

/-- The first `n` coordinates of `snocIt n m x w` recover `x`. -/
private lemma snocIt_castAdd_fun (n m : ℕ) (x : Fin n → ℝ) (w : Fin m → ℝ) :
    (fun i : Fin n => Work.WilG0.snocIt n m x w (Fin.castAdd m i)) = x := by
  funext i; rw [Work.WilG0.snocIt_castAdd]

/-- The last `m` coordinates of `snocIt n m x w` recover `w`. -/
private lemma snocIt_natAdd_fun (n m : ℕ) (x : Fin n → ℝ) (w : Fin m → ℝ) :
    (fun j : Fin m => Work.WilG0.snocIt n m x w (Fin.natAdd n j)) = w := by
  funext j; rw [Work.WilG0.snocIt_natAdd]

/-- A glued vector lies in `liftNM n m X` exactly when its last block lies in `X`. -/
private lemma snocIt_mem_liftNM {n m : ℕ} {X : Set (Fin m → ℝ)} {x : Fin n → ℝ}
    {w : Fin m → ℝ} :
    Work.WilG0.snocIt n m x w ∈ Work.WilG0.liftNM n m X ↔ w ∈ X := by
  rw [Work.WilG0.liftNM]
  simp only [Set.mem_ofPred_eq]
  rw [snocIt_natAdd_fun]

/-- A glued vector lies in `affPullDiag n c M` exactly when its last block is
`affPullMap c M` of its first block. -/
private lemma snocIt_mem_affPullDiag {n : ℕ} {c : Fin n → ℝ} {M : Fin n → Fin n → ℝ}
    {x w : Fin n → ℝ} :
    Work.WilG0.snocIt n n x w ∈ Work.WilkG4c.affPullDiag n c M ↔
      w = Work.WilkG4c.affPullMap c M x := by
  rw [Work.WilkG4c.mem_affPullDiag]
  constructor
  · intro h
    funext i
    rw [← Work.WilG0.snocIt_natAdd n n x w i, h i]
    simp only [Work.WilG0.snocIt_castAdd, Work.WilkG4c.affPullMap_apply]
  · intro h i
    rw [h]
    simp only [Work.WilG0.snocIt_natAdd, Work.WilG0.snocIt_castAdd, Work.WilkG4c.affPullMap_apply]

theorem affPullDiag_proj_eq (N : ℕ) (c : Fin N → ℝ) (M : Fin N → Fin N → ℝ)
    (X : Set (Fin N → ℝ)) :
    Work.WilG0.projLastIter N N (Work.WilG0.liftNM N N X ∩ Work.WilkG4c.affPullDiag N c M)
      = {x : Fin N → ℝ | Work.WilkG4c.affPullMap c M x ∈ X} := by
  rw [Work.WilG0.projLastIter_eq]
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, snocIt_mem_liftNM, snocIt_mem_affPullDiag]
  constructor
  · rintro ⟨w, hwX, hwD⟩
    rw [← hwD]; exact hwX
  · intro hx
    exact ⟨Work.WilkG4c.affPullMap c M x, hx, rfl⟩

end Work.WilG4c
