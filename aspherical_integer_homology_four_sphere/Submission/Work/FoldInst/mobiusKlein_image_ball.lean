import Mathlib
import Submission.Work.FoldInst.Voronoi

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The Klein ball is mapped onto the upper half space by any Lorentz matrix

For a matrix `A` in the Lorentz group preserving the upper sheet
(`HypModel.IsLorentzMat A`), the induced action on the Klein model

`mobiusKlein A y = uhsOfHyp (A *ᵥ hypOfKlein y)`

is a bijection from the open unit ball onto the upper half space `{q : 0 < q 3}`.

The inclusion `⊆` is `mobiusKlein_mem` (the image lands in the upper half space).  For the
reverse inclusion, a point `q` of the upper half space is hit by

`y = kleinOfHyp (A⁻¹ *ᵥ hypOfUHS q)`,

using that `A⁻¹` is again a Lorentz matrix preserving the upper sheet (built below), so that
`A⁻¹ *ᵥ hypOfUHS q` lies on the upper sheet and its central projection `y` lies in the ball.

The only tool the inverse step needs is that `A` is invertible with `A⁻¹ = J * Aᵀ * J`; this
follows from `Aᵀ J A = J` and `J * J = 1` alone, while `A * A⁻¹ = 1` is obtained from
`(det A)² = 1`.
-/

open scoped Matrix
open Work.HypModel

namespace Work.FoldInst

/-- The Gram matrix `J` of the Lorentz form is symmetric. -/
private theorem lorentzJ_transpose : Jᵀ = J := by
  have : J = Matrix.diagonal (fun i : Fin 5 => if i = 4 then (-1 : ℝ) else 1) := rfl
  rw [this]
  ext i j
  rw [Matrix.transpose_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]

/-- The Gram matrix `J` of the Lorentz form is an involution: `J * J = 1`. -/
private theorem lorentzJ_mul_self : J * J = 1 := by
  have h1 : J = Matrix.diagonal (fun i : Fin 5 => if i = 4 then (-1 : ℝ) else 1) := rfl
  rw [h1, Matrix.diagonal_mul_diagonal]
  have h : (fun i : Fin 5 =>
      (if i = 4 then (-1 : ℝ) else 1) * (if i = 4 then (-1 : ℝ) else 1)) = fun _ => 1 := by
    funext i; by_cases h4 : i = 4 <;> simp [h4]
  rw [h, Matrix.diagonal_one]

/-- The determinant of the Gram matrix of the Lorentz form is `-1`. -/
private theorem det_lorentzJ : J.det = (-1 : ℝ) := by
  have h1 : J = Matrix.diagonal (fun i : Fin 5 => if i = 4 then (-1 : ℝ) else 1) := rfl
  rw [h1, Matrix.det_diagonal, Fin.prod_univ_five]
  norm_num [Fin.isValue]

/-- For a Lorentz matrix, `(det A)² = 1`. -/
private theorem isLorentzMat_det_sq {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : IsLorentzMat A) :
    A.det ^ 2 = 1 := by
  have h := congrArg Matrix.det hA.1
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_lorentzJ] at h
  rw [pow_two]
  linarith

/-- The inverse of a Lorentz matrix: `A⁻¹ = J * Aᵀ * J`. -/
private theorem isLorentzMat_inv_eq {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : IsLorentzMat A) :
    A⁻¹ = J * Aᵀ * J := by
  apply Matrix.inv_eq_left_inv
  calc J * Aᵀ * J * A = J * (Aᵀ * J * A) := by noncomm_ring
    _ = J * J := by rw [hA.1]
    _ = 1 := lorentzJ_mul_self

/-- A Lorentz matrix times its inverse is the identity. -/
private theorem isLorentzMat_mul_inv {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : IsLorentzMat A) :
    A * A⁻¹ = 1 := by
  have h := isLorentzMat_det_sq hA
  rw [pow_two] at h
  exact Matrix.mul_nonsing_inv A (IsUnit.of_mul_eq_one A.det h)

/-- **The inverse of a Lorentz matrix is again a Lorentz matrix preserving the upper sheet.** -/
private theorem isLorentzMat_inv {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : IsLorentzMat A) :
    IsLorentzMat A⁻¹ := by
  have hC : A * A⁻¹ = 1 := isLorentzMat_mul_inv hA
  have hCt : (A⁻¹)ᵀ * Aᵀ = 1 := by
    have h : (A * A⁻¹)ᵀ = (1 : Matrix (Fin 5) (Fin 5) ℝ)ᵀ := by rw [hC]
    rwa [Matrix.transpose_mul, Matrix.transpose_one] at h
  refine ⟨?_, ?_⟩
  · calc (A⁻¹)ᵀ * J * A⁻¹ = (A⁻¹)ᵀ * (Aᵀ * J * A) * A⁻¹ := by rw [hA.1]
      _ = ((A⁻¹)ᵀ * Aᵀ) * J * (A * A⁻¹) := by noncomm_ring
      _ = J := by rw [hCt, hC]; simp
  · have h44 : (A⁻¹) 4 4 = A 4 4 := by
      rw [isLorentzMat_inv_eq hA]
      rw [show J = Matrix.diagonal (fun i : Fin 5 => if i = 4 then (-1 : ℝ) else 1) from rfl]
      simp [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.transpose_apply]
    rw [h44]; exact hA.2

/-- **The Klein action of a Lorentz matrix maps the open unit ball onto the upper half space.** -/
theorem mobiusKlein_image_ball {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : HypModel.IsLorentzMat A) :
    HypModel.mobiusKlein A '' HypModel.ball = HypModel.upperHalfSpace := by
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rw [Set.image_subset_iff]
    intro y hy
    exact mobiusKlein_mem hA hy
  · intro q hq
    rw [Set.mem_image]
    have hq3 : 0 < q 3 := hq
    have hP : hypOfUHS q ∈ upperSheet :=
      ⟨lorentz_hypOfUHS_self (ne_of_gt hq3), hypOfUHS_four_pos hq3⟩
    have hQ : A⁻¹ *ᵥ hypOfUHS q ∈ upperSheet :=
      isLorentzMat_mem_upperSheet (isLorentzMat_inv hA) hP
    refine ⟨kleinOfHyp (A⁻¹ *ᵥ hypOfUHS q), kleinOfHyp_mem_ball hQ, ?_⟩
    rw [mobiusKlein, hypOfKlein_kleinOfHyp hQ]
    rw [Matrix.mulVec_mulVec, isLorentzMat_mul_inv hA, Matrix.one_mulVec]
    exact uhsOfHyp_hypOfUHS (ne_of_gt hq3)

end Work.FoldInst
