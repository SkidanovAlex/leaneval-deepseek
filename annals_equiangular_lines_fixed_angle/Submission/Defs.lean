import ChallengeDeps

open EquiangularLinesFixedAngle
open Filter
open scoped RealInnerProductSpace

/-! Core definitions for the development of Theorem 1.2 of
"Equiangular lines with a fixed angle" (Jiang--Tidor--Yao--Zhang--Zhao, Ann. of Math. 2021). -/

namespace Submission

/-- `λ(α) = (1-α)/(2α)` as in the paper. -/
noncomputable def lam (α : ℝ) : ℝ := (1 - α) / (2 * α)

/-- The all-ones matrix. -/
def allOne {n : ℕ} : Matrix (Fin n) (Fin n) ℝ := fun _ _ => 1

/-- The matrix `M = λ I - A_G + (1/2) J` from the paper (up to the Gram scaling).
Entrywise: `M_ii = λ + 1/2` and `M_ij = -1/2` (edge) / `1/2` (non-edge) for `i ≠ j`. -/
noncomputable def graphMatrix (α : ℝ) {n : ℕ} (G : SimpleGraph (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ := by
  classical
  exact fun i j => if i = j then lam α + 1 / 2 else (if G.Adj i j then -(1 / 2) else 1 / 2)

/-- There exist `n` unit vectors in `𝔼^d` with pairwise inner products `±α` (`n` equiangular lines). -/
def HasLines (α : ℝ) (n d : ℕ) : Prop :=
  ∃ v : Fin n → EuclideanSpace ℝ (Fin d),
    (∀ i : Fin n, ‖v i‖ = 1) ∧
    ∀ ⦃i j : Fin n⦄, i ≠ j → |⟪v i, v j⟫| = α

/-- Arithmetic facts about `λ(α)`. -/
lemma lam_pos {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) : 0 < lam α := by
  unfold lam
  positivity

lemma two_mul_lam {α : ℝ} (hα : α ≠ 0) : 2 * α * lam α = 1 - α := by
  unfold lam
  field_simp [hα]

lemma lam_add_half {α : ℝ} (hα : α ≠ 0) : lam α + 1 / 2 = 1 / (2 * α) := by
  unfold lam
  field_simp [hα]
  ring

lemma lam_ne_zero {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) : lam α ≠ 0 := by
  exact ne_of_gt (lam_pos hα0 hα1)

lemma lam_ne_zero' {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) : lam α ≠ 0 := lam_ne_zero hα0 hα1

/-- `(1-α) / λ(α) = 2α`. -/
lemma one_sub_div_lam {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) : (1 - α) / lam α = 2 * α := by
  unfold lam
  field_simp [ne_of_gt hα0, ne_of_gt (by linarith : 0 < 1 - α)]

/-- `(1-α) · (1/λ(α)) = 2α`. -/
lemma one_sub_mul_inv_lam {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) : (1 - α) * (1 / lam α) = 2 * α := by
  unfold lam
  field_simp [ne_of_gt hα0, ne_of_gt (by linarith : 0 < 1 - α)]

/-- `(1-α)·(-1/λ) + α = -α`. -/
lemma adj_value {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (1 - α) * (- (1 / lam α)) + α = -α := by
  have h := one_sub_mul_inv_lam hα0 hα1
  linarith

/-- The diagonal per-copy entry contributes `1`. -/
lemma diag_value {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) : (1 - α) * 1 + α = 1 := by
  linarith

end Submission
