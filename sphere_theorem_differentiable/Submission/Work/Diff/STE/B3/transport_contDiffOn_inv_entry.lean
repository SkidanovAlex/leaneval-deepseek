import Mathlib
import Submission.Work.Diff.STE.B3.Comp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness of the entries of the inverse of a smooth invertible matrix family

`transport_contDiffOn_inv_entry`: if every component `z ↦ X z i j` of a matrix family
`X : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ` is `C^∞`, then every entry of the inverse
`z ↦ ((X z)⁻¹) i j` is `C^∞` on the open set `{z | (X z).det ≠ 0}`.

The proof is Cramer's rule, `A⁻¹ = (det A)⁻¹ • A.adjugate` (Mathlib's `Matrix.inv_def`): every entry
of the adjugate is a determinant of a matrix whose `j`-th row has been replaced by a constant basis
vector (`Matrix.adjugate_apply`), the determinant is a finite sum of finite products of the entries
(Leibniz's formula, `Matrix.det_apply'`), so both `z ↦ (X z).det` and `z ↦ (X z).adjugate i j` are
`C^∞` as soon as the components of `X` are; and inversion of a scalar is `C^∞` away from `0`
(`ContDiffOn.inv`).
-/

namespace Work.Diff.STE.B3

open scoped ContDiff BigOperators

/-- The determinant of a componentwise smooth matrix family is smooth. -/
private lemma contDiff_det_of_components {n : ℕ} {Y : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hY : ∀ p q, ContDiff ℝ (⊤ : ℕ∞) (fun z => Y z p q)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => (Y z).det) := by
  classical
  rw [show (fun z : Fin n → ℝ => (Y z).det)
      = fun z => ∑ σ : Equiv.Perm (Fin n),
          (↑↑(Equiv.Perm.sign σ) : ℝ) * ∏ k, Y z (σ k) k from by
    funext z; rw [Matrix.det_apply']]
  exact ContDiff.sum (fun σ _ => contDiff_const.mul (contDiff_prod (fun k _ => hY (σ k) k)))

/-- Replacing the `q`-th row of a componentwise smooth matrix family by a constant row gives a
componentwise smooth matrix family. -/
private lemma contDiff_updateRow_of_components {n : ℕ}
    {Y : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hY : ∀ p q, ContDiff ℝ (⊤ : ℕ∞) (fun z => Y z p q)) (q : Fin n) (b : Fin n → ℝ) :
    ∀ k l, ContDiff ℝ (⊤ : ℕ∞) (fun z => (Y z).updateRow q b k l) := by
  intro k l
  have h2 : (fun z : Fin n → ℝ => (Y z).updateRow q b k l)
      = fun z => if k = q then b l else Y z k l := by
    funext z; rw [Matrix.updateRow_apply]
  rw [h2]
  by_cases hk : k = q
  · simp only [hk, ite_true]
    exact contDiff_const
  · simp only [hk, ite_false]
    exact hY k l

/-- Every entry of the adjugate of a componentwise smooth matrix family is smooth. -/
private lemma contDiff_adjugate_entry_of_components {n : ℕ}
    {Y : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hY : ∀ p q, ContDiff ℝ (⊤ : ℕ∞) (fun z => Y z p q)) (p q : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => (Y z).adjugate p q) := by
  classical
  have hrw : (fun z : Fin n → ℝ => (Y z).adjugate p q)
      = fun z => ((Y z).updateRow q (Pi.single p 1)).det := by
    funext z; rw [Matrix.adjugate_apply]
  rw [hrw]
  exact contDiff_det_of_components (contDiff_updateRow_of_components hY q (Pi.single p 1))

theorem transport_contDiffOn_inv_entry {n : ℕ} (X : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hX : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun z => X z i j)) (i j : Fin n) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => ((X z)⁻¹) i j) {z | (X z).det ≠ 0} := by
  classical
  have hdet : ContDiff ℝ (⊤ : ℕ∞) (fun z => (X z).det) := contDiff_det_of_components hX
  have hdetinv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => ((X z).det)⁻¹) {z | (X z).det ≠ 0} :=
    hdet.contDiffOn.inv (fun z hz => hz)
  refine ContDiffOn.congr
    (hdetinv.mul (contDiff_adjugate_entry_of_components hX i j).contDiffOn) ?_
  intro z hz
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]
  congr 1
  exact congrFun Ring.inverse_eq_inv' _

end Work.Diff.STE.B3
