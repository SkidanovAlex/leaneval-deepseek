import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness of `τ ↦ (Γ τ)⁻¹ *ᵥ p τ`

If a family of square matrices `Γ : ℝ → Matrix (Fin n) (Fin n) ℝ` is smooth componentwise at `t₀`
and `Γ t₀` is invertible, and `p : ℝ → Fin n → ℝ` is smooth componentwise at `t₀`, then every
component of `τ ↦ (Γ τ)⁻¹ *ᵥ (p τ)` is smooth at `t₀`.

The proof is the classical one: `A⁻¹ = (det A)⁻¹ • A.adjugate`, the determinant and every entry of
the adjugate are polynomials in the entries of the matrix (Leibniz formula resp. Cramer's rule), so
they are smooth as soon as the entries are; and `det (Γ t₀) ≠ 0` makes the scalar function
`τ ↦ (det (Γ τ))⁻¹` smooth at `t₀` by `ContDiffAt.inv`.
-/

namespace Work.Diff.GE

open scoped ContDiff BigOperators

section Helpers

/-- The determinant of a componentwise smooth family of matrices is smooth. -/
lemma contDiffAt_det_of_components {n : ℕ} {Γ : ℝ → Matrix (Fin n) (Fin n) ℝ} {t₀ : ℝ}
    (hΓ : ∀ i j, ContDiffAt ℝ (⊤ : ℕ∞) (fun τ : ℝ ↦ Γ τ i j) t₀) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun τ : ℝ ↦ (Γ τ).det) t₀ := by
  rw [show (fun τ : ℝ ↦ (Γ τ).det)
      = fun τ ↦ ∑ σ : Equiv.Perm (Fin n),
          ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, Γ τ (σ i) i from by
    funext τ; rw [Matrix.det_apply']]
  refine ContDiffAt.sum fun σ _ ↦ ?_
  refine ContDiffAt.mul contDiffAt_const ?_
  refine contDiffAt_prod fun i _ ↦ ?_
  exact hΓ (σ i) i

/-- Every entry of the adjugate of a componentwise smooth family of matrices is smooth. -/
lemma contDiffAt_adjugate_entry {n : ℕ} {Γ : ℝ → Matrix (Fin n) (Fin n) ℝ} {t₀ : ℝ}
    (hΓ : ∀ i j, ContDiffAt ℝ (⊤ : ℕ∞) (fun τ : ℝ ↦ Γ τ i j) t₀) (i j : Fin n) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun τ : ℝ ↦ (Γ τ).adjugate i j) t₀ := by
  have h : (fun τ : ℝ ↦ (Γ τ).adjugate i j)
      = fun τ ↦ ((Γ τ).updateRow j (Pi.single i 1)).det := by
    funext τ; rw [Matrix.adjugate_apply]
  rw [h]
  apply contDiffAt_det_of_components
  intro k l
  have h2 : (fun τ : ℝ ↦ (Γ τ).updateRow j (Pi.single i 1) k l)
      = fun τ ↦ if k = j then (Pi.single i 1 : Fin n → ℝ) l else Γ τ k l := by
    funext τ; rw [Matrix.updateRow_apply]
  rw [h2]
  by_cases hkj : k = j
  · simp only [hkj, ite_true]
    exact contDiffAt_const
  · simp only [hkj, ite_false]
    exact hΓ k l

/-- Every entry of the inverse of a componentwise smooth family of invertible matrices is smooth. -/
lemma contDiffAt_inv_entry_of_components {n : ℕ} {Γ : ℝ → Matrix (Fin n) (Fin n) ℝ} {t₀ : ℝ}
    (hΓ : ∀ i j, ContDiffAt ℝ (⊤ : ℕ∞) (fun τ : ℝ ↦ Γ τ i j) t₀) (hdet : (Γ t₀).det ≠ 0)
    (k i : Fin n) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun τ : ℝ ↦ (Γ τ)⁻¹ k i) t₀ := by
  have hdet' : ContDiffAt ℝ (⊤ : ℕ∞) (fun τ : ℝ ↦ (Γ τ).det) t₀ :=
    contDiffAt_det_of_components hΓ
  have hinv : ContDiffAt ℝ (⊤ : ℕ∞) (fun τ : ℝ ↦ ((Γ τ).det)⁻¹) t₀ := hdet'.inv hdet
  have hadj := contDiffAt_adjugate_entry hΓ k i
  have h : (fun τ : ℝ ↦ (Γ τ)⁻¹ k i)
      = fun τ ↦ ((Γ τ).det)⁻¹ * (Γ τ).adjugate k i := by
    funext τ
    rw [Matrix.inv_def, Ring.inverse_eq_inv]
    rfl
  rw [h]
  exact hinv.mul hadj

end Helpers

theorem matrix_mulVec_inv_contDiffAt {n : ℕ} {Γ : ℝ → Matrix (Fin n) (Fin n) ℝ} {p : ℝ → Fin n → ℝ}
    {t₀ : ℝ}
    (hΓ : ∀ i j, ContDiffAt ℝ (⊤ : ℕ∞) (fun τ : ℝ ↦ Γ τ i j) t₀)
    (hdet : (Γ t₀).det ≠ 0)
    (hp : ∀ k, ContDiffAt ℝ (⊤ : ℕ∞) (fun τ : ℝ ↦ p τ k) t₀) :
    ∀ k, ContDiffAt ℝ (⊤ : ℕ∞) (fun τ : ℝ ↦ Matrix.mulVec (Γ τ)⁻¹ (p τ) k) t₀ := by
  intro k
  have h : (fun τ : ℝ ↦ Matrix.mulVec (Γ τ)⁻¹ (p τ) k)
      = fun τ ↦ ∑ i : Fin n, (Γ τ)⁻¹ k i * p τ i := by
    funext τ; rw [Matrix.mulVec_apply_eq_sum]
  rw [h]
  refine ContDiffAt.sum fun i _ ↦ ?_
  exact (contDiffAt_inv_entry_of_components hΓ hdet k i).mul (hp i)

end Work.Diff.GE
