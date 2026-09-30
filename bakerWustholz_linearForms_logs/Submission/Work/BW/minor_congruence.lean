import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.wuestholzDefs
import Submission.Work.BW.exists_minor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open scoped BigOperators

/-- Dualising the generators: if `derH (w k) (u j) ≡ A j k • D j` modulo `𝔓` and `A` has rank `ℓ`,
then an invertible `ℓ × ℓ` minor `A.submatrix Ji Ki` produces coefficients `c` with
`Λ i := ∑ a, c i a • derH (w (Ki a))` satisfying `Λ i (u (Ji b)) ≡ D (Ji b) · δᵢ_b` modulo `𝔓`.
Take `c i a := (A.submatrix Ji Ki)⁻¹ a i` and use `(A.submatrix Ji Ki) * (A.submatrix Ji Ki)⁻¹ = 1`
(so `∑ a, c i a * A (Ji b) (Ki a) = δᵢ_b`). -/
theorem minor_congruence {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (𝔓 : Ideal (MR N)) {ℓ n : ℕ}
    (A : Matrix (Fin n) (Fin q) ℂ) (u D : Fin n → MR N) (hrank : A.rank = ℓ)
    (hder : ∀ (j : Fin n) (k : Fin q), derH (w k) (u j) - A j k • D j ∈ 𝔓) :
    ∃ (Ji : Fin ℓ ↪ Fin n) (Ki : Fin ℓ ↪ Fin q) (c : Fin ℓ → Fin ℓ → ℂ),
      ∀ i b, opOf (fun a : Fin ℓ => w (Ki a)) c i (u (Ji b))
          - D (Ji b) * (if i = b then 1 else 0) ∈ 𝔓 := by
  classical
  obtain ⟨Ji, Ki, hdet⟩ := exists_minor A hrank
  refine ⟨Ji, Ki, fun i a => (A.submatrix Ji Ki)⁻¹ a i, ?_⟩
  intro i b
  -- The scalar collapsing: `∑ k, (A.submatrix Ji Ki)⁻¹ k i * A (Ji b) (Ki k) = δᵢ_b`.
  have hsum : (∑ k, (A.submatrix Ji Ki)⁻¹ k i * A (Ji b) (Ki k))
      = (if i = b then (1 : ℂ) else 0) := by
    have h1 : (∑ k, (A.submatrix Ji Ki)⁻¹ k i * A (Ji b) (Ki k))
        = ((A.submatrix Ji Ki) * (A.submatrix Ji Ki)⁻¹) b i := by
      rw [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro k _
      rw [Matrix.submatrix_apply, mul_comm]
    rw [h1, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_apply]
    exact if_congr eq_comm rfl rfl
  -- The diagonal matrix `δᵢ_b` acts as multiplication by the scalar `δᵢ_b` on the algebra.
  have hif : D (Ji b) * (if i = b then 1 else 0)
      = (if i = b then (1 : ℂ) else 0) • D (Ji b) := by
    have hite : (if i = b then (1 : MR N) else 0)
        = algebraMap ℂ (MR N) (if i = b then (1 : ℂ) else 0) := by
      by_cases h : i = b <;> simp [h]
    rw [hite, Algebra.smul_def, mul_comm]
  -- Rewrite the operator as the sum of the (small) error terms plus the diagonal term.
  have key : opOf (fun a : Fin ℓ => w (Ki a)) (fun i a => (A.submatrix Ji Ki)⁻¹ a i)
        i (u (Ji b)) - D (Ji b) * (if i = b then 1 else 0)
      = ∑ k, (A.submatrix Ji Ki)⁻¹ k i •
          (derH (w (Ki k)) (u (Ji b)) - A (Ji b) (Ki k) • D (Ji b)) := by
    simp only [opOf]
    rw [hif, ← hsum, Finset.sum_smul]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [smul_sub, smul_smul]
  rw [key]
  -- Each summand lies in `𝔓`, so the sum does.
  apply Ideal.sum_mem
  intro k _
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_left _ _ (hder (Ji b) (Ki k))

end Work.BW
