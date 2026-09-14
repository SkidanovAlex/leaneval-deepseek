import Mathlib
import Submission.Commons.Analysis.Fourier.sum_sq_le_const_sum_sq_mulVec
import Submission.Commons.LinearAlgebra.Matrix.det_gram_mul_relative_lower

open scoped Matrix BigOperators
open Matrix
set_option autoImplicit false

namespace Commons.LinearAlgebra.Matrix

theorem det_gram_mul_relative_lower_all {m : ℕ} (B₀ : Matrix (Fin m) (Fin m) ℝ)
    (hB : B₀.det ≠ 0) :
    ∃ (C : ℝ), 0 < C ∧
    ∀ (δ : ℝ), 0 ≤ δ → C * δ ≤ (1 : ℝ) / 2 →
    ∀ (A : Matrix (Fin m) (Fin m) ℝ),
      (∀ j i : Fin m, |A j i - B₀ j i| ≤ δ) →
      ∀ {r : ℕ}, ∀ U : Matrix (Fin m) (Fin r) ℤ,
        let Uc : Matrix (Fin m) (Fin r) ℝ := U.map (fun z : ℤ => (z : ℝ))
        (1 - C * δ) ^ (2 * r) * ((Uc.transpose * B₀.transpose * B₀ * Uc).det) ≤
          ((Uc.transpose * A.transpose * A * Uc).det) := by
  classical
  obtain ⟨c, hc0, hc⟩ := Commons.Analysis.Fourier.sum_sq_le_const_sum_sq_mulVec B₀ hB
  let C : ℝ := (m : ℝ) * (c + 1) + 1
  have hCpos : 0 < C := by
    dsimp [C]
    have h : 0 ≤ (m : ℝ) * (c + 1) := by
      exact mul_nonneg (Nat.cast_nonneg m) (by linarith)
    linarith
  refine ⟨C, hCpos, ?_⟩
  intro δ hδ0 hCδ A hA r U
  have hC0 : 0 ≤ C := le_of_lt hCpos
  have hε0 : 0 ≤ C * δ := mul_nonneg hC0 hδ0
  have hε1 : C * δ ≤ 1 := by linarith
  have hdiff : ∀ x : Fin m → ℝ,
      (∑ i : Fin m, (((A - B₀).mulVec x) i) ^ 2) ≤
        (C * δ) ^ 2 * (∑ i : Fin m, ((B₀.mulVec x) i) ^ 2) := by
    intro x
    dsimp [C]
    exact entrywise_diff_sq_le B₀ A x hc0 (hc x) hδ0 hA
  let ε : ℝ := C * δ
  have hquad : ∀ x : Fin m → ℝ,
      (1 - ε) ^ 2 * (x ⬝ᵥ ((B₀.transpose * B₀) *ᵥ x)) ≤
        x ⬝ᵥ ((A.transpose * A) *ᵥ x) := by
    exact quad_perturb_dot B₀ A ε hε0 hε1 (by
      intro x
      simpa [ε] using hdiff x)
  have hpsd : ((A.transpose * A) - (1 - ε) ^ 2 • (B₀.transpose * B₀)).PosSemidef :=
    gram_sub_psd B₀ A (1 - ε) hquad
  have hrel := det_gram_psd_relative B₀ A (1 - ε) (U.map (fun z : ℤ => (z : ℝ))) hpsd
  dsimp [ε] at hrel ⊢
  simpa using hrel

end Commons.LinearAlgebra.Matrix
