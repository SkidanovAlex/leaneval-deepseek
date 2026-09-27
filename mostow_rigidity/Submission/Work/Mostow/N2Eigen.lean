import Mathlib
import Submission.Work.Mostow.BCGDefs
import Submission.Work.Mostow.HEigen

/-!
# `HEigenId` — the eigenvalue decomposition of `H`, with the "all eigenvalues equal" case

This is `HEigen` with one extra conjunct: if all the eigenvalues of `H` are `1/n` then `H` is the
scalar operator `(1/n) • 1`.  It is the linear-algebra input used in the equality case of the
Besson–Courtois–Gallot Jacobian inequality (area N2).
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

theorem HEigenId (n : ℕ) (H : Submission.Mostow.E n →L[ℝ] Submission.Mostow.E n)
    (hsym : ∀ v w : Submission.Mostow.E n, inner ℝ (H v) w = inner ℝ v (H w))
    (hpsd : ∀ v : Submission.Mostow.E n, 0 ≤ inner ℝ (H v) v)
    (hpd : ∀ v : Submission.Mostow.E n, v ≠ 0 → 0 < inner ℝ v v - inner ℝ (H v) v)
    (htr : LinearMap.trace ℝ (Submission.Mostow.E n) H.toLinearMap = 1) :
    ∃ lam : Fin n → ℝ,
      (∀ i, 0 ≤ lam i) ∧ (∀ i, lam i < 1) ∧ (∑ i, lam i = 1) ∧
      (1 - H.toLinearMap).det = ∏ i, (1 - lam i) ∧ H.toLinearMap.det = ∏ i, lam i ∧
      ((∀ i, lam i = 1 / (n : ℝ)) → H = (1 / (n : ℝ)) • 1) := by
  classical
  have hT : H.toLinearMap.IsSymmetric := hsym
  have hn : Module.finrank ℝ (Submission.Mostow.E n) = n := finrank_euclideanSpace_fin
  refine ⟨hT.eigenvalues hn, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    refine eigenvalue_nonneg_of_nonneg (hT.hasEigenvalue_eigenvalues hn i) (fun x => ?_)
    simpa [real_inner_comm] using hpsd x
  · intro i
    have hvne : hT.eigenvectorBasis hn i ≠ 0 := (hT.eigenvectorBasis hn).toBasis.ne_zero i
    have hpos : 0 < inner ℝ (hT.eigenvectorBasis hn i) (hT.eigenvectorBasis hn i) :=
      real_inner_self_pos.mpr hvne
    have hev := hT.apply_eigenvectorBasis hn i
    have hg : inner ℝ (H (hT.eigenvectorBasis hn i)) (hT.eigenvectorBasis hn i)
        = hT.eigenvalues hn i * inner ℝ (hT.eigenvectorBasis hn i) (hT.eigenvectorBasis hn i) := by
      rw [show H (hT.eigenvectorBasis hn i) = H.toLinearMap (hT.eigenvectorBasis hn i) from rfl,
        hev, inner_smul_left]
      simp
    have h2 : 0 < inner ℝ (hT.eigenvectorBasis hn i) (hT.eigenvectorBasis hn i)
        - hT.eigenvalues hn i * inner ℝ (hT.eigenvectorBasis hn i) (hT.eigenvectorBasis hn i) := by
      have hh := hpd (hT.eigenvectorBasis hn i) hvne
      rwa [hg] at hh
    have h3 : (1 - hT.eigenvalues hn i) * inner ℝ (hT.eigenvectorBasis hn i) (hT.eigenvectorBasis hn i)
        = inner ℝ (hT.eigenvectorBasis hn i) (hT.eigenvectorBasis hn i)
          - hT.eigenvalues hn i * inner ℝ (hT.eigenvectorBasis hn i) (hT.eigenvectorBasis hn i) := by
      ring
    have h4 : 0 < 1 - hT.eigenvalues hn i :=
      (mul_pos_iff_of_pos_right hpos).mp (h3 ▸ h2)
    linarith
  · have h := hT.trace_eq_sum_eigenvalues hn
    rw [htr] at h
    simpa using h.symm
  · have hM : LinearMap.toMatrix ((hT.eigenvectorBasis hn).toBasis) ((hT.eigenvectorBasis hn).toBasis) (1 - H.toLinearMap)
        = Matrix.diagonal (fun i => 1 - hT.eigenvalues hn i) := by
      simp only [map_sub, LinearMap.toMatrix_one, hT.toMatrix_eigenvectorBasis hn, ← Matrix.diagonal_one,
        Matrix.diagonal_sub, Function.comp_apply]
      simp
    rw [← LinearMap.det_toMatrix ((hT.eigenvectorBasis hn).toBasis) (1 - H.toLinearMap), hM, Matrix.det_diagonal]
  · have h := hT.det_eq_prod_eigenvalues hn
    simpa using h
  · intro hall
    have hM : (LinearMap.toMatrix ((hT.eigenvectorBasis hn).toBasis) ((hT.eigenvectorBasis hn).toBasis)) H.toLinearMap
        = Matrix.diagonal (fun _ : Fin n => (1 / (n : ℝ) : ℝ)) := by
      rw [hT.toMatrix_eigenvectorBasis hn]
      ext i j
      rw [Matrix.diagonal_apply, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij; simp [hall i]
      · simp [hij]
    have hM2 : (LinearMap.toMatrix ((hT.eigenvectorBasis hn).toBasis) ((hT.eigenvectorBasis hn).toBasis))
        ((1 / (n : ℝ)) • (1 : Submission.Mostow.E n →L[ℝ] Submission.Mostow.E n)).toLinearMap
        = Matrix.diagonal (fun _ : Fin n => (1 / (n : ℝ) : ℝ)) := by
      rw [ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.toLinearMap_one, map_smul,
        LinearMap.toMatrix_one]
      exact Matrix.smul_one_eq_diagonal (1 / (n : ℝ))
    exact ContinuousLinearMap.coe_injective
      ((LinearMap.toMatrix ((hT.eigenvectorBasis hn).toBasis) ((hT.eigenvectorBasis hn).toBasis)).injective (by rw [hM, hM2]))

end Work.Mostow
