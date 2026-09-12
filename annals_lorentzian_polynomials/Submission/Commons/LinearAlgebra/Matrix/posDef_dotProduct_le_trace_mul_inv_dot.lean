import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.PosDef

open scoped Matrix

namespace Commons.LinearAlgebra.Matrix


/-- If `A` is a real Hermitian matrix with eigenvector unitary `U`, then the quadratic form
`w ⬝ᵥ A *ᵥ w` is the sum of the eigenvalues weighted by the squares of the coordinates of
`Uᵀ *ᵥ w`. -/
lemma dotProduct_mulVec_eq_sum_eigenvalues_sq {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (w : Fin n → ℝ) :
    w ⬝ᵥ A *ᵥ w =
      ∑ i, hA.eigenvalues i * (((hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)ᵀ *ᵥ w) i) ^ 2 := by
  classical
  let U : Matrix (Fin n) (Fin n) ℝ := hA.eigenvectorUnitary
  have hspec := hA.spectral_theorem (𝕜 := ℝ)
  nth_rewrite 1 [hspec]
  rw [Unitary.conjStarAlgAut_apply]
  simp [_root_.Matrix.star_eq_conjTranspose, _root_.Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [show w ⬝ᵥ ((U * _root_.Matrix.diagonal hA.eigenvalues * Uᵀ) *ᵥ w) =
      (Uᵀ *ᵥ w) ⬝ᵥ (_root_.Matrix.diagonal hA.eigenvalues *ᵥ (Uᵀ *ᵥ w)) from by
    calc
      w ⬝ᵥ ((U * _root_.Matrix.diagonal hA.eigenvalues * Uᵀ) *ᵥ w)
          = w ⬝ᵥ (U *ᵥ (_root_.Matrix.diagonal hA.eigenvalues *ᵥ (Uᵀ *ᵥ w))) := by
              rw [_root_.Matrix.mul_assoc]
              rw [← _root_.Matrix.mulVec_mulVec w U (_root_.Matrix.diagonal hA.eigenvalues * Uᵀ)]
              rw [← _root_.Matrix.mulVec_mulVec w (_root_.Matrix.diagonal hA.eigenvalues) Uᵀ]
      _ = (Uᵀ *ᵥ w) ⬝ᵥ (_root_.Matrix.diagonal hA.eigenvalues *ᵥ (Uᵀ *ᵥ w)) := by
              simpa using (_root_.Matrix.dotProduct_transpose_mulVec Uᵀ w
                (_root_.Matrix.diagonal hA.eigenvalues *ᵥ (Uᵀ *ᵥ w))).trans
                (dotProduct_comm (_root_.Matrix.diagonal hA.eigenvalues *ᵥ (Uᵀ *ᵥ w)) (Uᵀ *ᵥ w))]
  simp [U, _root_.Matrix.mulVec_diagonal, dotProduct, sq, mul_assoc, mul_comm, mul_left_comm]

/-- For an orthogonal matrix `U`, the standard dot product is invariant under `Uᵀ`. -/
lemma dotProduct_self_eq_sum_sq_mulVec_transpose {n : ℕ}
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : U * Uᵀ = 1) (w : Fin n → ℝ) :
    w ⬝ᵥ w = ∑ i, ((Uᵀ *ᵥ w) i) ^ 2 := by
  classical
  have hpres : w ⬝ᵥ w = (Uᵀ *ᵥ w) ⬝ᵥ (Uᵀ *ᵥ w) := by
    rw [_root_.Matrix.dotProduct_mulVec (Uᵀ *ᵥ w) Uᵀ w, _root_.Matrix.vecMul_mulVec Uᵀ Uᵀ w]
    simpa [hU, _root_.Matrix.vecMul_one]
  rw [hpres]
  simp [dotProduct, sq]

/-- Sedrakyan-type inequality for a finite positive sequence:
`∑ yᵢ² ≤ (∑ dᵢ) * (∑ yᵢ² / dᵢ)` when all `dᵢ` are positive. -/
lemma sum_sq_le_sum_pos_mul_sum_div {n : ℕ} (d : Fin n → ℝ) (hd : ∀ i, 0 < d i)
    (y : Fin n → ℝ) :
    ∑ i, y i ^ 2 ≤ (∑ i, d i) * ∑ i, y i ^ 2 / d i := by
  have hle_i : ∀ i, y i ^ 2 ≤ d i * ∑ j, y j ^ 2 / d j := by
    intro i
    have hterm : y i ^ 2 = d i * (y i ^ 2 / d i) := by
      exact (mul_div_cancel₀ (y i ^ 2) (ne_of_gt (hd i))).symm
    rw [hterm]
    have hle := Finset.single_le_sum
      (s := Finset.univ) (f := fun j => d i * (y j ^ 2 / d j))
      (fun j hj => mul_nonneg (le_of_lt (hd i))
        (div_nonneg (sq_nonneg (y j)) (le_of_lt (hd j))))
      (Finset.mem_univ i)
    simpa [Finset.mul_sum] using hle
  calc
    ∑ i, y i ^ 2 ≤ ∑ i, d i * ∑ j, y j ^ 2 / d j :=
      Finset.sum_le_sum (fun i hi => hle_i i)
    _ = (∑ i, d i) * ∑ j, y j ^ 2 / d j := by
      rw [Finset.sum_mul]

/-- If `E` is positive definite, then every eigenvalue of `E⁻¹` is at least `1 / trace E`. -/
lemma one_le_trace_mul_eigenvalue_inv {n : ℕ}
    (E : Matrix (Fin n) (Fin n) ℝ) (hE : E.PosDef) (i : Fin n) :
    1 ≤ E.trace * hE.inv.isHermitian.eigenvalues i := by
  classical
  let ν : Fin n → ℝ := hE.inv.isHermitian.eigenvalues
  let lam : Fin n → ℝ := hE.isHermitian.eigenvalues
  have hν_pos : 0 < ν i := by
    simpa [ν] using hE.inv.eigenvalues_pos i
  have htrace : E.trace = ∑ k, lam k := by
    simpa [lam] using hE.isHermitian.trace_eq_sum_eigenvalues
  obtain ⟨j, hj⟩ : ∃ j, lam j = (ν i)⁻¹ := by
    let u : (Matrix (Fin n) (Fin n) ℝ)ˣ := hE.isUnit.unit
    have hEval : (u : Matrix (Fin n) (Fin n) ℝ) = E := hE.isUnit.unit_spec
    have hν_mem_Einv : ν i ∈ spectrum ℝ (E⁻¹) := by
      simpa [ν] using hE.inv.isHermitian.eigenvalues_mem_spectrum_real i
    have hν_mem_u_inv : ν i ∈ spectrum ℝ (↑u⁻¹ : Matrix (Fin n) (Fin n) ℝ) := by
      simpa [u, hEval] using hν_mem_Einv
    have hν_inv_mem_u : (ν i)⁻¹ ∈ spectrum ℝ (u : Matrix (Fin n) (Fin n) ℝ) :=
      spectrum.inv₀_mem (R := ℝ) (A := Matrix (Fin n) (Fin n) ℝ) (r := ν i) (a := u) hν_mem_u_inv
    have hν_inv_mem_E : (ν i)⁻¹ ∈ spectrum ℝ E := by
      simpa [hEval] using hν_inv_mem_u
    have hrange := hE.isHermitian.spectrum_real_eq_range_eigenvalues
    rw [hrange] at hν_inv_mem_E
    rcases hν_inv_mem_E with ⟨j, hj⟩
    exact ⟨j, by simpa [lam] using hj⟩
  have hlam_pos : ∀ k, 0 < lam k := by
    intro k
    simpa [lam] using hE.eigenvalues_pos k
  have hj_le : lam j ≤ ∑ k, lam k := by
    exact Finset.single_le_sum (s := Finset.univ) (f := lam)
      (fun k hk => le_of_lt (hlam_pos k)) (Finset.mem_univ j)
  have hinv_le : (ν i)⁻¹ ≤ E.trace := by
    rw [hj.symm]
    rwa [htrace]
  exact (inv_le_iff_one_le_mul₀ hν_pos).mp hinv_le

theorem posDef_dotProduct_le_trace_mul_inv_dot {n : ℕ}
    (E : Matrix (Fin n) (Fin n) ℝ) (hE : E.PosDef) (w : Fin n → ℝ) :
    w ⬝ᵥ w ≤ E.trace * (w ⬝ᵥ E⁻¹ *ᵥ w) := by
  classical
  let A : Matrix (Fin n) (Fin n) ℝ := E⁻¹
  have hA : A.PosDef := by
    simpa [A] using hE.inv
  let U : Matrix (Fin n) (Fin n) ℝ := hA.isHermitian.eigenvectorUnitary
  have hUU : U * Uᵀ = 1 := by
    simpa [U, _root_.Matrix.star_eq_conjTranspose, _root_.Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Unitary.coe_mul_star_self hA.isHermitian.eigenvectorUnitary)
  have hquad_ident : w ⬝ᵥ w = ∑ i, ((Uᵀ *ᵥ w) i) ^ 2 := by
    simpa [U] using dotProduct_self_eq_sum_sq_mulVec_transpose U hUU w
  have hquad_inv : w ⬝ᵥ A *ᵥ w =
      ∑ i, hA.isHermitian.eigenvalues i * ((Uᵀ *ᵥ w) i) ^ 2 := by
    simpa [U] using dotProduct_mulVec_eq_sum_eigenvalues_sq A hA.isHermitian w
  have hb : ∀ i, 1 ≤ E.trace * hA.isHermitian.eigenvalues i := by
    intro i
    simpa [A] using one_le_trace_mul_eigenvalue_inv E hE i
  calc
    w ⬝ᵥ w = ∑ i, ((Uᵀ *ᵥ w) i) ^ 2 := hquad_ident
    _ ≤ ∑ i, (E.trace * hA.isHermitian.eigenvalues i) * ((Uᵀ *ᵥ w) i) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        simpa using mul_le_mul_of_nonneg_right (hb i) (sq_nonneg _)
    _ = E.trace * ∑ i, hA.isHermitian.eigenvalues i * ((Uᵀ *ᵥ w) i) ^ 2 := by
        calc
          ∑ i, (E.trace * hA.isHermitian.eigenvalues i) * ((Uᵀ *ᵥ w) i) ^ 2
              = ∑ i, E.trace * (hA.isHermitian.eigenvalues i * ((Uᵀ *ᵥ w) i) ^ 2) := by
                  simp [mul_assoc]
          _ = E.trace * ∑ i, hA.isHermitian.eigenvalues i * ((Uᵀ *ᵥ w) i) ^ 2 := by
                  rw [Finset.mul_sum]
    _ = E.trace * (w ⬝ᵥ A *ᵥ w) := by rw [hquad_inv]
    _ = E.trace * (w ⬝ᵥ E⁻¹ *ᵥ w) := by simp [A]

end Commons.LinearAlgebra.Matrix