import Mathlib
import Submission.Work.PSTAB.Defs

namespace Work.PSTAB

/-- Over a field in which `2 ≠ 0`, a `2 × 2` matrix `M` with `M * M = 1` and `det M = 1`
that is not the identity is `-1`.

This is the Cayley–Hamilton computation behind the uniqueness of the involution `-1` in
`SL₂` over a field of characteristic different from `2`: the minimal polynomial of such an
involution divides `(X - 1)(X + 1)`, hence the only non-trivial possibility with determinant
one is `-1`. -/
lemma matrix_fin_two_sq_eq_one_det_eq_one_eq_neg_one (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    {M : Matrix (Fin 2) (Fin 2) F} (hM : M * M = 1) (hM1 : M ≠ 1) (hd : M.det = 1) :
    M = -1 := by
  -- Cayley–Hamilton for a `2 × 2` matrix: `M * M - tr M • M + det M • 1 = 0`.
  have hCH : M * M - M.trace • M + M.det • 1 = 0 := by
    have h := Matrix.aeval_self_charpoly M
    rw [Matrix.charpoly_fin_two] at h
    simpa [Algebra.algebraMap_eq_smul_one, pow_two, smul_mul_assoc, mul_smul_comm] using h
  rw [hM, hd, one_smul] at hCH
  -- Hence `tr M • M = 1 + 1`.
  have htm : M.trace • M = 1 + 1 := by
    have h : (1 : Matrix (Fin 2) (Fin 2) F) + 1 - M.trace • M = 0 := by
      rw [← hCH]; abel
    exact (sub_eq_zero.mp h).symm
  -- The `(0,0)` entry of this identity shows that the trace is nonzero (as `2 ≠ 0`).
  have h00 : M.trace * M 0 0 = 1 + 1 := by
    have h := congrArg (fun N : Matrix (Fin 2) (Fin 2) F => N 0 0) htm
    simpa [Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply] using h
  have ht0 : M.trace ≠ 0 := by
    intro h
    rw [h, zero_mul] at h00
    have : (2 : F) = 0 := by
      rw [show (2 : F) = 1 + 1 by norm_num]
      exact h00.symm
    exact h2 this
  -- So `M` is a scalar matrix.
  set c : F := M.trace⁻¹ + M.trace⁻¹ with hc
  have h1 : M.trace⁻¹ • (M.trace • M) = M := by
    rw [smul_smul, inv_mul_cancel₀ ht0, one_smul]
  have hM' : M = c • 1 := by
    rw [← h1, htm, hc, smul_add, ← add_smul]
  -- Its scalar `c` satisfies `c * c = 1`.
  have hmul : (c • (1 : Matrix (Fin 2) (Fin 2) F)) * (c • 1) =
      (c * c) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [Matrix.smul_mul, one_mul, smul_smul]
  have hcc : c * c = 1 := by
    have h : (c • (1 : Matrix (Fin 2) (Fin 2) F)) * (c • 1) = 1 := by
      rw [← hM']; exact hM
    have h2' : (c * c) • (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [← hmul]; exact h
    have h3 := congrArg (fun N : Matrix (Fin 2) (Fin 2) F => N 0 0) h2'
    simpa [Matrix.smul_apply, Matrix.one_apply] using h3
  have hc1 : c ≠ 1 := by
    intro h
    exact hM1 (by rw [hM', h, one_smul])
  -- `(c - 1)(c + 1) = 0` with `c ≠ 1` forces `c = -1`.
  have hcfac : (c - 1) * (c + 1) = 0 := by
    have h : c * c - 1 = 0 := by rw [hcc]; ring
    rw [show (c - 1) * (c + 1) = c * c - 1 by ring]
    exact h
  rcases mul_eq_zero.mp hcfac with h | h
  · exact absurd (sub_eq_zero.mp h) hc1
  · rw [hM', eq_neg_of_add_eq_zero_left h, neg_one_smul]

theorem SL2UniqueInvolution {F : Type*} [Field F] {W : Type*} [AddCommGroup W] [Module F W]
    [Module.Finite F W] [Module.Free F W] (h2 : (2 : F) ≠ 0) (hdim : Module.finrank F W = 2)
    {z : Module.End F W} (hz : z * z = 1) (hz1 : z ≠ 1) (hdet : LinearMap.det z = 1) :
    z = -1 := by
  -- Choose a basis of the two-dimensional space `W`, and transport `z` to a `2 × 2` matrix.
  have hb : Module.Basis (Fin 2) F W := (Module.finBasis F W).reindex (finCongr hdim)
  let φ : (W →ₗ[F] W) ≃ₐ[F] Matrix (Fin 2) (Fin 2) F := LinearMap.toMatrixAlgEquiv hb
  have hMM : φ z * φ z = 1 := by rw [← map_mul, hz, map_one]
  have hMdet : (φ z).det = 1 := by
    change (LinearMap.toMatrix hb hb z).det = 1
    rw [LinearMap.det_toMatrix, hdet]
  have hM1 : φ z ≠ 1 := by
    intro h
    apply hz1
    have : φ z = φ 1 := by rw [h, map_one]
    exact φ.injective this
  have hM : φ z = -1 :=
    matrix_fin_two_sq_eq_one_det_eq_one_eq_neg_one F h2 hMM hM1 hMdet
  have : φ z = φ (-1) := by rw [hM, map_neg, map_one]
  exact φ.injective this

end Work.PSTAB
