import Mathlib

open scoped Matrix

namespace Work.RPB.B5

/-- **Seeley-type weights.**  Given `n + 1` pairwise distinct real nodes `s 0, …, s n`, there
are weights `c 0, …, c n` such that the moment conditions `∑ k, c k * (s k) ^ j = 1` hold for every
exponent `j ≤ n`.

The matrix `V j k = (s k) ^ j` is the transpose of the Vandermonde matrix of the nodes `s`, hence
invertible because the nodes are distinct (`Matrix.det_vandermonde_ne_zero_iff`).  The vector of
weights `c = V⁻¹ *ᵥ 1` is then an explicit solution of `V *ᵥ c = 1`, which is exactly the stated
system of equations (up to commutativity of multiplication in `ℝ`). -/
theorem existsSeeleyWeights (n : ℕ) (s : Fin (n + 1) → ℝ) (hs : Function.Injective s) :
    ∃ c : Fin (n + 1) → ℝ, ∀ j : Fin (n + 1), ∑ k : Fin (n + 1), c k * (s k) ^ (j : ℕ) = 1 := by
  set V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := Matrix.transpose (Matrix.vandermonde s) with hV
  have hdet : V.det ≠ 0 := by
    rw [hV, Matrix.det_transpose]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hs
  have hunit : IsUnit V.det := isUnit_iff_ne_zero.mpr hdet
  refine ⟨V⁻¹ *ᵥ (fun _ => (1 : ℝ)), fun j => ?_⟩
  have h1 : V *ᵥ (V⁻¹ *ᵥ (fun _ : Fin (n + 1) => (1 : ℝ))) = (fun _ => (1 : ℝ)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv V hunit, Matrix.one_mulVec]
  have h2 : (V *ᵥ (V⁻¹ *ᵥ (fun _ : Fin (n + 1) => (1 : ℝ)))) j = 1 := congrFun h1 j
  have hsum : ∑ k : Fin (n + 1), (V⁻¹ *ᵥ (fun _ : Fin (n + 1) => (1 : ℝ))) k * (s k) ^ (j : ℕ)
      = (V *ᵥ (V⁻¹ *ᵥ (fun _ : Fin (n + 1) => (1 : ℝ)))) j := by
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hV, Matrix.transpose_apply, Matrix.vandermonde_apply]
    ring
  rw [hsum, h2]

end Work.RPB.B5
