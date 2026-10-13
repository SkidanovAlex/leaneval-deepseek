import Mathlib

namespace Work.WilE7.Aux

/-- If the `m × q` matrix `M` has full row rank `m`, then the continuous linear map
`(Fin q → ℝ) →L[ℝ] (Fin m → ℝ)` given by `x ↦ fun a => ∑ j, M a j * x j` is surjective;
its range is therefore `⊤`. -/
theorem rangePiEqTopOfRank {m q : ℕ} (M : Fin m → Fin q → ℝ)
    (hrank : (Matrix.of M).rank = m) :
    (ContinuousLinearMap.pi (fun a : Fin m =>
      (∑ j : Fin q, M a j • (ContinuousLinearMap.proj j : (Fin q → ℝ) →L[ℝ] ℝ)))).range
      = ⊤ := by
  -- Name the map under consideration.
  let f : (Fin q → ℝ) →L[ℝ] (Fin m → ℝ) := ContinuousLinearMap.pi (fun a : Fin m =>
      (∑ j : Fin q, M a j • (ContinuousLinearMap.proj j : (Fin q → ℝ) →L[ℝ] ℝ)))
  -- Its underlying linear map is matrix-vector multiplication by `M`.
  have hcoe : (f : (Fin q → ℝ) →ₗ[ℝ] (Fin m → ℝ)) = (Matrix.of M).mulVecLin := by
    ext v a
    simp [f, ContinuousLinearMap.coe_pi, LinearMap.pi_apply, Matrix.mulVec, dotProduct]
  show f.range = ⊤
  rw [show f.range = LinearMap.range (f : (Fin q → ℝ) →ₗ[ℝ] (Fin m → ℝ)) from rfl, hcoe]
  -- `Matrix.rank` is by definition the finrank of the range of `mulVecLin`, so full row
  -- rank means the range already has the dimension of the target.
  apply Submodule.eq_top_of_finrank_eq
  rw [Matrix.rank] at hrank
  rw [hrank]
  simp

end Work.WilE7.Aux
