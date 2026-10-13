import Mathlib

open Matrix

namespace Work.WilE7.auxiliary

/-- The continuous linear map `x ↦ fun b => ∑ l, A b l * x l` (i.e. multiplication by the matrix
`A` acting on the right) has full range as soon as the matrix has maximal rank `m`.

Equivalently: the columns of `A` span `ℝ^m` when `A.rank = m`. -/
theorem piRangeTopOfRank {m q : ℕ} (A : Fin m → Fin q → ℝ)
    (hrank : (Matrix.of A).rank = m) :
    (ContinuousLinearMap.pi (fun b : Fin m =>
      (∑ l : Fin q, A b l • (ContinuousLinearMap.proj l : (Fin q → ℝ) →L[ℝ] ℝ)))).range
      = ⊤ := by
  -- Identify the continuous linear map with `A.mulVecLin`, whose range has dimension `A.rank`.
  have hlin : (ContinuousLinearMap.pi (fun b : Fin m =>
      (∑ l : Fin q, A b l • (ContinuousLinearMap.proj l : (Fin q → ℝ) →L[ℝ] ℝ))) :
        (Fin q → ℝ) →ₛₗ[RingHom.id ℝ] (Fin m → ℝ))
      = (Matrix.of A).mulVecLin := by
    apply LinearMap.ext
    intro x
    funext b
    simp only [ContinuousLinearMap.coe_pi, LinearMap.pi_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec, dotProduct, Matrix.of_apply]
    simp
  rw [hlin]
  -- A submodule of dimension equal to that of the whole space is everything.
  apply Submodule.eq_top_of_finrank_eq
  have h2 : Module.finrank ℝ (LinearMap.range ((Matrix.of A).mulVecLin)) = m := hrank
  rw [h2, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

end Work.WilE7.auxiliary
