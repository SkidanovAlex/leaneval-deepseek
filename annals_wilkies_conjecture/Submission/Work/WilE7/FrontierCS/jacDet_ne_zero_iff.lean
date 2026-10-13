import Mathlib

namespace Work.WilE7.FrontierCS

/-- The Jacobian matrix of `g` at `e`, built from the Fréchet derivative applied to the
standard basis vectors, is nonsingular if and only if that derivative is surjective.

Indeed, `M a l = fderiv ℝ g e (Pi.single l 1) a`, so `M.mulVec` agrees with `fderiv ℝ g e`
as a function; over the field `ℝ` a square matrix has nonzero determinant exactly when its
`mulVec` map is surjective, and a linear map on a finite-dimensional space is surjective
exactly when its range is everything. -/
theorem jacDet_ne_zero_iff {j : ℕ} (g : (Fin j → ℝ) → (Fin j → ℝ)) (e : Fin j → ℝ) :
    (Matrix.of fun (a l : Fin j) => fderiv ℝ g e (Pi.single l 1) a).det ≠ 0 ↔
      (fderiv ℝ g e).range = ⊤ := by
  set f : (Fin j → ℝ) →L[ℝ] (Fin j → ℝ) := fderiv ℝ g e with hf
  set M : Matrix (Fin j) (Fin j) ℝ := Matrix.of fun (a l : Fin j) => f (Pi.single l 1) a with hM
  -- `M` represents `f` in the standard basis: the two agree as functions.
  have hMmulVec : ∀ v : Fin j → ℝ,
      M.mulVec v = (f : (Fin j → ℝ) →ₗ[ℝ] (Fin j → ℝ)) v := by
    have hlin : M.mulVecLin = (f : (Fin j → ℝ) →ₗ[ℝ] (Fin j → ℝ)) := by
      refine (Pi.basisFun ℝ (Fin j)).ext ?_
      intro l
      rw [Matrix.mulVecLin_apply, Pi.basisFun_apply, Matrix.mulVec_single_one]
      rfl
    intro v
    rw [← Matrix.mulVecLin_apply, hlin]
  constructor
  · intro hdet
    have hU : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hdet)
    have hsurj : Function.Surjective M.mulVec := Matrix.mulVec_surjective_iff_isUnit.mpr hU
    refine LinearMap.range_eq_top.mpr ?_
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    exact ⟨x, by rw [← hMmulVec x]; exact hx⟩
  · intro hrange
    have hsurjf : Function.Surjective (f : (Fin j → ℝ) →ₗ[ℝ] (Fin j → ℝ)) :=
      LinearMap.range_eq_top.mp hrange
    have hsurj : Function.Surjective M.mulVec := fun y => by
      obtain ⟨x, hx⟩ := hsurjf y
      exact ⟨x, by rw [hMmulVec x]; exact hx⟩
    have hU : IsUnit M := Matrix.mulVec_surjective_iff_isUnit.mp hsurj
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det M).mp hU)

end Work.WilE7.FrontierCS
