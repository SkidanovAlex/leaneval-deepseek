import Mathlib

namespace Work.KT.Fund

/-- Evaluating the determinant of a matrix of continuous functions at a point equals the
determinant of the pointwise evaluation of the matrix. -/
lemma det_map_apply {X : Type} [TopologicalSpace X] (n : ℕ)
    (M : Matrix (Fin n) (Fin n) C(X, ℂ)) (x : X) :
    (M.map (fun f : C(X, ℂ) => f x)).det = M.det x :=
  ((ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom.map_det M).symm

theorem isUnit_matrix_forall {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (n : ℕ)
    (M : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    IsUnit M ↔ ∀ x : X, IsUnit (M.map (fun f => f x)) := by
  rw [Matrix.isUnit_iff_isUnit_det, ContinuousMap.isUnit_iff_forall_ne_zero]
  constructor
  · intro h x
    rw [Matrix.isUnit_iff_isUnit_det, det_map_apply]
    exact isUnit_iff_ne_zero.mpr (h x)
  · intro h x
    have hx : IsUnit (M.map (fun f => f x)) := h x
    rw [Matrix.isUnit_iff_isUnit_det, det_map_apply] at hx
    exact hx.ne_zero

end Work.KT.Fund
