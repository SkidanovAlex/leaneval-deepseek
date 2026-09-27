import Mathlib
import Submission.Work.KT.D2.Winding

namespace Work.KT.D2

open Matrix

/-- If the disc family `toCM N M` of a matrix `M` over `Kpair ℝ²` is pointwise invertible, then
`M` is invertible.  Pointwise invertibility of `toCM N M` says exactly that `det M`, viewed as a
continuous function on the closed disc, never vanishes; since `det M` is constant on the boundary
circle, its pointwise inverse is again an element of `Kpair ℝ²`, so `det M` is a unit of
`Kpair ℝ²` and `M` is a unit of the matrix ring. -/
theorem isUnit_of_forall_isUnit_toCM (N : ℕ)
    (M : Matrix (Fin N) (Fin N) (Work.KT.Kpair (EuclideanSpace ℝ (Fin 2))))
    (h : ∀ x, IsUnit (Work.KT.D2.toCM N M x)) : IsUnit M := by
  rw [Matrix.isUnit_iff_isUnit_det]
  -- `d` is the underlying continuous function of the determinant.
  set d : C(Ball (EuclideanSpace ℝ (Fin 2)), ℂ) :=
    ((M.det : Work.KT.Kpair (EuclideanSpace ℝ (Fin 2))) :
      C(Ball (EuclideanSpace ℝ (Fin 2)), ℂ)) with hd
  -- pointwise invertibility of `toCM N M` means `d` vanishes nowhere.
  have hne : ∀ x : Ball (EuclideanSpace ℝ (Fin 2)), d x ≠ 0 := by
    intro x
    have hx : IsUnit ((toCM N M x).det) := (Matrix.isUnit_iff_isUnit_det _).mp (h x)
    rw [isUnit_iff_ne_zero] at hx
    have h1 : (evalAt x) M.det = (toCM N M x).det := by
      rw [RingHom.map_det]
      congr 1
    have h2 : d x = (evalAt x) M.det := rfl
    rw [h2, h1]
    exact hx
  -- the pointwise inverse is constant on the boundary, hence lies in `Kpair ℝ²`.
  have hconst : ∀ x ∈ bdry (EuclideanSpace ℝ (Fin 2)),
      ∀ x' ∈ bdry (EuclideanSpace ℝ (Fin 2)), d x = d x' := fun x hx x' hx' => (M.det).2 x hx x' hx'
  let g : C(Ball (EuclideanSpace ℝ (Fin 2)), ℂ) :=
    ⟨fun x => (d x)⁻¹, d.continuous.inv₀ hne⟩
  have g_apply : ∀ x, g x = (d x)⁻¹ := fun x => rfl
  have hgconst : ∀ x ∈ bdry (EuclideanSpace ℝ (Fin 2)),
      ∀ x' ∈ bdry (EuclideanSpace ℝ (Fin 2)), g x = g x' := by
    intro x hx x' hx'
    rw [g_apply, g_apply, hconst x hx x' hx']
  let gK : Work.KT.Kpair (EuclideanSpace ℝ (Fin 2)) := ⟨g, hgconst⟩
  have hd_eq : ((M.det : Work.KT.Kpair (EuclideanSpace ℝ (Fin 2))) :
      C(Ball (EuclideanSpace ℝ (Fin 2)), ℂ)) = d := rfl
  have hdg : M.det * gK = 1 := by
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, Subalgebra.coe_one]
    rw [hd_eq]
    ext x
    rw [ContinuousMap.mul_apply, ContinuousMap.one_apply, g_apply]
    exact mul_inv_cancel₀ (hne x)
  have hgd : gK * M.det = 1 := by
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, Subalgebra.coe_one]
    rw [hd_eq]
    ext x
    rw [ContinuousMap.mul_apply, ContinuousMap.one_apply, g_apply]
    exact inv_mul_cancel₀ (hne x)
  exact isUnit_iff_exists.mpr ⟨gK, hdg, hgd⟩

end Work.KT.D2
