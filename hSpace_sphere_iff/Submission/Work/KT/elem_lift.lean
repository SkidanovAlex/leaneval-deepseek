import Mathlib
import Submission.Work.KT.ClutchGeom

namespace Work.KT

open Matrix

noncomputable section

/-- Every elementary (`i ≠ j`) matrix over the boundary sphere `C(Sph V, ℂ)` lifts along the
restriction `restRho` to an invertible matrix over the ball `C(Ball V, ℂ)`: lift the function
`a` to some `ã` with `ã|_{Sph V} = a` (Tietze) and use the transvection `1 + Matrix.single i j ã`,
which is invertible with inverse `1 - Matrix.single i j ã`. -/
theorem elem_lift (V : Type) [NormedAddCommGroup V] {m : ℕ} (i j : Fin m) (hij : i ≠ j)
    (a : C(Sph V, ℂ)) :
    ∃ E : (Matrix (Fin m) (Fin m) C(Ball V, ℂ))ˣ,
      RingHom.mapMatrix (Work.KT.restRho V) (↑E : Matrix (Fin m) (Fin m) C(Ball V, ℂ)) =
        1 + Matrix.single i j a := by
  -- The boundary sphere sits inside the ball as the closed set `bdry V`; identify it with `Sph V`.
  let ψ : C(bdry V, Sph V) :=
    ⟨fun y => ⟨((y : Ball V) : V), mem_sphere_zero_iff_norm.mpr y.2⟩, by fun_prop⟩
  have hcls : IsClosed (bdry V) := by
    rw [show bdry V = Subtype.val ⁻¹' Metric.sphere (0 : V) 1 from by
      ext y; simp [bdry]]
    exact Metric.isClosed_sphere.preimage continuous_subtype_val
  -- Tietze: lift `a` from the boundary sphere to the whole ball.
  obtain ⟨g, hg⟩ := ContinuousMap.exists_restrict_eq (Y := ℂ) (s := bdry V) hcls (a.comp ψ)
  have hkey : ∀ x : Sph V, g (sphToBall V x) = a x := by
    intro x
    have hx : sphToBall V x ∈ bdry V := by
      simp [bdry, sphToBall_apply]
    have h2 := congrFun (congrArg DFunLike.coe hg) ⟨sphToBall V x, hx⟩
    simp only [ContinuousMap.restrict_apply, ContinuousMap.comp_apply] at h2
    rw [h2]
    exact congrArg a (Subtype.ext (by simp [ψ, sphToBall_apply]))
  have hgrest : restRho V g = a := by
    ext x; simpa [restRho_apply] using hkey x
  -- The transvection `1 + single i j g` is invertible with inverse `1 - single i j g`.
  have hN2 : Matrix.single i j g * Matrix.single i j g = 0 := by
    rw [Matrix.single_mul_single_of_ne]; exact fun h => hij h.symm
  have h1 : (1 + Matrix.single i j g) * (1 - Matrix.single i j g) = 1 := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hN2]; simp
  have h2 : (1 - Matrix.single i j g) * (1 + Matrix.single i j g) = 1 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, hN2]; simp
  refine ⟨⟨1 + Matrix.single i j g, 1 - Matrix.single i j g, h1, h2⟩, ?_⟩
  have hmap : RingHom.mapMatrix (restRho V) (Matrix.single i j g) = Matrix.single i j a := by
    rw [RingHom.mapMatrix_apply, Matrix.map_single, hgrest]
  simp only [hmap, map_add, map_one]

end

end Work.KT
