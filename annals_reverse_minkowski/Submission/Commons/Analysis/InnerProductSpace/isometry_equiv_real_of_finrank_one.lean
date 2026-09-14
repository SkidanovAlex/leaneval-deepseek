import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Commons.Analysis.InnerProductSpace

open scoped Real Topology InnerProductSpace

/-- A one-dimensional real inner product space is linearly isometric to `ℝ`. -/
theorem isometry_equiv_real_of_finrank_one {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (h : Module.finrank ℝ E = 1) :
    Nonempty (E ≃ₗᵢ[ℝ] ℝ) := by
  -- An orthonormal basis with a single element `u`.
  let b : OrthonormalBasis (Fin 1) ℝ E := (stdOrthonormalBasis ℝ E).reindex (finCongr h)
  let u : E := b 0
  have hu_norm : ‖u‖ = 1 := b.norm_eq_one 0
  -- Every vector is its `u`-coordinate times `u`.
  have hdecomp : ∀ x : E, x = (inner ℝ u x) • u := by
    intro x
    have := b.sum_repr' x
    simpa [u] using this.symm
  -- The coordinate functional is a linear isometry onto `ℝ`.
  let f : E →ₗ[ℝ] ℝ :=
    { toFun := fun x => inner ℝ u x
      map_add' := by intro x y; rw [inner_add_right]
      map_smul' := by intro c x; simp [inner_smul_right] }
  have hf_norm : ∀ x, ‖f x‖ = ‖x‖ := by
    intro x
    have hfx : f x = inner ℝ u x := rfl
    rw [hfx]
    conv_rhs => rw [hdecomp x]
    rw [norm_smul, hu_norm, mul_one]
  -- Upgrade the linear isometry to a linear isometry equivalence using `finrank E = finrank ℝ`.
  refine ⟨({ toLinearMap := f, norm_map' := hf_norm } : E →ₗᵢ[ℝ] ℝ).toLinearIsometryEquiv ?_⟩
  rw [h, Module.finrank_self]

end Commons.Analysis.InnerProductSpace