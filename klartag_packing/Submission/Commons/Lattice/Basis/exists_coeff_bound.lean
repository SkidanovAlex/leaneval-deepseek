import Mathlib.Algebra.Module.ZLattice.Basic

namespace Commons.Lattice.Basis

/-- For a `ℤ`-lattice `Λ` in `ℝ^d` with a chosen `ℤ`-basis `b`, the basis coordinate
functionals are bounded by a constant multiple of the ambient Euclidean norm. -/
theorem exists_coeff_bound {d : ℕ} (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d)))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (b : Module.Basis (Fin d) ℤ Λ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (x : Λ) (i : Fin d),
      |((b.repr x) i : ℝ)| ≤ K * ‖(x : EuclideanSpace ℝ (Fin d))‖ := by
  -- A `ℤ`-basis of a `ℤ`-lattice is also an `ℝ`-basis of the ambient space.
  let bℝ : Module.Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) :=
    Module.Basis.ofZLatticeBasis ℝ Λ b
  -- The basis coordinate map, viewed as an `ℝ`-linear map to `Fin d → ℝ`.
  let f : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] (Fin d → ℝ) :=
    (Finsupp.linearEquivFunOnFinite ℝ ℝ (Fin d)).toLinearMap.comp bℝ.repr.toLinearMap
  -- It is continuous because the domain is finite-dimensional, hence bounded.
  obtain ⟨C, hCpos, hC⟩ := SemilinearMapClass.bound_of_continuous f
    (LinearMap.continuous_of_finiteDimensional f)
  refine ⟨C, hCpos, ?_⟩
  intro x i
  have hxi : f (x : EuclideanSpace ℝ (Fin d)) i = ((b.repr x) i : ℝ) := by
    change ((Module.Basis.ofZLatticeBasis ℝ Λ b).repr
      (x : EuclideanSpace ℝ (Fin d))) i = ((b.repr x) i : ℝ)
    rw [Module.Basis.ofZLatticeBasis_repr_apply]
  rw [← hxi]
  calc |f (x : EuclideanSpace ℝ (Fin d)) i| = ‖f (x : EuclideanSpace ℝ (Fin d)) i‖ := by
        rw [Real.norm_eq_abs]
    _ ≤ ‖f (x : EuclideanSpace ℝ (Fin d))‖ := norm_le_pi_norm _ i
    _ ≤ C * ‖(x : EuclideanSpace ℝ (Fin d))‖ := hC _

end Commons.Lattice.Basis