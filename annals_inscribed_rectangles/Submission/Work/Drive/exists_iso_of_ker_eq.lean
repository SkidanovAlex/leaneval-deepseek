import Mathlib

namespace Work.Drive

/-- Two surjective linear maps `ℝ⁴ → ℝ³` with the same kernel differ by a linear automorphism
of the target: the descent of `f` through `g`.

The proof: `hker` forces `g` to be surjective as well (rank–nullity), and then both `f` and `g`
factor as `M ⧸ ker ≃ N`, which are glued by `Submodule.quotEquivOfEq`. -/
theorem exists_iso_of_ker_eq
    (f g : EuclideanSpace ℝ (Fin 4) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3))
    (hker : f.ker = g.ker) (hf : Function.Surjective f) :
    ∃ ψ : EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3),
      f = ψ.toLinearMap.comp g := by
  -- `g` is surjective too, by rank–nullity applied to `f` and `g`.
  have hg : Function.Surjective g := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    have h1 : Module.finrank ℝ (LinearMap.range f) + Module.finrank ℝ (LinearMap.ker g)
        = Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) := by
      rw [← hker]
      exact f.finrank_range_add_finrank_ker
    have h2 := g.finrank_range_add_finrank_ker
    have h3 : Module.finrank ℝ (LinearMap.range f) = Module.finrank ℝ (LinearMap.range g) := by
      omega
    have h4 : Module.finrank ℝ (LinearMap.range f)
        = Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by
      rw [LinearMap.range_eq_top.mpr hf, finrank_top]
    rw [← h3, h4]
  -- Both `f` and `g` identify the target with the quotient by their common kernel.
  refine ⟨(g.quotKerEquivOfSurjective hg).symm.trans
      ((Submodule.quotEquivOfEq _ _ hker.symm).trans (f.quotKerEquivOfSurjective hf)), ?_⟩
  ext x
  simp only [LinearEquiv.trans_apply, LinearMap.quotKerEquivOfSurjective_symm_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap]

end Work.Drive
