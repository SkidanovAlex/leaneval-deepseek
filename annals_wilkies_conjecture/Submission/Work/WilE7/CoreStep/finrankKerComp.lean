import Mathlib

namespace Work.WilE7.CoreStep

/-- Dimension count for the composite `Ψ ∘ ι`, where `ι` is injective with range equal to
the kernel of `π`.

Decomposing: `ker (Ψ ∘ ι) = ι ⁻¹' (ker Ψ)`, which is linearly isomorphic to
`ker Ψ ⊓ range ι`. On the other hand, restricting `π` to `ker Ψ` and applying rank–nullity
gives `finrank (ker Ψ) = finrank (ker Ψ ⊓ ker π) + finrank (ker Ψ.map π)`. Since
`range ι = ker π` this yields the claim. -/
theorem finrankKerComp {U V W Z : Type*}
    [AddCommGroup U] [Module ℝ U] [FiniteDimensional ℝ U]
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup W] [Module ℝ W]
    [AddCommGroup Z] [Module ℝ Z]
    (ι : U →ₗ[ℝ] V) (hι : Function.Injective ι) (π : V →ₗ[ℝ] W) (Ψ : V →ₗ[ℝ] Z)
    (hr : ι.range = π.ker) :
    Module.finrank ℝ (Ψ.comp ι).ker
      = Module.finrank ℝ Ψ.ker - Module.finrank ℝ (Ψ.ker.map π) := by
  -- `ι` restricted to the preimage of `ker Ψ` maps it isomorphically onto `ker Ψ ⊓ range ι`.
  have h2 : Module.finrank ℝ (Ψ.ker.comap ι)
      = Module.finrank ℝ ↥(Ψ.ker ⊓ ι.range) := by
    have hinj : Function.Injective (ι.domRestrict (Ψ.ker.comap ι)) := by
      intro x y hxy
      exact Subtype.ext (hι hxy)
    rw [← LinearMap.finrank_range_of_inj hinj, LinearMap.range_domRestrict,
      Submodule.map_comap_eq, inf_comm]
  -- Rank–nullity for `π` restricted to `ker Ψ`.
  have hker : Module.finrank ℝ ((π.domRestrict Ψ.ker).ker)
      = Module.finrank ℝ ↥(Ψ.ker ⊓ π.ker) := by
    rw [LinearMap.ker_domRestrict,
      ← Submodule.finrank_map_subtype_eq Ψ.ker (Submodule.comap Ψ.ker.subtype π.ker),
      Submodule.map_comap_eq, Submodule.range_subtype]
  have h3 : Module.finrank ℝ (Ψ.ker.map π) + Module.finrank ℝ ↥(Ψ.ker ⊓ π.ker)
      = Module.finrank ℝ Ψ.ker := by
    have h := LinearMap.finrank_range_add_finrank_ker (π.domRestrict Ψ.ker)
    rw [LinearMap.range_domRestrict, hker] at h
    exact h
  have h4 : Module.finrank ℝ ↥(Ψ.ker ⊓ π.ker) + Module.finrank ℝ (Ψ.ker.map π)
      = Module.finrank ℝ Ψ.ker := by
    rw [add_comm]
    exact h3
  rw [LinearMap.ker_comp, h2, hr]
  exact Nat.eq_sub_of_add_eq h4

end Work.WilE7.CoreStep
