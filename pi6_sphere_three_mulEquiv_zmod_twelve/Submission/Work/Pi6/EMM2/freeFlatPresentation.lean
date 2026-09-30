import Mathlib
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Free presentations with flat kernel

`Work.Pi6.EMM2.freeFlatPresentation` is the input of the universal coefficient argument for
arbitrary coefficient modules: every `ℤ`-module `M` sits in a short exact sequence
`0 → P → Q → M → 0` with `Q` a free `ℤ`-module and `P` flat.

Take `Q := ↥M →₀ ℤ` (the free module on the underlying set of `M`) with the evaluation
`Finsupp.linearCombination ℤ (id : ↥M → ↥M)`, which is surjective since `single m 1 ↦ m` and has
`P := ker` as its kernel.  `P` is a submodule of the free, hence torsion free, module `Q`, so it is
torsion free, and over the Dedekind domain `ℤ` torsion free implies flat
(`IsDedekindDomain.flat_iff_torsion_eq_bot`).
-/

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] Submodule.module
attribute [-instance] AddCommGroup.toIntModule

namespace Work.Pi6.EMM2

/-- **Every `ℤ`-module has a presentation by a free module with flat kernel.** -/
theorem freeFlatPresentation (M : ModuleCat ℤ) :
    ∃ S : ShortComplex (ModuleCat ℤ),
      S.X₃ = M ∧ S.ShortExact ∧ Module.Free ℤ ↥(S.X₂) ∧ Module.Flat ℤ ↥(S.X₁) := by
  let e : (↥M →₀ ℤ) →ₗ[ℤ] ↥M := Finsupp.linearCombination ℤ (id : ↥M → ↥M)
  have he : Function.Surjective e := fun m =>
    ⟨Finsupp.single m 1, by
      show Finsupp.linearCombination ℤ (id : ↥M → ↥M) (Finsupp.single m 1) = m
      rw [Finsupp.linearCombination_single]
      exact (inferInstance : DistribMulAction ℤ ↥M).one_smul m⟩
  refine ⟨ShortComplex.mk (ModuleCat.ofHom (LinearMap.ker e).subtype) (ModuleCat.ofHom e) ?_,
    rfl, ?_, ?_, ?_⟩
  · apply ModuleCat.hom_ext
    ext x
    simpa using (x : ↥(LinearMap.ker e)).2
  · refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · refine (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr ?_
      rw [LinearMap.exact_iff]
      simp only [ModuleCat.hom_ofHom, Submodule.range_subtype]
    · exact (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
    · exact (ModuleCat.epi_iff_surjective _).mpr he
  · infer_instance
  · infer_instance

end Work.Pi6.EMM2
