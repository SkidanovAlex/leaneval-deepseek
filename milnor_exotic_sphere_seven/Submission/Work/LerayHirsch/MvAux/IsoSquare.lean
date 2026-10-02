import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# Kernels and ranges under an isomorphism of short complexes

If `f : M ⟶ N`, `f' : M' ⟶ N'` are morphisms of `ℤ`-modules and `e : M ≅ M'`, `e' : N ≅ N'` are
isomorphisms with `e ≫ f' = f ≫ e'`, then `f'` is the conjugate of `f` by these isomorphisms; in
particular the isomorphism carries the kernel of `f` onto the kernel of `f'`, and the isomorphism
`e'` carries the range of `f` onto the range of `f'`.

This is the tool with which the exactness of the Mayer–Vietoris ladder of
`Submission/Work/LerayHirsch/Mv_exact.lean` is transported between the two presentations of the
`P`-term (`∏_i (H(U_i) ⊕ H(V_i))` and `(∏_i H(U_i)) ⊕ (∏_i H(V_i))`).
-/

namespace Work.LerayHirsch.MvAux

open CategoryTheory CategoryTheory.Limits

variable {M M' N N' : ModuleCat ℤ}

/-- **The kernel is carried to the kernel** by an isomorphism of short complexes. -/
theorem map_ker_of_iso_square (e : M ≅ M') (e' : N ≅ N') (f : M ⟶ N) (f' : M' ⟶ N')
    (hsq : e.hom ≫ f' = f ≫ e'.hom) :
    Submodule.map (ModuleCat.Hom.hom e.hom) (ModuleCat.Hom.hom f).ker
      = (ModuleCat.Hom.hom f').ker := by
  have hfun : ∀ y, ModuleCat.Hom.hom f' (ModuleCat.Hom.hom e.hom y)
      = ModuleCat.Hom.hom e'.hom (ModuleCat.Hom.hom f y) := by
    intro y
    have h := congrArg (fun (φ : M ⟶ N') => ModuleCat.Hom.hom φ y) hsq
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
  have hinj : Function.Injective (ModuleCat.Hom.hom e'.hom) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    rw [LinearMap.mem_ker, hfun y, LinearMap.mem_ker.mp hy, map_zero]
  · intro x hx
    rw [LinearMap.mem_ker] at hx
    refine Submodule.mem_map.mpr ⟨ModuleCat.Hom.hom e.inv x, ?_, ?_⟩
    · rw [LinearMap.mem_ker]
      apply hinj
      rw [map_zero, ← hfun (ModuleCat.Hom.hom e.inv x), ModuleCat.hom_inv_apply e x, hx]
    · exact ModuleCat.hom_inv_apply e x

/-- **The range is carried to the range** by an isomorphism of short complexes. -/
theorem map_range_of_iso_square (e : M ≅ M') (e' : N ≅ N') (f : M ⟶ N) (f' : M' ⟶ N')
    (hsq : e.hom ≫ f' = f ≫ e'.hom) :
    Submodule.map (ModuleCat.Hom.hom e'.hom) (ModuleCat.Hom.hom f).range
      = (ModuleCat.Hom.hom f').range := by
  have hfun : ∀ y, ModuleCat.Hom.hom f' (ModuleCat.Hom.hom e.hom y)
      = ModuleCat.Hom.hom e'.hom (ModuleCat.Hom.hom f y) := by
    intro y
    have h := congrArg (fun (φ : M ⟶ N') => ModuleCat.Hom.hom φ y) hsq
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hy
    exact LinearMap.mem_range.mpr ⟨ModuleCat.Hom.hom e.hom z, by rw [hfun z]⟩
  · intro x hx
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
    refine Submodule.mem_map.mpr
      ⟨ModuleCat.Hom.hom f (ModuleCat.Hom.hom e.inv y),
        LinearMap.mem_range.mpr ⟨ModuleCat.Hom.hom e.inv y, rfl⟩, ?_⟩
    rw [← hfun (ModuleCat.Hom.hom e.inv y), ModuleCat.hom_inv_apply e y]

/-- The two statements above, bundled (this is the reviewed statement of this path). -/
theorem IsoSquare (e : M ≅ M') (e' : N ≅ N') (f : M ⟶ N) (f' : M' ⟶ N')
    (hsq : e.hom ≫ f' = f ≫ e'.hom) :
    (Submodule.map (ModuleCat.Hom.hom e.hom) (ModuleCat.Hom.hom f).ker
        = (ModuleCat.Hom.hom f').ker) ∧
    (Submodule.map (ModuleCat.Hom.hom e'.hom) (ModuleCat.Hom.hom f).range
        = (ModuleCat.Hom.hom f').range) :=
  ⟨map_ker_of_iso_square e e' f f' hsq, map_range_of_iso_square e e' f f' hsq⟩

end Work.LerayHirsch.MvAux
