import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Freeness (and flatness) over `ULift ℤ` versus over `ℤ`

For a type `M` carrying both a `ℤ`-module structure and a `ULift ℤ`-module structure which agree
on the nose (`(ULift.up k) • m = k • m`), we show that `M` is free (resp. flat) over `ULift ℤ`
as soon as it is free over `ℤ`.

This is the coefficient-ring transfer used when `Rep Coeff G` (with `Coeff = ULift ℤ`) is
forgotten to `ModuleCat Coeff`: the underlying `ℤ`-lattice structure of a `Rep Coeff G` is
automatically a free `ULift ℤ`-module, hence flat, which is what makes `- ⊗ R` exact.

The `ULift.*` instances are locally pushed down in priority so that the *ambient* module
structures (the ones appearing in the hypotheses) win the instance search, cf. the note in
`E2_STATUS.md`.
-/

attribute [local instance 1] ULift.smulLeft ULift.smulZeroClass ULift.mulAction ULift.distribSMul
  ULift.distribMulAction ULift.smulWithZero ULift.mulActionWithZero ULift.module ZSMul.toSMul

namespace Work.SSGRoute

/-- If the `ULift ℤ`-module structure on `M` agrees with the `ℤ`-module structure pointwise,
then `M` is free over `ℤ` as soon as it is free over `ULift ℤ`. -/
theorem module_free_ulift_int {M : Type} [AddCommGroup M] [Module ℤ M] [Module (ULift.{0} ℤ) M]
    (h : ∀ (s : ULift.{0} ℤ) (m : M), s • m = s.down • m) (hM : Module.Free ℤ M) :
    Module.Free (ULift.{0} ℤ) M := by
  obtain ⟨ι, b⟩ := Module.Free.exists_basis ℤ M
  refine Module.Free.mk ⟨ι, Module.Basis.mk (v := b) ?_ ?_⟩
  · rw [linearIndependent_iff']
    intro s g hg i hi
    have hs : (∑ j ∈ s, (g j).down • b j) = 0 := by
      rw [← hg]
      exact Finset.sum_congr rfl (fun j _ => (h (g j) (b j)).symm)
    have := (linearIndependent_iff'.mp b.linearIndependent) s (fun j => (g j).down) hs i hi
    exact ULift.down_injective (by simpa using this)
  · rw [top_le_iff, Submodule.eq_top_iff']
    intro x
    have hx : x ∈ Submodule.span ℤ (Set.range b) := by
      rw [b.span_eq]; trivial
    exact Submodule.span_induction (p := fun y _ => y ∈ Submodule.span (ULift.{0} ℤ) (Set.range b))
      (fun y hy => Submodule.subset_span hy) (Submodule.zero_mem _)
      (fun y z _ _ hy hz => Submodule.add_mem _ hy hz)
      (fun c y _ hy => by
        have hc : (ULift.up c) • y ∈ Submodule.span (ULift.{0} ℤ) (Set.range b) :=
          Submodule.smul_mem _ (ULift.up c) hy
        rwa [h (ULift.up c) y] at hc) hx

/-- Flatness transfer: `M` flat over `ℤ` and the `ULift ℤ`-structure agreeing pointwise with
the `ℤ`-structure imply `M` flat over `ULift ℤ`. -/
theorem module_flat_ulift_int {M : Type} [AddCommGroup M] [Module ℤ M] [Module (ULift.{0} ℤ) M]
    (h : ∀ (s : ULift.{0} ℤ) (m : M), s • m = s.down • m) (hM : Module.Free ℤ M) :
    Module.Flat (ULift.{0} ℤ) M := by
  haveI : Module.Free (ULift.{0} ℤ) M := module_free_ulift_int h hM
  exact Module.Flat.of_free

end Work.SSGRoute
