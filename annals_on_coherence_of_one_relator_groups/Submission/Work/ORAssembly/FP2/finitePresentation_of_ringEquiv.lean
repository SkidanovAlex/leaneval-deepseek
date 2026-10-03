import Mathlib

set_option linter.style.haveILetI false

namespace Work.ORAssembly.FP2

/-- Finite presentability of a module is invariant under transport of the module structure along a
ring isomorphism.

Concretely, if `M` is a finitely presented `A`-module and `φ : A ≃+* B` is a ring isomorphism,
then `M`, viewed as a `B`-module through `b • m = φ.symm b • m` (`Module.compHom`), is finitely
presented over `B`.

The proof takes a right exact sequence `(Fin m → A) → (Fin n → A) → M → 0` witnessing finite
presentation over `A` (`Module.FinitePresentation.exists_fin'`), identifies the free `A`-modules
with free `B`-modules via the componentwise application of `φ`, and observes that the resulting
`B`-linear presentation has a finitely generated kernel (the range of a map out of a finite free
`B`-module). -/
theorem finitePresentation_of_ringEquiv {A B : Type*} [Ring A] [Ring B] {M : Type*}
    [AddCommGroup M] [Module A M] (φ : A ≃+* B) (h : Module.FinitePresentation A M) :
    letI : Module B M := Module.compHom M (φ.symm : B →+* A)
    Module.FinitePresentation B M := by
  letI : Module B M := Module.compHom M (φ.symm : B →+* A)
  change Module.FinitePresentation B M
  letI : Module B A := Module.compHom A (φ.symm : B →+* A)
  let ψ : B ≃+* A := φ.symm
  obtain ⟨n, m, f, g, hf, hg⟩ := Module.FinitePresentation.exists_fin' A M
  -- `f` and `g` viewed as `B`-linear maps (an `A`-linear map is `B`-linear for the `compHom`
  -- structures, since `b • x = ψ b • x`).
  let fB : (Fin n → A) →ₗ[B] M :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun b x => f.map_smul (ψ b) x }
  let gB : (Fin m → A) →ₗ[B] (Fin n → A) :=
    { toFun := g
      map_add' := g.map_add
      map_smul' := fun b x => g.map_smul (ψ b) x }
  -- Componentwise identification of free `A`-modules with free `B`-modules.
  let en : (Fin n → B) ≃ₗ[B] (Fin n → A) :=
    LinearEquiv.piCongrRight (fun _ => Module.compHom.toLinearEquiv ψ)
  let em : (Fin m → B) ≃ₗ[B] (Fin m → A) :=
    LinearEquiv.piCongrRight (fun _ => Module.compHom.toLinearEquiv ψ)
  -- The transported presentation.
  let f' : (Fin n → B) →ₗ[B] M := fB.comp en.toLinearMap
  let g' : (Fin m → B) →ₗ[B] (Fin n → B) := en.symm.toLinearMap.comp (gB.comp em.toLinearMap)
  -- Exactness at `Fin n`, transported to the `B`-linear setting.
  have hker : LinearMap.ker fB = LinearMap.range gB := by
    have h0 := LinearMap.exact_iff.mp hg
    refine SetLike.ext fun x => ?_
    have hx := SetLike.ext_iff.mp h0 x
    simp only [LinearMap.mem_ker, LinearMap.mem_range]
    exact hx
  have hem : LinearMap.range em.toLinearMap = ⊤ := LinearMap.range_eq_top.mpr em.surjective
  have hrange : LinearMap.range g' = Submodule.map en.symm.toLinearMap (LinearMap.range gB) := by
    rw [LinearMap.range_comp, LinearMap.range_comp, hem, Submodule.map_top]
  have hkerf' : LinearMap.ker f' = LinearMap.range g' := by
    rw [LinearMap.ker_comp, Submodule.comap_equiv_eq_map_symm, hker, ← hrange]
  -- The kernel is the range of a map from a finite free `B`-module, hence finitely generated.
  have hfg : (LinearMap.range g').FG := Submodule.fg_range g'
  exact Module.finitePresentation_of_surjective f' (hf.comp en.surjective) (hkerf' ▸ hfg)

end Work.ORAssembly.FP2
