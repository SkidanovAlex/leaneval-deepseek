import Mathlib.RingTheory.Finiteness.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Algebra.Module

/-- **Finite generation of a module is transported along a compatible pair of ring isomorphisms.**

If `E` is a finite `B`-module and `eB : B ≃+* B₀`, `eE : E ≃+* E₀` are ring isomorphisms
compatible with the algebra maps, then `E₀` is a finite `B₀`-module. -/
theorem moduleFinite_of_ringEquiv {B E B₀ E₀ : Type*} [Field B] [Field E] [Field B₀] [Field E₀]
    [Algebra B E] [Algebra B₀ E₀] (eB : B ≃+* B₀) (eE : E ≃+* E₀)
    (h : ∀ x : B, eE (algebraMap B E x) = algebraMap B₀ E₀ (eB x)) [Module.Finite B E] :
    Module.Finite B₀ E₀ := by
  -- `eE` is semilinear over `eB`, hence a surjective semilinear map `E →ₛₗ[eB] E₀`,
  -- and finite generation is preserved by surjective semilinear maps.
  let f : E →ₛₗ[eB.toRingHom] E₀ :=
    { toFun := eE
      map_add' := fun x y => map_add eE x y
      map_smul' := fun b x => by
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, h b]
        rfl }
  exact Module.Finite.of_surjective f eE.surjective

end Commons.Algebra.Module