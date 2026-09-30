import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.CurveBasics.Order

/-- If `A` and `A'` are isomorphic commutative rings whose structure maps into a field `N` agree
along the isomorphism `e` (so that `A` and `A'` have the same image in `N`), then the integral
closure of `A` in `N` is a finite `A`-module as soon as the integral closure of `A'` in `N` is a
finite `A'`-module.  (The two integral closures have the same underlying subset of `N`.) -/
theorem module_finite_integralClosure_of_ringEquiv {A A' N : Type*} [CommRing A] [CommRing A']
    [Field N] [Algebra A N] [Algebra A' N] (e : A ≃+* A')
    (h : (algebraMap A' N).comp e.toRingHom = algebraMap A N)
    (hf : Module.Finite A' ↥(integralClosure A' N)) :
    Module.Finite A ↥(integralClosure A N) := by
  -- The two structure maps agree along `e`, hence the integral elements coincide.
  have h1 : ∀ a : A', algebraMap A' N a = algebraMap A N (e.symm a) := fun a => by
    rw [← h]; simp
  -- The identity on `N` restricts to a surjective semilinear map between the integral closures,
  -- semilinear over `e.symm : A' ≃+* A`.
  let f : ↥(integralClosure A' N) →ₛₗ[e.symm.toRingHom] ↥(integralClosure A N) :=
    { toFun := fun y => ⟨y.1, (RingEquiv.isIntegral_iff e h y.1).mpr y.2⟩
      map_add' := fun x y => Subtype.ext rfl
      map_smul' := fun a y => Subtype.ext (by
        rw [Subalgebra.coe_smul, Subalgebra.coe_smul, Algebra.smul_def, Algebra.smul_def, h1 a]
        simp) }
  exact Module.Finite.of_surjective f
    (fun z => ⟨⟨z.1, (RingEquiv.isIntegral_iff e h z.1).mp z.2⟩, Subtype.ext rfl⟩)

end Work.CurveBasics.Order
