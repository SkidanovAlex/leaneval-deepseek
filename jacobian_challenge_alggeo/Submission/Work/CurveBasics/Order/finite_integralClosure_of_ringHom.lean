import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.style.haveILetI false

namespace Work.CurveBasics.Order

/-- If `A ≃+* A'` and `f : M →+* M'` is an injective ring map compatible with the base change
(`f (algebraMap A M a) = algebraMap A' M' (σ a)`), then finiteness of the integral closure of
`A'` in `M'` as an `A'`-module implies finiteness of the integral closure of `A` in `M` as an
`A`-module. -/
theorem finite_integralClosure_of_ringHom {A A' M M' : Type*} [CommRing A] [CommRing A']
    [IsNoetherianRing A'] [Field M] [Field M'] [Algebra A M] [Algebra A' M']
    (σ : A ≃+* A') (f : M →+* M') (hinj : Function.Injective f)
    (hcomp : ∀ a, f (algebraMap A M a) = algebraMap A' M' (σ a)) :
    Module.Finite A' (integralClosure A' M') → Module.Finite A (integralClosure A M) := by
  intro hfin
  -- `A'` is Noetherian, so its finitely generated module of integral elements is Noetherian.
  haveI : IsNoetherian A' (integralClosure A' M') :=
    isNoetherian_of_isNoetherianRing_of_finite A' (integralClosure A' M')
  -- The equality of base maps, packaged as a `RingHom` equality.
  have hmap : (algebraMap A' M').comp (σ : A →+* A') = f.comp (algebraMap A M) :=
    RingHom.ext fun a => (hcomp a).symm
  -- `f` restricts to an `A`-semilinear map between the integral closures.
  let g : ↥(integralClosure A M) →ₛₗ[(σ : A →+* A')] ↥(integralClosure A' M') :=
  { toFun := fun x => ⟨f x.1, IsIntegral.map_of_comp_eq (σ : A →+* A') f hmap x.2⟩
    map_add' := fun x y => by ext; simp
    map_smul' := fun a x => by
      ext
      simp only [Algebra.smul_def, Subalgebra.coe_mul,
        Subalgebra.coe_algebraMap, map_mul, hcomp]
      rfl }
  have hg : Function.Injective g := fun x y h => by
    apply Subtype.ext
    apply hinj
    exact congrArg Subtype.val h
  haveI h1 : RingHomInvPair (σ : A →+* A') (σ.symm : A' →+* A) := RingHomInvPair.of_ringEquiv σ
  haveI h2 : RingHomInvPair (σ.symm : A' →+* A) (σ : A →+* A') := h1.symm
  exact Module.Finite.of_injective g hg

end Work.CurveBasics.Order
