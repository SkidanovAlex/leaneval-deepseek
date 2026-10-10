import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.mapExactFunctor_id
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open CategoryTheory

/-- **A general identity lemma for `extHMap` at `MonoidHom.id`**: for a trivial coefficient module
`V`, the change-of-group map `extHMap (MonoidHom.id G) (trivResInv (MonoidHom.id G) V)` — which
unfolds to `(mk₀ (unitRes id)).comp ((y.mapExactFunctor (resFunctor id)).comp (mk₀ (trivResInv id V)) _) _`
— is the identity on `Hⁿ(G, V)`.

This is the computational core of `inflTrivIn_refl`.  Two reductions are used:
`x.mapExactFunctor (Rep.resFunctor (MonoidHom.id G)) = x` (from
`Work.SSGRoute.mapExactFunctor_id`, since `Rep.resFunctor (MonoidHom.id G)` is the identity functor),
and `unitRes (MonoidHom.id G) = 𝟙 _`, `trivResInv (MonoidHom.id G) V = 𝟙 _` (both `rfl`), after which
only `Abelian.Ext.mk₀_id_comp` and `Abelian.Ext.comp_mk₀_id` remain. -/
theorem extHMap_id_triv {G : Type} [Group G] (V : Type) [AddCommGroup V]
    [Module SSGRoute.PTExt.Coeff V] {n : ℕ}
    (y : SSGRoute.PTExt.extH (Rep.trivial SSGRoute.PTExt.Coeff G V) n) :
    SSGRoute.PTExt.extHMap (MonoidHom.id G) (SSGRoute.PTExt.trivResInv (MonoidHom.id G) V) y
      = y := by
  have hres : ∀ {X Y : Rep.{0} SSGRoute.PTExt.Coeff G} {m : ℕ}
      (x : CategoryTheory.Abelian.Ext X Y m),
      x.mapExactFunctor (Rep.resFunctor (MonoidHom.id G)) = x := by
    intro X Y m x
    convert Work.SSGRoute.mapExactFunctor_id x using 2 <;> rfl
  simp only [SSGRoute.PTExt.extHMap, SSGRoute.PTExt.extRes]
  rw [hres]
  rw [show SSGRoute.PTExt.unitRes (MonoidHom.id G) = 𝟙 (SSGRoute.PTExt.unitRep G) from rfl]
  rw [show SSGRoute.PTExt.trivResInv (MonoidHom.id G) V
      = 𝟙 (Rep.trivial SSGRoute.PTExt.Coeff G V) from rfl]
  simp only [Abelian.Ext.comp_mk₀_id y, Abelian.Ext.mk₀_id_comp]

/-- **The inflation maps are the identity at `le_refl`** (the `map_self` axiom for the level system
of the colimit step of `Work.SSGRoute.phi1_mono_step_in`; equivalent to `levelMap_self` in
`Submission/Work/SSGRoute/phi1_level_system.lean`).  `inflTrivIn h V` is
`extHMap (galRes k L L) (trivResInv (galRes k L L) V)`; `galRes k L L = AlgEquiv.restrictNormalHom
(↥L) = MonoidHom.id` (`AlgEquiv.restrictNormalHom_id`), `Rep.resFunctor (MonoidHom.id)` is
definitionally `𝟭` (`Rep.res_id` is `rfl`) so `Work.SSGRoute.mapExactFunctor_id`
(`Submission/Work/SSGRoute/mapExactFunctor_id.lean`) applies, and `unitRes`/`trivResInv` are the
identities on the coefficient type, so the goal reduces to
`(mk₀ 𝟙).comp ((y).comp (mk₀ 𝟙) _) _ = y`, closed by `Abelian.Ext.mk₀_id_comp`.

The two group homomorphisms `galRes k ↥L ↥L` (with the `Algebra ↥L ↥L` instance induced by
`IntermediateField.inclusion (le_refl L)`) and `MonoidHom.id` are propositionally equal by
`AlgEquiv.restrictNormalHom_id`; the `change` passes between the two because the two `Algebra ↥L ↥L`
instances are *definitionally* equal (`rfl`), which is what makes the given instance-carrying
subterm rewriteable. -/
theorem inflTrivIn_refl {k K Ω : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [Field Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    {L : IntermediateField K Ω} [FiniteDimensional k L] [IsGalois k L]
    (V : Type) [AddCommGroup V] [Module SSGRoute.PTExt.Coeff V] {n : ℕ}
    (y : SSGRoute.PTExt.extH (Rep.trivial SSGRoute.PTExt.Coeff (↥L ≃ₐ[k] ↥L) V) n) :
    SSGRoute.PTExt.inflTrivIn (le_refl L) V y = y := by
  unfold SSGRoute.PTExt.inflTrivIn SSGRoute.PTExt.inflTriv
  simp only [SSGRoute.PTExt.galRes]
  -- The `Algebra ↥L ↥L` instance used by the unfolded `galRes k ↥L ↥L` is
  -- `(IntermediateField.inclusion (le_refl L)).toAlgebra`, which is definitionally `Algebra.id ↥L`;
  -- `change` moves to the (globally instance-resolved) occurrence so that
  -- `AlgEquiv.restrictNormalHom_id` matches.
  change SSGRoute.PTExt.extHMap (AlgEquiv.restrictNormalHom (K₁ := ↥L) (E := ↥L))
    (SSGRoute.PTExt.trivResInv (AlgEquiv.restrictNormalHom (K₁ := ↥L) (E := ↥L)) V) y = y
  rw [AlgEquiv.restrictNormalHom_id k ↥L]
  exact extHMap_id_triv V y

end Work.SSGRoute
