import Mathlib
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Exactness and additivity of `Coind_S^G` over `Coeff = ULift ℤ`

`Abelian.Ext.mapExactFunctor` needs `[F.Additive]`, `[F.PreservesFiniteLimits]` and
`[F.PreservesFiniteColimits]`.  For `Rep.coindFunctor Coeff S.subtype` Mathlib provides only the
limit side (it is the right adjoint of the restriction functor).  Here:

* `Representation.coindMap_add` / `coindMap_zero`: `coindMap` is additive (pointwise).
* `Rep.instAdditiveCoindFunctor` / `instPreservesZeroCoindFunctor`: hence `Coind_S^G` is additive.
* `instPreservesFiniteColimitsCoindFunctor`: for `S` of finite index, `Coind_S^G ≅ Ind_S^G`
  (`Rep.indCoindNatIso`) and `Ind_S^G` is a left adjoint, hence preserves finite colimits; transport
  along the natural isomorphism.

The `attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module` bump is the workspace's
standard remedy for the `ULift.module` instance competing with the module structure stored in a
representation (see `Submission/NK/HassePrinciple/IdeleLevel.lean`).
-/

open CategoryTheory SSGRoute.PTExt

namespace Representation

universe u v

variable {k G H : Type} [CommRing k] [Monoid G] [Monoid H] (φ : G →* H)
variable {A : Type u} [AddCommGroup A] [Module k A] {σ : Representation k G A}
variable {B : Type v} [AddCommGroup B] [Module k B] {ρ : Representation k G B}

/-- `coindMap` (postcomposition of `S`-equivariant functions) is additive. -/
theorem coindMap_add (f g : σ.IntertwiningMap ρ) :
    coindMap φ (f + g) = coindMap φ f + coindMap φ g := by
  ext x h
  simp [coindMap_coe_apply_apply]

/-- `coindMap` sends `0` to `0`. -/
theorem coindMap_zero : coindMap φ (0 : σ.IntertwiningMap ρ) = 0 := by
  ext x h
  simp [coindMap_coe_apply_apply]

end Representation

namespace Rep

open CategoryTheory SSGRoute.PTExt

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

variable {G H : Type} [Group G] [Monoid H] (φ : G →* H)

/-- `Coind_φ` preserves zero morphisms. -/
instance instPreservesZeroCoindFunctor : (Rep.coindFunctor Coeff φ).PreservesZeroMorphisms where
  map_zero {X Y} := by
    ext1
    exact Representation.coindMap_zero (σ := X.ρ) (ρ := Y.ρ) φ

/-- `Coind_φ` is additive. -/
instance instAdditiveCoindFunctor : (Rep.coindFunctor Coeff φ).Additive where
  map_add {X Y} f g := by
    ext1
    rw [Rep.add_hom]
    exact Representation.coindMap_add (σ := X.ρ) (ρ := Y.ρ) φ f.hom g.hom

/-- `Coind_S^G` preserves finite colimits when `S ≤ G` has finite index, by transport along
`Rep.indCoindNatIso` from the left adjoint `Ind_S^G`. -/
instance instPreservesFiniteColimitsCoindFunctor {G : Type} [Group G] (S : Subgroup G) [S.FiniteIndex]
    [DecidableRel (QuotientGroup.rightRel S)] :
    Limits.PreservesFiniteColimits (Rep.coindFunctor Coeff S.subtype) :=
  Limits.preservesFiniteColimits_of_natIso (Rep.indCoindNatIso Coeff S)

end Rep

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

/-- Both exactness conditions and additivity needed by `mapExactFunctor` are available for
`Rep.coindFunctor Coeff S.subtype` for a finite-index subgroup `S`. -/
noncomputable example {G : Type} [Group G] (S : Subgroup G) [S.FiniteIndex]
    [DecidableRel (QuotientGroup.rightRel S)] (M A : Rep Coeff G) (n : ℕ)
    (x : Abelian.Ext (Rep.res S.subtype M) (Rep.res S.subtype A) n) :
    Abelian.Ext (Rep.coind S.subtype (Rep.res S.subtype M))
      (Rep.coind S.subtype (Rep.res S.subtype A)) n :=
  x.mapExactFunctor (Rep.coindFunctor Coeff S.subtype)

end Work.SSGRoute
