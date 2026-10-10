import Mathlib.RepresentationTheory.Coinduced
import Submission.Work.SSGRoute.mackey_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open CategoryTheory SSGRoute.PTExt

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

/-- **The Mackey isomorphism for a surjection, compatible with the adjunction units and the
traces.** For a surjection `f : G →* D` and a subgroup `S ≤ D` with `S' := S.comap f`, the two
functors `Rep ↥S ⥤ Rep G` given by `X ↦ Rep.res f (Rep.coind S.subtype X)` and
`X ↦ Rep.coind (S.comap f).subtype (Rep.res (f.subgroupComap S) X)` are naturally isomorphic. The
component at `X` is the map `φ ↦ φ ∘ f` on the underlying function spaces
(`Rep.coind S.subtype X` is the submodule of `S`-equivariant functions `D → X.V`, while
`Rep.coind (S.comap f).subtype _` is the submodule of `S'`-equivariant functions `G → X.V`), and it
is bijective because `f` is onto: the inverse sends an `S'`-equivariant `ψ : G → X.V` to the
well-defined `φ` with `φ (f x) = ψ x` (well defined since `f x = f y` implies `x * y⁻¹ ∈ S'`, and
`S`-equivariant since `f` maps `S'` onto `S`).

The isomorphism is required to be compatible with

* the unit of the adjunction `Rep.resCoindAdjunction Coeff S.subtype` and the unit of
  `Rep.resCoindAdjunction Coeff (S.comap f).subtype` (composition is
  `CategoryTheory.CategoryStruct.comp`), and
* the traces `Work.SSGRoute.coindTrace`, at `Rep.res S.subtype A` for `A : Rep Coeff D` —

this is the "Mackey" content for a surjection: `G/S' ≅ D/S`, hence the two coset sums agree. All
notions are Mathlib's (`Rep.coind`, `Rep.res`, `Rep.resCoindAdjunction`) together with
`Work.SSGRoute.coindTrace` from `Submission.Work.SSGRoute.ext_cor`. -/
theorem coind_res_mackey {G D : Type} [Group G] [Group D] [Fintype G] [Fintype D]
    (f : G →* D) (hf : Function.Surjective f) (S : Subgroup D)
    [DecidableRel (QuotientGroup.rightRel S)] [Fintype (D ⧸ S)]
    [DecidableRel (QuotientGroup.rightRel (S.comap f))] [Fintype (G ⧸ S.comap f)] :
    ∃ θ : CategoryTheory.Iso
        (CategoryTheory.Functor.comp (Rep.coindFunctor SSGRoute.PTExt.Coeff S.subtype)
          (Rep.resFunctor f))
        (CategoryTheory.Functor.comp (Rep.resFunctor (f.subgroupComap S))
          (Rep.coindFunctor SSGRoute.PTExt.Coeff (S.comap f).subtype)),
      (∀ (X : Rep SSGRoute.PTExt.Coeff S) (φ : (Rep.coind S.subtype X).V) (x : G),
        (((θ.hom.app X).hom φ).1 x) = φ.1 (f x))
      ∧ (∀ (M : Rep SSGRoute.PTExt.Coeff D),
        CategoryTheory.CategoryStruct.comp
          ((Rep.resFunctor f).map
            ((Rep.resCoindAdjunction SSGRoute.PTExt.Coeff S.subtype).unit.app M))
          (θ.hom.app (Rep.res S.subtype M))
        = (Rep.resCoindAdjunction SSGRoute.PTExt.Coeff (S.comap f).subtype).unit.app
            (Rep.res f M))
      ∧ (∀ (A : Rep SSGRoute.PTExt.Coeff D),
        CategoryTheory.CategoryStruct.comp
          (θ.inv.app (Rep.res S.subtype A))
          ((Rep.resFunctor f).map (Work.SSGRoute.coindTrace S A))
        = Work.SSGRoute.coindTrace (S.comap f) (Rep.res f A)) := by
  refine ⟨mackeyNatIso f hf S, ?_, ?_, ?_⟩
  · intro X φ x
    rfl
  · intro M
    exact mackey_unit_compat f hf S M
  · intro A
    exact mackey_trace_compat f hf S A

end Work.SSGRoute
