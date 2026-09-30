/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The comparison map from the stalk of the graph closure to `K(X)` (area DM, part 3)

Let `g : X ⇢ Y` be a partial `S`-map with dense open domain `U`, and let `η ∈ U` be the point of
`U` lying over the generic point of `X`.  For every point `γ` of the graph closure `Γ` of `g` we
construct a ring homomorphism

`θ_γ : O_{Γ,γ} ⟶ K(X)`

as the composite `O_{Γ,γ} → O_{Γ,η_Γ} → O_{U,η} → K(X)` of germ maps along the generic point.
This is the "restriction to the generic point of the graph", and it is the map on which the
domain engine runs:

* `Work.Domain.PartialMap.theta_comp_stalkMap`:
  `p.stalkMap γ ≫ θ_γ = algebraMap O_{X,x} K(X)` when `p γ = x`;
* `Work.Domain.PartialMap.spec_theta_fromSpecStalk`:
  `Spec.map θ_γ ≫ Γ.fromSpecStalk γ ≫ pr₂ = g.fromFunctionField`.
-/
import Submission.Work.Domain.Graph
import Submission.Work.Domain.Ring

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.Domain

/-- The structure morphism `X ⟶ S` of an `S`-scheme, exposed as a plain abbreviation (so that
statements about area `DM` can avoid the `↘` notation). -/
abbrev overHom (S X : Scheme.{u}) [X.Over S] : X ⟶ S := X ↘ S

namespace PartialMap

variable {S X Y : Scheme.{u}} [X.Over S] [Y.Over S]

/-- The generic point of `X` lies in every dense open. -/
lemma genericPoint_mem_domain (g : X.PartialMap Y) [IrreducibleSpace X] :
    genericPoint X ∈ g.domain := by
  obtain ⟨y, hy⟩ := g.dense_domain.nonempty
  exact ((genericPoint_spec X).specializes (y := y) trivial).mem_open g.domain.2 hy

/-- The generic point of `X`, viewed as a point of the domain of `g`. -/
noncomputable def etaDomain (g : X.PartialMap Y) [IrreducibleSpace X] : g.domain.toScheme :=
  ⟨genericPoint X, genericPoint_mem_domain g⟩

instance etaDomain.nonempty (g : X.PartialMap Y) [IrreducibleSpace X] :
    Nonempty g.domain.toScheme :=
  ⟨etaDomain g⟩

/-- The generic point of the domain, as a point of `X`. -/
lemma domain_genericPoint_ι (g : X.PartialMap Y) [IrreducibleSpace X]
    [IrreducibleSpace g.domain.toScheme] :
    g.domain.ι (genericPoint g.domain.toScheme) = genericPoint X :=
  genericPoint_eq_of_isOpenImmersion g.domain.ι

/-- `etaDomain` really is the generic point of the domain. -/
lemma etaDomain_eq (g : X.PartialMap Y) [IrreducibleSpace X]
    [IrreducibleSpace g.domain.toScheme] :
    etaDomain g = genericPoint g.domain.toScheme := by
  apply Subtype.ext
  show genericPoint X = g.domain.ι (genericPoint g.domain.toScheme)
  exact (domain_genericPoint_ι g).symm

/-- The comparison map `O_{U,η} ⟶ K(X)`: the germ at the generic point of `X`, transported along
the open immersion `U ⊆ X`. -/
noncomputable def germMapToFunctionField (g : X.PartialMap Y) [IrreducibleSpace X] :
    (g.domain.toScheme).presheaf.stalk (etaDomain g) ⟶ X.functionField :=
  (g.domain.stalkIso (etaDomain g)).hom

/-- The generic point of the graph closure (as the image of `etaDomain`) specialises to every
point of the graph closure. -/
lemma specializes_toGraph_etaDomain (g : X.PartialMap Y) [g.IsOver S] [IrreducibleSpace X]
    [IrreducibleSpace g.domain.toScheme] [QuasiCompact (graphMap S g)] (γ : graph S g) :
    Specializes (toGraph S g (etaDomain g)) γ :=
  (etaDomain_eq g) ▸ specializes_toGraph_genericPoint S g (γ := γ)

/-- The comparison map `θ_γ : O_{Γ,γ} ⟶ K(X)`. -/
noncomputable def theta (g : X.PartialMap Y) [g.IsOver S] [IrreducibleSpace X]
    [IrreducibleSpace g.domain.toScheme] [QuasiCompact (graphMap S g)] (γ : graph S g) :
    (graph S g).presheaf.stalk γ ⟶ X.functionField :=
  (graph S g).presheaf.stalkSpecializes (specializes_toGraph_etaDomain g γ) ≫
    (toGraph S g).stalkMap (etaDomain g) ≫ germMapToFunctionField g


end PartialMap

end Work.Domain
