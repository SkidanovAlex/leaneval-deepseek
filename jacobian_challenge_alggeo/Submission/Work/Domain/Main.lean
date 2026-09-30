/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area DM — assembly of the domain engine

This file collects the domain engine of area `DM` and re-exports its results under the names used
in `NOTES_LEAD_jacobian_GC.md` §3.3, so that downstream areas (CH, GC, RESID) can state their
inputs without depending on the internal file layout.

* `Work.Domain.mem_domain_of_finite_fibre` — the engine: a finite fibre of the graph closure over
  `x` implies that the rational map is defined at `x`.
* `Work.Domain.mem_domain_of_unique_extension` — the blueprint's DOM fact: the valuative
  hypothesis `H` implies that the rational map is defined at `x`.
* `Work.Domain.fibre_pr₂_eq_of_unique_limit` — `H` forces the second projection to be constant on
  the fibre of the graph closure.
* `Work.Domain.theta_comp_stalkMap`, `Work.Domain.spec_theta_fromSpecStalk` — the two comparison
  identities for `θ_γ`.
* `Work.Domain.algebraMap_surjective_of_finite_of_isIntegrallyClosed` — the ring lemma.
-/
import Submission.Work.Domain.Graph
import Submission.Work.Domain.Ring
import Submission.Work.Domain.Theta
import Submission.Work.Domain.Engine.comp_stalkMap
import Submission.Work.Domain.Engine.fromSpecStalk
import Submission.Work.Domain.Engine.fibreValue
import Submission.Work.Domain.Engine.memDomainFiniteFibre
import Submission.Work.Domain.Engine.memDomainUniqueExtension

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

variable {S X Y : Scheme.{u}} [X.Over S] [Y.Over S]

/-- **The domain engine.**  If the fibre of the graph closure of `g` over `x` is finite, then the
rational map `g` is defined at `x`. -/
theorem mem_domain_of_finite_fibre [IsIntegral X] [IsLocallyNoetherian X]
    [IsProper (Y ↘ S)] (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (g : X.PartialMap Y) [g.IsOver S] {x : X}
    (hfin : (PartialMap.pr₁ S g ⁻¹' ({x} : Set X)).Finite) :
    x ∈ g.toRationalMap.domain :=
  Engine.memDomainFiniteFibre hX g hfin

/-- **DOM (the blueprint's Fact B).**  If for every valuation subring `A ⊆ K(X)` dominating
`O_{X,x}` every extension of `g` over `A` sends the closed point to the same point `y₀`, then `g`
is defined at `x`. -/
theorem mem_domain_of_unique_extension [IsIntegral X] [IsLocallyNoetherian X]
    [IsProper (Y ↘ S)] (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (g : X.PartialMap Y) [g.IsOver S] (x : X) (y₀ : Y)
    (H : ∀ (A : ValuationSubring X.functionField)
        (hA : ∀ s : X.presheaf.stalk x,
          algebraMap (X.presheaf.stalk x) X.functionField s ∈ A)
        (_ : IsLocalHom ((algebraMap (X.presheaf.stalk x) X.functionField).codRestrict
          A.toSubring hA))
        (ψ : Spec (CommRingCat.of A) ⟶ Y),
        ψ ≫ (Y ↘ S) = Spec.map (CommRingCat.ofHom ((algebraMap (X.presheaf.stalk x)
            X.functionField).codRestrict A.toSubring hA)) ≫ X.fromSpecStalk x ≫ (X ↘ S) →
        Spec.map (CommRingCat.ofHom (algebraMap A X.functionField)) ≫ ψ = g.fromFunctionField →
        ψ (IsLocalRing.closedPoint A) = y₀) :
    x ∈ g.toRationalMap.domain :=
  Engine.memDomainUniqueExtension hX g x y₀ (by
    intro A hA hloc ψ h1 h2
    exact H A hA hloc ψ h1 h2)

/-- **The valuative value lemma.**  Under the hypothesis `H` of DOM, the second projection of the
graph closure is constant `= y₀` on the fibre of `pr₁` over `x`. -/
theorem fibre_pr₂_eq_of_unique_limit [IsIntegral X] [IsLocallyNoetherian X]
    [IsProper (Y ↘ S)] (g : X.PartialMap Y) [g.IsOver S] {x : X} {y₀ : Y}
    (H : ∀ (A : ValuationSubring X.functionField)
        (hA : ∀ s : X.presheaf.stalk x,
          algebraMap (X.presheaf.stalk x) X.functionField s ∈ A)
        (_ : IsLocalHom ((algebraMap (X.presheaf.stalk x) X.functionField).codRestrict
          A.toSubring hA))
        (ψ : Spec (CommRingCat.of A) ⟶ Y),
        ψ ≫ (Y ↘ S) = Spec.map (CommRingCat.ofHom ((algebraMap (X.presheaf.stalk x)
            X.functionField).codRestrict A.toSubring hA)) ≫ X.fromSpecStalk x ≫ (X ↘ S) →
        Spec.map (CommRingCat.ofHom (algebraMap A X.functionField)) ≫ ψ = g.fromFunctionField →
        ψ (IsLocalRing.closedPoint A) = y₀)
    (γ : PartialMap.graph S g) (hγ : PartialMap.pr₁ S g γ = x) :
    PartialMap.pr₂ S g γ = y₀ :=
  Engine.fibreValue g (by
    intro A hA hloc ψ h1 h2
    exact H A hA hloc ψ h1 h2) γ hγ

/-- **First comparison identity** for the map `θ_γ`. -/
theorem theta_comp_stalkMap [IsIntegral X] [IsLocallyNoetherian X]
    [IsProper (Y ↘ S)] (g : X.PartialMap Y) [g.IsOver S] (γ : PartialMap.graph S g) :
    (PartialMap.pr₁ S g).stalkMap γ ≫ PartialMap.theta g γ =
      CommRingCat.ofHom (algebraMap
        (X.presheaf.stalk (PartialMap.pr₁ S g γ)) X.functionField) :=
  Engine.comp_stalkMap g γ

/-- **Second comparison identity** for the map `θ_γ`. -/
theorem spec_theta_fromSpecStalk [IsIntegral X] [IsLocallyNoetherian X]
    [IsProper (Y ↘ S)] (g : X.PartialMap Y) [g.IsOver S] (γ : PartialMap.graph S g) :
    Spec.map (PartialMap.theta g γ) ≫ (PartialMap.graph S g).fromSpecStalk γ ≫
        PartialMap.pr₂ S g = Scheme.PartialMap.fromFunctionField g :=
  Engine.fromSpecStalk g γ

end Work.Domain
