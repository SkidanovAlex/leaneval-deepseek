/-
Copyright (c) 2025. All rights reserved.

# Vocabulary for the continuous descent `Ext¹_{ℤ[Q]}(X, Kˣ) ≅ H¹_cont(G, Hom_ℤ(infl X, Mˣ))`

Shared definitions for the pieces of `Work.SSGRoute.ext_continuous_descent`:
`L` a field, `M` an algebraic closure of `L`, `K ⊆ M` a finite Galois intermediate field,
`Q = Gal(K/L)` (finite), `G = Gal(M/L)` (profinite, Krull topology).

The definitions are written in the *unfolded* shape used by the target statement
(`ext_continuous_descent.lean`), so that consumers can `exact` results stated with these
abbreviations.
-/
import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.homRep
import Submission.Work.AbsoluteKummer.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute
namespace SSGDescent

open CategoryTheory SSGRoute.PTExt

variable (L M : Type) [Field L] [Field M] [Algebra L M]

/-- The restriction map `Gal(M/L) →* Gal(K/L)`. -/
noncomputable abbrev ssgResHom (K : IntermediateField L M) [Normal L ↥K] :
    (M ≃ₐ[L] M) →* (K ≃ₐ[L] K) :=
  AlgEquiv.restrictNormalHom (F := L) (K₁ := M) K

/-- `Kˣ` as a `Gal(K/L)`-module: the coefficient object of the left-hand side. -/
noncomputable abbrev ssgCoeffK (K : IntermediateField L M) : Rep.{0} Coeff (K ≃ₐ[L] K) :=
  modRep (K ≃ₐ[L] K) (Additive (Units ↥K))

/-- `Mˣ` as a `Gal(M/L)`-module. -/
noncomputable abbrev ssgCoeffM : Rep.{0} Coeff (M ≃ₐ[L] M) :=
  modRep (M ≃ₐ[L] M) (Additive (Units M))

/-- The `Gal(M/L)`-module `Hom_ℤ(infl X, Mˣ)`, in the unfolded form of the target statement. -/
noncomputable abbrev ssgHom (K : IntermediateField L M) [Normal L ↥K]
    (X : Rep.{0} Coeff (K ≃ₐ[L] K)) : Type :=
  (Rep.res (ssgResHom L M K) X).V →ₗ[Coeff] (ssgCoeffM L M).V

/-- The right-hand side of the target statement (coefficient type in the unfolded form). -/
noncomputable abbrev ssgH1 (K : IntermediateField L M) [Normal L ↥K]
    (X : Rep.{0} Coeff (K ≃ₐ[L] K)) : Type :=
  Work.AbsoluteKummer.H1 (M ≃ₐ[L] M) (ssgHom L M K X)

/-- The `Hom`-space of `Rep Coeff Gal(K/L)`-morphisms `N ⟶ Kˣ`. -/
noncomputable abbrev ssgHomK (K : IntermediateField L M) (N : Rep.{0} Coeff (K ≃ₐ[L] K)) : Type :=
  N ⟶ ssgCoeffK L M K

/-- Precomposition with a morphism `f : A ⟶ B` of `Rep Coeff G`, as an additive homomorphism on
`Hom`-groups. -/
def precompHom {G : Type} [Group G] {A B : Rep.{0} Coeff G} (f : A ⟶ B) (Y : Rep.{0} Coeff G) :
    (B ⟶ Y) →+ (A ⟶ Y) :=
  AddMonoidHom.mk' (fun g => f ≫ g) (by intro a b; rw [Preadditive.comp_add])

end SSGDescent
end Work.SSGRoute
