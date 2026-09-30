/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area DescentGeom (geometric half of area DS)
-/
import Submission.Work.Descent.All
import Submission.Work.Packaging.Basic
import Submission.Work.CurveBasics.All

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area `DescentGeom` — Galois descent of the group chunk: the geometric half

This is the geometric half of §3.7 of `NOTES_LEAD_jacobian_GC.md`: the effective Galois descent of
the group chunk `G'` over a finite Galois extension `k'/k` to the Jacobian `J` over `k`, and the
result `Work.Packaging.JacPkg C P0`.

The algebra half of §3.7 (Speiser's lemma, `baseChange_isQuotient`, `desc_of_invariant`) is
delivered in `Submission/Work/Descent/` and is imported here.

## Conventions

* `Sch k` is the category `Over (Spec k)` of `k`-schemes, `bcFun k k' : Sch k ⥤ Sch k'` is the base
  change functor `Over.pullback (Spec.map (algebraMap k k'))` and `bc X = (bcFun k k').obj X`;
* `Work.Descent.galAct X σ` is the semilinear automorphism `id_X × Spec σ` of `bc X`;
* `specGal σ` is `Spec σ` as a morphism of `k`-schemes;
* the Galois group is `Γ = Work.Descent.Gal k k' = k' ≃ₐ[k] k'`.

Everything in this file is generic (`k`-schemes only); the curve and the group chunk appear only in
the interface `Input` below.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonObj MonoidalCategory
open CartesianMonoidalCategory

universe u

namespace Work.DescentGeom

noncomputable section

/-- The category of `k`-schemes (the notation used throughout area `DescentGeom`). -/
abbrev Sch (k : Type u) [Field k] : Type (u + 1) := Over (Spec (.of k))

/-- The base change functor `Sch k ⥤ Sch k'`. -/
abbrev bcFun (k k' : Type u) [Field k] [Field k'] [Algebra k k'] : Sch k ⥤ Sch k' :=
  Work.Descent.baseChangeFunctor k k'

/-- The base change `X_{k'}` of a `k`-scheme, as a `k'`-scheme (the extension `k'` is an explicit
argument, so that the type is determined without unification). -/
abbrev bc {k : Type u} [Field k] (k' : Type u) [Field k'] [Algebra k k'] (X : Sch k) : Sch k' :=
  (bcFun k k').obj X

/-- The projection `X_{k'} ⟶ X` (with the extension `k'` explicit). -/
abbrev bcπ {k : Type u} [Field k] (k' : Type u) [Field k'] [Algebra k k'] (X : Sch k) :
    (bc k' X).left ⟶ X.left :=
  Work.Descent.baseChangeπ X

/-- The structure morphism `Spec σ` of a Galois automorphism, as a morphism of `k`-schemes. -/
abbrev specGal {k k' : Type u} [Field k] [Field k'] [Algebra k k'] (σ : Work.Descent.Gal k k') :
    Spec (.of k') ⟶ Spec (.of k') :=
  Spec.map (CommRingCat.ofHom (σ : k' →+* k'))

@[simp] lemma specGal_one {k k' : Type u} [Field k] [Field k'] [Algebra k k'] :
    specGal (1 : Work.Descent.Gal k k') = 𝟙 _ := by
  simp [specGal]

lemma specGal_mul {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    (σ τ : Work.Descent.Gal k k') :
    specGal (σ * τ) = specGal σ ≫ specGal τ := by
  simpa [specGal] using Work.Descent.specMap_mul (k := k) (k' := k') σ τ

section Generic

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']

/-- The Galois action on `bc X`, as a family of morphisms (of the correct type). -/
abbrev galActK (k' : Type u) [Field k'] [Algebra k k'] (X : Sch k) :
    Work.Descent.Gal k k' → ((bc k' X).left ⟶ (bc k' X).left) :=
  fun σ => Work.Descent.galAct X σ

/-- The Galois action on `bc X` is semilinear over `Spec k'`. -/
theorem galActK_hom (X : Sch k) (σ : Work.Descent.Gal k k') :
    galActK k' X σ ≫ (bc k' X).hom = (bc k' X).hom ≫ specGal σ :=
  Work.Descent.galAct_hom X σ

/-- The (twisted) diagonal action of `σ` on a product `G ⊗ H` of two `k'`-schemes equipped with
semilinear Galois actions: the unique morphism making both projections equivariant. -/
def galActProdMap {k k' : Type u} [Field k] [Field k'] [Algebra k k'] (G H : Sch k')
    (ga : Work.Descent.Gal k k' → (G.left ⟶ G.left))
    (hb : Work.Descent.Gal k k' → (H.left ⟶ H.left))
    (hga : ∀ σ, ga σ ≫ G.hom = G.hom ≫ specGal σ)
    (hhb : ∀ σ, hb σ ≫ H.hom = H.hom ≫ specGal σ) (σ : Work.Descent.Gal k k') :
    (G ⊗ H).left ⟶ (G ⊗ H).left :=
  pullback.map G.hom H.hom G.hom H.hom (ga σ) (hb σ) (specGal σ) (hga σ).symm (hhb σ).symm

/-- The diagonal action on `G ⊗ G` for a family of automorphisms. -/
def galActProd {k k' : Type u} [Field k] [Field k'] [Algebra k k'] (G : Sch k')
    (ga : Work.Descent.Gal k k' → (G.left ≅ G.left))
    (hga : ∀ σ, (ga σ).hom ≫ G.hom = G.hom ≫ specGal σ) (σ : Work.Descent.Gal k k') :
    (G ⊗ G).left ⟶ (G ⊗ G).left :=
  galActProdMap G G (fun σ => (ga σ).hom) (fun σ => (ga σ).hom) hga hga σ

end Generic

/-! ## The interface

The interface of area `DescentGeom`: the *primitive* outputs of the other areas of the drive, taken
as named hypotheses in their current Lean form.

* `k'`, `G'`, `grpObj'`, `isProper'`, `smooth'`, `geomIrred'`, `connected'` — the group chunk of
  area `GC` over `k'` (`Work.GroupChunk.G D` with the group structure of §3.6 of the design notes);
* `galAct` and its properties — the semilinear Galois action on `G'` (`GroupChunk.desc` of
  `chart_E ↦ chart_{σE} ∘ (id_V × Spec σ)`);
* `hcover` — a `Γ`-stable affine cover of `G'` (area `CH`: COV′ plus the affine charts); it is the
  input of the effective descent of `G'` to `k`, from which `Work.DescentGeom.Input.J` (the
  quotient `J = G'/Γ`) and `Input.bcIso : J_{k'} ≅ G'` are *constructed* in `JExists.lean` via
  `Work.DescentGeom.exists_descentData` (area `SY`/SY1 + `Work.Descent.speiser`);
* `AJ'` and its properties — the Abel–Jacobi map of area `GC` over `k'`;
* `univ'`, `epi'` — the universal property of area `UP` over `k'`.
-/
structure Input {k : Type u} [Field k] (C : Sch k) (P0 : 𝟙_ (Sch k) ⟶ C) where
  /-- the finite Galois extension over which the group chunk is defined -/
  k' : Type u
  [field' : Field k']
  [algebra' : Algebra k k']
  [isGalois' : IsGalois k k']
  [finiteDimensional' : FiniteDimensional k k']
  /-- the group chunk `G'` over `k'` (area `GC`) -/
  G' : Sch k'
  [grpObj' : GrpObj G']
  [isProper' : IsProper G'.hom]
  [smooth' : Smooth G'.hom]
  [geomIrred' : GeometricallyIrreducible G'.hom]
  [connected' : ConnectedSpace G'.left]
  -- (the connectedness of `G'` is part of area `GC`'s output; the connectedness of `D.J` itself is
  -- derived from geometric irreducibility, see `Work.DescentGeom.Input.connected_J`)
  /-- the semilinear Galois action on `G'` -/
  galAct : Work.Descent.Gal k k' → (G'.left ≅ G'.left)
  /-- it is semilinear over `Spec k'` -/
  galAct_hom : ∀ σ, (galAct σ).hom ≫ G'.hom = G'.hom ≫ specGal σ
  /-- it is an action -/
  galAct_one : galAct 1 = Iso.refl G'.left
  galAct_mul : ∀ σ τ, galAct (σ * τ) = (galAct σ).trans (galAct τ)
  /-- the group law is equivariant -/
  galAct_mul_compat : ∀ σ,
    galActProd G' galAct galAct_hom σ ≫ μ[G'].left = μ[G'].left ≫ (galAct σ).hom
  /-- the unit is equivariant -/
  galAct_one_compat : ∀ σ, specGal σ ≫ η[G'].left = η[G'].left ≫ (galAct σ).hom
  /-- the inverse is equivariant -/
  galAct_inv_compat : ∀ σ, (galAct σ).hom ≫ ι[G'].left = ι[G'].left ≫ (galAct σ).hom
  /-- **the `Γ`-stable affine cover** of `G'`: the input of the effective descent
  (SGA1 VIII 7.6); it is what COV′ and the affine charts of area `CH` provide. -/
  hcover : ∀ x : G'.left, ∃ Ω : G'.left.Opens, IsAffineOpen Ω ∧
    (∀ σ, (galAct σ).hom ⁻¹ᵁ Ω = Ω) ∧ x ∈ Ω
  /-- the Abel–Jacobi map over `k'` (area `GC`) -/
  AJ' : bc k' C ⟶ G'
  /-- it sends `P0` to the origin -/
  AJ'_pt : (bcFun k k').map P0 ≫ AJ' =
    (CartesianMonoidalCategory.preservesTerminalIso (bcFun k k')).hom ≫ η[G']
  /-- it is equivariant -/
  AJ'_compat : ∀ σ,
    galActK k' C σ ≫ AJ'.left = AJ'.left ≫ (galAct σ).hom
  /-- the universal property over `k'` (area `UP`) -/
  univ' : ∀ (A' : Sch k') [Smooth A'.hom] [IsProper A'.hom] [GeometricallyIrreducible A'.hom]
    [GrpObj A'] (f : bc k' C ⟶ A'), (bcFun k k').map P0 ≫ f =
      (CartesianMonoidalCategory.preservesTerminalIso (bcFun k k')).hom ≫ η[A'] →
    ∃! g : G' ⟶ A', f = AJ' ≫ g
  /-- the generation property over `k'` (area `UP`) -/
  epi' : ∀ (A' : Sch k') [Smooth A'.hom] [IsProper A'.hom] [GeometricallyIrreducible A'.hom]
    [GrpObj A'] (u v : G' ⟶ A'), AJ' ≫ u = AJ' ≫ v → u = v

namespace Input

variable {k : Type u} [Field k] {C : Sch k} {P0 : 𝟙_ (Sch k) ⟶ C}

instance instField' (D : Input C P0) : Field D.k' := D.field'

instance instAlgebra' (D : Input C P0) : Algebra k D.k' := D.algebra'

instance instIsGalois' (D : Input C P0) : IsGalois k D.k' := D.isGalois'

instance instFiniteDimensional' (D : Input C P0) : FiniteDimensional k D.k' := D.finiteDimensional'

instance instGrpObj' (D : Input C P0) : GrpObj D.G' := D.grpObj'

instance instIsProper' (D : Input C P0) : IsProper D.G'.hom := D.isProper'

instance instSmooth' (D : Input C P0) : Smooth D.G'.hom := D.smooth'

instance instGeomIrred' (D : Input C P0) : GeometricallyIrreducible D.G'.hom := D.geomIrred'

instance instConnected' (D : Input C P0) : ConnectedSpace D.G'.left := D.connected'

end Input

end

end Work.DescentGeom
