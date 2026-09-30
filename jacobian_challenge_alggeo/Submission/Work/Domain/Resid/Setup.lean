/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# RESID (area DM): the hypotheses of the residue map

The two theorems on the residue map (`Work.Domain.Resid.residMap_value` and
`Work.Domain.Resid.residMap_mem_domain`) take, besides the curve `C` and the symmetric powers
`symGeom` (interfaces `Work.SpecLin.DivBase C`, `Work.SpecLin.SymGeom C n`), the following
inputs, which are the outputs of areas `SY`, `RR`, `PR` and `CB`:

* `addMap`, `addMap_divOf`: addition of symmetric powers (area `SY`, fields of
  `Work.GroupChunk.Input` of the same name);
* `rr7`: a divisor of degree at least the genus `g` has an effective representative of the same
  degree (area `RR`, field `rr7` of `Work.GroupChunk.Input`);
* `isProper`, `locallyOfFiniteType`: the geometry of the symmetric powers (area `SY`);
* `ell_bc`: `ℓ` is invariant under base change of the field (area `CB`, the field `pull_ell` of
  `Work.GCBasics.DivBaseChange`, stated for `SpecLin.DivBase.bc`);
* `hspecLin`: the specialisation of linear equivalence along a valuation ring (area `PR`,
  `Work.SpecLin.specLin`, a theorem on disk).

They are bundled here so that the statements of the residue-map theorems stay readable.
-/
import Submission.Work.Domain.Resid.AEngine
import Submission.Work.GCBasics.DivBaseChange

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

universe u

namespace Work.Domain.Resid

open Work.GCBasics

variable {K : Type u} [Field K] {C : CurveBasics.Curve K} [SpecLin.DivBase C]

noncomputable section

/-- The inputs of the residue-map theorems, from areas `SY`, `RR`, `CB` and `PR`. -/
structure ResidData (symGeom : ∀ n, SpecLin.SymGeom C n) (g : ℕ) where
  /-- addition of symmetric powers (area `SY`). -/
  addMap : ∀ m n, (symGeom m).S ⊗ (symGeom n).S ⟶ (symGeom (m + n)).S
  /-- `divOf` of a sum of pullbacks is the sum of the divisors (area `SY`). -/
  addMap_divOf : ∀ m n {X : Sch K} (u : X ⟶ (symGeom m).S) (v : X ⟶ (symGeom n).S)
    {F : Type u} [Field F] [Algebra K F] (p : FPt X F),
    (symGeom (m + n)).divOf ((p ≫ CartesianMonoidalCategory.liftEquiv (u, v)) ≫ addMap m n)
      = (symGeom m).divOf (p ≫ u) + (symGeom n).divOf (p ≫ v)
  /-- **RR7** (area `RR`): a divisor of degree at least the genus has an effective
  representative of the same degree. -/
  rr7 : ∀ {F : Type u} [Field F] [Algebra K F] (A : Dv C F), (g : ℤ) ≤ Ddeg C F A →
    ∃ E : Dv C F, E.IsEffective ∧ Ddeg C F E = Ddeg C F A ∧ LinEquiv C A E
  /-- `Sym^n C` is proper over `K` (area `SY`). -/
  isProper : ∀ n, IsProper ((symGeom n).S).hom
  /-- `Sym^n C` is locally of finite type over `K` (area `SY`). -/
  locallyOfFiniteType : ∀ n, LocallyOfFiniteType ((symGeom n).S).hom
  /-- `ℓ` is invariant under base change of the field (area `CB`). -/
  ell_bc : ∀ {F F' : Type u} [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (e : F →ₐ[K] F') (D : Dv C F), ell C (SpecLin.DivBase.bc e D) = ell C D
  /-- **SPEC-LIN** (area `PR`): linear equivalence is detected on the closed point of a
  valuation ring. -/
  specLin : ∀ {n : ℕ} (G : SpecLin.SymGeom C n) (R : Type u) [CommRing R] [IsDomain R]
    [ValuationRing R] [Algebra K R] (a b : SpecLin.RPt G.S R),
    SpecLin.LinEquiv C (G.divOf (SpecLin.genPt R ≫ a)) (G.divOf (SpecLin.genPt R ≫ b)) →
    SpecLin.LinEquiv C (G.divOf (SpecLin.closedPt R ≫ a)) (G.divOf (SpecLin.closedPt R ≫ b))

namespace ResidData

variable {symGeom : ∀ n, SpecLin.SymGeom C n} {g : ℕ}

/-- The properness of `Sym^n C` over `K`, from the data. -/
theorem isProper_of_data (D : ResidData (K := K) symGeom g) (n : ℕ) :
    IsProper ((symGeom n).S).hom := D.isProper n

/-- The separatedness of `Sym^n C` over `K`, from the data. -/
theorem isSeparated_of_data (D : ResidData (K := K) symGeom g) (n : ℕ) :
    IsSeparated ((symGeom n).S).hom := by
  haveI := D.isProper n
  infer_instance

/-- Addition of a point of `Sym^r C` and a point of `Sym^m C` (area `SY`). -/
abbrev add (D : ResidData (K := K) symGeom g) {X : Sch K} {r m : ℕ}
    (u : X ⟶ (symGeom r).S) (y : X ⟶ (symGeom m).S) : X ⟶ (symGeom (r + m)).S :=
  addMor symGeom D.addMap u y

/-- **The residue map** attached to the data: the rational map `X ⤏ Sym^m C` whose value at a
point `p` is the effective representative of the class of `divOf (b p) - divOf (a p)`. -/
abbrev residMap (D : ResidData (K := K) symGeom g) {X : Sch K} [IsIntegral X.left]
    {r m : ℕ} (a : X ⟶ (symGeom r).S) (b : X ⟶ (symGeom (r + m)).S) (hm : g ≤ m) :
    X.left ⤏ (symGeom m).S.left :=
  Work.Domain.Resid.residMap a b D.rr7 hm (D.locallyOfFiniteType m)

theorem residMap_isOver (D : ResidData (K := K) symGeom g) {X : Sch K} [IsIntegral X.left]
    {r m : ℕ} (a : X ⟶ (symGeom r).S) (b : X ⟶ (symGeom (r + m)).S) (hm : g ≤ m) :
    (D.residMap a b hm).IsOver (Spec (CommRingCat.of K)) :=
  Work.Domain.Resid.residMap_isOver a b D.rr7 hm (D.locallyOfFiniteType m)

theorem residMap_fromFunctionField (D : ResidData (K := K) symGeom g) {X : Sch K}
    [IsIntegral X.left] {r m : ℕ} (a : X ⟶ (symGeom r).S) (b : X ⟶ (symGeom (r + m)).S)
    (hm : g ≤ m) :
    (D.residMap a b hm).fromFunctionField = (genValue a b D.rr7 hm).left :=
  Work.Domain.Resid.residMap_fromFunctionField a b D.rr7 hm (D.locallyOfFiniteType m)

/-- The generic value of the residue map represents the class of
`divD symGeom a b (genericFPt X)`: this is the generic half of the RESID specification, and the
definition of the residue map (it is the rational map with that generic fibre). -/
theorem residMap_generic (D : ResidData (K := K) symGeom g) {X : Sch K} [IsIntegral X.left]
    {r m : ℕ} (a : X ⟶ (symGeom r).S) (b : X ⟶ (symGeom (r + m)).S) (hm : g ≤ m) :
    Rel symGeom a b (genericFPt X) (genValue a b D.rr7 hm) :=
  genValue_spec a b D.rr7 hm

end ResidData

end

end Work.Domain.Resid
