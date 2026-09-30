/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area UP — setup: the interface, the sum map and the chart maps

Area **UP** of the Jacobian drive, `Submission/Work/NOTES_LEAD_jacobian_GC.md` §3.8.

Everything is over a field `K`, for a curve `C : CurveBasics.Curve K`, a base point
`P0 : 𝟙_ (Sch K) ⟶ C.toOver`, a chart datum `D : GroupChunk.Input C P0` (area GC) and an
abelian variety `A` over `K` (`[GrpObj A] [IsAbelianVariety A]`).

The goal of the area is the universal property of the Abel–Jacobi map

* `factor : G D ⟶ A` for a pointed morphism `f : C ⟶ A`,
* `Work.Universal.univ : ∃! g : G D ⟶ A, f = AJ₀ ≫ g`,
* `Work.Universal.epi : AJ₀ ≫ u = AJ₀ ≫ v → u = v`.

This file provides the vocabulary:

* `quotMap` — the quotient map `Cⁿ ⟶ Symⁿ C`;
* `SymQuotData` — the named hypothesis (area SY) that `Symⁿ C` is the quotient of `Cⁿ` by the
  permutation action of `Sₙ`;
* `sumMap` — the sum morphism `Σᵐ f : Symⁿ C ⟶ A`, with its API (`sumMap_spec`, `sumMap_unique`,
  `sumMap_powMap`, `sumMap_comp_hom`);
* `sumDiv` — the sum `Σ f(E)` of an effective divisor `E` (the form in which the key lemma of
  area KL is stated), and `sumDiv_eq_of_divOf`;
* `Input` — the named hypotheses of areas GC (the group chunk `G D`, its group structure, the
  Abel–Jacobi maps and the universal property of the gluing) and KL (the key lemma: `Σ f` is
  constant on linear equivalence classes and additive);
* `chartMap`, `factorCompat`, `factorWith` — the local chart maps out of which `factor` is glued.

**Notation.**  Group-valued points are written multiplicatively; the "difference" of two points of
`A` is `x / y` (`Sub` is not available for groups in Mathlib).  Division of divisors (`E - E'`) is
additive notation as usual.
-/
import Submission.Work.GCBasics.All
import Submission.Work.AbVar.Main
import Submission.Work.GroupChunk.Glue
import Submission.Work.GroupChunk.Defs
import Submission.Work.GroupChunk.Transitions
import Submission.Work.SymQuot.Product.permIso_hom_proj
import Submission.Work.SpecLin.Points.Basic
import Submission.Work.SpecLin.Points.ptDiv_deg

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical MonObj
open scoped Work.GCBasics

universe u v

namespace Work.Universal

noncomputable section

open Work.GCBasics Work.GroupChunk

variable {K : Type u} [Field K]

/-! ## 1. The quotient map `Cⁿ ⟶ Symⁿ C` and the interface SY -/

/-- The `m`-th projection of the `n`-fold product of `C` with itself. -/
abbrev proj (C : CurveBasics.Curve K) (n : ℕ) (m : Fin n) :
    SymQuot.prod C.toOver n ⟶ C.toOver :=
  SymQuot.proj C.toOver n m

/-- **The quotient map `Cⁿ ⟶ Symⁿ C`**: the `n`-fold sum of the universal family of points of
`Cⁿ`.  For the symmetric power `Sym C n` of area SY (whose `powMap` is `Sym.powMap`) this is
the quotient map `Sym.quot C n`. -/
def quotMap {C : CurveBasics.Curve K} {P0 : 𝟙_ (Sch K) ⟶ C.toOver} [SpecLin.DivBase C]
    (D : GroupChunk.Input C P0) (n : ℕ) : SymQuot.prod C.toOver n ⟶ D.Sym n :=
  (D.symGeom n).powMap (fun m => proj C n m)

/-- **Interface (area SY).**  `Symⁿ C` is the quotient of `Cⁿ` by the action of the symmetric
group `Sₙ` by permutation of the factors: every `Sₙ`-invariant morphism `Cⁿ ⟶ Z` factors
uniquely through the quotient map `quotMap`.

For the symmetric powers of area SY this is `Sym.desc`
(`Submission/Work/SymQuot/Sym.lean`), read along the identification of `(symGeom n).S` with
`Sym C n`.  It is the *only* input from area SY used by area UP: it is what makes the sum
morphism `sumMap` below exist. -/
class SymQuotData (C : CurveBasics.Curve K) (P0 : 𝟙_ (Sch K) ⟶ C.toOver) [SpecLin.DivBase C]
    (D : GroupChunk.Input C P0) where
  desc : ∀ (n : ℕ) {Z : Sch K} (φ : SymQuot.prod C.toOver n ⟶ Z),
    (∀ σ : Equiv.Perm (Fin n), (SymQuot.permIso C.toOver σ).hom ≫ φ = φ) →
    ∃! g : D.Sym n ⟶ Z, quotMap D n ≫ g = φ

/-! ## 2. Finite products of morphisms into a group object -/

/-- `g ≫ ·` as a monoid homomorphism `Hom(Y,M) →* Hom(X,M)`. -/
def compMonoidHom {M X Y : Sch K} [MonObj M] [IsCommMonObj M] (g : X ⟶ Y) :
    (Y ⟶ M) →* (X ⟶ M) where
  toFun u := g ≫ u
  map_one' := MonObj.comp_one g
  map_mul' u v := MonObj.comp_mul g u v

/-- `· ≫ h` as a monoid homomorphism `Hom(X,M) →* Hom(X,N)`, for a monoid homomorphism `h`. -/
def monoidHomComp {M N X : Sch K} [MonObj M] [MonObj N] [IsCommMonObj M] [IsCommMonObj N]
    (h : M ⟶ N) [IsMonHom h] : (X ⟶ M) →* (X ⟶ N) where
  toFun u := u ≫ h
  map_one' := MonObj.one_comp h
  map_mul' u v := MonObj.mul_comp u v h

/-- A morphism out of a product distributes over a finite product of morphisms into a monoid
object: `g ≫ ∏ i, u i = ∏ i, (g ≫ u i)`. -/
theorem comp_prod_finset {M X Y : Sch K} [MonObj M] [IsCommMonObj M] {I : Type v}
    (s : Finset I) (g : X ⟶ Y) (u : I → (Y ⟶ M)) :
    g ≫ (∏ i ∈ s, u i) = ∏ i ∈ s, (g ≫ u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [MonObj.comp_one]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, MonObj.comp_mul, ih]

/-- A morphism out of a product distributes over a finite product of morphisms into a monoid
object: `g ≫ ∏ i, u i = ∏ i, (g ≫ u i)`. -/
theorem comp_prod {M X Y : Sch K} [MonObj M] [IsCommMonObj M] {I : Type v} [Fintype I]
    (g : X ⟶ Y) (u : I → (Y ⟶ M)) : g ≫ (∏ i, u i) = ∏ i, (g ≫ u i) :=
  comp_prod_finset (Finset.univ : Finset I) g u

/-- A finite product of morphisms into a monoid object composes with a monoid homomorphism:
`(∏ i, u i) ≫ h = ∏ i, (u i ≫ h)`. -/
theorem prod_comp_finset {M N X : Sch K} [MonObj M] [MonObj N] [IsCommMonObj M]
    [IsCommMonObj N] {I : Type v} (s : Finset I) (u : I → (X ⟶ M)) (h : M ⟶ N) [IsMonHom h] :
    (∏ i ∈ s, u i) ≫ h = ∏ i ∈ s, (u i ≫ h) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [MonObj.one_comp]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, MonObj.mul_comp, ih]

/-- A finite product of morphisms into a monoid object composes with a monoid homomorphism. -/
theorem prod_comp {M N X : Sch K} [MonObj M] [MonObj N] [IsCommMonObj M] [IsCommMonObj N]
    {I : Type v} [Fintype I] (u : I → (X ⟶ M)) (h : M ⟶ N) [IsMonHom h] :
    (∏ i, u i) ≫ h = ∏ i, (u i ≫ h) :=
  prod_comp_finset (Finset.univ : Finset I) u h

/-! ## 3. The sum morphism `Σᵐ f : Symⁿ C ⟶ A` -/

/-- The `n`-fold sum `Σ_m (pr_m ≫ f)` of the universal family of points of `Cⁿ`, computed in the
group `Hom(Cⁿ, A)`. -/
def sumTerm (C : CurveBasics.Curve K) {A : Sch K} [MonObj A] [IsCommMonObj A]
    (f : C.toOver ⟶ A) (n : ℕ) : SymQuot.prod C.toOver n ⟶ A :=
  ∏ m : Fin n, (proj C n m ≫ f)

/-- `Σ_m (pr_m ≫ f)` does not depend on the ordering of the factors: **commutativity of the group
law of `A`**. -/
theorem sumTerm_perm (C : CurveBasics.Curve K) {A : Sch K} [MonObj A] [IsCommMonObj A]
    (f : C.toOver ⟶ A) (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (SymQuot.permIso C.toOver σ).hom ≫ sumTerm C f n = sumTerm C f n := by
  have key : ∀ s : Finset (Fin n),
      (SymQuot.permIso C.toOver σ).hom ≫ (∏ m ∈ s, (proj C n m ≫ f))
        = ∏ m ∈ s, ((SymQuot.permIso C.toOver σ).hom ≫ (proj C n m ≫ f)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [MonObj.comp_one]
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, MonObj.comp_mul, ih]
  rw [sumTerm, key]
  refine Fintype.prod_equiv σ.symm _ _ (fun m => ?_)
  simp only [← Category.assoc, SymQuot.Product.permIso_hom_proj]

/-- **The sum morphism `Σᵐ f : Symⁿ C ⟶ A`**: the `Sₙ`-invariant morphism
`(x_1, …, x_n) ↦ Σ_m f(x_m)` of `Cⁿ`, factored through the quotient `Cⁿ ⟶ Symⁿ C` (interface
`SymQuotData`, i.e. area SY). -/
def sumMap {C : CurveBasics.Curve K} {P0 : 𝟙_ (Sch K) ⟶ C.toOver} [SpecLin.DivBase C]
    (D : GroupChunk.Input C P0) [SymQuotData C P0 D] {A : Sch K} [GrpObj A]
    [IsCommMonObj A] (f : C.toOver ⟶ A) (n : ℕ) : D.Sym n ⟶ A :=
  Classical.choose
    ((inferInstance : SymQuotData C P0 D).desc n (sumTerm C f n) (sumTerm_perm C f n))

/-- The defining property of `sumMap`: composed with the quotient map `Cⁿ ⟶ Symⁿ C` it is the
`n`-fold sum `Σ_m (pr_m ≫ f)`. -/
theorem sumMap_spec {C : CurveBasics.Curve K} {P0 : 𝟙_ (Sch K) ⟶ C.toOver} [SpecLin.DivBase C]
    (D : GroupChunk.Input C P0) [SymQuotData C P0 D] {A : Sch K} [GrpObj A] [IsCommMonObj A]
    (f : C.toOver ⟶ A) (n : ℕ) :
    quotMap D n ≫ sumMap D f n = sumTerm C f n :=
  (Classical.choose_spec
    ((inferInstance : SymQuotData C P0 D).desc n (sumTerm C f n) (sumTerm_perm C f n))).1

/-- The uniqueness part of the defining property of `sumMap`. -/
theorem sumMap_unique {C : CurveBasics.Curve K} {P0 : 𝟙_ (Sch K) ⟶ C.toOver}
    [SpecLin.DivBase C] (D : GroupChunk.Input C P0) [SymQuotData C P0 D] {A : Sch K}
    [GrpObj A] [IsCommMonObj A] (f : C.toOver ⟶ A) (n : ℕ) {g : D.Sym n ⟶ A}
    (hg : quotMap D n ≫ g = sumTerm C f n) : g = sumMap D f n :=
  (Classical.choose_spec
    ((inferInstance : SymQuotData C P0 D).desc n (sumTerm C f n) (sumTerm_perm C f n))).2 g hg

/-! ## 4. The sum of `f` over an effective divisor -/

/-- **The sum `Σ f(E)` of `f` over an effective divisor `E` of degree `n`**: the value of the sum
morphism `sumMap` at the point of `Symⁿ C` classified by `E` (`SymGeom.divOf_complete`).  This is
the form in which the key lemma of area KL (constancy on linear equivalence classes, additivity)
is stated; see `Input.kl` and `Input.kl_add`. -/
def sumDiv {C : CurveBasics.Curve K} {P0 : 𝟙_ (Sch K) ⟶ C.toOver} [SpecLin.DivBase C]
    (D : GroupChunk.Input C P0) [SymQuotData C P0 D] {A : Sch K} [GrpObj A] [IsCommMonObj A]
    (f : C.toOver ⟶ A) {F : Type u} [Field F] [Algebra K F] (E : Dv C F) (hE : E.IsEffective)
    (n : ℕ) (hn : Ddeg C F E = (n : ℤ)) : FPt A F :=
  (Classical.choose ((D.symGeom n).divOf_complete E hE hn)) ≫ sumMap D f n

/-- `sumDiv` is the value of `sumMap` at the point classified by the divisor: if `divOf p = E`
then `Σ f(E) = p ≫ Σᵐ f`. -/
theorem sumDiv_eq_of_divOf {C : CurveBasics.Curve K} {P0 : 𝟙_ (Sch K) ⟶ C.toOver}
    [SpecLin.DivBase C] (D : GroupChunk.Input C P0) [SymQuotData C P0 D] {A : Sch K}
    [GrpObj A] [IsCommMonObj A] (f : C.toOver ⟶ A) {F : Type u} [Field F] [Algebra K F]
    {E : Dv C F} (hE : E.IsEffective) {n : ℕ} (hn : Ddeg C F E = (n : ℤ))
    {p : FPt (D.Sym n) F} (hp : (D.symGeom n).divOf p = E) :
    sumDiv D f E hE n hn = p ≫ sumMap D f n := by
  unfold sumDiv
  have h : Classical.choose ((D.symGeom n).divOf_complete E hE hn) = p :=
    (D.symGeom n).divOf_injective _ _
      ((Classical.choose_spec ((D.symGeom n).divOf_complete E hE hn)).trans hp.symm)
  rw [h]

/-! ## 5. Bookkeeping for divisors and `Pic⁰` -/

/-- The degree of the sum of effective divisors of degrees `n`, `m` is `n + m`. -/
theorem ddeg_add {C : CurveBasics.Curve K} {F : Type u} [Field F] [Algebra K F]
    {E E' : Dv C F} {n m : ℕ} (h : Ddeg C F E = (n : ℤ)) (h' : Ddeg C F E' = (m : ℤ)) :
    Ddeg C F (E + E') = ((n + m : ℕ) : ℤ) := by
  rw [map_add, h, h', Nat.cast_add]

/-- The difference of two effective divisors of the same degree `n` has degree zero. -/
theorem ddeg_sub_zero {C : CurveBasics.Curve K} {F : Type u} [Field F] [Algebra K F]
    {E E' : Dv C F} {n : ℕ} (h : Ddeg C F E = (n : ℤ)) (h' : Ddeg C F E' = (n : ℤ)) :
    Ddeg C F (E - E') = 0 := by
  rw [map_sub, h, h', sub_self]

/-- The class of `E - E'` in `Pic⁰`, for effective divisors of the same degree. -/
def mkCls {C : CurveBasics.Curve K} {F : Type u} [Field F] [Algebra K F] (E E' : Dv C F)
    (n : ℕ) (h : Ddeg C F E = (n : ℤ)) (h' : Ddeg C F E' = (n : ℤ)) : Pic0 C F :=
  Pic0.mk (E - E') (ddeg_sub_zero h h')

/-- The degree of a divisor is its degree over the base change of the curve: `Ddeg` is
`Curve.deg` of the base-changed curve. -/
theorem ddeg_eq_deg {C : CurveBasics.Curve K} {F : Type u} [Field F] [Algebra K F]
    (D : Dv C F) : Ddeg C F D = (C.baseChange F).deg D := rfl

/-- Base change of divisors preserves the degree. -/
theorem ddeg_bcKF {C : CurveBasics.Curve K} [SpecLin.DivBase C] {F : Type u} [Field F]
    [Algebra K F] (E : Dv C K) :
    Ddeg C F (bcKF (C := C) F E) = Ddeg C K E := by
  have h := SpecLin.DivBase.deg_bc (C := C) (e := Algebra.ofId K F) E
  rw [ddeg_eq_deg, bcKF]
  exact h

/-- The base divisor `P0Div`, base changed to any field, is effective. -/
theorem bcKF_isEffective {C : CurveBasics.Curve K} {P0 : 𝟙_ (Sch K) ⟶ C.toOver}
    [SpecLin.DivBase C] (D : GroupChunk.Input C P0) {F : Type u} [Field F] [Algebra K F] :
    (bcKF (C := C) F D.P0Div).IsEffective :=
  SpecLin.DivBase.isEffective_bc (Algebra.ofId K F) D.P0Div_isEffective

/-- The base divisor `P0Div` of a chart datum has degree one after base change to any field. -/
theorem bcKF_P0Div_deg {C : CurveBasics.Curve K} {P0 : 𝟙_ (Sch K) ⟶ C.toOver}
    [SpecLin.DivBase C] (D : GroupChunk.Input C P0) {F : Type u} [Field F] [Algebra K F] :
    Ddeg C F (bcKF (C := C) F D.P0Div) = (1 : ℤ) := by
  have h : (C.baseChange K).deg D.P0Div = (1 : ℤ) := D.P0Div_deg
  rw [ddeg_eq_deg, bcKF, SpecLin.DivBase.deg_bc, h]

/-! ## 5b. The unit, the product and the difference of group-valued points

The three definitions below are the vocabulary in which the results of area UP are stated.
They exist so that the statements of area UP can be read without opening the scoped notation
`MonObj` (which is what provides the group structure on `X ⟶ A` for a group object `A`). -/

/-- The finite product `∏ i, u i` of a family of morphisms into a commutative group object:
the sum of the `u i`. -/
def prodHom {A X : Sch K} [GrpObj A] [IsCommMonObj A] {I : Type v} [Fintype I]
    (u : I → (X ⟶ A)) : X ⟶ A :=
  ∏ i, u i

/-- The origin of a group object, as an `F`-point, for a field `F` over `K`: the unit of the
group of `F`-points of `A`. -/
def zeroPt (A : Sch K) [GrpObj A] (F : Type u) [Field F] [Algebra K F] : FPt A F :=
  GroupChunk.toUnit (specOf K F) ≫ η[A]

/-- The quotient (difference) of two `F`-points of a group object. -/
def divPt {A : Sch K} [GrpObj A] {F : Type u} [Field F] [Algebra K F] (x y : FPt A F) :
    FPt A F :=
  x / y

/-! ## 6. The interface: the named hypotheses of areas GC and KL -/

/-- The base point `P0`, base changed to a field `F`: the composite of the unique morphism
`Spec F ⟶ 𝟙_` with `P0`.  (The canonical `K`-point `P0` is a morphism `𝟙_ (Sch K) ⟶ C`)
This is the point whose divisor is the base divisor `P0Div` (see `Input.P0Div_ptDiv`). -/
def P0Pt (C : CurveBasics.Curve K) (P0 : 𝟙_ (Sch K) ⟶ C.toOver) (F : Type u) [Field F]
    [Algebra K F] : FPt C.toOver F :=
  GroupChunk.toUnit (specOf K F) ≫ P0

/-- **The named hypotheses of area UP.**  Beyond the chart datum `D` of area GC and the symmetric
powers, area UP needs

* (GC) the glued group chunk `G D`, its group law, the universal property of the gluing
  (`descG`), properness, geometric integrality and separatedness of `G D`, the Abel–Jacobi maps
  `AJ₀`, `AJSym`, the surjectivity of `AJSym` and the two defining properties of `AJ₀`
  (`AJ₀_pt`, `cls_AJ₀`);
* (KL) the key lemma in its divisor form: `Σ f` is constant on linear equivalence classes
  (`kl`) and additive on sums of effective divisors (`kl_add`).

Every field is an output of another area (GC: `Submission/Work/GroupChunk`, KL:
`Submission/Work/KeyLemma`, SY: `Submission/Work/SymQuot`); none of them is an additional
mathematical assumption. -/
class Input (C : CurveBasics.Curve K) (P0 : 𝟙_ (Sch K) ⟶ C.toOver) [SpecLin.DivBase C]
    [D : GroupChunk.Input C P0] extends SymQuotData C P0 D where
  /-- **(GC)** the glued group chunk. -/
  glued : GroupChunk.Glued (C := C) (P0 := P0)
  /-- **(GC)** the group law of the glued group chunk. -/
  grpObj : GrpObj glued.G
  /-- **(GC)** `G D` is proper over `K`. -/
  isProper_G : IsProper glued.G.hom
  /-- **(GC)** `G D` is geometrically integral over `K`. -/
  geomIntegral_G : GeometricallyIntegral glued.G.hom
  /-- **(GC)** `G D` is separated over `K`. -/
  isSeparated_G : IsSeparated glued.G.hom
  /-- **(GC)** the universal property of the gluing: a family of chart maps which agree on the
  transitions glues to a morphism out of `G D`. -/
  descG : ∀ {Y : Sch K} (φ : ∀ i : D.Idx, Opens.toOver D.V ⟶ Y),
    (∀ i j : D.Idx, Opens.ιOver (GroupChunk.U i j) ≫ φ i =
      (GroupChunk.t i j ≫ Opens.ιOver (GroupChunk.U j i)) ≫ φ j) →
    ∃! g : glued.G ⟶ Y, ∀ i : D.Idx, glued.chart i ≫ g = φ i
  /-- **(GC)** the Abel–Jacobi map based at `P0`. -/
  AJ₀ : C.toOver ⟶ glued.G
  /-- **(GC)** `AJ₀` sends `P0` to the origin. -/
  AJ₀_pt : P0 ≫ AJ₀ = η[glued.G]
  /-- **(GC)** the Abel–Jacobi morphism `Sym^g C ⟶ G D`. -/
  AJSym : D.Sym D.g ⟶ glued.G
  /-- **(GC)** `AJSym` is the `g`-fold sum of `AJ₀` (the lead's `AJSym_quot`). -/
  AJSym_powMap : ∀ {T : Sch K} (x : Fin D.g → (T ⟶ C.toOver)),
    (D.symGeom D.g).powMap x ≫ AJSym = ∏ m, (x m ≫ AJ₀)
  /-- **(GC)** `AJSym` is surjective. -/
  AJSym_surjective : Function.Surjective AJSym.left
  /-- **(GC)** the class of `AJ₀(x)` is `[x] - [P0]`. -/
  cls_AJ₀ : ∀ {F : Type u} [Field F] [Algebra K F] (x : FPt C.toOver F),
    glued.cls (x ≫ AJ₀) =
      mkCls (SpecLin.ptDiv x) (bcKF (C := C) F D.P0Div) 1 (SpecLin.Points.ptDiv_deg x)
        (bcKF_P0Div_deg D)
  /-- **(GC)** the base divisor `P0Div` is the divisor of the point `P0`. -/
  P0Div_ptDiv : ∀ {F : Type u} [Field F] [Algebra K F],
    SpecLin.ptDiv (P0Pt C P0 F) = bcKF (C := C) F D.P0Div
  /-- **(KL, the key lemma.)**  The sum `Σ f` is constant on linear equivalence classes of
  effective divisors of the same degree. -/
  kl : ∀ {A : Sch K} [GrpObj A] [IsCommMonObj A] [IsProper A.hom] (f : C.toOver ⟶ A)
    {F : Type u} [Field F] [Algebra K F] (E E' : Dv C F) (hE : E.IsEffective)
    (hE' : E'.IsEffective) (n : ℕ)
    (hn : Ddeg C F E = (n : ℤ)) (hn' : Ddeg C F E' = (n : ℤ)), LinEquiv C E E' →
    sumDiv D f E hE n hn = sumDiv D f E' hE' n hn'
  /-- **(KL, additivity.)**  The sum `Σ f` is additive on sums of effective divisors. -/
  kl_add : ∀ {A : Sch K} [GrpObj A] [IsCommMonObj A] [IsProper A.hom] (f : C.toOver ⟶ A)
    {F : Type u} [Field F] [Algebra K F] (E E' : Dv C F) (hE : E.IsEffective) (hE' : E'.IsEffective)
    (n m : ℕ) (hn : Ddeg C F E = (n : ℤ)) (hm : Ddeg C F E' = (m : ℤ))
    (hEE' : (E + E').IsEffective),
    sumDiv D f (E + E') hEE' (n + m) (ddeg_add hn hm) =
      sumDiv D f E hE n hn * sumDiv D f E' hE' m hm

/-- The divisor of a point of `Symⁿ C` has degree `n`. -/
theorem ddeg_divOf {C : CurveBasics.Curve K} {P0 : 𝟙_ (Sch K) ⟶ C.toOver}
    [SpecLin.DivBase C] (D : GroupChunk.Input C P0) {n : ℕ} {F : Type u} [Field F]
    [Algebra K F] (p : FPt (D.Sym n) F) : Ddeg C F (D.divOf n p) = (n : ℤ) :=
  (D.symGeom n).divOf_deg p

/-- **The value of `sumMap` at a point is the sum of `f` over the divisor of that point.**  This
is the point-level form of `sumDiv` (the lead's `sumMap_fpt`): the sum `Σ f` of an effective
divisor is the value of the sum morphism at the point of `Symⁿ C` which classifies it. -/
theorem sumMap_fpt {C : CurveBasics.Curve K} {P0 : 𝟙_ (Sch K) ⟶ C.toOver}
    [SpecLin.DivBase C] (D : GroupChunk.Input C P0) [SymQuotData C P0 D] {A : Sch K}
    [GrpObj A] [IsCommMonObj A] (f : C.toOver ⟶ A) (n : ℕ) {F : Type u} [Field F]
    [Algebra K F] (p : FPt (D.Sym n) F) :
    sumDiv D f (D.divOf n p) ((D.symGeom n).divOf_isEffective p) n (ddeg_divOf D p) =
      p ≫ sumMap D f n :=
  sumDiv_eq_of_divOf D f _ _ rfl

/-- `sumDiv` only depends on the divisor. -/
theorem sumDiv_congr {C : CurveBasics.Curve K} {P0 : 𝟙_ (Sch K) ⟶ C.toOver}
    [SpecLin.DivBase C] (D : GroupChunk.Input C P0) [SymQuotData C P0 D] {A : Sch K}
    [GrpObj A] [IsCommMonObj A] (f : C.toOver ⟶ A) {F : Type u} [Field F] [Algebra K F]
    {E E' : Dv C F} (h : E = E') (hE : E.IsEffective) (hE' : E'.IsEffective) (n : ℕ)
    (hn : Ddeg C F E = (n : ℤ)) (hn' : Ddeg C F E' = (n : ℤ)) :
    sumDiv D f E hE n hn = sumDiv D f E' hE' n hn' := by
  subst h
  rfl

/-- The degree of the base-changed divisor of a chart centre `E i` is the genus. -/
theorem ddeg_bcKF_EDiv {C : CurveBasics.Curve K} {P0 : 𝟙_ (Sch K) ⟶ C.toOver}
    [SpecLin.DivBase C] (D : GroupChunk.Input C P0) (i : D.Idx) {F : Type u} [Field F]
    [Algebra K F] : Ddeg C F (bcKF (C := C) F (D.EDiv i)) = (D.g : ℤ) := by
  rw [ddeg_bcKF, D.EDiv_deg]

namespace Input

variable {C : CurveBasics.Curve K} {P0 : 𝟙_ (Sch K) ⟶ C.toOver} [SpecLin.DivBase C]
  [D : GroupChunk.Input C P0] (U : Input C P0)

instance instGrpObj : GrpObj U.glued.G := U.grpObj
instance instIsProper : IsProper U.glued.G.hom := U.isProper_G
instance instGeomIntegral : GeometricallyIntegral U.glued.G.hom := U.geomIntegral_G
instance instIsSeparated : IsSeparated U.glued.G.hom := U.isSeparated_G
instance instIsIntegral : IsIntegral U.glued.G.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton U.glued.G.hom
instance instIsReduced : IsReduced U.glued.G.left := inferInstance

/-- `AJSym` is the `g`-fold sum of `AJ₀`. -/
theorem AJSym_eq_sumMap : U.AJSym = sumMap D U.AJ₀ D.g := by
  refine sumMap_unique D U.AJ₀ D.g ?_
  rw [quotMap]
  simpa only [sumTerm] using U.AJSym_powMap (x := fun m => proj C D.g m)

end Input

/-! ## 7. The chart maps of `factor` -/

/-- **The local chart map of `factor` on the `i`-th chart**: the `i`-th translate of the sum
morphism `Σ^g f` by the centre `E i` of the chart.  This is the lead's
`(V.ι ≫ sumMap f g) - (toUnit ≫ Sym.ofDiv (E i) ≫ sumMap f g)`, with `-` written `/`. -/
def chartMap {C : CurveBasics.Curve K} {P0 : 𝟙_ (Sch K) ⟶ C.toOver} [SpecLin.DivBase C]
    [D : GroupChunk.Input C P0] [U : Input C P0] {A : Sch K} [GrpObj A] [IsCommMonObj A]
    (f : C.toOver ⟶ A) (i : D.Idx) : Opens.toOver D.V ⟶ A :=
  (Opens.ιOver D.V ≫ sumMap D f D.g) /
    (GroupChunk.constE i (Opens.toOver D.V) ≫ sumMap D f D.g)

/-- **The compatibility of the chart maps of `factor`**: on the transition domain `U i j` the
`i`-th and the `j`-th chart map agree, after transporting along the transition `t i j`.  This is
exactly the statement proved from the key lemma of area KL (`Input.kl`) together with the
additivity of the sum (`Input.kl_add`). -/
def factorCompat {C : CurveBasics.Curve K} {P0 : 𝟙_ (Sch K) ⟶ C.toOver} [SpecLin.DivBase C]
    [D : GroupChunk.Input C P0] [U : Input C P0] {A : Sch K} [GrpObj A] [IsCommMonObj A]
    (f : C.toOver ⟶ A) : Prop :=
  ∀ i j : D.Idx, Opens.ιOver (GroupChunk.U i j) ≫ chartMap (D := D) f i =
    (GroupChunk.t i j ≫ Opens.ιOver (GroupChunk.U j i)) ≫ chartMap (D := D) f j

/-- **The morphism `factor` glued from the chart maps**: given the compatibility
`factorCompat f`, the universal property of the gluing (`Input.descG`) produces a morphism
`G D ⟶ A` whose restriction to the `i`-th chart is `chartMap f i`. -/
def factorWith {C : CurveBasics.Curve K} {P0 : 𝟙_ (Sch K) ⟶ C.toOver} [SpecLin.DivBase C]
    [D : GroupChunk.Input C P0] [U : Input C P0] {A : Sch K} [GrpObj A] [IsCommMonObj A]
    (f : C.toOver ⟶ A) (h : factorCompat (D := D) f) : U.glued.G ⟶ A :=
  Classical.choose (U.descG (fun i => chartMap (D := D) f i) h)

/-- The defining property of `factorWith`. -/
theorem factorWith_spec {C : CurveBasics.Curve K} {P0 : 𝟙_ (Sch K) ⟶ C.toOver}
    [SpecLin.DivBase C] [D : GroupChunk.Input C P0] [U : Input C P0] {A : Sch K} [GrpObj A]
    [IsCommMonObj A] (f : C.toOver ⟶ A) (h : factorCompat (D := D) f) (i : D.Idx) :
    U.glued.chart i ≫ factorWith (D := D) f h = chartMap (D := D) f i :=
  (Classical.choose_spec (U.descG (fun i => chartMap (D := D) f i) h)).1 i

end

end Work.Universal
