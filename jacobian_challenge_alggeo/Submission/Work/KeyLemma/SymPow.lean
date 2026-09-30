/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area KL: the sum `Σ f(D)` for *every* effective divisor, through the symmetric power

The key lemma `KL` asks for the sum `Σ f(D) ∈ A(k)` of the images under `f : C ⟶ A` of the
points of an effective divisor `D` of degree `n` on a curve `C` over a field `k`.  The
multiset form of this sum (`Curve.SumDiv.sumOfPoints`) is only available for divisors which
are *split* over `k`, i.e. presented by a multiset of `k`-points (`Curve.SumDiv.toDiv`).

This file removes that restriction.  It records, as an interface, the facts about the
`n`-th symmetric power `Sym^n C` which area `SY` delivers:

* `Curve.SymPow C n` — the scheme `S = Sym^n C` (proper over `k`), the *classification*
  `divOf : Pt k S → C.Div` of `k`-points by effective divisors of degree `n`
  (injective, surjective onto the effective divisors of degree `n`), the addition
  `powMap` of `n` points of `C` together with `divOf (powMap x) = toDiv (∑ m, [x m])`,
  and the *pencil family*: the classifying morphism of the family of fibres of a
  rational function `h` is a morphism `ℙ¹ ⟶ S` whose values at two distinct points are
  the divisors of zeros and of poles of `h` (blueprint KL items 2 and 3).

* `Curve.SymPow.BaseChange` — the naturality of the symmetric power under a base change of
  the field: `(Sym^n C)_F = Sym^n (C_F)`, with the classification of divisors commuting
  with the pullback of divisors `Curve.divMap`.

The two structures contain *no* statement about an abelian variety: they are pure
symmetric-power data.  On top of them this file defines, for `Φ : Sym^n C ⟶ A`,

* `Curve.sumMapPow G Φ D hD hn = Σ f(D) ∈ A(k)`: the value at the point of `S` classified
  by `D` of the morphism `Φ`.  This is a function of `D` (`Curve.sumMapPow_spec`) defined for
  *every* effective divisor of degree `n`, and `Curve.sumMap G Φ : EffDiv C n → Pt k A` is
  the resulting total map (blueprint item 6);

* `Curve.IsSumMorphism G Φ f`: the specification of `Φ` as the sum morphism of `f`, and
  `Curve.sumMapPow_eq_sum`: on a divisor which is split, `Σ f(D)` is the sum of the images
  of its points.
-/
import Submission.Work.KeyLemma.Main
import Submission.Work.AbVar.ProjectiveLine

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonObj MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.Obj

universe u

namespace Work.KeyLemma

open Work.CurveBasics

namespace Curve

noncomputable section

variable {k : Type u} [Field k]

/-- **The `n`-th symmetric power of a curve** (area `SY`), in the form in which area `KL`
uses it.  Every field is a fact about `Sym^n C` alone; none of them mentions an abelian
variety. -/
structure SymPow (C : Curve k) (n : ℕ) where
  /-- The scheme `Sym^n C`. -/
  S : Over (Spec (CommRingCat.of k))
  /-- `Sym^n C` is proper (hence separated) over `k`. -/
  isProper : IsProper S.hom
  /-- The effective divisor of degree `n` classified by a `k`-point of `Sym^n C`. -/
  divOf : Pt k S → C.Div
  /-- A point of `Sym^n C` is determined by the divisor it classifies. -/
  divOf_injective : Function.Injective divOf
  /-- The classified divisor is effective. -/
  divOf_isEffective : ∀ p : Pt k S, (divOf p).IsEffective
  /-- The classified divisor has degree `n`. -/
  divOf_deg : ∀ p : Pt k S, C.deg (divOf p) = (n : ℤ)
  /-- Every effective divisor of degree `n` is classified by a point of `Sym^n C`. -/
  divOf_complete : ∀ D : C.Div, D.IsEffective → C.deg D = (n : ℤ) → ∃ p : Pt k S, divOf p = D
  /-- The sum of `n` points of `C`, as a point of `Sym^n C`. -/
  powMap : (Fin n → Point C) → Pt k S
  /-- The divisor classified by the sum of `n` points is the sum of their divisors. -/
  divOf_powMap : ∀ x : Fin n → Point C,
    divOf (powMap x) = SumDiv.toDiv C (∑ m, Finsupp.single (x m) 1)
  /-- **The pencil family** (blueprint KL items 2 and 3, area `SY`): the classifying morphism
  of the family of fibres of a rational function `h` of degree `n` is a morphism
  `ℙ¹ ⟶ Sym^n C`, whose values at two distinct points of `ℙ¹` are the divisors of zeros and
  of poles of `h`.  Its existence is the statement that `Sym^n C` classifies *families* of
  relative effective divisors (not only divisors over a field). -/
  pencil : ∀ h : C.functionField, h ≠ 0 → ¬ IsConstant C h →
    C.deg (posPart C h) = (n : ℤ) →
    ∃ (ψ : Work.AbVar.P1 k ⟶ S) (z i : Pt k (Work.AbVar.P1 k)), z ≠ i ∧
      divOf (z ≫ ψ) = posPart C h ∧ divOf (i ≫ ψ) = negPart C h

namespace SymPow

variable {C : Curve k} {n : ℕ}

/-- **The naturality of the symmetric power under base change of the field** (area `SY`):
the base change of `Sym^n C` is the symmetric power of `C_F`, and the classification of
divisors, as well as the addition of points, commute with the base change functor. -/
structure BaseChange (G : SymPow C n) (F : Type u) [Field F] [Algebra k F] where
  /-- The symmetric power of the base-changed curve. -/
  G' : SymPow (C.baseChange F) n
  /-- The identification of the base change of `S = Sym^n C` with `S' = Sym^n (C_F)`. -/
  iso : (baseChangeFunctor k F).obj G.S ≅ G'.S
  /-- The classification of divisors commutes with base change. -/
  divOf_iso : ∀ p : Pt k G.S,
    G'.divOf (Pt.baseChange F p ≫ iso.hom) = Curve.divMap C F (G.divOf p)
  /-- The addition of points commutes with base change. -/
  powMap_iso : ∀ x : Fin n → Point C,
    G'.powMap (fun m => Pt.baseChange F (x m)) =
      Pt.baseChange F (G.powMap x) ≫ iso.hom
  /-- The pullback of divisors along a field extension preserves effectivity (area `CB`). -/
  divMap_isEffective : ∀ {D : C.Div}, D.IsEffective → (Curve.divMap C F D).IsEffective
  /-- The pullback of divisors along a field extension preserves the degree (area `CB`). -/
  divMap_deg : ∀ D : C.Div, (C.baseChange F).deg (Curve.divMap C F D) = C.deg D

end SymPow

/-! ## The sum map -/

variable {C : Curve k} {n : ℕ}

/-- **The sum morphism**: `Φ : Sym^n C ⟶ A` computes the sum of the images of `n` points
of `C` under `f : C ⟶ A`.  This is the specification of the sum morphism of area `UP`. -/
def IsSumMorphism (G : SymPow C n) {A : Over (Spec (CommRingCat.of k))} [GrpObj A]
    [IsCommMonObj A] (Φ : G.S ⟶ A) (f : C.toOver ⟶ A) : Prop :=
  ∀ x : Fin n → Point C, G.powMap x ≫ Φ = ∏ m, (x m ≫ f)

/-- **The sum `Σ f(D)` of an effective divisor `D` of degree `n`**, computed through the
symmetric power: the value at the point of `Sym^n C` classified by `D` of the sum morphism
`Φ`.  This is defined for *every* effective divisor of degree `n`; no splitting hypothesis
is needed. -/
noncomputable def sumMapPow (G : SymPow C n)
    {A : Over (Spec (CommRingCat.of k))} [GrpObj A] (Φ : G.S ⟶ A) (D : C.Div)
    (hD : D.IsEffective) (hn : C.deg D = (n : ℤ)) : Pt k A :=
  (Classical.choose (G.divOf_complete D hD hn)) ≫ Φ

/-- The defining property of `sumMapPow`: it is the value of `Φ` at the point of `Sym^n C`
classified by `D`.  In particular `Σ f(D)` depends only on `D`. -/
theorem sumMapPow_spec (G : SymPow C n)
    {A : Over (Spec (CommRingCat.of k))} [GrpObj A] (Φ : G.S ⟶ A)
    {D : C.Div} (hD : D.IsEffective) (hn : C.deg D = (n : ℤ))
    {p : Pt k G.S} (hp : G.divOf p = D) : sumMapPow G Φ D hD hn = p ≫ Φ := by
  unfold sumMapPow
  have h : G.divOf (Classical.choose (G.divOf_complete D hD hn)) = G.divOf p := by
    rw [Classical.choose_spec (G.divOf_complete D hD hn), hp]
  rw [G.divOf_injective h]

/-- **The sum map** on the effective divisors of degree `n` (blueprint item 6): the function
`Σ f : EffDiv_n(C) → A(k)`, defined for *every* effective divisor of degree `n`. -/
noncomputable def sumMap (G : SymPow C n)
    {A : Over (Spec (CommRingCat.of k))} [GrpObj A] (Φ : G.S ⟶ A) (E : EffDiv C n) :
    Pt k A :=
  sumMapPow G Φ E.1 E.isEffective E.deg_eq

@[simp]
theorem sumMap_apply (G : SymPow C n)
    {A : Over (Spec (CommRingCat.of k))} [GrpObj A] (Φ : G.S ⟶ A) (E : EffDiv C n) :
    sumMap G Φ E = sumMapPow G Φ E.1 E.isEffective E.deg_eq := rfl

/-- On a divisor which is a sum of `n` points of `C` (i.e. on `divOf (powMap x)`), the sum
map computes the sum of the images of those points. -/
theorem sumMapPow_eq_sum (G : SymPow C n)
    {A : Over (Spec (CommRingCat.of k))} [GrpObj A] [IsCommMonObj A]
    {Φ : G.S ⟶ A} {f : C.toOver ⟶ A} (hΦ : IsSumMorphism G Φ f)
    {D : C.Div} (hD : D.IsEffective) (hn : C.deg D = (n : ℤ)) {x : Fin n → Point C}
    (hx : G.divOf (G.powMap x) = D) : sumMapPow G Φ D hD hn = ∏ m, (x m ≫ f) := by
  rw [sumMapPow_spec G Φ hD hn hx, hΦ]

/-! ## The base change of the sum map

The following definitions package, in the form in which the base-change lemmas are stated,
the two sides of the statement "`Σ f` commutes with the base change of the field": the base
change `Pt.baseChange` of `Σ f(D)`, and the sum `Σ f` computed on the base-changed curve.
Stating the lemmas in terms of these definitions keeps their statements free of the
scoped instances which the base change functor carries. -/

/-- **The sum `Σ f` computed on the base-changed curve**: the value of the base-changed sum
morphism `bc.iso.inv ≫ F.map Φ` at the point classified by the pullback of `D`. -/
noncomputable def sumMapPowBC (G : SymPow C n)
    {A : Over (Spec (CommRingCat.of k))} [GrpObj A] (Φ : G.S ⟶ A)
    {L : Type u} [Field L] [Algebra k L] (bc : G.BaseChange L) (D : C.Div)
    (hD : D.IsEffective) (hn : C.deg D = (n : ℤ)) : Pt L ((baseChangeFunctor k L).obj A) :=
  sumMapPow bc.G' (bc.iso.inv ≫ (baseChangeFunctor k L).map Φ) (Curve.divMap C L D)
    (bc.divMap_isEffective hD) ((bc.divMap_deg D).trans hn)

/-- **The base change of the sum `Σ f(D)`** along a field extension. -/
noncomputable def sumMapPowBaseChange (G : SymPow C n)
    {A : Over (Spec (CommRingCat.of k))} [GrpObj A] (Φ : G.S ⟶ A)
    {L : Type u} [Field L] [Algebra k L] (D : C.Div) (hD : D.IsEffective)
    (hn : C.deg D = (n : ℤ)) : Pt L ((baseChangeFunctor k L).obj A) :=
  Pt.baseChange L (sumMapPow G Φ D hD hn)

/-- **The base change of the summation property of `Φ`**: the base-changed sum morphism
computes the sums of the images of the base-changed points. -/
def IsSumMorphismBC (G : SymPow C n)
    {A : Over (Spec (CommRingCat.of k))} [GrpObj A] [IsCommMonObj A] (Φ : G.S ⟶ A)
    {L : Type u} [Field L] [Algebra k L] (bc : G.BaseChange L) (f : C.toOver ⟶ A) : Prop :=
  IsSumMorphism bc.G' (bc.iso.inv ≫ (baseChangeFunctor k L).map Φ)
    ((baseChangeFunctor k L).map f)

/-- **The pencil statement in degree `n`**: for a nonconstant rational function `h` whose
divisor of zeros has degree `n`, the sums of the images of the points of the divisors of zeros
and of poles of `h` are the values of a single morphism `ℙ¹ ⟶ A` at two distinct points.
This is the degree-`n` case of `Curve.PencilGeometric`; it *is* a consequence of the
symmetric-power interface (`Curve.pencil_of_symPow`), because a pencil of degree `n` is a
family of divisors of degree `n`, hence classified by `Sym^n C`.

It is *not* the full `Curve.PencilGeometric`: the key lemma reduces a pair `D ~ D'` of
effective divisors of degree `n` to the pencil of a rational function `h` with
`D = div₀ h + E`, `D' = div_∞ h + E` for a common effective `E`, and `div₀ h` has degree
`n - deg E`, which is in general *strictly smaller* than `n`.  Divisors of degree `< n` are
not classified by `Sym^n C`, so the lower-degree pencil statement is genuinely additional
input (the specialisation of the sums of the fibres of `h`, blueprint KL item 3). -/
def PencilAt (C : Curve k) (n : ℕ)
    {A : Over (Spec (CommRingCat.of k))} [GrpObj A] [IsCommMonObj A]
    (f : C.toOver ⟶ A) : Prop :=
  ∀ (h : C.functionField), h ≠ 0 → ¬ IsConstant C h → C.deg (posPart C h) = (n : ℤ) →
    ∀ s₀ s₁ : SumDiv C, SumDiv.toDiv C s₀ = posPart C h → SumDiv.toDiv C s₁ = negPart C h →
    ∃ (φ : Work.AbVar.P1 k ⟶ A) (z i : Pt k (Work.AbVar.P1 k)), z ≠ i ∧
      z ≫ φ = SumDiv.sumOfPoints C f s₀ ∧ i ≫ φ = SumDiv.sumOfPoints C f s₁

/-- **The pencil statement after a base change of the field**: the geometric input of the key
lemma for the base-changed curve and the base-changed abelian variety.  Stating it as a
definition keeps the statement of the base-change results free of the scoped instances which
the base change functor carries. -/
def PencilGeometricBaseChange {k : Type u} [Field k] {C : Curve k} (L : Type u) [Field L]
    [Algebra k L] {A : Over (Spec (CommRingCat.of k))} [GrpObj A] [IsCommMonObj A]
    (f : C.toOver ⟶ A) : Prop :=
  PencilGeometric (C.baseChange L) ((baseChangeFunctor k L).map f)

/-- **The sum morphisms of `f` at every level**: for every `m` a symmetric power `Sym^m C`
and a morphism from it to `A` which computes the sum of the images of `m` points of `C`
under `f`.  This is the data which area `UP` produces from `f` (the `S_m`-invariant morphism
`C^m ⟶ A` factored through the quotient `Sym^m C`); it is what turns the symmetric-power
statement "the fibres of a rational function are classified by a morphism out of `ℙ¹`" into
the geometric input `Curve.PencilGeometric` of the key lemma, *without* any further
assumption about `A`. -/
structure SumMorphisms (C : Curve k) {A : Over (Spec (CommRingCat.of k))} [GrpObj A]
    [IsCommMonObj A] (f : C.toOver ⟶ A) where
  /-- The `m`-th symmetric power of `C`. -/
  sym : ∀ m : ℕ, SymPow C m
  /-- The sum morphism `Sym^m C ⟶ A`. -/
  Φ : ∀ m : ℕ, (sym m).S ⟶ A
  /-- The sum morphism computes the sums of the images of `m` points. -/
  isSum : ∀ m : ℕ, IsSumMorphism (sym m) (Φ m) f

/-- **The sum morphisms after a base change of the field**: the data of `Curve.SumMorphisms`
for the base-changed curve and the base-changed abelian variety.  Stated as `Nonempty` so that
it can be used as a hypothesis without carrying the scoped instances of the base change
functor in the statement. -/
def SumMorphismsBC {k : Type u} [Field k] {C : Curve k}
    {A : Over (Spec (CommRingCat.of k))} [GrpObj A] [IsCommMonObj A]
    (f : C.toOver ⟶ A) (L : Type u) [Field L] [Algebra k L] : Prop :=
  Nonempty (SumMorphisms (C.baseChange L) ((baseChangeFunctor k L).map f))

end

end Curve

end Work.KeyLemma
