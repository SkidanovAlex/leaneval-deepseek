/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area KL, layer 3: the key lemma from the pencil input

This file proves the key lemma `KL` of the Jacobian challenge (see
`Submission/Work/NOTES_LEAD_jacobian_blueprint.md`, §3, area KL):

> if `D`, `D'` are effective divisors of a curve `C` over a field `k` with
> `D - D' = div h`, then `Σ f(D) = Σ f(D')` in `A(k)`,

in the "split" form in which it is actually used (see `Work.KeyLemma.Curve.SumDiv`): the
divisors are given by *multisets of `k`-points* of `C` -- their models -- and the sums are
the sums of the images of those points in the commutative group `A(k)` of `k`-points of `A`.

Two ingredients are *not* proved here, because they belong to other areas of the blueprint;
they are the two fields of the structure `KeyLemmaInput`:

* `pencil_geometric`: the fibrewise sum of a pencil `h` is represented by a morphism
  `ℙ¹ ⟶ A`.  This is `SY` (the symmetric powers `Sym^n C` and their points, i.e. the
  statement that the multiset of geometric points of the generic fibre of `h` is Galois
  invariant and that `t ↦ Σ f(h⁻¹(t))` is a morphism) together with the specialisation
  bookkeeping at `t = 0, ∞` (blueprint KL items 2 and 3).
* `p1_const`: every morphism `ℙ¹ ⟶ B` into a proper group scheme over `k` is constant
  (`P1CONST`, area `AV`, `Work.AbVar.ProjectiveLine.isConstant_of_projectiveLine`).

Everything else -- the reduction of linear equivalence to a pencil, the splitting of the
models, and the conclusion -- is proved here.

## Main results

* `Work.KeyLemma.Curve.pencil_eq`: for models of `div₀ h` and `div_∞ h`, the sums agree.
* `Work.KeyLemma.Curve.sumOfPoints_eq_of_linEquiv`: the key lemma in model form, from
  `KeyLemmaInput`.
* `Work.KeyLemma.Curve.SumDiv.sumOfPoints_eq_of_div_eq`: the same for a divisor
  `D` given by *two* models (equality of divisors instead of linear equivalence); this
  is the case `h` constant and only needs `toDiv`-injectivity.
-/
import Submission.Work.KeyLemma.Sum
import Submission.Work.KeyLemma.Sum.exists_common_add_of_toDiv_eq_add
import Submission.Work.AbVar.ProjectiveLine
import Submission.Work.AbVar.ProjectiveLine.isConstant_of_projectiveLine

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonObj MonoidalCategory CartesianMonoidalCategory

universe u

namespace Work.KeyLemma

open Work.CurveBasics

namespace Curve

noncomputable section

variable {k : Type u} [Field k]

/-! ## The two inputs -/

/-- A rational function on a curve is *constant* if it is the image of an element of the
base field.  (`div h = 0` implies that `h` is constant; only the converse is needed and
proved below.) -/
def IsConstant (C : Curve k) (h : C.functionField) : Prop :=
  ∃ c : k, h = algebraMap k C.functionField c

theorem div_eq_zero_of_isConstant (C : Curve k) {h : C.functionField} (hh : IsConstant C h) :
    C.div h = 0 := by
  obtain ⟨c, rfl⟩ := hh
  exact Work.CurveBasics.Order.div_algebraMap_eq_zero C c

/-- **The geometric input of the key lemma** (blueprint KL items 2 and 3): for a
nonconstant rational function `h` and any two multisets of `k`-points whose divisors are the
divisors of zeros and of poles of `h`, the two sums are the values of a *single* morphism
`ℙ¹ ⟶ A` at two distinct points of `ℙ¹`.

Concretely, the morphism is `t ↦ Σ f(h⁻¹(t))`: it is a morphism because the multiset of
points of the fibre of a finite morphism of curves is a morphism into the symmetric power
`Sym^n C` (area `SY`) and because `Σ f` is an `Sₙ`-invariant morphism `C^n ⟶ A`; the values
at `t = 0` and `t = ∞` are the two sums, by the specialisation of the characteristic
polynomial of a section of the structure sheaf along the pencil (blueprint KL item 3).

This is the only place where the geometry of pencils is used; it is *not* assumed for
constant `h`, where the two models have the same divisor and `toDiv`-injectivity applies. -/
def PencilGeometric (C : Curve k) {A : Over (Spec (CommRingCat.of k))} [GrpObj A]
    [IsCommMonObj A] (f : C.toOver ⟶ A) : Prop :=
  ∀ (h : C.functionField) (_ : h ≠ 0) (_ : ¬ IsConstant C h) (s₀ s₁ : SumDiv C),
    SumDiv.toDiv C s₀ = posPart C h → SumDiv.toDiv C s₁ = negPart C h →
    ∃ (φ : Work.AbVar.P1 k ⟶ A) (z i : Pt k (Work.AbVar.P1 k)), z ≠ i ∧
      z ≫ φ = SumDiv.sumOfPoints C f s₀ ∧ i ≫ φ = SumDiv.sumOfPoints C f s₁

/-- **`P1CONST`** (area `AV`): every morphism from the projective line into a proper group
scheme over `k` is constant.  This is verbatim
`Work.AbVar.ProjectiveLine.isConstant_of_projectiveLine`
(`Submission/Work/AbVar/ProjectiveLine/isConstant_of_projectiveLine.lean`). -/
def P1Const (k : Type u) [Field k] : Prop :=
  ∀ {B : Over (Spec (CommRingCat.of k))} [GrpObj B] [IsProper B.hom]
    (φ : Work.AbVar.P1 k ⟶ B),
    ∃ c : Pt k B, φ = SemiCartesianMonoidalCategory.toUnit (Work.AbVar.P1 k) ≫ c

/-- **`P1CONST` is a theorem of the workspace, not an input of the key lemma**: it is the
statement `Work.AbVar.ProjectiveLine.isConstant_of_projectiveLine` of area `AV` (rigidity of
morphisms out of `ℙ¹`), restated here in the vocabulary of this area. -/
theorem p1Const (k : Type u) [Field k] : P1Const k := by
  intro B _ _ φ
  exact Work.AbVar.ProjectiveLine.isConstant_of_projectiveLine φ

/-- The inputs of the key lemma, isolated so that the theorem below is a statement about
them: `pencil_geometric` is the `SY` + specialisation input, and `toDiv_injective` is the
fact that a multiset of `k`-points is determined by the effective divisor it defines
(`Work.KeyLemma.Sum.toDiv_injective`).  The remaining geometric input `P1CONST` is *proved*
in this area (`Work.KeyLemma.Curve.p1Const`). -/
structure KeyLemmaInput (C : Curve k) (A : Over (Spec (CommRingCat.of k))) [GrpObj A]
    [IsProper A.hom] [IsCommMonObj A] (f : C.toOver ⟶ A) : Prop where
  /-- A `k`-point of a curve is determined by its image place: the sum `Σ f(D)` of an
  effective divisor which is split over `k` is well defined. -/
  toDiv_injective : Function.Injective (SumDiv.toDiv C)
  /-- The fibrewise sum of a pencil is a morphism `ℙ¹ ⟶ A` (area `SY` + specialisation). -/
  pencil_geometric : PencilGeometric C f

/-! ## The pencil case -/

/-- **Pencil case of the key lemma.**  If the divisors of zeros and of poles of a
nonconstant rational function `h` are split over `k` with models `s₀` and `s₁`, then the
sums of the images of the points of `s₀` and `s₁` agree.

This is the step in which `P1CONST` is used: `PencilGeometric` exhibits the two sums as the
values at two distinct points of a morphism `ℙ¹ ⟶ A`, which is constant. -/
theorem pencil_eq (C : Curve k) {A : Over (Spec (CommRingCat.of k))} [GrpObj A]
    [IsProper A.hom] [IsCommMonObj A] (f : C.toOver ⟶ A) (K : KeyLemmaInput C A f)
    {h : C.functionField} (hh : h ≠ 0) (hnc : ¬ IsConstant C h) {s₀ s₁ : SumDiv C}
    (hs₀ : SumDiv.toDiv C s₀ = posPart C h) (hs₁ : SumDiv.toDiv C s₁ = negPart C h) :
    SumDiv.sumOfPoints C f s₀ = SumDiv.sumOfPoints C f s₁ := by
  obtain ⟨φ, z, i, _, hz, hi⟩ := K.pencil_geometric h hh hnc s₀ s₁ hs₀ hs₁
  obtain ⟨c, hc⟩ := p1Const k φ
  have hz' : z ≫ φ = c := by
    rw [hc, ← Category.assoc,
      show z ≫ SemiCartesianMonoidalCategory.toUnit (Work.AbVar.P1 k) =
        𝟙 (𝟙_ (Over (Spec (CommRingCat.of k)))) from Subsingleton.elim _ _, Category.id_comp]
  have hi' : i ≫ φ = c := by
    rw [hc, ← Category.assoc,
      show i ≫ SemiCartesianMonoidalCategory.toUnit (Work.AbVar.P1 k) =
        𝟙 (𝟙_ (Over (Spec (CommRingCat.of k)))) from Subsingleton.elim _ _, Category.id_comp]
  rw [← hz, ← hi, hz', hi']

/-! ## The key lemma -/

/-- If two multisets of `k`-points of `C` define the same effective divisor, then the sums
of their images agree.  This is the "constant `h`" case of the key lemma and uses only the
injectivity of `toDiv`. -/
theorem sumOfPoints_eq_of_toDiv_eq (C : Curve k)
    {A : Over (Spec (CommRingCat.of k))} [GrpObj A] [IsCommMonObj A]
    (f : C.toOver ⟶ A) (hinj : Function.Injective (SumDiv.toDiv C)) {s s' : SumDiv C}
    (h : SumDiv.toDiv C s = SumDiv.toDiv C s') :
    SumDiv.sumOfPoints C f s = SumDiv.sumOfPoints C f s' :=
  SumDiv.sumOfPoints_of_toDiv_eq C f hinj h

/-- **The key lemma `KL`** (in model form).  Let `s`, `s'` be multisets of `k`-points of a
curve `C` whose effective divisors `toDiv s`, `toDiv s'` are linearly equivalent, say
`div h = toDiv s - toDiv s'` for a nonzero rational function `h`.  Then the sums of the
images of the points of `s` and of `s'` in the commutative group `A(k)` of `k`-points of an
abelian variety `A` agree.

The proof is the one of the blueprint: write `D = div₀ h + E` and `D' = div_∞ h + E` with
`E` effective (the *pencil decomposition*, `Work.KeyLemma.Curve.pencil_decomposition`); split
the two multisets into a common part `sE` (the model of `E`) and models `sA`, `sA'` of
`div₀ h` and `div_∞ h` (`Work.KeyLemma.Sum.exists_common_add_of_toDiv_eq_add`); the sums are
then `Σ sA * Σ sE` and `Σ sA' * Σ sE`, and `Σ sA = Σ sA'` is the pencil case
`Work.KeyLemma.Curve.pencil_eq`. -/
theorem sumOfPoints_eq_of_linEquiv (C : Curve k)
    {A : Over (Spec (CommRingCat.of k))} [GrpObj A] [IsProper A.hom] [IsCommMonObj A]
    (f : C.toOver ⟶ A) (K : KeyLemmaInput C A f) {s s' : SumDiv C} {h : C.functionField}
    (hh : h ≠ 0) (hdiv : C.div h = SumDiv.toDiv C s - SumDiv.toDiv C s') :
    SumDiv.sumOfPoints C f s = SumDiv.sumOfPoints C f s' := by
  by_cases hc : IsConstant C h
  · have h0 : C.div h = 0 := div_eq_zero_of_isConstant C hc
    rw [h0] at hdiv
    exact sumOfPoints_eq_of_toDiv_eq C f K.toDiv_injective (sub_eq_zero.mp hdiv.symm)
  · have hD : (SumDiv.toDiv C s).IsEffective := SumDiv.toDiv_isEffective C s
    have hD' : (SumDiv.toDiv C s').IsEffective := SumDiv.toDiv_isEffective C s'
    obtain ⟨E, hE, hDeq, hD'eq⟩ := exists_pencil_decomposition C hD hD' hdiv
    obtain ⟨sA, sA', sE, hs1, hs2, htA, htA', _⟩ :=
      Work.KeyLemma.Sum.exists_common_add_of_toDiv_eq_add (C := C) (s := s) (s' := s')
        (A := posPart C h) (A' := negPart C h) (E := E)
        (posPart_isEffective C h) (negPart_isEffective C h) hE hDeq hD'eq
    have hpen : SumDiv.sumOfPoints C f sA = SumDiv.sumOfPoints C f sA' :=
      pencil_eq C f K hh hc htA htA'
    rw [hs1, hs2, SumDiv.sumOfPoints_add, SumDiv.sumOfPoints_add, hpen]

end

end Curve

end Work.KeyLemma
