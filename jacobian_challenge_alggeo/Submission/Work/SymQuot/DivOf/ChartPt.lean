/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A point of `Symⁿ C` in a chart (area SY, `divOf`)

This file provides `Work.SymQuot.DivOf.ChartPt`: the data of a point `p` of `Symⁿ C` over a
field `F` together with

* an affine open `V ⊆ C` whose chart in `Symⁿ C` contains the image of `p` (the chart of
  `U = piOpen C.toOver V n = Vⁿ ⊆ Cⁿ` is `Spec A` with `A = Γ(Cⁿ,U)^{S_n}`, whose elements are
  the `S_n`-invariant regular functions on `Vⁿ`), and
* the induced point `q` of that chart, i.e. the ring homomorphism `ChartPt.φ : A →+* F`.

The construction of `ChartPt` (`ChartPt.exists`) is proved downstream, as is the *key lemma*
`ChartPt.φ_eq_evalMap`: the value under `φ` of an invariant function on `Vⁿ` equals its value at
any lift `x : Fin n → C(F')` of `p` to a field extension `F' ⊇ F`.

The characteristic polynomial `χ_b ∈ F[T]` of `b ∈ Γ(C,V)` at `p` is `ChartPt.charpolyValue`,
and `ChartPt.localIdealSet` is the set of `b` with `χ_b = Tⁿ` — the ideal of definition of the
divisor of `p` (the ideal property is proved downstream).

* `ChartPt.φ` — the point of the chart as a ring hom `A →+* F`;
* `ChartPt.evalMap` — the evaluation `Γ(Cⁿ,Vⁿ) →+* F'` at an `F'`-point `x` of `Vⁿ`;
* `ChartPt.charpolyValue` — the characteristic polynomial `χ_b ∈ F[T]`;
* `ChartPt.localIdealSet` — the set `{b | χ_b = Tⁿ}`.
-/
import Submission.Work.SymQuot.DivOf.SymChart
import Submission.Work.SpecLin.Points.Setup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot

namespace DivOf

open Work.SpecLin (FPt CurveFPt RPt)

variable {K : Type u} [Field K]
variable (C : Work.CurveBasics.Curve K) (n : ℕ) [NeZero n] [CurveAffineCover C]

/-- **A point of `Symⁿ C` together with a chart containing it.**

`V` is an affine open of `C`, the chart of `U = piOpen C.toOver V n` is `Spec A` with
`A = Γ(Cⁿ,U)^{S_n}`, and `q : Spec F ⟶ Spec A` is the point of the chart whose image under the
chart inclusion is `p`. -/
structure ChartPt {F : Type u} [Field F] [Algebra K F] (p : FPt (Sym C n) F) where
  /-- the affine open of `C` whose chart contains the image of `p` -/
  V : C.left.Opens
  /-- it is affine -/
  isAffineOpen_V : IsAffineOpen V
  /-- the point of the chart `Spec Γ(Cⁿ,Vⁿ)^{S_n}` -/
  q : Spec (CommRingCat.of F) ⟶
    (symAction C n).chart (piOpen C.toOver V n) (symPiOpen_invariant C n V)
  /-- the compatibility with `p` -/
  fac : q ≫ (symData C n).chartι ⟨piOpen C.toOver V n,
      Prod.isAffineOpen_piOpen C.toOver n V isAffineOpen_V,
      symPiOpen_invariant C n V⟩ = p.left

namespace ChartPt

variable {C n} {F : Type u} [Field F] [Algebra K F] {p : FPt (Sym C n) F} (d : ChartPt C n p)

/-- The chart ring `A = Γ(Cⁿ, Vⁿ)^{S_n}` of the chart containing the point. -/
noncomputable abbrev chartRingOf : Subring Γ((prod C.toOver n).left, piOpen C.toOver d.V n) :=
  chartInvariants (C := C) (n := n) (piOpen C.toOver d.V n) (symPiOpen_invariant C n d.V)

/-- The invariant open `Vⁿ ⊆ Cⁿ` of the chart. -/
noncomputable abbrev openOf (d : ChartPt C n p) : (prod C.toOver n).left.Opens := piOpen C.toOver d.V n

/-- **The point of the chart as a ring homomorphism `A →+* F`**, obtained from `q` by
identifying the sections of `Spec A` with `A` and those of `Spec F` with `F`. -/
noncomputable def φ (d : ChartPt C n p) : ↥d.chartRingOf →+* F :=
  ((Scheme.ΓSpecIso (GAction.chartRing (symAction C n) d.openOf (symPiOpen_invariant C n d.V))).inv ≫
    d.q.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of F)).hom).hom

/-- **The evaluation map** `Γ(Cⁿ, Vⁿ) →+* F'` of an `F'`-point `x` of `Vⁿ ⊆ Cⁿ`: the pullback
of regular functions along `Π m, x_m : Spec F' ⟶ Cⁿ`, using that the image lies in `Vⁿ`. -/
noncomputable def evalMap (d : ChartPt C n p) {F' : Type u} [Field F'] [Algebra K F']
    (x : Fin n → CurveFPt C F')
    (h : ⊤ ≤ ((Limits.Pi.lift x : Work.SpecLin.specOf (K := K) F' ⟶ prod C.toOver n)).left ⁻¹ᵁ
      d.openOf) :
    Γ((prod C.toOver n).left, d.openOf) →+* F' :=
  ((Scheme.ΓSpecIso (CommRingCat.of F')).hom.hom).comp
    ((Scheme.Hom.appLE (Limits.Pi.lift x).left d.openOf ⊤ h).hom)

/-- **The characteristic polynomial `χ_b ∈ F[T]` of `b ∈ Γ(C,V)` at the point `p`**: the
polynomial whose coefficients are the elementary symmetric functions of the values of `b` on
the divisor of `p`.  It is `charpoly` with every coefficient evaluated through `φ`. -/
noncomputable def charpolyValue (d : ChartPt C n p) (b : Γ(C.left, d.V)) : Polynomial F :=
  ∑ i ∈ Finset.range (n + 1),
    Polynomial.C (d.φ ⟨(charpoly C n d.V b).coeff i,
      charpoly_coeff_mem_chartInvariants C n d.V (symPiOpen_invariant C n d.V) b i⟩) *
      Polynomial.X ^ i

@[simp]
theorem charpolyValue_def (d : ChartPt C n p) (b : Γ(C.left, d.V)) :
    d.charpolyValue b =
      ∑ i ∈ Finset.range (n + 1),
        Polynomial.C (d.φ ⟨(charpoly C n d.V b).coeff i,
          charpoly_coeff_mem_chartInvariants C n d.V (symPiOpen_invariant C n d.V) b i⟩) *
          Polynomial.X ^ i := rfl

/-- **The local ideal of definition of the divisor of `p`**, as a set: the elements `b` of
`Γ(C,V)` whose characteristic polynomial at `p` is `Tⁿ`, i.e. the regular functions on `V`
vanishing on the divisor of `p`.

The fact that this is an ideal, and that it equals `⋂_m ker (ev_x ∘ b ↦ b^(m))` for any lift
`x`, is proved downstream (`Work.SymQuot.DivOf.isIdeal_localIdealSet`). -/
def localIdealSet (d : ChartPt C n p) : Set Γ(C.left, d.V) :=
  {b | d.charpolyValue b = Polynomial.X ^ n}

@[simp]
theorem mem_localIdealSet (d : ChartPt C n p) (b : Γ(C.left, d.V)) :
    b ∈ d.localIdealSet ↔ d.charpolyValue b = Polynomial.X ^ n := Iff.rfl

end ChartPt

end DivOf

end Work.SymQuot
