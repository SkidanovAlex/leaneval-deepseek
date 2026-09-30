/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area CH: the Brill–Noether chart built on the product `C^g`

The Brill–Noether chart of §3.5 of `NOTES_LEAD_jacobian_GC.md` is the open subscheme
`D(δ) ⊆ Sym^g C` where `δ = det (h_j(x_m))²` is the determinant of the values of a basis
`h_1, …, h_g` of `L(W)` at the `g` points of a degree-`g` divisor.

The design constructs `δ` as a section of the *affine chart* `Sym^g(U)` of the symmetric
power (area `SY`).  This file builds it instead on the `g`-fold **product** `C^g`, whose
geometry is available from the interface `Work.SpecLin.SymGeom` alone: the quotient map

  `quotMap C g : C^g ⟶ Sym^g C`,   `(x_m) ↦ Σ_m [x_m]`

is `SymGeom.powMap` applied to the coordinate projections.  A section `δ` of `Γ(C^g, U^g)`
with `δ(q) = det (h_j(x_m))²` is what one needs, and the chart of `Sym^g C` is then recovered
from `δ` by taking the complement of the image of `C^g ∖ D(δ)` under `quotMap`.

## Contents

* `Cprod C n`, `coord`, `quotMap` — the product, its coordinates and the quotient map;
* `divOf_quotMap` — `divOf (quotMap q) = Σ_m [x_m]`;
* `cgOpen C U n` — the product open `U^n ⊆ C^n`;
* `pullSection`, `bnMatrix`, `bnDelta`, `bnOpen` — the determinant section `δ = det (h_j)²`;
* `evalSection` — the value of a section at a field point;
* `chartOpen` — the Brill–Noether chart of `Sym^g C` cut out by `δ`.
-/
import Submission.Work.Charts.Basic
import Submission.Work.SymQuot.ProdOpen

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 1000000

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.Charts

open Work.CurveBasics
open Work.GCBasics

noncomputable section

variable {K : Type u} [Field K]

/-! ### The product `C^n` and the quotient map -/

/-- The `n`-fold product of the curve `C` over `K`. -/
abbrev Cprod (C : Curve K) (n : ℕ) : Sch K := Work.SymQuot.prod C.toOver n

/-- The `m`-th coordinate of a point of `C^n`: an `F`-point of `C`. -/
def coord {C : Curve K} {n : ℕ} {F : Type u} [Field F] [Algebra K F]
    (p : FPt (Cprod C n) F) (m : Fin n) : Work.SpecLin.CurveFPt C F :=
  p ≫ Work.SymQuot.proj C.toOver n m

/-- **The quotient map `C^n ⟶ Sym^n C`**: the sum of the `n` coordinates, i.e. area `SY`'s
quotient map `C^n ⟶ C^n/S_n`. -/
def quotMap (C : Curve K) (n : ℕ) [Work.SpecLin.DivBase C] [Work.SpecLin.SymGeom C n] :
    Cprod C n ⟶ Sym C n :=
  Work.SpecLin.SymGeom.powMap (fun m => Work.SymQuot.proj C.toOver n m)

theorem quotMap_apply {C : Curve K} {n : ℕ} [Work.SpecLin.DivBase C]
    [Work.SpecLin.SymGeom C n] {F : Type u} [Field F] [Algebra K F]
    (p : FPt (Cprod C n) F) :
    p ≫ quotMap C n = Work.SpecLin.SymGeom.powMap (fun m => coord p m) :=
  (Work.SpecLin.SymGeom.powMap_comp p (fun m => Work.SymQuot.proj C.toOver n m)).symm

/-- **`divOf` of the quotient point**: the divisor of `quotMap q` is the sum of the point
divisors of the coordinates of `q`. -/
theorem divOf_quotMap {C : Curve K} {n : ℕ} [Work.SpecLin.DivBase C]
    [Work.SpecLin.SymGeom C n] {F : Type u} [Field F] [Algebra K F]
    (p : FPt (Cprod C n) F) :
    divOf (p ≫ quotMap C n) = ∑ m, Work.SpecLin.ptDiv (coord p m) := by
  rw [quotMap_apply]
  exact Work.SpecLin.SymGeom.divOf_powMap (fun m => coord p m)

/-! ### The product open `U^n` and the section ring -/

/-- The product open `U^n ⊆ C^n`: the points all of whose coordinates lie in `U`. -/
def cgOpen (C : Curve K) (U : C.left.Opens) (n : ℕ) : (Cprod C n).left.Opens :=
  ⟨⋂ m, ((Work.SymQuot.proj C.toOver n m).left ⁻¹ᵁ U : Set (Cprod C n).left),
    isOpen_iInter_of_finite fun m => ((Work.SymQuot.proj C.toOver n m).left ⁻¹ᵁ U).2⟩

@[simp]
theorem mem_cgOpen {C : Curve K} {U : C.left.Opens} {n : ℕ} {x : (Cprod C n).left} :
    x ∈ cgOpen C U n ↔ ∀ m, (Work.SymQuot.proj C.toOver n m).left x ∈ U := by
  change x ∈ (⋂ m, ((Work.SymQuot.proj C.toOver n m).left ⁻¹ᵁ U : Set (Cprod C n).left)) ↔ _
  rw [Set.mem_iInter]
  exact forall_congr' (fun m => Scheme.Hom.mem_preimage
    (f := (Work.SymQuot.proj C.toOver n m).left))

theorem cgOpen_le {C : Curve K} {U : C.left.Opens} {n : ℕ} (m : Fin n) :
    cgOpen C U n ≤ (Work.SymQuot.proj C.toOver n m).left ⁻¹ᵁ U :=
  fun _ hx => (mem_cgOpen.mp hx) m

/-- The pullback of a section of `Γ(C,U)` along the `m`-th projection, as a section of
`Γ(C^n, U^n)`. -/
def pullSection (C : Curve K) (U : C.left.Opens) (n : ℕ) (m : Fin n)
    (s : Γ(C.left, U)) : Γ((Cprod C n).left, cgOpen C U n) :=
  Scheme.Hom.appLE (Work.SymQuot.proj C.toOver n m).left U (cgOpen C U n)
    (cgOpen_le m) s

/-- **The Brill–Noether matrix**: the matrix with entries the pullbacks of the sections `s j`
along the coordinate projections (the `j`-th section in the `m`-th tensor factor). -/
def bnMatrix (C : Curve K) (U : C.left.Opens) (n : ℕ) (s : Fin n → Γ(C.left, U)) :
    Matrix (Fin n) (Fin n) Γ((Cprod C n).left, cgOpen C U n) :=
  fun j m => pullSection C U n m (s j)

/-- **The Brill–Noether section** `δ = det (h_j(x_m))²` on `U^n ⊆ C^n`. -/
def bnDelta (C : Curve K) (U : C.left.Opens) (n : ℕ) (s : Fin n → Γ(C.left, U)) :
    Γ((Cprod C n).left, cgOpen C U n) :=
  (bnMatrix C U n s).det ^ 2

/-- The open `D(δ) ⊆ U^n` where the Brill–Noether determinant does not vanish. -/
def bnOpen (C : Curve K) (U : C.left.Opens) (n : ℕ) (s : Fin n → Γ(C.left, U)) :
    (Cprod C n).left.Opens :=
  (Cprod C n).left.basicOpen (bnDelta C U n s)

theorem bnOpen_le {C : Curve K} {U : C.left.Opens} {n : ℕ} (s : Fin n → Γ(C.left, U)) :
    bnOpen C U n s ≤ cgOpen C U n :=
  Scheme.basicOpen_le _ _

/-- The coordinates of a point of `C^n` that lands in the product open `U^n` land in `U`. -/
theorem coord_landsIn {C : Curve K} {n : ℕ} {U : C.left.Opens} {F : Type u} [Field F]
    [Algebra K F] {p : FPt (Cprod C n) F} (hp : RPt.LandsIn p (cgOpen C U n)) (m : Fin n) :
    RPt.LandsIn (coord p m) U :=
  (mem_cgOpen.mp hp) m

/-! ### The value of a section at a field point -/

/-- **The value of a section at a field point.**  For a scheme `X`, an open `U ⊆ X`, a section
`s ∈ Γ(X,U)` and an `F`-point `p` of `X` landing in `U`, the pullback of `s` along `p`, read in
`F ≅ Γ(Spec F, ⊤)`. -/
def evalSection {X : Scheme.{u}} {F : Type u} [Field F] {U : X.Opens}
    (p : Spec (CommRingCat.of F) ⟶ X) (hp : p.base (IsLocalRing.closedPoint F) ∈ U)
    (s : Γ(X, U)) : F :=
  (Scheme.ΓSpecIso (CommRingCat.of F)).hom
    (Scheme.Hom.appLE p U ⊤ (fun x _ => by
      show p x ∈ U
      have hx : x = IsLocalRing.closedPoint F := Subsingleton.elim _ _
      rw [hx]
      exact hp) s)

/-! ### The Brill–Noether chart of `Sym^n C` -/

/-- **The Brill–Noether chart of `Sym^n C` cut out by `δ`**: the complement of the image of
`C^n ∖ D(δ)` under the quotient map `quotMap`.  The hypothesis `hclosed` (a theorem for
`SymGeom`, since `quotMap` is a morphism between proper `K`-schemes) is what makes this set
open; the point of the definition is that a point `p` of the chart has all its lifts in
`D(δ)`, where the evaluation matrix `(h_j(x_m))` is invertible. -/
def chartOpen (C : Curve K) (n : ℕ) [Work.SpecLin.DivBase C] [Work.SpecLin.SymGeom C n]
    (U : C.left.Opens) (s : Fin n → Γ(C.left, U))
    (hclosed : IsClosedMap (quotMap C n).left.base) : (Sym C n).left.Opens :=
  ⟨((quotMap C n).left.base '' (bnOpen C U n s : Set (Cprod C n).left)ᶜ)ᶜ,
    (hclosed _ (bnOpen C U n s).2.isClosed_compl).isOpen_compl⟩

theorem mem_chartOpen {C : Curve K} {n : ℕ} [Work.SpecLin.DivBase C]
    [Work.SpecLin.SymGeom C n] {U : C.left.Opens} {s : Fin n → Γ(C.left, U)}
    {hclosed : IsClosedMap (quotMap C n).left.base} {y : (Sym C n).left} :
    y ∈ chartOpen C n U s hclosed ↔
      ∀ x : (Cprod C n).left, (quotMap C n).left x = y → x ∈ bnOpen C U n s := by
  constructor
  · intro hy x hx
    by_contra hxb
    exact hy ⟨x, hxb, hx⟩
  · rintro h ⟨x, hxb, hx⟩
    exact hxb (h x hx)

end

end Work.Charts
