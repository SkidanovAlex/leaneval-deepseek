/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Base change of the divisor of a point of `Symⁿ C` (area SY, `divOf`)

This file proves the hub lemma **C1′** of `Submission/Work/NOTES_LEAD_jacobian_divof.md` (§2):

> for a point `p` of `Symⁿ C` over `F`, a chart `d` of `p` and a lift `x : Fin n → C(F')` of `p`
> over a field extension `F' ⊇ F`,
> `divMap_{F → F'} (divOfChart F d) = Σ_m ptDiv (x m)`.

It is the assembly of the three delegated ingredients:

* RAM (`divisorOfIdeal_map_bcSec`): extending an ideal along the tower square multiplies the
  orders of vanishing by the ramification indices, so
  `divisorOfIdeal (J · B_{F'}) = divMap (divisorOfIdeal J)`;
* C1 (`charIdealGen_map_eq`): the divisor ideal of the chart extends to the product of the
  maximal ideals of the lifted points, `charIdealGen F d · B_{F'} = ∏_m m_{x_m}`;
* the Dedekind dictionary (`divisorOfIdeal_prod_placeIdeal`):
  `divisorOfIdeal (∏_m m_{x_m}) = Σ_m [x_m]`.

The only extra input needed here is that the divisor ideal of a point of `Symⁿ C` is nonzero
(`charIdealGen_ne_bot`), which is deduced from C1 by lifting the point over a finite extension
(`Sym.exists_finite_lift`) and using that a product of place ideals is nonzero in the domain
`Γ(C_{F'}, V_{F'})`.
-/
import Mathlib
import Submission.Work.SymQuot.DivOf.C1Defs
import Submission.Work.SymQuot.DivOf.charIdealGen_map_eq
import Submission.Work.SymQuot.DivOf.divisorOfIdeal_map_bcSec
import Submission.Work.SymQuot.DivOf.divisorOfIdeal_prod_placeIdeal
import Submission.Work.SymQuot.DivOf.lift_mem_V
import Submission.Work.SymQuot.DivOf.ptPlace_mem_bcOpens
import Submission.Work.SymQuot.Sym.exists_finite_lift

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.unusedSectionVars false
-- The delegated statements live in files whose namespace is duplicated
-- (`Work.SymQuot.DivOf.Work.SymQuot.DivOf.…`); these wrappers isolate the name.
set_option linter.dupNamespace false

universe u
open CategoryTheory Limits AlgebraicGeometry
open scoped Classical
namespace Work.SymQuot.DivOf

open Work.CurveBasics

/-! ### Wrappers for the delegated ingredients, insulated from their namespaces -/

/-- The hub lemma C1 (`Work.SymQuot.DivOf.charIdealGen_map_eq`). -/
theorem charIdealGen_map_eq' {K : Type u} [Field K] {C : Curve K} {n : ℕ}
    [NeZero n] [CurveAffineCover C] {F : Type u} [Field F] [Algebra K F]
    {p : Work.SpecLin.FPt (Sym C n) F} (d : ChartPt C n p)
    {F'' : Type u} [Field F''] [Algebra K F''] [Algebra F F''] [IsScalarTower K F F'']
    (x : Fin n → Work.SpecLin.CurveFPt C F'')
    (hx : Work.SymQuot.Sym.powMap C n x =
      Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K F F'') p) :
    (charIdealGen F d).map (bcSec F F'' d.V) =
      prodPtPlaceIdeal d x
        (fun m => ptPlace_mem_bcOpens d x m (lift_mem_V d x hx)) := by
  first
  | exact Work.SymQuot.DivOf.charIdealGen_map_eq d x hx
  | exact Work.SymQuot.DivOf.Work.SymQuot.DivOf.charIdealGen_map_eq d x hx

/-- RAM (`Work.SymQuot.DivOf.divisorOfIdeal_map_bcSec`): extension of ideals along the tower. -/
theorem divisorOfIdeal_map_bcSec' {K : Type u} [Field K] {C : Curve K}
    (F F'' : Type u) [Field F] [Field F''] [Algebra K F] [Algebra K F''] [Algebra F F'']
    [IsScalarTower K F F''] (V : C.left.Opens) (hV : IsAffineOpen V)
    [Nonempty V] [Nonempty (C.bcOpens F V)] [Nonempty (C.bcOpens F'' V)]
    [IsDedekindDomain Γ((C.baseChange F).left, C.bcOpens F V)]
    [IsDedekindDomain Γ((C.baseChange F'').left, C.bcOpens F'' V)]
    (J : Ideal Γ((C.baseChange F).left, C.bcOpens F V)) (hJ : J ≠ ⊥) :
    divisorOfIdeal (C.baseChange F'') (C.bcOpens F'' V)
        (BaseChange.isAffineOpen_bcOpens F'' V hV) (J.map (bcSec F F'' V)) =
      (bcSquareTower (C := C) F F'').divMap
        (divisorOfIdeal (C.baseChange F) (C.bcOpens F V)
          (BaseChange.isAffineOpen_bcOpens F V hV) J) := by
  first
  | exact Work.SymQuot.DivOf.divisorOfIdeal_map_bcSec F F'' V hV J hJ
  | exact Work.SymQuot.DivOf.Work.SymQuot.DivOf.divisorOfIdeal_map_bcSec F F'' V hV J hJ

/-! ### The place ideals and their products are nonzero -/

/-- **The maximal ideal of a place lying in an affine open is nonzero.** -/
theorem placeIdeal_ne_bot {F : Type u} [Field F] {C : Curve F} {V : C.left.Opens} [Nonempty V]
    (hV : IsAffineOpen V) [IsDedekindDomain Γ(C.left, V)] (z : C.Place) (hz : z.point ∈ V) :
    placeIdeal C V z hz ≠ ⊥ := by
  rw [← heightOneEquiv_apply C V hV ⟨z, hz⟩]
  exact (heightOneEquiv C V hV ⟨z, hz⟩).ne_bot

/-- **A finite product of place ideals is nonzero**: `Γ(C,V)` is a domain, so a product of
nonzero ideals is nonzero. -/
theorem prod_placeIdeal_ne_bot {F : Type u} [Field F] {C : Curve F} {ι : Type*} [Fintype ι]
    (V : C.left.Opens) [Nonempty V] (hV : IsAffineOpen V) [IsDedekindDomain Γ(C.left, V)]
    (y : ι → C.Place) (hy : ∀ i, (y i).point ∈ V) :
    (∏ i, placeIdeal C V (y i) (hy i)) ≠ ⊥ := by
  have hone : ∀ i, placeIdeal C V (y i) (hy i) ≠ ⊥ := fun i =>
    placeIdeal_ne_bot hV (y i) (hy i)
  have hgen : ∀ s : Finset ι, (∀ i ∈ s, placeIdeal C V (y i) (hy i) ≠ ⊥) →
      (∏ i ∈ s, placeIdeal C V (y i) (hy i)) ≠ ⊥ := by
    intro s
    induction s using Finset.induction with
    | empty => intro _; simp
    | insert a s ha ih =>
      intro hs h
      rw [Finset.prod_insert ha] at h
      rcases (Ideal.mul_eq_bot).mp h with h' | h'
      · exact hs a (Finset.mem_insert_self a s) h'
      · exact ih (fun i hi => hs i (Finset.mem_insert_of_mem hi)) h'
  simpa using hgen Finset.univ (fun i _ => hone i)

/-! ### The divisor ideal of a point of `Symⁿ C` is nonzero -/

/-- **The divisor ideal of a point of `Symⁿ C` is nonzero.**  Lift the point over a finite
extension `F'' ⊇ F` (`Sym.exists_finite_lift`); by C1 the extension of `charIdealGen F d` to
`Γ(C_{F''}, V_{F''})` is the product of the maximal ideals of the lifted points, which is nonzero
by `prod_placeIdeal_ne_bot`.  Since `⊥.map _ = ⊥`, the ideal itself is nonzero. -/
theorem charIdealGen_ne_bot {K : Type u} [Field K] {C : Curve K} {n : ℕ}
    [NeZero n] [CurveAffineCover C] {F : Type u} [Field F] [Algebra K F]
    {p : Work.SpecLin.FPt (Sym C n) F} (d : ChartPt C n p) [Nonempty d.V] :
    charIdealGen F d ≠ ⊥ := by
  obtain ⟨F'', hF'', hAlgK, hAlgF, hTower, _hFin, x, hx⟩ :=
    Work.SymQuot.Sym.exists_finite_lift (K := K) C n p
  letI := hF''
  letI := hAlgK
  letI := hAlgF
  letI := hTower
  haveI : Nonempty (C.bcOpens F'' d.V) := Curve.bcOpens_nonempty C F'' d.V
  haveI : IsDedekindDomain Γ((C.baseChange F'').left, C.bcOpens F'' d.V) :=
    isDedekindDomain_sections (BaseChange.isAffineOpen_bcOpens F'' d.V d.isAffineOpen_V)
  have hC1 := charIdealGen_map_eq' (C := C) (n := n) d x hx
  have hprod : prodPtPlaceIdeal d x
      (fun m => ptPlace_mem_bcOpens d x m (lift_mem_V d x hx)) ≠ ⊥ := by
    rw [show prodPtPlaceIdeal d x (fun m => ptPlace_mem_bcOpens d x m (lift_mem_V d x hx))
        = ∏ m, placeIdeal (C.baseChange F'') (C.bcOpens F'' d.V)
            (Work.SpecLin.ptPlace (x m))
            (ptPlace_mem_bcOpens d x m (lift_mem_V d x hx)) from rfl]
    exact prod_placeIdeal_ne_bot (C := C.baseChange F'') (C.bcOpens F'' d.V)
      (BaseChange.isAffineOpen_bcOpens F'' d.V d.isAffineOpen_V)
      (fun m => Work.SpecLin.ptPlace (x m))
      (fun m => ptPlace_mem_bcOpens d x m (lift_mem_V d x hx))
  have hmap : (charIdealGen F d).map (bcSec F F'' d.V) ≠ ⊥ := by
    rw [hC1]
    exact hprod
  intro hbot
  exact hmap (by rw [hbot, Ideal.map_bot])

/-! ### C1′ -/

theorem divMap_divOfChart {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    [NeZero n] [Work.SymQuot.CurveAffineCover C] {F : Type u} [Field F] [Algebra K F]
    {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F} (d : ChartPt C n p) [Nonempty d.V]
    {F' : Type u} [Field F'] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    (x : Fin n → Work.SpecLin.CurveFPt C F')
    (hx : Work.SymQuot.Sym.powMap C n x =
      Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K F F') p) :
    (bcSquareTower (C := C) F F').divMap (divOfChart F d) =
      ∑ m, Work.SpecLin.ptDiv (x m) := by
  haveI : Nonempty (C.bcOpens F d.V) := Curve.bcOpens_nonempty C F d.V
  haveI : Nonempty (C.bcOpens F' d.V) := Curve.bcOpens_nonempty C F' d.V
  haveI : IsDedekindDomain Γ((C.baseChange F).left, C.bcOpens F d.V) :=
    isDedekindDomain_sections (BaseChange.isAffineOpen_bcOpens F d.V d.isAffineOpen_V)
  haveI : IsDedekindDomain Γ((C.baseChange F').left, C.bcOpens F' d.V) :=
    isDedekindDomain_sections (BaseChange.isAffineOpen_bcOpens F' d.V d.isAffineOpen_V)
  have hram := divisorOfIdeal_map_bcSec' (C := C) F F' d.V d.isAffineOpen_V
    (charIdealGen F d) (charIdealGen_ne_bot d)
  have hdict : divisorOfIdeal (C.baseChange F') (C.bcOpens F' d.V)
        (BaseChange.isAffineOpen_bcOpens F' d.V d.isAffineOpen_V)
        (prodPtPlaceIdeal d x (fun m => ptPlace_mem_bcOpens d x m (lift_mem_V d x hx))) =
      ∑ m, Work.SpecLin.ptDiv (x m) := by
    rw [show prodPtPlaceIdeal d x (fun m => ptPlace_mem_bcOpens d x m (lift_mem_V d x hx))
        = ∏ m, placeIdeal (C.baseChange F') (C.bcOpens F' d.V)
            (Work.SpecLin.ptPlace (x m))
            (ptPlace_mem_bcOpens d x m (lift_mem_V d x hx)) from rfl]
    rw [divisorOfIdeal_prod_placeIdeal (C := C.baseChange F') (C.bcOpens F' d.V)
      (BaseChange.isAffineOpen_bcOpens F' d.V d.isAffineOpen_V)
      (fun m => Work.SpecLin.ptPlace (x m))
      (fun m => ptPlace_mem_bcOpens d x m (lift_mem_V d x hx))]
    simp [Work.SpecLin.ptDiv]
  rw [divOfChart_def, ← hram, charIdealGen_map_eq' d x hx]
  exact hdict

end Work.SymQuot.DivOf
