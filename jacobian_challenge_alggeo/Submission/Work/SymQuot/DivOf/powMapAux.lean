/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `divOf (powMap x) = ∑ ptDiv (x m)`

The proof that the divisor of the point `powMap C n x` of `Symⁿ C` obtained from `n` points of
`C` is the sum of the point divisors `ptDiv (x m)`.

This file contains the accompanying API: the chosen chart of a point of `Symⁿ C`, the value maps
`valAt m : Γ(C,V) →+* F` (the values of a function at the `F`-point `x m`), and the two key
identifications

* the generators of `charIdeal` are the products `∏ m, (α b - s (valAt m b))`
  (`charIdeal_generator`), where `α = baseChangeFst^*` and `s` is the structure map `F → Γ(C_F,W)`;
* the membership of a section in the place ideal of `ptPlace (x m)` is the vanishing of its value
  (`mem_placeIdeal_iff_rgMap_eq_zero`, `mem_placeIdeal_iff_valAt_eq`).
-/
import Mathlib
import Submission.Work.SymQuot.DivOf.DivOf
import Submission.Work.SymQuot.DivOf.SecAlpha
import Submission.Work.SymQuot.DivOf.CharIdeal
import Submission.Work.SymQuot.DivOf.le_placeOrder_iff
import Submission.Work.SymQuot.DivOf.localIdealSet_mem_iff
import Submission.Work.SpecLin.Points.Basic
import Submission.Work.SpecLin.Core.mem_primeIdealOf_ptToPoint_iff
import Submission.Work.SymQuot.Chart.quotientMap_fiber_orbit
import Submission.Work.SymQuot.Sym.powMap_eq_iff_exists_perm

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

namespace Work.SymQuot.DivOf

open Work.CurveBasics

variable {K : Type u} [Field K]

/-! ## The chosen chart of a point of `Symⁿ C` -/

/-- The chart of a point of `Symⁿ C` chosen by `Classical.choose` in `divOf`. -/
noncomputable abbrev chartOf (C : Curve K) (n : ℕ) [NeZero n] [CurveAffineCover C]
    {F : Type u} [Field F] [Algebra K F] (p : Work.SpecLin.FPt (Sym C n) F) : ChartPt C n p :=
  Classical.choose (exists_chartPt_nonempty (C := C) (n := n) p)

theorem chartOf_nonempty (C : Curve K) (n : ℕ) [NeZero n] [CurveAffineCover C]
    {F : Type u} [Field F] [Algebra K F] (p : Work.SpecLin.FPt (Sym C n) F) :
    Nonempty (chartOf C n p).V :=
  Classical.choose_spec (exists_chartPt_nonempty (C := C) (n := n) p)

/-! ## The lift lands in the chart -/

variable {C : Curve K} {n : ℕ} [NeZero n] [CurveAffineCover C] {F : Type u} [Field F]
  [Algebra K F]

/-- **The lift `Π x_m : Spec F ⟶ Cⁿ` of `powMap x` lands in the open of any chart containing
the point.** -/
theorem lift_mem_chartOpen (x : Fin n → Work.SpecLin.CurveFPt C F)
    (d : ChartPt C n (Sym.powMap C n x)) :
    (⊤ : (Work.SpecLin.specOf (K := K) F).left.Opens) ≤
      (TopologicalSpace.Opens.map ((Limits.Pi.lift x :
        Work.SpecLin.specOf (K := K) F ⟶ prod C.toOver n)).left.base).obj d.openOf := by
  classical
  have hUaff : IsAffineOpen d.openOf :=
    Prod.isAffineOpen_piOpen C.toOver n d.V d.isAffineOpen_V
  have hUinv : (symData C n).action.IsInvariantOpen d.openOf :=
    symPiOpen_invariant C n d.V
  have h1 : (Sym.powMap C n x).left (IsLocalRing.closedPoint F) =
      (symData C n).chartι (⟨d.openOf, hUaff, hUinv⟩ : (symData C n).Chart)
        (d.q (IsLocalRing.closedPoint F)) := by
    exact (congrArg (fun f => f (IsLocalRing.closedPoint F)) d.fac).symm
  obtain ⟨u, hu⟩ := Chart.chartMap_surjective (symData C n).action hUaff hUinv
    (d.q (IsLocalRing.closedPoint F))
  have h2 : (symData C n).quotientMap (d.openOf.ι u) =
      (Sym.powMap C n x).left (IsLocalRing.closedPoint F) := by
    have hq := congrArg (fun f => f u)
      (QuotientData.quotientMap_chartι (symData C n)
        (⟨d.openOf, hUaff, hUinv⟩ : (symData C n).Chart))
    simp only [Scheme.Hom.comp_apply] at hq
    rw [hq, hu, h1]
  have hu' : (d.openOf.ι u : (prod C.toOver n).left) ∈ d.openOf := by
    have h : (d.openOf.ι u : (prod C.toOver n).left) ∈ Set.range (d.openOf.ι) := ⟨u, rfl⟩
    rwa [Scheme.Opens.range_ι] at h
  have h3 : (symData C n).quotientMap
      ((Limits.Pi.lift x).left (IsLocalRing.closedPoint F)) =
      (Sym.powMap C n x).left (IsLocalRing.closedPoint F) := rfl
  obtain ⟨g, hg⟩ := (GAction.mem_orbit_iff (symData C n).action).mp
    (Chart.quotientMap_fiber_orbit (symData C n) (h3.trans h2.symm))
  have hyU : (Limits.Pi.lift x).left (IsLocalRing.closedPoint F) ∈ d.openOf := by
    have h4 := hUinv.mem_iff g ((Limits.Pi.lift x).left (IsLocalRing.closedPoint F))
    rw [hg] at h4
    exact h4.mp hu'
  haveI : Subsingleton ↥(Work.SpecLin.specOf (K := K) F).left :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of F)))
  intro z _
  rw [show z = IsLocalRing.closedPoint F from Subsingleton.elim _ _]
  exact hyU

/-! ## The value maps and the generators of `charIdeal` -/

section Generators

variable {p : Work.SpecLin.FPt (Sym C n) F}

/-- The value of a function on the chart at the `m`-th `F`-point `x m`. -/
noncomputable def valAt (d : ChartPt C n p) (x : Fin n → Work.SpecLin.CurveFPt C F)
    (h : (⊤ : (Work.SpecLin.specOf (K := K) F).left.Opens) ≤
      (TopologicalSpace.Opens.map ((Limits.Pi.lift x :
        Work.SpecLin.specOf (K := K) F ⟶ prod C.toOver n)).left.base).obj d.openOf)
    (m : Fin n) : Γ(C.left, d.V) →+* F :=
  (d.evalMap x h).comp (coordPullbackAt C n d.V m)

theorem valAt_apply (d : ChartPt C n p) (x : Fin n → Work.SpecLin.CurveFPt C F)
    (h : (⊤ : (Work.SpecLin.specOf (K := K) F).left.Opens) ≤
      (TopologicalSpace.Opens.map ((Limits.Pi.lift x :
        Work.SpecLin.specOf (K := K) F ⟶ prod C.toOver n)).left.base).obj d.openOf)
    (m : Fin n) (b : Γ(C.left, d.V)) :
    valAt d x h m b = d.evalMap x h (coordPullbackAt C n d.V m b) := rfl

/-- The specialization of `chartPt_evalMap_eq` to `F' = F`. -/
theorem chartPt_eval_eq_self (d : ChartPt C n p)
    (x : Fin n → Work.SpecLin.CurveFPt C F)
    (hx : Sym.powMap C n x = p)
    (h : (⊤ : (Work.SpecLin.specOf (K := K) F).left.Opens) ≤
      (TopologicalSpace.Opens.map ((Limits.Pi.lift x :
        Work.SpecLin.specOf (K := K) F ⟶ prod C.toOver n)).left.base).obj d.openOf)
    (a : ↥d.chartRingOf) : d.φ a = d.evalMap x h ↑a := by
  have hx' : Sym.powMap C n x = Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K F F) p := by
    rw [show IsScalarTower.toAlgHom K F F = AlgHom.id K F from
      AlgHom.ext (fun c => by simp [IsScalarTower.toAlgHom_apply]), Work.SpecLin.RPt.map_id]
    exact hx
  have key := chartPt_evalMap_eq (F := F) (F' := F) d x hx' h a
  simpa using key

/-- **The characteristic polynomial evaluated at `b`** is the image of `χ_b` under the
evaluation map. -/
theorem charpolyValue_eq_map (d : ChartPt C n p)
    (x : Fin n → Work.SpecLin.CurveFPt C F)
    (hx : Sym.powMap C n x = p)
    (h : (⊤ : (Work.SpecLin.specOf (K := K) F).left.Opens) ≤
      (TopologicalSpace.Opens.map ((Limits.Pi.lift x :
        Work.SpecLin.specOf (K := K) F ⟶ prod C.toOver n)).left.base).obj d.openOf)
    (b : Γ(C.left, d.V)) :
    d.charpolyValue b = (charpoly C n d.V b).map (d.evalMap x h) := by
  have hdeg : (charpoly C n d.V b).natDegree ≤ n := by
    rw [charpoly]
    refine le_trans (Polynomial.natDegree_prod_le Finset.univ
      (fun m : Fin n => Polynomial.X - Polynomial.C (coordPullbackAt C n d.V m b))) ?_
    refine le_trans (Finset.sum_le_sum (f := fun i : Fin n =>
        (Polynomial.X - Polynomial.C (coordPullbackAt C n d.V i b)).natDegree)
      (g := fun _ : Fin n => (1 : ℕ)) fun i _ => Polynomial.natDegree_X_sub_C_le _) ?_
    simp
  rw [ChartPt.charpolyValue_def,
    localIdealAux_map_eq_sum_range_C_mul_X_pow (d.evalMap x h) (charpoly C n d.V b) n hdeg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [chartPt_eval_eq_self d x hx h]

/-- **The generators of `charIdeal` are products of differences**: the generator attached to a
section `b` of the chart is `∏ m, (α b - s (valAt m b))`. -/
theorem charIdeal_generator (d : ChartPt C n p)
    (x : Fin n → Work.SpecLin.CurveFPt C F)
    (hx : Sym.powMap C n x = p)
    (h : (⊤ : (Work.SpecLin.specOf (K := K) F).left.Opens) ≤
      (TopologicalSpace.Opens.map ((Limits.Pi.lift x :
        Work.SpecLin.specOf (K := K) F ⟶ prod C.toOver n)).left.base).obj d.openOf)
    (b : Γ(C.left, d.V)) :
    Polynomial.eval₂ (sectionsAlgebraMap (C.baseChange F) (C.bcOpens F d.V))
      (secAlpha C F d.V b) (d.charpolyValue b)
    = ∏ m, (secAlpha C F d.V b - secConst C F d.V (valAt d x h m b)) := by
  rw [charpolyValue_eq_map d x hx h b, Polynomial.eval₂_map]
  rw [charpoly, Polynomial.eval₂_eq_eval_map, Polynomial.map_prod, Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun m _ => ?_
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, valAt_apply]
  rw [RingHom.comp_apply, ← secConst_apply]

end Generators

/-! ## The value of a chart section at an `F`-point -/

section Value

variable {C : Curve K} {F : Type u} [Field F] [Algebra K F]

/-- **The value of a chart section at an `F`-point**: a section of the chart vanishes at the
place of an `F`-point if and only if its value at the point (i.e. the image under `rgMap`) is
zero. -/
theorem mem_placeIdeal_iff_rgMap_eq_zero (W : C.left.Opens) (hW : IsAffineOpen W)
    (s : Work.SpecLin.CurveFPt C F) (hs : Set.range s.left.base ⊆ (W : Set C.left))
    (hmem : Work.SpecLin.ptToPoint s ∈ C.bcOpens F W) (a : Γ(C.left, W)) :
    secAlpha C F W a ∈ Work.SymQuot.DivOf.placeIdeal (C.baseChange F) (C.bcOpens F W)
        ⟨Work.SpecLin.ptToPoint s, Work.SpecLin.Points.ptToPoint_isClosed s⟩ hmem ↔
      Work.SpecLin.Core.rgMap F W hW s hs a = 0 := by
  classical
  have hle : C.bcOpens F W ≤ (C.baseChangeFst F) ⁻¹ᵁ W := le_rfl
  haveI hWne : Nonempty W := ⟨⟨s.left.base (IsLocalRing.closedPoint F), hs (Set.mem_range_self _)⟩⟩
  haveI := Work.CurveBasics.Curve.bcOpens_nonempty C F W
  rw [Work.SymQuot.DivOf.placeIdeal_eq_primeIdealOf
    (Work.CurveBasics.BaseChange.isAffineOpen_bcOpens F W hW) _ hmem]
  show (Curve.baseChangeFst C F).appLE W (C.bcOpens F W) le_rfl a
      ∈ ((Work.CurveBasics.BaseChange.isAffineOpen_bcOpens F W hW).primeIdealOf
          ⟨Work.SpecLin.ptToPoint s, hmem⟩).asIdeal ↔
      Work.SpecLin.Core.rgMap F W hW s hs a = 0
  have hfac : s.left = (Work.SpecLin.specOfMap (K := K) (Work.SpecLin.Core.rgMap F W hW s hs)).left
      ≫ hW.fromSpec := (Work.SpecLin.Core.rgMap_fac F W hW s hs).symm
  have hpt : C.baseChangeFst F (Work.SpecLin.ptToPoint s)
      = hW.fromSpec (Spec.map (CommRingCat.ofHom
          (Work.SpecLin.Core.rgMap F W hW s hs).toRingHom)
          (IsLocalRing.closedPoint F)) := by
    rw [Work.SpecLin.Alt.baseChangeFst_ptToPoint, hfac]
    rfl
  have key : hW.primeIdealOf ⟨C.baseChangeFst F (Work.SpecLin.ptToPoint s), hle hmem⟩
      = PrimeSpectrum.comap (Work.SpecLin.Core.rgMap F W hW s hs).toRingHom
          (IsLocalRing.closedPoint F) :=
    Work.SpecLin.Core.primeIdealOf_eq_of_fromSpec_eq hW
      (Work.SpecLin.Core.rgMap F W hW s hs).toRingHom _ (hle hmem) hpt
  rw [← Ideal.mem_comap, ← PrimeSpectrum.comap_asIdeal,
    IsAffineOpen.comap_primeIdealOf_appLE W hW (C.bcOpens F W)
      (Work.CurveBasics.BaseChange.isAffineOpen_bcOpens F W hW) hle hmem]
  show a ∈ (hW.primeIdealOf ⟨C.baseChangeFst F (Work.SpecLin.ptToPoint s), hle hmem⟩).asIdeal
    ↔ Work.SpecLin.Core.rgMap F W hW s hs a = 0
  rw [key, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
    Work.SpecLin.Core.closedPoint_asIdeal_eq_bot, Ideal.mem_bot]
  exact Iff.rfl

end Value

/-! ## The condition that the lift lands in a chart -/

section LandsIn

variable {p : Work.SpecLin.FPt (Sym C n) F}

/-- The condition that the lift `Π x_m : Spec F ⟶ Cⁿ` of a point of `Symⁿ C` lands in the
given chart open. -/
abbrev LandsInChart (d : ChartPt C n p) (x : Fin n → Work.SpecLin.CurveFPt C F) : Prop :=
  (⊤ : (Work.SpecLin.specOf (K := K) F).left.Opens) ≤
    (TopologicalSpace.Opens.map ((Limits.Pi.lift x :
      Work.SpecLin.specOf (K := K) F ⟶ prod C.toOver n)).left.base).obj d.openOf

end LandsIn

end Work.SymQuot.DivOf
