import Mathlib
import Submission.Work.SymQuot.DivOf.Complete.PtOfChartHom
import Submission.Work.SymQuot.DivOf.Complete.RhoData
import Submission.Work.SymQuot.DivOf.Complete.ptOfChartHom_evalAlg
import Submission.Work.SymQuot.DivOf.Complete.chartEval_chartConst
import Submission.Work.SymQuot.DivOf.Complete.RPt_map_ptOfChartHom
import Submission.Work.SymQuot.DivOf.Complete.divisorOfIdeal_idealOfDiv
import Submission.Work.SymQuot.DivOf.Complete.exists_affine_of_div
import Submission.Work.SymQuot.DivOf.Complete.idealOfDiv_ne_bot
import Submission.Work.SymQuot.DivOf.Complete.exists_ptDiv_sum_of_div
import Submission.Work.SymQuot.DivOf.Complete.chartIota_comp_hom
import Submission.Work.SymQuot.DivOf.divMap_divOfChart
import Submission.Work.SymQuot.DivOf.divMap_injective
import Submission.Work.SymQuot.NormPoint.NormPoint
import Submission.Work.SymQuot.NormPoint.normVal_bcT
import Submission.Work.SymQuot.NormPoint.normVal_basis_indep
import Submission.Work.SymQuot.NormPoint.normVal_eq_evalT
import Submission.Work.SymQuot.NormPoint.exists_flagBasis
import Submission.Work.SymQuot.NormPoint.detT_mul
import Submission.Work.SymQuot.DivOf.Complete.RPt_map_ptOfAlgHom
import Submission.Work.SymQuot.DivOf.Complete.ptOfAlgHom_mem
import Submission.Work.SymQuot.DivOf.Complete.ptPlace_mem_bcOpens_of_bc
import Submission.Work.SymQuot.DivOf.Complete.exists_basis_normVal_rho_eq_evalAlg

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot.DivOf.Complete

open CategoryTheory Limits AlgebraicGeometry in
/-- **The assembly of `divOf_complete`.**  Given an effective divisor `D` on `C_F`, an affine open
`V ⊆ C` containing its support, a splitting `Σ_m [y_m]` of `D` over an algebraically closed
extension `L ⊇ F` (with the `y_m` landing in `V`), and the norm-point identity over `L`, the
point `p_D := ptOfChartHom Φ` of `Symⁿ C` built from the norm point `Φ` satisfies
`divOf F p_D = D`.

The point is that `divOf` is computed by the hub lemma C1′ in the *chosen* chart of `p_D`: the
pullback of `divOf F p_D` to `L` is `Σ_m [y_m]`, which is also the pullback of `D` by hypothesis;
`divMap_injective` finishes. -/
theorem divOf_complete_aux {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    [NeZero n] [Work.SymQuot.CurveAffineCover C] {F : Type u} [Field F] [Algebra K F]
    (D : Work.SpecLin.Dv C F) {V : C.left.Opens} [Nonempty V] (hV : IsAffineOpen V)
    (hsupp : ∀ z ∈ D.support, z.point ∈ C.bcOpens F V)
    (y : Fin n → Work.SpecLin.CurveFPt C (AlgebraicClosure F))
    (hy : Work.SpecLin.DivBase.bc (IsScalarTower.toAlgHom K F (AlgebraicClosure F)) D =
      ∑ m, Work.SpecLin.ptDiv (y m))
    (hlands : ⊤ ≤ (Limits.Pi.lift y : Work.SpecLin.specOf (K := K) (AlgebraicClosure F) ⟶
      Work.SymQuot.prod C.toOver n).left ⁻¹ᵁ Work.SymQuot.piOpen C.toOver V n)
    (hv : ∃ v : Module.Basis (Fin n) F (Γ((C.baseChange F).left, C.bcOpens F V) ⧸
        Work.SymQuot.DivOf.Complete.divIdeal (C := C) (F := F) V hV D hsupp),
      ∀ a : ↥(Work.SymQuot.chartInvariants (C := C) (n := n)
          (Work.SymQuot.piOpen C.toOver V n) (Work.SymQuot.DivOf.symPiOpen_invariant C n V)),
        algebraMap F (AlgebraicClosure F)
          (Work.SymQuot.DivOf.Complete.phiD (C := C) (F := F) (n := n) V hV
            (Work.SymQuot.DivOf.Complete.divIdeal (C := C) (F := F) V hV D hsupp) v a)
        = Work.SymQuot.DivOf.evalAlg C V n y hlands ↑a) :
    ∃ p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F, Work.SymQuot.DivOf.divOf F p = D := by
  obtain ⟨v, hv⟩ := hv
  let Φ : ↥(Work.SymQuot.chartInvariants (C := C) (n := n)
      (Work.SymQuot.piOpen C.toOver V n) (Work.SymQuot.DivOf.symPiOpen_invariant C n V)) →+* F :=
    Work.SymQuot.DivOf.Complete.phiD (C := C) (F := F) (n := n) V hV
      (Work.SymQuot.DivOf.Complete.divIdeal (C := C) (F := F) V hV D hsupp) v
  have hphi : ∀ a : ↥(Work.SymQuot.chartInvariants (C := C) (n := n)
      (Work.SymQuot.piOpen C.toOver V n) (Work.SymQuot.DivOf.symPiOpen_invariant C n V)),
      Φ a = Work.SymQuot.DivOf.Complete.phiD (C := C) (F := F) (n := n) V hV
        (Work.SymQuot.DivOf.Complete.divIdeal (C := C) (F := F) V hV D hsupp) v a :=
    fun a => rfl
  have hΦ : ∀ k : K, Φ (Work.SymQuot.DivOf.chartConst C n
      (Work.SymQuot.DivOf.Complete.chartOf C n hV) k) = algebraMap K F k := by
    intro k
    refine (algebraMap F (AlgebraicClosure F)).injective ?_
    show algebraMap F (AlgebraicClosure F)
        (Φ (Work.SymQuot.DivOf.chartConst C n (Work.SymQuot.DivOf.Complete.chartOf C n hV) k)) =
      algebraMap F (AlgebraicClosure F) (algebraMap K F k)
    rw [hphi (Work.SymQuot.DivOf.chartConst C n (Work.SymQuot.DivOf.Complete.chartOf C n hV) k),
      hv (Work.SymQuot.DivOf.chartConst C n (Work.SymQuot.DivOf.Complete.chartOf C n hV) k)]
    have h2 : (Work.SymQuot.DivOf.evalAlg C V n y hlands)
        (Subring.subtype (Work.SymQuot.chartInvariants (C := C) (n := n)
          (Work.SymQuot.piOpen C.toOver V n) (Work.SymQuot.DivOf.symPiOpen_invariant C n V))
          ((Work.SymQuot.DivOf.chartConst C n (Work.SymQuot.DivOf.Complete.chartOf C n hV)) k)) =
        algebraMap K (AlgebraicClosure F) k :=
      Work.SymQuot.DivOf.Complete.chartEval_chartConst (C := C) (n := n) hV y hlands k
    exact h2.trans (IsScalarTower.algebraMap_apply K F (AlgebraicClosure F) k)
  have hpow : Work.SymQuot.Sym.powMap C n y =
      Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K F (AlgebraicClosure F))
        (Work.SymQuot.DivOf.Complete.ptOfChartHom C n hV Φ hΦ) := by
    have hΦ' : ∀ k : K, ((IsScalarTower.toAlgHom K F (AlgebraicClosure F)).toRingHom.comp Φ)
        (Work.SymQuot.DivOf.chartConst C n (Work.SymQuot.DivOf.Complete.chartOf C n hV) k) =
        algebraMap K (AlgebraicClosure F) k := by
      intro k
      rw [RingHom.comp_apply, hΦ k]
      exact AlgHom.commutes (IsScalarTower.toAlgHom K F (AlgebraicClosure F)) k
    have hreq : (IsScalarTower.toAlgHom K F (AlgebraicClosure F)).toRingHom.comp Φ =
        Work.SymQuot.DivOf.Complete.chartEval C n y hlands := by
      ext a
      change algebraMap F (AlgebraicClosure F) (Φ a) =
        Work.SymQuot.DivOf.Complete.chartEval C n y hlands a
      rw [hphi a, hv a]
      rfl
    have hchartΦ : ∀ k : K, (Work.SymQuot.DivOf.Complete.chartEval C n y hlands)
        (Work.SymQuot.DivOf.chartConst C n (Work.SymQuot.DivOf.Complete.chartOf C n hV) k) =
        algebraMap K (AlgebraicClosure F) k :=
      Work.SymQuot.DivOf.Complete.chartEval_chartConst (C := C) (n := n) hV y hlands
    have hstep : Work.SymQuot.DivOf.Complete.ptOfChartHom C n hV
          ((IsScalarTower.toAlgHom K F (AlgebraicClosure F)).toRingHom.comp Φ) hΦ' =
        Work.SymQuot.DivOf.Complete.ptOfChartHom C n hV
          (Work.SymQuot.DivOf.Complete.chartEval C n y hlands) hchartΦ := by
      apply Over.OverMorphism.ext
      show Spec.map (CommRingCat.ofHom
            ((IsScalarTower.toAlgHom K F (AlgebraicClosure F)).toRingHom.comp Φ)) ≫
          (Work.SymQuot.symData C n).chartι (Work.SymQuot.DivOf.Complete.chartOf C n hV) =
        Spec.map (CommRingCat.ofHom (Work.SymQuot.DivOf.Complete.chartEval C n y hlands)) ≫
          (Work.SymQuot.symData C n).chartι (Work.SymQuot.DivOf.Complete.chartOf C n hV)
      rw [hreq]
    have hcalc : Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K F (AlgebraicClosure F))
        (Work.SymQuot.DivOf.Complete.ptOfChartHom C n hV Φ hΦ) =
        Work.SymQuot.Sym.powMap C n y := by
      rw [Work.SymQuot.DivOf.Complete.RPt_map_ptOfChartHom (C := C) (n := n)
        (IsScalarTower.toAlgHom K F (AlgebraicClosure F)) hV Φ hΦ hΦ', hstep]
      exact Work.SymQuot.DivOf.Complete.ptOfChartHom_evalAlg (C := C) (n := n)
        hV y hlands hchartΦ
    exact hcalc.symm
  refine ⟨Work.SymQuot.DivOf.Complete.ptOfChartHom C n hV Φ hΦ, ?_⟩
  haveI hdne : Nonempty (Classical.choose (Work.SymQuot.DivOf.exists_chartPt_nonempty
      (C := C) (n := n) (Work.SymQuot.DivOf.Complete.ptOfChartHom C n hV Φ hΦ))).V :=
    Classical.choose_spec (Work.SymQuot.DivOf.exists_chartPt_nonempty (C := C) (n := n)
      (Work.SymQuot.DivOf.Complete.ptOfChartHom C n hV Φ hΦ))
  have h1 : (Work.SymQuot.DivOf.bcSquareTower (C := C) F (AlgebraicClosure F)).divMap
      (Work.SymQuot.DivOf.divOf F (Work.SymQuot.DivOf.Complete.ptOfChartHom C n hV Φ hΦ)) =
      ∑ m, Work.SpecLin.ptDiv (y m) := by
    rw [show Work.SymQuot.DivOf.divOf F (Work.SymQuot.DivOf.Complete.ptOfChartHom C n hV Φ hΦ) =
        Work.SymQuot.DivOf.divOfChart F (Classical.choose (Work.SymQuot.DivOf.exists_chartPt_nonempty
          (C := C) (n := n) (Work.SymQuot.DivOf.Complete.ptOfChartHom C n hV Φ hΦ))) from rfl]
    exact Work.SymQuot.DivOf.divMap_divOfChart (C := C) (n := n) (F := F)
      (F' := AlgebraicClosure F) (p := Work.SymQuot.DivOf.Complete.ptOfChartHom C n hV Φ hΦ)
      (Classical.choose (Work.SymQuot.DivOf.exists_chartPt_nonempty (C := C) (n := n)
        (Work.SymQuot.DivOf.Complete.ptOfChartHom C n hV Φ hΦ))) y hpow
  have h2 : (Work.SymQuot.DivOf.bcSquareTower (C := C) F (AlgebraicClosure F)).divMap D =
      ∑ m, Work.SpecLin.ptDiv (y m) := by
    rw [← hy]
    rfl
  exact Work.SymQuot.DivOf.divMap_injective
    (Work.SymQuot.DivOf.bcSquareTower (C := C) F (AlgebraicClosure F)) (by rw [h1, h2])

open CategoryTheory Limits AlgebraicGeometry in
theorem divOf_complete {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    [NeZero n] [Work.SymQuot.CurveAffineCover C] {F : Type u} [Field F] [Algebra K F]
    (D : Work.SpecLin.Dv C F) (hD : D.IsEffective) (hdeg : (C.baseChange F).deg D = n) :
    ∃ p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F, divOf F p = D := by
  obtain ⟨V, hVaff, hVne, hsupp⟩ :=
    Work.SymQuot.DivOf.Complete.exists_affine_of_div (C := C) D
  haveI : Nonempty V := hVne
  obtain ⟨y, hy⟩ := Work.SymQuot.DivOf.Complete.exists_ptDiv_sum_of_div (C := C) (F := F)
    (L := AlgebraicClosure F) D hD hdeg
  have hplace : ∀ m : Fin n,
      (Work.SpecLin.ptPlace (y m)).point ∈ C.bcOpens (AlgebraicClosure F) V :=
    fun m => Work.SymQuot.DivOf.Complete.ptPlace_mem_bcOpens_of_bc (C := C) (n := n) D
      (V := V) hsupp y hy m
  obtain ⟨v, hv⟩ := Work.SymQuot.DivOf.Complete.exists_basis_normVal_rho_eq_evalAlg
    (C := C) (n := n) D hD hdeg hVaff hsupp y hy hplace
    (Work.SymQuot.DivOf.Complete.piOpen_landsIn_of_place_mem (C := C) (n := n) V y hplace)
  exact Work.SymQuot.DivOf.Complete.divOf_complete_aux (C := C) (n := n) D hVaff hsupp
    y hy (Work.SymQuot.DivOf.Complete.piOpen_landsIn_of_place_mem (C := C) (n := n) V y hplace)
    ⟨v, hv⟩

end Work.SymQuot.DivOf.Complete
