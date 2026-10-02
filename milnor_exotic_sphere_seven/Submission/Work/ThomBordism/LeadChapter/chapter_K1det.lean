import Mathlib
import Submission.Work.ThomBordism.LeadChapter.K1Aux
import Submission.Work.ThomBordism.LeadChapter.lvlChartCompDeriv
import Submission.Work.ThomBordism.LeadChapter.sgnZ_cofIndex
import Submission.Work.ThomBordism.LeadChapter.Defs
import Submission.Work.ThomBordism.orientationFamily_valued_of_coframing
import Submission.Work.ThomBordism.CofAtlas.fderiv_transAux_int
import Submission.Work.ThomBordism.CofAtlas.Omega_eq_fderiv
import Submission.Work.ThomBordism.CofAtlas.range_mfderiv_v_eq_range_e
import Submission.Work.ThomBordism.CofAtlas.range_chartIota_eq_ker_Omega
import Submission.Work.ThomBordism.CofAtlas.Delta_comp_DeltaInv
import Submission.Work.ThomBordism.CofAtlas.det_section_prod
import Submission.Work.ThomBordism.blockDetDefs
import Submission.Work.ThomBordism.blockDet
import Submission.Work.ThomBordism.sgnBlockFactor
import Submission.Work.ThomBordism.PosAtlas.chartTrChangeSigned_gen
import Submission.Work.PTGeometric.HOFChart
import Submission.Work.PTGeometric.Lvl.Chart

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-! Guidance from the project lead (the requester):

# S1 `Work.ThomBordism.chapter_K1det` — (K1) in determinant form, any chart
File: `Submission/Work/ThomBordism/LeadChapter/S1_K1det.lean` (defs: `LeadChapter/Defs.lean`).

**Statement.** ∃ ε = ±1 (after `k n`, before everything else) such that for every coframed level set
`D : CofAtlas.Cof k n M`, interior point `x` of `W`, chart `κ` of `W` at `x`, `A` = derivative at `κ x`
of `u ↦ extChartAt (x:M) (κ.symm u)`, `Lv` = derivative of `D.v ∘ (extChartAt (x:M)).symm` at
`extChartAt x x`, coframing index `j` with `x ∈ U j`, and `N` with `blockDet k A N ≠ 0`:
`flipSign x • chartTr (icChart x) = (ε · sgnZ(blockDet A N) · sgnZ(det(ℓ j ∘ Lv ∘ N))) • chartTr κ`.

**Proof sketch** (expected ε = 1).
1. `Lv ∘ A = 0`: `D.v ∘ κ.symm ≡ 0` on `κ.target`; chain rule through `extChartAt x`.
2. The Lvl chart `icChart 8 _ x` is, near `x`, `chartBeta x (domExt x · - chartZ x) + chartEps • e₀`;
   its derivative in ambient coordinates at `x` is `β ∘ Δ` (`Δ = CofAtlas.Cof.Delta x x`).
   So `icChart ∘ κ.symm` has derivative `β Δ A` at `κ x`; with `hdet` it is bijective.
3. `PosAtlas.chartTrChangeSigned_gen` (e := κ, f := icChart x): `chartTr κ = sgn det(βΔA) • chartTr icChart`.
4. Block determinant: `σ ∘ phiD ∘ Δ ∘ [A|N] ∘ σ⁻¹` is conjugate to `phiD Δ [A|N] = [[βΔA, *],[0, ℓ_jx Lv N]]`
   because `Omega x x ∘ Δ = ℓ_jx ∘ Lv` (`Cx x x = Δ⁻¹`). Hence
   `sgn·tau·sgn(blockDet) = sgn det(βΔA) · sgn det(ℓ_jx Lv N)`, i.e. `flipSign = …`.
5. `j ↔ jx x`: `hpos` (`0 < det(ℓ j ∘ e (jx x) x)`) and `range (Lv ∘ N) ⊆ range P x = range e` give equal signs.

**Proved lemmas.** `Work.ThomBordism.PosAtlas.chartTrChangeSigned_gen` (`…/PosAtlas/chartTrChangeSigned_gen`),
`CofAtlas.Cof.{Delta,Cx,Omega,phiD,sgn,tau,flipSign}` (`…/CofAtlas/Signs`),
`Work.CofAtlas.phiDSplitBlocks` (`Submission.Work.CofAtlas.phiDSplitBlocks`),
`Work.CofAtlas.sgnPackaging` (`Submission.Work.CofAtlas.sgnPackaging`),
`range_chartIota_eq_ker_Omega` (`…/CofAtlas/range_chartIota_eq_ker_Omega`),
`hasFDerivAt_icN_icL`, `icN_coe`, `icL_coe` (`…/orientationFamily_valued_of_coframing`),
`chartBeta_iota`, `chartFun_invFun` (`Submission.Work.PTGeometric.Lvl.Chart`),
`icChart_coe`, `icChart_coe_symm` (`Submission.Work.PTGeometric.exists_halfOrientationFamily_of_det_pos`),
`packingK1` (`…/packingK1`, for the sign bookkeeping pattern `sgz`, `signDetCxEqTau`).

**Traps.**
- No `set_option backward.isDefEq.respectTransparency false` (whnf loops).
- Keep explicit `(W := TopCat.of D.S.Pre) (N := 9)` on every `chartTr`; build intermediate chart
  transfers with `set`/`let` inside the proof.
- Do not move ε inside the `∀`; do not specialise κ to the Lvl chart (the statement is for ANY κ).
- `x` is interior: `x ∉ ∂W` ⇒ `(x:M) ∈ interior M`; at interior points `fderivWithin (range I) = fderiv`.
-/

namespace Work.ThomBordism.LeadChapter

open scoped Manifold ContDiff Topology in
open CategoryTheory Work.PTGeometric in
theorem chapter_K1det (k n : ℕ) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      ∀ (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
        [ChartedSpace (EuclideanHalfSpace (CofAtlas.NN k)) M]
        [IsManifold (modelWithCornersEuclideanHalfSpace (CofAtlas.NN k))
          ((⊤ : ENat) : WithTop ENat) M]
        (D : CofAtlas.Cof k n M) (x : D.S.Pre),
        (by
          letI : ChartedSpace (EuclideanHalfSpace 9) D.S.Pre :=
            Work.PTGeometric.Lvl.Setup.instChartedSpace D.S
          letI : IsManifold (modelWithCornersEuclideanHalfSpace 9)
              ((⊤ : ENat) : WithTop ENat) D.S.Pre :=
            Work.PTGeometric.Lvl.Setup.instIsManifold D.S
          letI : IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 D.S.Pre :=
            IsManifold.of_le (n := ((⊤ : ENat) : WithTop ENat)) (by simp)
          exact
            ∀ (hxW : x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary D.S.Pre)
              (κ : OpenPartialHomeomorph D.S.Pre CofAtlas.E9) (hκ : x ∈ κ.source)
              (A : CofAtlas.E9 →L[ℝ] CofAtlas.ModN k)
              (hA : HasFDerivAt (fun u : CofAtlas.E9 =>
                  extChartAt (modelWithCornersEuclideanHalfSpace (CofAtlas.NN k)) (x : M)
                    ((κ.symm u : D.S.Pre) : M)) A (κ x))
              (Lv : CofAtlas.ModN k →L[ℝ] EuclideanSpace ℝ (Fin n))
              (hLv : HasFDerivAt (fun u : CofAtlas.ModN k =>
                  D.v ((extChartAt (modelWithCornersEuclideanHalfSpace (CofAtlas.NN k))
                    (x : M)).symm u)) Lv
                  (extChartAt (modelWithCornersEuclideanHalfSpace (CofAtlas.NN k)) (x : M)
                    (x : M)))
              (j : Fin D.m) (hj : (x : M) ∈ D.U j)
              (N : EuclideanSpace ℝ (Fin k) →L[ℝ] CofAtlas.ModN k)
              (hdet : blockDet k A N ≠ 0),
              (if D.flipSign x = 1 then (1 : ℤ) else -1) •
                  Work.PTGeometric.HOF.chartTr (W := TopCat.of D.S.Pre) (N := 9)
                    (icChart 8 (TopCat.of D.S.Pre) x) x
                    (icChart_mem_source 8 (TopCat.of D.S.Pre) x x hxW
                      (mem_extChartAt_source x))
                    (Work.PTGeometric.HOF.eucFam 9 (by norm_num)
                      (icChart 8 (TopCat.of D.S.Pre) x x))
                = (ε * sgnZ (blockDet k A N) *
                    sgnZ (LinearMap.det (((D.ℓ j).comp (Lv.comp N)) :
                      EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)))) •
                  Work.PTGeometric.HOF.chartTr (W := TopCat.of D.S.Pre) (N := 9) κ x hκ
                    (Work.PTGeometric.HOF.eucFam 9 (by norm_num) (κ x))) := by
  refine ⟨1, Or.inl rfl, ?_⟩
  intro M _ _ _ _ _ D x hxW κ hκ A hA Lv hLv j hj N hdet
  -- the level-set chart structure
  letI : ChartedSpace (EuclideanHalfSpace 9) D.S.Pre :=
    Work.PTGeometric.Lvl.Setup.instChartedSpace D.S
  letI : IsManifold (modelWithCornersEuclideanHalfSpace 9)
      ((⊤ : ENat) : WithTop ENat) D.S.Pre :=
    Work.PTGeometric.Lvl.Setup.instIsManifold D.S
  letI : IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 D.S.Pre :=
    IsManifold.of_le (n := ((⊤ : ENat) : WithTop ENat)) (by simp)
  -- `x` is an interior point of `M`
  have hxMb : (x : M) ∉ (modelWithCornersEuclideanHalfSpace (CofAtlas.NN k)).boundary M := by
    intro h
    exact hxW ((Work.PTGeometric.Lvl.Setup.mem_boundary_iff D.S x).mpr h)
  have hxMint : (x : M) ∈ (modelWithCornersEuclideanHalfSpace (CofAtlas.NN k)).interior M := by
    rw [← ModelWithCorners.compl_boundary]
    exact hxMb
  -- the three inputs of the sign identity
  have hLA := Work.ThomBordism.LeadChapter.Lv_comp_A_eq_zero D x κ hκ A hA Lv hLv
  have hcof := Work.ThomBordism.LeadChapter.sgnZ_cofIndex k n M D x Lv N
    (Work.ThomBordism.LeadChapter.range_Lv_eq D x hxMint Lv hLv) j hj
  have hsign := Work.ThomBordism.LeadChapter.sign_identity D x hxMint A N Lv hLv hLA hdet j hcof
  -- non-vanishing of the determinants
  have hblk := Work.ThomBordism.LeadChapter.blockDet_delta_identity D x hxMint A N Lv hLv hLA
  have hA1nz := Work.ThomBordism.CofAtlas.sgn_det_ne_zero D x (D.mem_src_self x) hxMint
  have hA2nz := Work.ThomBordism.CofAtlas.tau_det_ne_zero D x (D.mem_src_self x) hxMint
  have hRHSnz : LinearMap.det (((D.S.chartBeta x).toLinearMap).comp
        (((D.Delta x (x : M)).toLinearMap).comp A.toLinearMap))
      * LinearMap.det (((D.ℓ (D.jx x)).comp (Lv.comp N)) :
          EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) ≠ 0 := by
    rw [← hblk]
    exact mul_ne_zero (mul_ne_zero hA1nz hA2nz) hdet
  have hB1nz : LinearMap.det ((D.S.chartBeta x).comp
      ((D.Delta x (x : M)).comp A)).toLinearMap ≠ 0 := by
    rw [show ((D.S.chartBeta x).comp ((D.Delta x (x : M)).comp A)).toLinearMap
      = (((D.S.chartBeta x).toLinearMap).comp
          (((D.Delta x (x : M)).toLinearMap).comp A.toLinearMap)) from by
        simp only [ContinuousLinearMap.toLinearMap_comp, LinearMap.comp_assoc]]
    exact (mul_ne_zero_iff.mp hRHSnz).1
  -- the chart transfer: `chartTr κ = s1 • chartTr (icChart x)`
  have hmem : x ∈ (icChart 8 (TopCat.of D.S.Pre) x).source :=
    icChart_mem_source 8 (TopCat.of D.S.Pre) x x hxW (mem_extChartAt_source x)
  have hbij : Function.Bijective ((D.S.chartBeta x).comp ((D.Delta x (x : M)).comp A)) :=
    Work.ThomBordism.LeadChapter.bijective_of_det_ne_zero _ hB1nz
  have hderiv := Work.ThomBordism.LeadChapter.lvlChartCompDeriv k n M D x κ hκ A hA hxMint
  have hd : HasFDerivAt (fun z : CofAtlas.E9 =>
      (icChart 8 (TopCat.of D.S.Pre) x) (κ.symm z))
      ((D.S.chartBeta x).comp ((D.Delta x (x : M)).comp A)) (κ x) := by
    refine hderiv.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
    funext z
    exact congrFun (Work.PTGeometric.icChart_coe 8 (TopCat.of D.S.Pre) x) (κ.symm z)
  have htransfer := Work.ThomBordism.PosAtlas.chartTrChangeSigned_gen 9 (by norm_num)
    κ (icChart 8 (TopCat.of D.S.Pre) x) x hκ hmem
    ((D.S.chartBeta x).comp ((D.Delta x (x : M)).comp A)) hbij hd
  -- the integer sign identity
  have heqdet : LinearMap.det ((D.S.chartBeta x).comp
        ((D.Delta x (x : M)).comp A)).toLinearMap
      = LinearMap.det (((D.S.chartBeta x).toLinearMap).comp
        (((D.Delta x (x : M)).toLinearMap).comp A.toLinearMap)) := by
    simp only [ContinuousLinearMap.toLinearMap_comp, LinearMap.comp_assoc]
  have hFs : (if D.flipSign x = 1 then (1 : ℤ) else -1)
        * (if 0 < LinearMap.det ((D.S.chartBeta x).comp
            ((D.Delta x (x : M)).comp A)).toLinearMap then 1 else -1)
      = 1 * sgnZ (blockDet k A N)
        * sgnZ (LinearMap.det (((D.ℓ j).comp (Lv.comp N)) :
            EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k))) := by
    rw [show (if 0 < LinearMap.det ((D.S.chartBeta x).comp
          ((D.Delta x (x : M)).comp A)).toLinearMap then (1 : ℤ) else -1)
        = sgnZ (LinearMap.det ((D.S.chartBeta x).comp
          ((D.Delta x (x : M)).comp A)).toLinearMap) from rfl, heqdet, hsign]
    ring
  -- the final scalar bookkeeping
  have hs1sq : (if 0 < LinearMap.det ((D.S.chartBeta x).comp
          ((D.Delta x (x : M)).comp A)).toLinearMap then (1 : ℤ) else -1)
        * (if 0 < LinearMap.det ((D.S.chartBeta x).comp
          ((D.Delta x (x : M)).comp A)).toLinearMap then 1 else -1) = 1 :=
    Work.ThomBordism.LeadChapter.sgnZ_sq _
  have htrans2 : (Work.PTGeometric.HOF.chartTr (W := TopCat.of D.S.Pre) (N := 9)
        (icChart 8 (TopCat.of D.S.Pre) x) x hmem
        (Work.PTGeometric.HOF.eucFam 9 (by norm_num)
          (icChart 8 (TopCat.of D.S.Pre) x x)))
      = (if 0 < LinearMap.det ((D.S.chartBeta x).comp
          ((D.Delta x (x : M)).comp A)).toLinearMap then (1 : ℤ) else -1) •
        (Work.PTGeometric.HOF.chartTr (W := TopCat.of D.S.Pre) (N := 9) κ x hκ
          (Work.PTGeometric.HOF.eucFam 9 (by norm_num) (κ x))) := by
    calc (Work.PTGeometric.HOF.chartTr (W := TopCat.of D.S.Pre) (N := 9)
          (icChart 8 (TopCat.of D.S.Pre) x) x hmem
          (Work.PTGeometric.HOF.eucFam 9 (by norm_num)
            (icChart 8 (TopCat.of D.S.Pre) x x)))
        = (1 : ℤ) • (Work.PTGeometric.HOF.chartTr (W := TopCat.of D.S.Pre) (N := 9)
            (icChart 8 (TopCat.of D.S.Pre) x) x hmem
            (Work.PTGeometric.HOF.eucFam 9 (by norm_num)
              (icChart 8 (TopCat.of D.S.Pre) x x))) := (one_smul _ _).symm
      _ = ((if 0 < LinearMap.det ((D.S.chartBeta x).comp
              ((D.Delta x (x : M)).comp A)).toLinearMap then (1 : ℤ) else -1)
            * (if 0 < LinearMap.det ((D.S.chartBeta x).comp
              ((D.Delta x (x : M)).comp A)).toLinearMap then 1 else -1)) •
            (Work.PTGeometric.HOF.chartTr (W := TopCat.of D.S.Pre) (N := 9)
              (icChart 8 (TopCat.of D.S.Pre) x) x hmem
              (Work.PTGeometric.HOF.eucFam 9 (by norm_num)
                (icChart 8 (TopCat.of D.S.Pre) x x))) := by rw [hs1sq]
      _ = (if 0 < LinearMap.det ((D.S.chartBeta x).comp
              ((D.Delta x (x : M)).comp A)).toLinearMap then (1 : ℤ) else -1) •
            ((if 0 < LinearMap.det ((D.S.chartBeta x).comp
              ((D.Delta x (x : M)).comp A)).toLinearMap then 1 else -1) •
            (Work.PTGeometric.HOF.chartTr (W := TopCat.of D.S.Pre) (N := 9)
              (icChart 8 (TopCat.of D.S.Pre) x) x hmem
              (Work.PTGeometric.HOF.eucFam 9 (by norm_num)
                (icChart 8 (TopCat.of D.S.Pre) x x)))) := (smul_smul _ _ _).symm
      _ = (if 0 < LinearMap.det ((D.S.chartBeta x).comp
              ((D.Delta x (x : M)).comp A)).toLinearMap then (1 : ℤ) else -1) •
            (Work.PTGeometric.HOF.chartTr (W := TopCat.of D.S.Pre) (N := 9) κ x hκ
              (Work.PTGeometric.HOF.eucFam 9 (by norm_num) (κ x))) := by rw [htransfer]
  rw [htrans2, smul_smul, hFs]

end Work.ThomBordism.LeadChapter
