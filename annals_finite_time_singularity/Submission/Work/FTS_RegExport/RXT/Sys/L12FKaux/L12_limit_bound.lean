import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.Nonlinear.Open.Row25Aux
import Submission.Work.FTS.Nonlinear.Pieces.RNP.RNP24.dzdIter_FK_eq_qang
import Submission.Work.FTS.OpenPkg.prod_field
import Submission.Work.FTS.StrongEps.SupPort.classC_mixed_sup_le
import Submission.Work.FTS.StrongPersist.H6Aux.E2Facts
import Submission.Work.FTS.StrongPersist.H6Rows.H6Pair_of_rows_C6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSlotInt
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundCore
import Submission.Work.FTS.TransportS.T2Sup.GenSlot
import Submission.Work.FTS_RegExport.C4.Dth_mixed_eq_C4
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKjet.L12
import Submission.Work.FTS_RegExport.RXT.Sys.abs_L12dens_Fstar_add_le
import Submission.Work.FTS_RegExport.RXT0.L12FtauTauLip
import Submission.Work.FTS_RegExport.RXT0.SJC.slotJetContinuousOn
import Submission.Work.FTS_RegExport.RXVP3.velPert_unif
import Submission.Work.FTS_RegExport.RXVP3.velVanish2_unif
import Submission.Work.FTS_RegExport.THL.Defs
import Submission.Work.FTS_RegExport.THL.vopPert_theta_holder
import Submission.Work.H2W.FstarDzIterFourPsiAe
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.StrongEps.H5.Nb5Pieces =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-- **The twenty level-`5` `NBlk` pieces, priced.** -/
theorem Nb5_pieces (hH : HAtoms5Pkg) (hWs : WStar5Pkg) (hWf : WFixed5Pkg) (hHf : HFixed5Pkg)
    (hsin5 : SinSqSlot5Pkg) :
    ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {C₀ B Ce Cs6 : ℝ} {Φs : Fn},
      ∃ Kbig : ℝ, 0 < Kbig ∧ ∀ {w Φg : Fn},
        Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
        Work.Spaces.HkNorm α 6 w ≤ B →
        Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
        Work.FTS.StrongPersist.StarPkg6 α Cs6 Φs →
        ∀ k ∈ Finset.range 20,
          Work.Spaces.HkMem α 5 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k) ∧
          Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k) ≤ Kbig := by
  intro α hαI C₀ B Ce Cs6 Φs
  have hα0 : 0 < α := hαI.1
  have hα1 : α ≤ 1 := hαI.2
  -- ## the universal rules
  obtain ⟨Cprod, hCprod, hPRf⟩ := Work.FTS.OpenPkg.prod_field
  obtain ⟨Cw, hCw, hWRf⟩ := wprod_field_winf5
  obtain ⟨Cang, hCang, hangfield⟩ := Work.FTS.StrongPersist.L3Rhs.ang_mul_HkSq_le 5
  obtain ⟨Bsin, hBsin, hSinInt, hSinB, hSinIt⟩ :=
    Work.FTS.Nonlinear.Pieces.RNP.RNP24.angProfile_sinSq
  obtain ⟨Bsin5, hBsin5, hSin5⟩ := hsin5
  have hPR : ∀ f g : Fn, Work.FTS.VocabO.HQo α 4 f → Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ Cprod * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g :=
    hPRf α hα0 hα1
  have hWR : ∀ f g : Fn, Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 5 f →
      Work.FTS.VocabO.HQo α 5 g →
      Work.Spaces.HkMem α 5 (fun z θ => f z θ * g z θ) ∧
      Work.Spaces.HkNorm α 5 (fun z θ => f z θ * g z θ)
        ≤ Cw * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 5 f * Work.Spaces.HkNorm α 5 g :=
    hWRf α hα0 hα1
  -- ## the atomic constants
  obtain ⟨aH, haH, hHA⟩ := hH hαI
  obtain ⟨aWs, haWs, hWA⟩ := hWs hαI (Cs6 := Cs6)
  obtain ⟨aWf, haWf, hWfA⟩ := hWf hαI
  obtain ⟨aHf, haHf, hHfA⟩ := hHf hαI
  set A : ℝ := max (max aH aWs) (max aWf aHf) with hAdef
  have hA1 : aH ≤ A := le_trans (le_max_left _ _) (le_max_left _ _)
  have hA2 : aWs ≤ A := le_trans (le_max_right _ _) (le_max_left _ _)
  have hA3 : aWf ≤ A := le_trans (le_max_left _ _) (le_max_right _ _)
  have hA4 : aHf ≤ A := le_trans (le_max_right _ _) (le_max_right _ _)
  have hAnn : 0 ≤ A := le_trans haH.le hA1
  -- ## the two coefficient levels and the angular coefficient
  set P1 : ℝ := 3 * (Cprod * α ^ (-(1 / 2 : ℝ)) * A * A) with hP1def
  set P2 : ℝ := Cw * α ^ (-(1 / 2 : ℝ)) * A * A with hP2def
  have hP1nn : 0 ≤ P1 := by
    rw [hP1def]
    exact mul_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg (mul_nonneg hCprod.le (Real.rpow_nonneg hα0.le _)) hAnn) hAnn)
  have hP2nn : 0 ≤ P2 := by
    rw [hP2def]
    exact mul_nonneg (mul_nonneg (mul_nonneg hCw.le (Real.rpow_nonneg hα0.le _)) hAnn) hAnn
  set Bmax : ℝ := max Bsin Bsin5 with hBmaxdef
  have hBmaxpos : 0 < Bmax := lt_of_lt_of_le hBsin (le_max_left _ _)
  have hSinSlots : ∀ i : ℕ, 1 ≤ i → i ≤ 5 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => -(Real.sin θ') ^ 2) 0 θ|
        ≤ Bmax * Real.sin (2 * θ) := by
    intro i hi1 hi5 θ hθ
    have hsin0 : 0 ≤ Real.sin (2 * θ) :=
      Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
    rcases eq_or_lt_of_le hi5 with h5 | h5
    · rw [h5]
      exact le_trans (hSin5 θ hθ) (mul_le_mul_of_nonneg_right (le_max_right _ _) hsin0)
    · exact le_trans (hSinIt i hi1 (by omega) θ hθ)
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hsin0)
  have hSinBnd : ∀ θ ∈ Work.Spaces.Iθ, |-(Real.sin θ) ^ 2| ≤ Bmax :=
    fun θ hθ => le_trans (hSinB θ hθ) (le_max_left _ _)
  set Sang : ℝ := Real.sqrt (Cang * Bmax ^ 2) with hSangdef
  have hSangnn : 0 ≤ Sang := Real.sqrt_nonneg _
  -- ## the table of the twenty bounds
  set T : ℕ → ℝ := fun k => match k with
    | 0 => |(2 : ℝ)| * P1
    | 1 => |(2 : ℝ)| * P2
    | 2 => |(2 : ℝ)| * P2
    | 3 => |(2 : ℝ)| * P2
    | 4 => |(-2 : ℝ)| * P1
    | 5 => |(-2 : ℝ)| * P2
    | 6 => |(-2 : ℝ)| * P2
    | 7 => |(-2 : ℝ)| * P2
    | 8 => |(-(2 * α))| * P1
    | 9 => |(-(2 * α))| * P2
    | 10 => |(-(2 * α))| * P2
    | 11 => |(-(2 * α))| * P2
    | 12 => |(-(1 / 2))| * P1
    | 13 => |(-(1 / 2))| * P2
    | 14 => |(1 / 2)| * P2
    | 15 => A
    | 16 => Sang * P1
    | 17 => Sang * P2
    | 18 => Sang * P2
    | _ => Sang * A with hTdef
  have hTnn : ∀ k ∈ Finset.range 20, 0 ≤ T k := by
    intro k hk
    have hk20 : k < 20 := Finset.mem_range.mp hk
    interval_cases k <;> simp only [hTdef] <;> first | positivity | exact hAnn
  set Kbig : ℝ := 1 + ∑ k ∈ Finset.range 20, T k with hKbigdef
  have hKbigpos : 0 < Kbig := by
    rw [hKbigdef]
    linarith [Finset.sum_nonneg hTnn]
  have hbE : ∀ k ∈ Finset.range 20, T k ≤ Kbig := by
    intro k hk
    rw [hKbigdef]
    linarith [Finset.single_le_sum hTnn hk]
  refine ⟨Kbig, hKbigpos, ?_⟩
  intro w Φg hw hXw hX6 hell hstar
  -- ## the atoms, for the actual `w`, `Φg`
  obtain ⟨hRp, hUp, hVp, hwp, hDthp, hDzp, hFKp, hφwp, hφDthp, hφDzp⟩ := hHA hw hXw hX6 hell
  have hqoR := hRp.1
  have hRbd' : Work.Spaces.HkNorm α 5
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg)) ≤ A := le_trans hRp.2 hA1
  have hqoU := hUp.1
  have hUbd' : Work.Spaces.HkNorm α 5 (fun z θ => Work.Construction.Uop α
      (Work.FTS.Nonlin.PhiTg α w Φg) z θ / Work.Construction.s2 θ) ≤ A := le_trans hUp.2 hA1
  have hqoV := hVp.1
  have hVbd' : Work.Spaces.HkNorm α 5
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg)) ≤ A := le_trans hVp.2 hA1
  have hqow := hwp.1
  have hwbd' : Work.Spaces.HkNorm α 5 w ≤ A := le_trans hwp.2 hA1
  have hqoDthw := hDthp.1
  have hDthwbd' : Work.Spaces.HkNorm α 5 (Work.Spaces.Dth w) ≤ A := le_trans hDthp.2 hA1
  have hqoDzw := hDzp.1
  have hDzwbd' : Work.Spaces.HkNorm α 5 (Work.Spaces.Dz w) ≤ A := le_trans hDzp.2 hA1
  have hqoFKw := hFKp.1
  have hFKwbd' : Work.Spaces.HkNorm α 5 (fun z _ => Work.Construction.FK w z) ≤ A :=
    le_trans hFKp.2 hA1
  have hqoφw := hφwp.1
  have hφwbd' : Work.Spaces.HkNorm α 5 (fun z θ => z / (1 + z) * w z θ) ≤ A :=
    le_trans hφwp.2 hA1
  have hqoφDthw := hφDthp.1
  have hφDthwbd' : Work.Spaces.HkNorm α 5
      (fun z θ => z / (1 + z) * Work.Spaces.Dth w z θ) ≤ A := le_trans hφDthp.2 hA1
  have hqoφDzw := hφDzp.1
  have hφDzwbd' : Work.Spaces.HkNorm α 5
      (fun z θ => z / (1 + z) * Work.Spaces.Dz w z θ) ≤ A := le_trans hφDzp.2 hA1
  obtain ⟨hRsp, hUsp, hVsp⟩ := hWA hstar
  have hRsm := hRsp.1
  have hRwm := hRsp.2.1
  have hRwb' : Work.Spaces.WlInf α 5 (fun z θ => (z + 1) / z
      * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ) ≤ A :=
    le_trans hRsp.2.2 hA2
  have hUsm := hUsp.1
  have hUwm := hUsp.2.1
  have hUwb' : Work.Spaces.WlInf α 5 (fun z θ => (z + 1) / z
      * (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
        / Work.Construction.s2 θ)) ≤ A := le_trans hUsp.2.2 hA2
  have hVsm := hVsp.1
  have hVwm := hVsp.2.1
  have hVwb' : Work.Spaces.WlInf α 5 (fun z θ => (z + 1) / z
      * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ) ≤ A :=
    le_trans hVsp.2.2 hA2
  obtain ⟨hFp, hDthFp, hDzFp, hKerp⟩ := hWfA
  have hFsm := hFp.1
  have hFwm := hFp.2.1
  have hFwb' : Work.Spaces.WlInf α 5 (Work.Construction.Fstar α) ≤ A :=
    le_trans hFp.2.2 hA3
  have hDthFsm := hDthFp.1
  have hDthFwm := hDthFp.2.1
  have hDthFwb' : Work.Spaces.WlInf α 5 (Work.Spaces.Dth (Work.Construction.Fstar α)) ≤ A :=
    le_trans hDthFp.2.2 hA3
  have hDzFsm := hDzFp.1
  have hDzFwm := hDzFp.2.1
  have hDzFwb' : Work.Spaces.WlInf α 5 (Work.Spaces.Dz (Work.Construction.Fstar α)) ≤ A :=
    le_trans hDzFp.2.2 hA3
  have hKersm := hKerp.1
  have hKerwm := hKerp.2.1
  have hKerwb' : Work.Spaces.WlInf α 5 (fun z _ => (-(2 * α)) * Work.Spaces.hKer z) ≤ A :=
    le_trans hKerp.2.2 hA3
  obtain ⟨hφFp, hφDthFp, hφDzFp, hFKthFp, hFKFp⟩ := hHfA
  have hφF := hφFp.1
  have hφFbd' : Work.Spaces.HkNorm α 5
      (fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ) ≤ A :=
    le_trans hφFp.2 hA4
  have hφDthF := hφDthFp.1
  have hφDthFbd' : Work.Spaces.HkNorm α 5 (fun z θ => z / (1 + z)
      * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ≤ A := le_trans hφDthFp.2 hA4
  have hφDzF := hφDzFp.1
  have hφDzFbd' : Work.Spaces.HkNorm α 5 (fun z θ => z / (1 + z)
      * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ≤ A := le_trans hφDzFp.2 hA4
  have hFKthF := hFKthFp.1
  have hFKthFbd' : Work.Spaces.HkNorm α 5 (fun z θ =>
      Work.Construction.FK (Work.Construction.Fstar α) z
        * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ≤ A := le_trans hFKthFp.2 hA4
  have hFKF := hFKFp.1
  have hFKFbd' : Work.Spaces.HkNorm α 5 (fun z θ =>
      Work.Construction.FK (Work.Construction.Fstar α) z
        * Work.Construction.Fstar α z θ) ≤ A := le_trans hFKFp.2 hA4
  -- ## the fourteen `ℋ × ℋ` / `𝒲 × ℋ` pieces
  have hp0 := prodHH5 (α := α) (Cprod := Cprod) (c := 2) (a := A) (b := A) hα0 hα1 hCprod
    hPR hAnn hAnn hqoR hRbd' hqow hwbd'
  have hp1 := prodWH5 (α := α) (Cw := Cw) (c := 2) (a := A) (b := A) hα0 hCw hWR hAnn hAnn
    hFsm hFwm hFwb' hqoR hRbd'
  have hp2 := prodWH5 (α := α) (Cw := Cw) (c := 2) (a := A) (b := A) hα0 hCw hWR hAnn hAnn
    hRsm hRwm hRwb' hqoφw hφwbd'
  have hp3 := prodWH5 (α := α) (Cw := Cw) (c := 2) (a := A) (b := A) hα0 hCw hWR hAnn hAnn
    hRsm hRwm hRwb' hφF hφFbd'
  have hp4 := prodHH5 (α := α) (Cprod := Cprod) (c := -2) (a := A) (b := A) hα0 hα1 hCprod
    hPR hAnn hAnn hqoU hUbd' hqoDthw hDthwbd'
  have hp5 := prodWH5 (α := α) (Cw := Cw) (c := -2) (a := A) (b := A) hα0 hCw hWR hAnn hAnn
    hDthFsm hDthFwm hDthFwb' hqoU hUbd'
  have hp6 := prodWH5 (α := α) (Cw := Cw) (c := -2) (a := A) (b := A) hα0 hCw hWR hAnn hAnn
    hUsm hUwm hUwb' hqoφDthw hφDthwbd'
  have hp7 := prodWH5 (α := α) (Cw := Cw) (c := -2) (a := A) (b := A) hα0 hCw hWR hAnn hAnn
    hUsm hUwm hUwb' hφDthF hφDthFbd'
  have hp8 := prodHH5 (α := α) (Cprod := Cprod) (c := -(2 * α)) (a := A) (b := A) hα0 hα1
    hCprod hPR hAnn hAnn hqoV hVbd' hqoDzw hDzwbd'
  have hp9 := prodWH5 (α := α) (Cw := Cw) (c := -(2 * α)) (a := A) (b := A) hα0 hCw hWR
    hAnn hAnn hDzFsm hDzFwm hDzFwb' hqoV hVbd'
  have hp10 := prodWH5 (α := α) (Cw := Cw) (c := -(2 * α)) (a := A) (b := A) hα0 hCw hWR
    hAnn hAnn hVsm hVwm hVwb' hqoφDzw hφDzwbd'
  have hp11 := prodWH5 (α := α) (Cw := Cw) (c := -(2 * α)) (a := A) (b := A) hα0 hCw hWR
    hAnn hAnn hVsm hVwm hVwb' hφDzF hφDzFbd'
  have hp12 := prodHH5 (α := α) (Cprod := Cprod) (c := -(1 / 2)) (a := A) (b := A) hα0 hα1
    hCprod hPR hAnn hAnn hqoFKw hFKwbd' hqoDthw hDthwbd'
  have hp13 := prodWH5 (α := α) (Cw := Cw) (c := -(1 / 2)) (a := A) (b := A) hα0 hCw hWR
    hAnn hAnn hDthFsm hDthFwm hDthFwb' hqoFKw hFKwbd'
  have hp14 := prodWH5 (α := α) (Cw := Cw) (c := (1 / 2)) (a := A) (b := A) hα0 hCw hWR
    hAnn hAnn hKersm hKerwm hKerwb' hqoDthw hDthwbd'
  -- ## the four `sin²θ`-pieces
  have hSinMul : ∀ G : Fn, Work.FTS.EllipticEst.SmoothOpen G → Work.Spaces.HkMem α 5 G →
      Work.Spaces.HkMem α 5 (fun z θ => -(Real.sin θ) ^ 2 * G z θ) ∧
      Work.Spaces.HkSq α 5 (fun z θ => -(Real.sin θ) ^ 2 * G z θ)
        ≤ Cang * Bmax ^ 2 * Work.Spaces.HkSq α 5 G := by
    intro G hGsm hGm
    exact hangfield α hα0 hα1 (fun θ => -(Real.sin θ) ^ 2) Bmax hBmaxpos
      Work.FTS.Nonlinear.Open.row25_smoothOpen_neg_sinSq hSinBnd hSinSlots G hGsm hGm
  have hSinNorm : ∀ {G : Fn}, Work.FTS.EllipticEst.SmoothOpen G → Work.Spaces.HkMem α 5 G →
      Work.Spaces.HkNorm α 5 (fun z θ => -(Real.sin θ) ^ 2 * G z θ)
        ≤ Sang * Work.Spaces.HkNorm α 5 G := by
    intro G hGsm hGm
    have h1 := (hSinMul G hGsm hGm).2
    calc Work.Spaces.HkNorm α 5 (fun z θ => -(Real.sin θ) ^ 2 * G z θ)
        = Real.sqrt (Work.Spaces.HkSq α 5 (fun z θ => -(Real.sin θ) ^ 2 * G z θ)) := rfl
      _ ≤ Real.sqrt (Cang * Bmax ^ 2 * Work.Spaces.HkSq α 5 G) := Real.sqrt_le_sqrt h1
      _ = Sang * Work.Spaces.HkNorm α 5 G := by
          rw [Real.sqrt_mul (by positivity), hSangdef]
          rfl
  have hFKwsmo : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.FK w z) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_FKw_of_classC hw
  have hFKesmo : Work.FTS.EllipticEst.SmoothOpen
      (fun z _ => Work.Construction.FK (Work.Construction.Fstar α) z) :=
    Work.FTS.GalFields.RHS.smoothOpen_FK_Fstar_rad α hα0 hα1
  have hp16i := prodHH5 (α := α) (Cprod := Cprod) (c := 1) (a := A) (b := A) hα0 hα1 hCprod
    hPR hAnn hAnn hqoFKw hFKwbd' hqow hwbd'
  have hp17i := prodWH5 (α := α) (Cw := Cw) (c := 1) (a := A) (b := A) hα0 hCw hWR hAnn hAnn
    hFsm hFwm hFwb' hqoFKw hFKwbd'
  have hp18i := prodWH5 (α := α) (Cw := Cw) (c := 1) (a := A) (b := A) hα0 hCw hWR hAnn hAnn
    hKersm hKerwm hKerwb' hqow hwbd'
  have hp16m : Work.Spaces.HkMem α 5 (fun z θ => -(Real.sin θ) ^ 2
      * (Work.Construction.FK w z * w z θ)) :=
    (hSinMul _ (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hFKwsmo hw.reg)
      (by simpa only [one_mul] using hp16i.1)).1
  have hp16b : Work.Spaces.HkNorm α 5 (fun z θ => -(Real.sin θ) ^ 2
      * (Work.Construction.FK w z * w z θ)) ≤ Sang * P1 := by
    refine le_trans (hSinNorm (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hFKwsmo hw.reg)
      (by simpa only [one_mul] using hp16i.1)) ?_
    exact mul_le_mul_of_nonneg_left (by simpa only [one_mul, abs_one] using hp16i.2) hSangnn
  have hp17m : Work.Spaces.HkMem α 5 (fun z θ => -(Real.sin θ) ^ 2
      * (Work.Construction.Fstar α z θ * Work.Construction.FK w z)) :=
    (hSinMul _ (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hFsm hFKwsmo)
      (by simpa only [one_mul] using hp17i.1)).1
  have hp17b : Work.Spaces.HkNorm α 5 (fun z θ => -(Real.sin θ) ^ 2
      * (Work.Construction.Fstar α z θ * Work.Construction.FK w z))
      ≤ Sang * P2 := by
    refine le_trans (hSinNorm (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hFsm hFKwsmo)
      (by simpa only [one_mul] using hp17i.1)) ?_
    exact mul_le_mul_of_nonneg_left (by simpa only [one_mul, abs_one] using hp17i.2) hSangnn
  have hp18m : Work.Spaces.HkMem α 5 (fun z θ => -(Real.sin θ) ^ 2
      * ((-(2 * α)) * Work.Spaces.hKer z * w z θ)) :=
    (hSinMul _ (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hKersm hw.reg)
      (by simpa only [one_mul] using hp18i.1)).1
  have hp18b : Work.Spaces.HkNorm α 5 (fun z θ => -(Real.sin θ) ^ 2
      * ((-(2 * α)) * Work.Spaces.hKer z * w z θ)) ≤ Sang * P2 := by
    refine le_trans (hSinNorm (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hKersm hw.reg)
      (by simpa only [one_mul] using hp18i.1)) ?_
    exact mul_le_mul_of_nonneg_left (by simpa only [one_mul, abs_one] using hp18i.2) hSangnn
  have hYeq : (fun z θ => (-1) * (-(Real.sin θ) ^ 2
        * ((-(2 * α)) * Work.Spaces.hKer z * w z θ)))
      = Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 18 := by
    funext z θ
    simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]
    rw [Work.FTS.Nonlin.FK_Fstar hα0 hα1, Work.Spaces.hKer_apply]
    ring
  have hp18mN : Work.Spaces.HkMem α 5 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 18) :=
    hYeq ▸ (Work.FTS.LocData.HkMem_const_mul α 5 (-1) hp18m)
  have hp18bN : Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 18)
      ≤ T 18 := by
    have hb : Work.Spaces.HkNorm α 5 (fun z θ => -(Real.sin θ) ^ 2
        * ((-(2 * α)) * Work.Spaces.hKer z * w z θ)) ≤ Sang * P2 := hp18b
    rw [← hYeq, HkNorm_const_mul5, hTdef]
    simpa only [abs_neg, abs_one, one_mul] using hb
  -- ## pieces 15 and 19: the two fixed `ℋ`-atoms
  have hp15m : Work.Spaces.HkMem α 5 (fun z θ => (-(1 / 2))
      * (Work.Construction.FK (Work.Construction.Fstar α) z
        * Work.Spaces.Dth (Work.Construction.Fstar α) z θ)) :=
    Work.FTS.LocData.HkMem_const_mul α 5 (-(1 / 2)) hFKthF.2
  have hp15b : Work.Spaces.HkNorm α 5 (fun z θ => (-(1 / 2))
      * (Work.Construction.FK (Work.Construction.Fstar α) z
        * Work.Spaces.Dth (Work.Construction.Fstar α) z θ)) ≤ A := by
    rw [HkNorm_const_mul5]
    calc |(-(1 / 2))| * Work.Spaces.HkNorm α 5 (fun z θ =>
          Work.Construction.FK (Work.Construction.Fstar α) z
            * Work.Spaces.Dth (Work.Construction.Fstar α) z θ)
        = (1 / 2) * Work.Spaces.HkNorm α 5 (fun z θ =>
            Work.Construction.FK (Work.Construction.Fstar α) z
              * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) := by norm_num
      _ ≤ (1 / 2) * A := mul_le_mul_of_nonneg_left hFKthFbd' (by norm_num)
      _ ≤ A := by linarith [hAnn]
  have hp19m : Work.Spaces.HkMem α 5 (fun z θ => -(Real.sin θ) ^ 2
      * (Work.Construction.FK (Work.Construction.Fstar α) z
        * Work.Construction.Fstar α z θ)) :=
    (hSinMul _ (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hFKesmo hFsm) hFKF.2).1
  have hp19b : Work.Spaces.HkNorm α 5 (fun z θ => -(Real.sin θ) ^ 2
      * (Work.Construction.FK (Work.Construction.Fstar α) z
        * Work.Construction.Fstar α z θ)) ≤ Sang * A := by
    refine le_trans (hSinNorm (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hFKesmo hFsm)
      hFKF.2) ?_
    exact mul_le_mul_of_nonneg_left hFKFbd' hSangnn
  -- ## the twenty pieces
  have hpiece : ∀ k ∈ Finset.range 20,
      Work.Spaces.HkMem α 5 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k) ∧
      Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k) ≤ T k := by
    intro k hk
    have hk20 : k < 20 := Finset.mem_range.mp hk
    interval_cases k
    · exact ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs] using hp0.1,
        by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs, hTdef] using hp0.2⟩
    · exact ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs] using hp1.1,
        by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs, hTdef] using hp1.2⟩
    · exact ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs] using hp2.1,
        by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs, hTdef] using hp2.2⟩
    · exact ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs] using hp3.1,
        by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs, hTdef] using hp3.2⟩
    · exact ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs] using hp4.1,
        by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs, hTdef] using hp4.2⟩
    · exact ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs] using hp5.1,
        by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs, hTdef] using hp5.2⟩
    · exact ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs] using hp6.1,
        by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs, hTdef] using hp6.2⟩
    · exact ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs] using hp7.1,
        by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs, hTdef] using hp7.2⟩
    · exact ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs] using hp8.1,
        by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs, hTdef] using hp8.2⟩
    · exact ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs] using hp9.1,
        by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs, hTdef] using hp9.2⟩
    · exact ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs] using hp10.1,
        by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs, hTdef] using hp10.2⟩
    · exact ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs] using hp11.1,
        by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs, hTdef] using hp11.2⟩
    · exact ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs] using hp12.1,
        by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs, hTdef] using hp12.2⟩
    · exact ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs] using hp13.1,
        by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs, hTdef] using hp13.2⟩
    · exact ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs] using hp14.1,
        by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs, hTdef] using hp14.2⟩
    · exact ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs] using hp15m,
        by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs, hTdef] using hp15b⟩
    · exact ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs] using hp16m,
        by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs, hTdef] using hp16b⟩
    · exact ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs] using hp17m,
        by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs, hTdef] using hp17b⟩
    · exact ⟨hp18mN, hp18bN⟩
    · exact ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs] using hp19m,
        by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs, hTdef] using hp19b⟩
  intro k hk
  exact ⟨(hpiece k hk).1, le_trans (hpiece k hk).2 (hbE k hk)⟩

end Work.FTS.StrongEps.H5
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR7.r7Joint =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS_RegExport.RXR7

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- **RX-R7, the `hFjoint` field.**  Joint `C¹`-regularity of the full profile of the R7
block, `Prof α g p.1 p.2.1 p.2.2 = profFull α (extG (gS α (tauExt g))) p.1 p.2.1 p.2.2`, on the
slab `R7Slab S = (0,∞) × (0,π/2) × [0,S]` — i.e. *including* `τ = 0`, where `RegPkgMin.c1` (only
`τ > 0`) gives nothing.

Route.  Write `K` for `K7 α Φs E g`.  Two inputs are needed.

(A) **`K` is jointly continuous on the slab.**  By `hVP S hS`, the triple
`(Vz7ᵣ, Vθ7ᵣ, cs7ᵣ)` is continuous on `Ioi 0 ×ˢ Icc 0 (π/2) ×ˢ Icc 0 S` (`VelPkg.cont`), and by
the proved `Work.FTS_RegExport.RXT.jc3` the mixed jets `mixed j i (slice g τ)` (`j+i ≤ 3`) are
continuous on `Ioi 0 ×ˢ Ioo 0 (π/2) ×ˢ Icc 0 T`.  On `z > 0` and `τ ≥ 0`, `Prof α g` agrees with
`Ftau (pExp α) (GR α g) τ = F_* + slice (GR α g) τ = F_* + slice g τ` (use
`extG_of_pos`, `gS`, `tauExt_of_nonneg`, `slice_tauExt`), so `Prof`, `Dz (Prof)` and `pth (Prof)`
are jointly continuous there (`jc3` at `(0,0)`, `(1,0)`, `(0,1)` plus the explicit smooth `F_*`;
`pth = mixed 0 1 / sin 2θ`).  Product of jointly continuous functions gives `K` continuous.

(B) **The one-sided `C¹` at the boundary `τ = 0`.**  Fix `q = (z,θ,0) ∈ R7Slab S` and
`y = (z',θ',τ') ∈ R7Slab S` near `q`.  Decompose
`Prof(y) - Prof(q) = [Prof(z',θ',0) - Prof(q)] + [Prof(z',θ',τ') - Prof(z',θ',0)]`.
The first bracket is `o(‖y-q‖)` because the `τ = 0` slice is `C⁴`, hence `C¹`, on `Q0`
(`hOK.1.1.c4 0`; on the quadrant `Prof α g z θ 0 = F_* + g z θ 0`).  For the second bracket:
the map `s ↦ Prof α g z' θ' s` has derivative `-K(z',θ',s)` at every `s ∈ (0,τ']` (`hEq`), so the
FTC on `[ε,τ']` for `ε ↓ 0` (using `hOK.1.1.cont` for continuity at `s = 0` and boundedness of
`K` near `q`) gives `Prof(z',θ',τ') - Prof(z',θ',0) = -∫₀^{τ'} K(z',θ',s) ds`, whence
`|Prof(z',θ',τ') - Prof(z',θ',0) + K(q)τ'| ≤ τ'·sup_{s∈(0,τ')}|K(z',θ',s) - K(q)| ≤ ‖y-q‖·(small)`
by (A).  So the profile is differentiable within the slab at `q`, with the linear map whose
`(z,θ)`-part is the `C¹` differential of the `τ = 0` slice and whose `τ`-component is `-K(q)`.

Assembly: at `τ > 0` the profile is `C¹` around the point by `hOK.1.1.c1`
(`ContDiffAt` on `Ioi 0 ×ˢ Ioo 0 (π/2) ×ˢ Ioi 0`, transported along
`extG (GR α g) = g` on the quadrant); at `τ = 0` use (B).  Conclude `ContDiffOn ℝ 1` from
`contDiffWithinAt_succ_iff_hasFDerivWithinAt` with `n = 0` and the slab `R7Slab S` as the set,
the derivative function being continuous on the slab ((A) plus `jc3` for the spatial partials),
then `ContDiffOn` from `ContDiffWithinAt` at every point. -/
theorem r7Joint {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam} {S : ℝ}
    (hS : 0 < S) (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hμ : Work.FTS.RegExportIface.ClockBd α Φs E g)
    (hVP : ∀ S > 0, Work.FTS.RegExportIface.VelPkg (Work.FTS.Regularity.pExp α)
      (Work.FTS_RegExport.RXR7.μR α Φs E g) (Work.FTS_RegExport.RXR7.GR α g)
      (Work.FTS_RegExport.RXR7.ΦR α Φs E g) S)
    (hEq : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S →
      HasDerivAt (fun s => Work.FTS_RegExport.RXR7.Prof α g z θ s)
        (-(Work.FTS_RegExport.RXR7.K7 α Φs E g z θ τ)) τ) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => Work.FTS_RegExport.RXR7.Prof α g p.1 p.2.1 p.2.2)
      (Work.FTS_RegExport.RXR7.R7Slab S) := by
  -- the derivative function is jointly continuous on the slab
  have hFD : ContinuousOn (fun p : ℝ × ℝ × ℝ => ProfD α Φs E g p) (R7Slab S) :=
    ProfD_contOn_slab hS hα hα13 hOK (hVP S hS)
  -- and it is the honest derivative at every point of the slab
  have hderiv := profile_hasFDerivWithinAt hS hα hα13 hOK (hVP S hS) hEq
  intro q hq
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl]
  rw [contDiffWithinAt_succ_iff_hasFDerivWithinAt' (n := 0)
    (by simp : (0 : WithTop ℕ∞) ≠ ((⊤ : ℕ∞) : WithTop ℕ∞))]
  refine ⟨R7Slab S, ?_, ?_, ?_, (fun p => ProfD α Φs E g p), hderiv, ?_⟩
  · rw [mem_nhdsWithin_insert]
    exact ⟨hq, self_mem_nhdsWithin⟩
  · exact subset_insert q (R7Slab S)
  · intro h; exact absurd h (by simp)
  · rw [contDiffWithinAt_zero hq]
    exact ⟨univ, Filter.univ_mem, by simpa using hFD⟩
end Work.FTS_RegExport.RXR7
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.Horizon =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `L12FKaux.Horizon` — the standing estimates on a fake-time horizon `[0,T]`

The class-`C` data of `LimApprox` restricted to a horizon `[0,T]` give, uniformly in the
approximating index `n` and in `τ ∈ [0,T]`:

* `approx_slot_bound` — the weighted slot bound
  `|D_z^k (slice (gn n) τ)| ≤ Cw · z^{3/2}/(1+z)²` (`k ≤ 2`) — the restricted variant of
  `Standing.app_slot_le`;
* `ftau_slot_bound` — the order-`3` slot bound of the profiles `F(τ) = F_* + slice (gn n) τ`,
  uniform in `τ ∈ [0,T]` (the restricted variant of `FKDeriv.Ftau_slot_le3`);
* `app_diff_unif_Icc` — the uniform `L^∞`-modulus in `τ` (restricted `Standing.app_diff_unif`);
* `app_diff_le_Icc` — the weighted `τ`-modulus (restricted `Standing.app_diff_le`).

Everything is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Sys.L12FKaux

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **Weighted slot bounds on a horizon**: `|D_z^k (slice (gn n) τ)| ≤ Cw · z^{3/2}/(1+z)²`. -/
theorem approx_slot_bound {α C₀ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {gn : ℕ → Fam} {T : ℝ} (hT : 0 < T)
    (hcl : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T →
      Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) (slice (gn n) τ))
    (hXn : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T →
      Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
        ≤ C₀ * (Work.FTS.Regularity.pExp α) ^ 2) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T → ∀ (k : ℕ), k ≤ 2 →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k (slice (gn n) τ) z θ| ≤ Cw * SW z := by
  have hβ : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hβ1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  obtain ⟨Cd, hCd0, hCd⟩ := Work.FTS_RegExport.RXA1w.abs_mixed_le_HkNorm_C4_w_proved hβ hβ1
  have hmem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
  have hX0 : 0 ≤ C₀ * (Work.FTS.Regularity.pExp α) ^ 2 :=
    le_trans (Work.Spaces.HkNorm_nonneg (Work.FTS.Regularity.pExp α) 4 (slice (gn 0) 0))
      (hXn 0 0 hmem0)
  refine ⟨Cd * (C₀ * (Work.FTS.Regularity.pExp α) ^ 2), mul_nonneg hCd0 hX0, ?_⟩
  intro n τ hτ k hk z θ hz hθ0 hθ1
  have hcln := hcl n τ hτ
  have h4 : ContDiffOn ℝ 4 (Function.uncurry (slice (gn n) τ)) Work.FTS.EllipticEst.Q0 :=
    hcln.reg.forall 4
  have hmem : Work.Spaces.HkMem (Work.FTS.Regularity.pExp α) 4 (slice (gn n) τ) :=
    Work.FTS.ClassC.classC_hkMem_four hcln
  have htr : Work.FTS.Nonlin.BdryTraces (Work.FTS.Regularity.pExp α) 4 (slice (gn n) τ) :=
    Work.FTS.ClassC.bdryTraces_mono (by norm_num) hcln.tr
  have h1 := hCd _ h4 hmem htr k 0 (by omega) z θ hz hθ0 hθ1
  have h2 : Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4 (slice (gn n) τ)
      ≤ C₀ * (Work.FTS.Regularity.pExp α) ^ 2 := hXn n τ hτ
  calc |Work.Spaces.DzIter k (slice (gn n) τ) z θ|
      = |Work.Spaces.mixed k 0 (slice (gn n) τ) z θ| := by rw [Work.Spaces.mixed_zero_right]
    _ ≤ Cd * SW z * Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4 (slice (gn n) τ) := h1
    _ ≤ Cd * SW z * (C₀ * (Work.FTS.Regularity.pExp α) ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg hCd0 (SW_nonneg hz.le))
    _ = (Cd * (C₀ * (Work.FTS.Regularity.pExp α) ^ 2)) * SW z := by ring

/-- **Order-`3` slot bounds of the profiles, uniform on the horizon.** -/
theorem ftau_slot_bound {α B : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {gn : ℕ → Fam} {T : ℝ}
    (hcl : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T →
      Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) (slice (gn n) τ))
    (hXn6 : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T →
      Work.FTS.StrongGlobal.Xn6 (Work.FTS.Regularity.pExp α) (slice (gn n) τ) ≤ B) :
    ∃ CB : ℝ, 0 ≤ CB ∧ ∀ (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T →
      ∀ (n : ℕ) (k : ℕ), k ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (gn n) τ) z θ| ≤ CB := by
  have hβ : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hβ1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  obtain ⟨C4, hC4pos, hC4⟩ := Work.FTS.StrongEps.classC_mixed_sup_le_four
  obtain ⟨M, hM0, hM⟩ := Work.FTS.StrongPersist.H6Pair6Aux.FstarJet7
  refine ⟨10 * M + C4 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1)
    * max B 0, ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ 10 * M := by linarith
    have h2 : (0 : ℝ) ≤ C4 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1)
        * max B 0 :=
      mul_nonneg (div_nonneg hC4pos.le (Real.sqrt_nonneg _)) (le_max_right B 0)
    linarith
  · intro τ hτ n k hk z θ hz h0 h1
    have hadd : Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (gn n) τ) z θ
        = Work.Spaces.DzIter k (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
          + Work.Spaces.DzIter k (slice (gn n) τ) z θ := by
      have h := Work.FTS.CoercivityFix.Transfer.E2pkg.DzIter_add_of_contDiffOn
        (n := 4) (f₁ := Work.Construction.Fstar (Work.FTS.Regularity.pExp α))
        (f₂ := fun z θ => gn n z θ τ) Work.FTS.EllipticEst.isOpen_Q0
        (Fstar_contDiffOn hβ hβ1 4) ((hcl n τ hτ).reg.forall 4) k (by omega)
        (z, θ) ⟨hz, h0, h1⟩
      rw [show Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ
          = Work.Construction.Fstar (Work.FTS.Regularity.pExp α)
            + fun z θ => gn n z θ τ from rfl]
      rw [show slice (gn n) τ = fun z θ => gn n z θ τ from rfl]
      exact h
    rw [hadd]
    have hA' : |Work.Spaces.DzIter k (Work.Construction.Fstar
        (Work.FTS.Regularity.pExp α)) z θ| ≤ 10 * M :=
      Work.FTS_RegExport.RXT.ftau_DzIter_Fstar_le (α := α) hα hα13 hM k (by omega)
        z θ hz h0 h1
    have hB' : |Work.Spaces.DzIter k (slice (gn n) τ) z θ|
        ≤ C4 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) * max B 0 := by
      have h := hC4 (Work.FTS.Regularity.pExp α) ⟨hβ, hβ1⟩ (hcl n τ hτ) k 0
        (by omega) ⟨hz, h0, h1⟩
      have hX : Work.FTS.StrongGlobal.Xn6 (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
          ≤ max B 0 := le_trans (hXn6 n τ hτ) (le_max_left B 0)
      rw [Work.Spaces.mixed_zero_right] at h
      exact le_trans h (mul_le_mul_of_nonneg_left hX
        (div_nonneg hC4pos.le (Real.sqrt_nonneg _)))
    calc |Work.Spaces.DzIter k (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
          + Work.Spaces.DzIter k (slice (gn n) τ) z θ|
        ≤ |Work.Spaces.DzIter k (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ|
          + |Work.Spaces.DzIter k (slice (gn n) τ) z θ| := abs_add_le _ _
      _ ≤ 10 * M + C4 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1)
            * max B 0 := add_le_add hA' hB'

/-- **Uniform `L^∞`-modulus in `τ`** on a horizon (the restricted `Standing.app_diff_unif`). -/
theorem app_diff_unif_Icc {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {gn : ℕ → Fam} {L : ℝ} {T : ℝ}
    (hcl : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T →
      Work.FTS.ClassC.ClassC α (slice (gn n) τ))
    (hlip : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T → ∀ τ' ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkNorm α 4 (slice (gn n) τ - slice (gn n) τ') ≤ L * |τ - τ'|) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T →
      ∀ τ' ∈ Set.Icc (0 : ℝ) T, ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      |slice (gn n) τ z θ - slice (gn n) τ' z θ| ≤ K * |τ - τ'| := by
  refine ⟨10 / Real.sqrt (Work.Spaces.gam α - 1) * max L 0,
    mul_nonneg (div_nonneg (by norm_num) (Real.sqrt_nonneg _)) (le_max_right L 0), ?_⟩
  intro n τ hτ τ' hτ' z θ hQd
  have hsub := Work.FTS.StrongEps.EComparison.classC_sub (hcl n τ hτ) (hcl n τ' hτ')
  have h1 := Work.FTS.StrongEps.SupPort.classC_mixed_sup_le hα hα1 hsub 0 0 (by norm_num) hQd
  have h2 : Work.FTS.Nonlin.Xn α (fun z θ => slice (gn n) τ z θ - slice (gn n) τ' z θ)
      ≤ max L 0 * |τ - τ'| :=
    le_trans (hlip n τ hτ τ' hτ') (mul_le_mul_of_nonneg_right (le_max_left L 0) (abs_nonneg _))
  have h3 : (0 : ℝ) ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) :=
    div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  calc |slice (gn n) τ z θ - slice (gn n) τ' z θ|
      = |Work.Spaces.mixed 0 0 (fun z θ => slice (gn n) τ z θ - slice (gn n) τ' z θ) z θ| := rfl
    _ ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1)
          * Work.FTS.Nonlin.Xn α
            (fun z θ => slice (gn n) τ z θ - slice (gn n) τ' z θ) := h1
    _ ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) * (max L 0 * |τ - τ'|) :=
        mul_le_mul_of_nonneg_left h2 h3
    _ = 10 / Real.sqrt (Work.Spaces.gam α - 1) * max L 0 * |τ - τ'| := by ring

/-- **Weighted `τ`-modulus** on a horizon (the restricted `Standing.app_diff_le`). -/
theorem app_diff_le_Icc {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {gn : ℕ → Fam} {L : ℝ} {T : ℝ}
    (hcl : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T →
      Work.FTS.ClassC.ClassC α (slice (gn n) τ))
    (hlip : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T → ∀ τ' ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkNorm α 4 (slice (gn n) τ - slice (gn n) τ') ≤ L * |τ - τ'|) :
    ∃ CwD : ℝ, 0 ≤ CwD ∧ ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T →
      ∀ τ' ∈ Set.Icc (0 : ℝ) T, ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ,
      0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k (fun z θ => slice (gn n) τ z θ - slice (gn n) τ' z θ) z θ|
        ≤ (CwD * |τ - τ'|) * SW z := by
  obtain ⟨C, hC0, hC⟩ := Work.FTS_RegExport.RXA1w.abs_mixed_le_HkNorm_C4_w_proved hα hα1
  refine ⟨C * max L 0, mul_nonneg hC0 (le_max_right L 0), ?_⟩
  intro n τ hτ τ' hτ' k hk z θ hz hθ0 hθ1
  obtain ⟨hsm, hm, hb⟩ := Work.FTS_RegExport.RXR1.classC_sub_hyp (hcl n τ hτ) (hcl n τ' hτ')
  have h1 := hC _ (hsm.forall 4) hm hb k 0 (by omega) z θ hz hθ0 hθ1
  have hHk : Work.Spaces.HkNorm α 4 (slice (gn n) τ - slice (gn n) τ')
      ≤ max L 0 * |τ - τ'| :=
    le_trans (hlip n τ hτ τ' hτ') (mul_le_mul_of_nonneg_right (le_max_left L 0) (abs_nonneg _))
  show |Work.Spaces.mixed k 0 (fun z θ => slice (gn n) τ z θ - slice (gn n) τ' z θ) z θ|
      ≤ (C * max L 0 * |τ - τ'|) * SW z
  calc |Work.Spaces.mixed k 0 (fun z θ => slice (gn n) τ z θ - slice (gn n) τ' z θ) z θ|
      ≤ C * SW z * Work.Spaces.HkNorm α 4 (slice (gn n) τ - slice (gn n) τ') := h1
    _ ≤ C * SW z * (max L 0 * |τ - τ'|) :=
        mul_le_mul_of_nonneg_left hHk (mul_nonneg hC0 (SW_nonneg hz.le))
    _ = (C * max L 0 * |τ - τ'|) * SW z := by ring

end Work.FTS_RegExport.RXT.Sys.L12FKaux
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.L12Deriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `L12FKaux.L12Deriv` — the `z`-derivative and the bounds of `L₁₂` along the approximants

The approximating families of `LimApprox` are class-`C` with uniformly bounded `ℋ⁴`-norm and
`ℋ⁴`-Lipschitz in the fake time.  This module turns those data into

* the derivative of `L₁₂ (F_* + slice (gn n) τ)` (via `FM.hasDerivAt_L12`, using the
  additivity `dens_add` of the density and the derivative formula `L12dens_hasDerivAt`);
* the `z`-derivative of `L₁₂` of the limit profile (passing to the limit with
  `RXR1.hasDerivAt_of_tendsto_deriv`);
* the uniform bounds and the fake-time Lipschitz bounds of `L₁₂` and of `FK`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Sys.L12FKaux

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- `L₁₂dens (F_* + u) = 2β/(1+s)² + L₁₂dens u` for `s > 0` (with the standing data of `u`). -/
theorem L12dens_Ftau_eq {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {u : ℝ → ℝ → ℝ} {C0 : ℝ}
    (hC0 : 0 ≤ C0)
    (h4 : ContDiffOn ℝ 4 (Function.uncurry u) Work.FTS.EllipticEst.Q0)
    (hbd : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k u z θ| ≤ C0 * SW z)
    {s : ℝ} (hs : 0 < s) :
    Work.FM.L12dens Work.Spaces.K (fun z θ => Work.Construction.Fstar β z θ + u z θ) s
      = 2 * β / (1 + s) ^ 2 + Work.FM.L12dens Work.Spaces.K u s := by
  have h := dens_add (β := β) hβ hβ1 hC0 h4 hbd (u := u) hs
  simpa only [Work.Construction.L12dens] using h

/-- The reference density `2β/(1+s)²` is integrable on a tail. -/
theorem integrable_Fstar_dens {β : ℝ} (hβ : 0 < β) {a : ℝ} (ha : 0 < a) :
    Integrable (fun s : ℝ => 2 * β / (1 + s) ^ 2) (volume.restrict (Set.Ioi a)) := by
  have hp : Integrable (fun s : ℝ => s ^ (-(2 : ℝ))) (volume.restrict (Set.Ioi a)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num : (-(2 : ℝ)) < -1) ha
  refine Integrable.mono' (hp.const_mul (2 * β)) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (s := Set.Ioi a) ?_ measurableSet_Ioi
    exact continuousOn_const.div ((continuousOn_const.add continuousOn_id).pow 2)
      (fun s hs => pow_ne_zero 2 (ne_of_gt (by linarith [ha.trans hs] : (0 : ℝ) < 1 + s)))
  · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
    have hs0 : 0 < s := ha.trans hs
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * β / (1 + s) ^ 2)]
    have h1 : 1 / (1 + s) ^ 2 ≤ 1 / s ^ 2 :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith [hs0])
    calc 2 * β / (1 + s) ^ 2 = 2 * β * (1 / (1 + s) ^ 2) := by ring
      _ ≤ 2 * β * (1 / s ^ 2) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2 * β * s ^ (-(2 : ℝ)) := by
          rw [Real.rpow_neg (le_of_lt hs0), Real.rpow_two, one_div]


/-! ## §2 The `z`-derivatives of `FK (F(τ))` and of `L₁₂ (F(τ))` -/

/-- **The `z`-jets of `FK` of the limit profile are the moments `Qlim · j`.** -/
theorem FK_DzIter_eq {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {gn : ℕ → Fam} {g : Fam} {τ : ℝ} (hτ : 0 ≤ τ) {Cw CB : ℝ}
    (hCw : 0 ≤ Cw) (hCB : 0 ≤ CB)
    (h4 : ∀ n : ℕ, ContDiffOn ℝ 4 (Function.uncurry (slice (gn n) τ))
      Work.FTS.EllipticEst.Q0)
    (hbd : ∀ (n : ℕ) (k : ℕ), k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k (slice (gn n) τ) z θ| ≤ Cw * SW z)
    (h2 : ∀ n : ℕ, ContDiffOn ℝ 4 (Function.uncurry
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ))
      Work.FTS.EllipticEst.Q0)
    (hsl : ∀ (n : ℕ) (k : ℕ), k ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (gn n) τ) z θ| ≤ CB)
    (hjet : ∀ (k : ℕ), k ≤ 2 → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n => Work.Spaces.DzIter k (slice (gn n) τ) z θ) Filter.atTop
        (𝓝 (Work.Spaces.DzIter k (slice g τ) z θ)))
    {z : ℝ} (hz : 0 < z) {j : ℕ} (hj : j ≤ 2) :
    Work.Spaces.DzIter j (fun z _ => Work.Construction.FK (Work.Construction.Ftau
      (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) z) z 0
      = Qlim α g τ j z := by
  have hFK : ∀ x : ℝ, 0 < x → Work.Construction.FK (Work.Construction.Ftau
      (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) x
      = Qlim α g τ 0 x := fun x hx => Qlim_eq_FK hα hτ hx
  have hd1 : ∀ x : ℝ, 0 < x → HasDerivAt (Qlim α g τ 0) (Qlim α g τ 1 x / x) x :=
    fun x hx => Qlim_hasDerivAt_1 (α := α) hα hα13 hCw hCB h4 hbd h2 hsl hjet hx
  have hd2 : ∀ x : ℝ, 0 < x → HasDerivAt (Qlim α g τ 1) (Qlim α g τ 2 x / x) x :=
    fun x hx => Qlim_hasDerivAt_2 (α := α) hα hα13 hCw hCB h4 hbd h2 hsl hjet hx
  have hstep1 : ∀ x : ℝ, 0 < x →
      Work.Spaces.DzIter 1 (fun z _ => Work.Construction.FK (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) z) x 0
      = Qlim α g τ 1 x := by
    intro x hx
    have hd : HasDerivAt (fun y => Work.Construction.FK (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) y)
        (Qlim α g τ 1 x / x) x :=
      (hd1 x hx).congr_of_eventuallyEq
        (by filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy; exact (hFK y hy))
    show x * deriv (fun y => Work.Construction.FK (Work.Construction.Ftau
      (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) y) x
      = Qlim α g τ 1 x
    rw [hd.deriv]
    field_simp
  have hstep2 : Work.Spaces.DzIter 2 (fun z _ => Work.Construction.FK (Work.Construction.Ftau
      (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) z) z 0
      = Qlim α g τ 2 z := by
    have hcongr : (fun y => Work.Spaces.DzIter 1 (fun z _ => Work.Construction.FK
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ) z) y 0) =ᶠ[𝓝 z] Qlim α g τ 1 := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
      exact hstep1 y hy
    have hd : HasDerivAt (fun y => Work.Spaces.DzIter 1 (fun z _ => Work.Construction.FK
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ) z) y 0) (Qlim α g τ 2 z / z) z :=
      (hd2 z hz).congr_of_eventuallyEq hcongr
    show z * deriv (fun y => Work.Spaces.DzIter 1 (fun z _ => Work.Construction.FK
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) τ) z) y 0) z = Qlim α g τ 2 z
    rw [hd.deriv]
    field_simp
  interval_cases j
  · show Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
      (Work.FTS.RegExportIface.RXT.GR α g) τ) z = Qlim α g τ 0 z
    exact hFK z hz
  · exact hstep1 z hz
  · exact hstep2


/-! ## §3 The derivative of `L₁₂` of the limit profile -/

/-- The `Ftau`-unfolding used throughout. -/
theorem Ftau_unfold (α : ℝ) (g : Fam) (τ : ℝ) :
    Work.Construction.Ftau α g τ
      = fun z θ => Work.Construction.Fstar α z θ + g z θ τ := rfl

/-- The derivative of the reference density `2β/(1+s)²`. -/
theorem hasDerivAt_Fstar_dens {β x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun s : ℝ => 2 * β / (1 + s) ^ 2) (-(4 * β / (1 + x) ^ 3)) x := by
  have h1 : HasDerivAt (fun s : ℝ => (1 + s) ^ 2) (2 * (1 + x)) x := by
    have h0 : HasDerivAt (fun s : ℝ => 1 + s) (1 : ℝ) x := by
      simpa only [id_eq, add_comm] using (hasDerivAt_id x).const_add 1
    have hp := h0.pow 2
    convert hp using 1
    ring
  have h2 : HasDerivAt (fun s : ℝ => 2 * β / (1 + s) ^ 2)
      ((0 * (1 + x) ^ 2 - 2 * β * (2 * (1 + x))) / ((1 + x) ^ 2) ^ 2) x :=
    (hasDerivAt_const x (2 * β)).div h1 (by positivity)
  convert h2 using 1
  field_simp
  ring

/-- **`L₁₂ (F(τ))` is differentiable with derivative `-L₁₂dens (F(τ))`**, by passing to the
limit in the corresponding statement for the approximants. -/
theorem L12_hasDerivAt {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {gn : ℕ → Fam} {g : Fam} {τ : ℝ} {Cw : ℝ} (hCw : 0 ≤ Cw)
    (h4 : ∀ n : ℕ, ContDiffOn ℝ 4 (Function.uncurry (slice (gn n) τ))
      Work.FTS.EllipticEst.Q0)
    (hbd : ∀ (n : ℕ) (k : ℕ), k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k (slice (gn n) τ) z θ| ≤ Cw * SW z)
    (hconv : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n => slice (gn n) τ z θ) Filter.atTop
        (𝓝 (slice (Work.FTS.RegExportIface.RXT.GR α g) τ z θ)))
    {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun x => Work.Construction.L12 (Work.Construction.Ftau
      (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) x)
      (-(Work.Construction.L12dens (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) z)) z := by
  have hβ : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hβ1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  have hsplit : ∀ (n : ℕ) {s : ℝ}, 0 < s →
      Work.FM.L12dens Work.Spaces.K (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (gn n) τ) s
      = 2 * Work.FTS.Regularity.pExp α / (1 + s) ^ 2
        + Work.FM.L12dens Work.Spaces.K (slice (gn n) τ) s := by
    intro n s hs
    have h := dens_add (β := Work.FTS.Regularity.pExp α) hβ hβ1 hCw (h4 n) (hbd n)
      (u := slice (gn n) τ) hs
    rw [Ftau_unfold]
    exact h
  have hder : ∀ n : ℕ, ∀ x ∈ Set.Ioo (z / 2) (2 * z),
      HasDerivAt (fun y => Work.Construction.L12 (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (gn n) τ) y)
        (-(Work.Construction.L12dens (Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α) (gn n) τ) x)) x := by
    intro n x hx
    have hx0 : 0 < x := by linarith [hx.1, hz]
    have hxa : 0 < x / 2 := by linarith
    have hcontF : ContinuousAt (fun s : ℝ => 2 * Work.FTS.Regularity.pExp α / (1 + s) ^ 2) x :=
      (hasDerivAt_Fstar_dens hx0).continuousAt
    have hcontU : ContinuousAt (fun s : ℝ => Work.FM.L12dens Work.Spaces.K (slice (gn n) τ) s) x :=
      (Work.FTS_RegExport.RXT.L12Iter.L12dens_continuousOn hCw (h4 n) (hbd n)).continuousAt
        (isOpen_Ioi.mem_nhds hx0)
    have hcontD : ContinuousAt (fun s : ℝ => Work.FM.L12dens Work.Spaces.K
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) s) x :=
      (hcontF.add hcontU).congr (by
        filter_upwards [isOpen_Ioi.mem_nhds hx0] with s hs
        exact (hsplit n hs).symm)
    have hIntF : Integrable (fun s : ℝ => 2 * Work.FTS.Regularity.pExp α / (1 + s) ^ 2)
        (volume.restrict (Set.Ioi (x / 2))) := integrable_Fstar_dens hβ hxa
    have hIntU : Integrable (fun s : ℝ => Work.FM.L12dens Work.Spaces.K (slice (gn n) τ) s)
        (volume.restrict (Set.Ioi (x / 2))) :=
      Work.FTS_RegExport.RXT.L12Iter.L12dens_integrableOn hCw (h4 n) (hbd n) hxa
    have hIntD : Integrable (fun s : ℝ => Work.FM.L12dens Work.Spaces.K
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) s)
        (volume.restrict (Set.Ioi (x / 2))) :=
      (hIntF.add hIntU).congr (by
        filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
        exact (hsplit n (lt_trans hxa (by simpa using hs))).symm)
    exact Work.FM.hasDerivAt_L12 hIntD hcontD (by linarith)
  have hvdiff : ∀ n : ℕ, DifferentiableOn ℝ (fun x => -(Work.FM.L12dens Work.Spaces.K
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) x))
      (Set.Ioo (z / 2) (2 * z)) := by
    intro n
    refine DifferentiableOn.neg ?_
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1, hz]
    have hd1 : HasDerivAt (fun s : ℝ => Work.FM.L12dens Work.Spaces.K (slice (gn n) τ) s)
        ((Work.Elliptic.Qang (slice (gn n) τ) 1 x - Work.Elliptic.Qang (slice (gn n) τ) 0 x)
          / x ^ 2) x := L12dens_hasDerivAt hCw (h4 n) (hbd n) hx0
    have hsum := (hasDerivAt_Fstar_dens (β := Work.FTS.Regularity.pExp α) hx0).add hd1
    refine (hsum.congr_of_eventuallyEq ?_).differentiableAt.differentiableWithinAt
    filter_upwards [isOpen_Ioi.mem_nhds hx0] with s hs
    show Work.FM.L12dens Work.Spaces.K (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
      (gn n) τ) s
      = 2 * Work.FTS.Regularity.pExp α / (1 + s) ^ 2
        + Work.FM.L12dens Work.Spaces.K (slice (gn n) τ) s
    exact hsplit n hs
  have hMabs : ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, ∀ x ∈ Set.Ioo (z / 2) (2 * z),
      |Work.FM.L12dens Work.Spaces.K (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (gn n) τ) x| ≤ M := by
    refine ⟨2 * Work.FTS.Regularity.pExp α + 3 * (Real.pi / 2) * Cw, by positivity, ?_⟩
    intro n x hx
    have hx0 : 0 < x := by linarith [hx.1, hz]
    rw [hsplit n hx0]
    have h1 : |2 * Work.FTS.Regularity.pExp α / (1 + x) ^ 2| ≤ 2 * Work.FTS.Regularity.pExp α := by
      rw [abs_of_nonneg (by positivity)]
      rw [div_le_iff₀ (by positivity : (0:ℝ) < (1 + x) ^ 2)]
      have h5 : (1 : ℝ) ≤ (1 + x) ^ 2 := by nlinarith
      nlinarith [h5, hβ]
    have h2 : |Work.FM.L12dens Work.Spaces.K (slice (gn n) τ) x| ≤ 3 * (Real.pi / 2) * Cw := by
      have h := Work.FTS_RegExport.RXT.L12Iter.abs_L12dens_le hCw (h4 n) (hbd n) hx0
      have h3 : x ^ ((1 : ℝ) / 2) / (1 + x) ^ 2 ≤ 1 := by
        rw [div_le_iff₀ (by positivity : (0:ℝ) < (1 + x) ^ 2)]
        by_cases hx1 : 1 ≤ x
        · have h4 : x ^ ((1 : ℝ) / 2) ≤ x ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
          have h5 : x ^ (1 : ℝ) = x := Real.rpow_one x
          have h6 : x ≤ 1 * (1 + x) ^ 2 := by nlinarith
          calc x ^ ((1 : ℝ) / 2) ≤ x ^ (1 : ℝ) := h4
            _ = x := h5
            _ ≤ 1 * (1 + x) ^ 2 := h6
        · have h4 : x ^ ((1 : ℝ) / 2) ≤ 1 :=
            Real.rpow_le_one hx0.le (not_le.mp hx1).le (by norm_num)
          have h6 : (1:ℝ) ≤ (1 + x) ^ 2 := by nlinarith
          linarith
      have h4' : (0:ℝ) ≤ 3 * (Real.pi / 2) * Cw := by positivity
      calc |Work.FM.L12dens Work.Spaces.K (slice (gn n) τ) x|
          ≤ 3 * (Real.pi / 2) * Cw * (x ^ ((1 : ℝ) / 2) / (1 + x) ^ 2) := h
        _ ≤ 3 * (Real.pi / 2) * Cw * 1 := mul_le_mul_of_nonneg_left h3 h4'
        _ = 3 * (Real.pi / 2) * Cw := by ring
    calc |2 * Work.FTS.Regularity.pExp α / (1 + x) ^ 2
          + Work.FM.L12dens Work.Spaces.K (slice (gn n) τ) x|
        ≤ |2 * Work.FTS.Regularity.pExp α / (1 + x) ^ 2|
          + |Work.FM.L12dens Work.Spaces.K (slice (gn n) τ) x| := abs_add_le _ _
      _ ≤ 2 * Work.FTS.Regularity.pExp α + 3 * (Real.pi / 2) * Cw := add_le_add h1 h2
  have hM : ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, ∀ x ∈ Set.Ioo (z / 2) (2 * z),
      |-(Work.FM.L12dens Work.Spaces.K (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (gn n) τ) x)| ≤ M := by
    obtain ⟨M, hM0, hMb⟩ := hMabs
    exact ⟨M, hM0, fun n x hx => by rw [abs_neg]; exact hMb n x hx⟩
  have hL : ∃ L : ℝ, 0 ≤ L ∧ ∀ n : ℕ, ∀ x ∈ Set.Ioo (z / 2) (2 * z),
      |deriv (fun y => -(Work.FM.L12dens Work.Spaces.K (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (gn n) τ) y)) x| ≤ L := by
    refine ⟨4 * Work.FTS.Regularity.pExp α / (1 + z / 2) ^ 3
      + 6 * (Real.pi / 2) * Cw / (z / 2) ^ 2, by positivity, ?_⟩
    intro n x hx
    have hx0 : 0 < x := by linarith [hx.1, hz]
    have hd1 : HasDerivAt (fun s : ℝ => Work.FM.L12dens Work.Spaces.K (slice (gn n) τ) s)
        ((Work.Elliptic.Qang (slice (gn n) τ) 1 x - Work.Elliptic.Qang (slice (gn n) τ) 0 x)
          / x ^ 2) x := L12dens_hasDerivAt hCw (h4 n) (hbd n) hx0
    have hdF := hasDerivAt_Fstar_dens (β := Work.FTS.Regularity.pExp α) hx0
    have hsum : HasDerivAt (fun s : ℝ => 2 * Work.FTS.Regularity.pExp α / (1 + s) ^ 2
        + Work.FM.L12dens Work.Spaces.K (slice (gn n) τ) s)
        (-(4 * Work.FTS.Regularity.pExp α / (1 + x) ^ 3)
          + (Work.Elliptic.Qang (slice (gn n) τ) 1 x - Work.Elliptic.Qang (slice (gn n) τ) 0 x)
            / x ^ 2) x := hdF.add hd1
    have hsum' : HasDerivAt (fun y => Work.FM.L12dens Work.Spaces.K (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (gn n) τ) y)
        (-(4 * Work.FTS.Regularity.pExp α / (1 + x) ^ 3)
          + (Work.Elliptic.Qang (slice (gn n) τ) 1 x - Work.Elliptic.Qang (slice (gn n) τ) 0 x)
            / x ^ 2) x :=
      hsum.congr_of_eventuallyEq (by
        filter_upwards [isOpen_Ioi.mem_nhds hx0] with s hs
        show Work.FM.L12dens Work.Spaces.K (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (gn n) τ) s
          = 2 * Work.FTS.Regularity.pExp α / (1 + s) ^ 2
            + Work.FM.L12dens Work.Spaces.K (slice (gn n) τ) s
        exact hsplit n hs)
    have hval : deriv (fun y => -(Work.FM.L12dens Work.Spaces.K (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (gn n) τ) y)) x
        = -(-(4 * Work.FTS.Regularity.pExp α / (1 + x) ^ 3)
          + (Work.Elliptic.Qang (slice (gn n) τ) 1 x - Work.Elliptic.Qang (slice (gn n) τ) 0 x)
            / x ^ 2) := hsum'.neg.deriv
    rw [hval, abs_neg]
    have hQ1 : |Work.Elliptic.Qang (slice (gn n) τ) 1 x| ≤ 3 * (Real.pi / 2) * Cw := by
      have h := Qang_le hCw (h4 n) (hbd n) (k := 1) (by norm_num) hx0
      have h3 : SW x ≤ 1 := SW_le_one hx0
      have h5 : Cw * SW x ≤ Cw * 1 := mul_le_mul_of_nonneg_left h3 hCw
      have h6 : 3 * (Real.pi / 2) * (Cw * SW x) ≤ 3 * (Real.pi / 2) * Cw := by
        have := mul_le_mul_of_nonneg_left h5 (by positivity : (0:ℝ) ≤ 3 * (Real.pi / 2))
        simpa using this
      linarith [h, h6]
    have hQ0 : |Work.Elliptic.Qang (slice (gn n) τ) 0 x| ≤ 3 * (Real.pi / 2) * Cw := by
      have h := Qang_le hCw (h4 n) (hbd n) (k := 0) (by norm_num) hx0
      have h3 : SW x ≤ 1 := SW_le_one hx0
      have h5 : Cw * SW x ≤ Cw * 1 := mul_le_mul_of_nonneg_left h3 hCw
      have h6 : 3 * (Real.pi / 2) * (Cw * SW x) ≤ 3 * (Real.pi / 2) * Cw := by
        have := mul_le_mul_of_nonneg_left h5 (by positivity : (0:ℝ) ≤ 3 * (Real.pi / 2))
        simpa using this
      linarith [h, h6]
    have hnum : |(Work.Elliptic.Qang (slice (gn n) τ) 1 x
        - Work.Elliptic.Qang (slice (gn n) τ) 0 x) / x ^ 2|
        ≤ 6 * (Real.pi / 2) * Cw / (z / 2) ^ 2 := by
      rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < x ^ 2)]
      have h2 : |Work.Elliptic.Qang (slice (gn n) τ) 1 x - Work.Elliptic.Qang (slice (gn n) τ) 0 x|
          ≤ 6 * (Real.pi / 2) * Cw := by
        calc |Work.Elliptic.Qang (slice (gn n) τ) 1 x - Work.Elliptic.Qang (slice (gn n) τ) 0 x|
            = |Work.Elliptic.Qang (slice (gn n) τ) 1 x + -Work.Elliptic.Qang (slice (gn n) τ) 0 x| := by
              ring_nf
          _ ≤ |Work.Elliptic.Qang (slice (gn n) τ) 1 x| + |-Work.Elliptic.Qang (slice (gn n) τ) 0 x| :=
              abs_add_le _ _
          _ = |Work.Elliptic.Qang (slice (gn n) τ) 1 x| + |Work.Elliptic.Qang (slice (gn n) τ) 0 x| := by
              rw [abs_neg]
          _ ≤ 6 * (Real.pi / 2) * Cw := by linarith
      have hxd : (z / 2) ^ 2 ≤ x ^ 2 := by
        have h1 : z / 2 ≤ x := hx.1.le
        have h2y : 0 ≤ z / 2 := by linarith [hz]
        nlinarith
      exact div_le_div₀ (by positivity) h2 (by positivity) hxd
    have hFs4 : |4 * Work.FTS.Regularity.pExp α / (1 + x) ^ 3| ≤ 4 * Work.FTS.Regularity.pExp α / (1 + z / 2) ^ 3 := by
      rw [abs_of_nonneg (by positivity)]
      refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
      have h1 : (1 + z / 2) ≤ (1 + x) := by linarith [hx.1]
      exact pow_le_pow_left₀ (by positivity) h1 3
    have hFs4b : 0 ≤ 4 * Work.FTS.Regularity.pExp α := by positivity
    have hFs4c : (0 : ℝ) < (1 + z / 2) ^ 3 := by positivity
    have hFs4d : (1 + z / 2) ^ 3 ≤ (1 + x) ^ 3 := by
      have h1 : (1 + z / 2) ≤ (1 + x) := by linarith [hx.1]
      exact pow_le_pow_left₀ (by positivity) h1 3
    calc |-(4 * Work.FTS.Regularity.pExp α / (1 + x) ^ 3)
          + (Work.Elliptic.Qang (slice (gn n) τ) 1 x - Work.Elliptic.Qang (slice (gn n) τ) 0 x)
            / x ^ 2|
        = |-(4 * Work.FTS.Regularity.pExp α / (1 + x) ^ 3)
            + ((Work.Elliptic.Qang (slice (gn n) τ) 1 x
              - Work.Elliptic.Qang (slice (gn n) τ) 0 x) / x ^ 2)| := rfl
      _ ≤ |4 * Work.FTS.Regularity.pExp α / (1 + x) ^ 3|
          + |(Work.Elliptic.Qang (slice (gn n) τ) 1 x
            - Work.Elliptic.Qang (slice (gn n) τ) 0 x) / x ^ 2| := by
          have h := abs_add_le (-(4 * Work.FTS.Regularity.pExp α / (1 + x) ^ 3))
            ((Work.Elliptic.Qang (slice (gn n) τ) 1 x
              - Work.Elliptic.Qang (slice (gn n) τ) 0 x) / x ^ 2)
          rwa [abs_neg] at h
      _ ≤ 4 * Work.FTS.Regularity.pExp α / (1 + z / 2) ^ 3
          + 6 * (Real.pi / 2) * Cw / (z / 2) ^ 2 := add_le_add hFs4 hnum
  have hu : ∀ x ∈ Set.Ioo (z / 2) (2 * z),
      Filter.Tendsto (fun n => Work.Construction.L12 (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (gn n) τ) x) Filter.atTop
        (𝓝 (Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ) x)) := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1, hz]
    have h := L12_tendsto (β := Work.FTS.Regularity.pExp α)
      hβ hβ1 hCw h4 hbd (h := Work.FTS.RegExportIface.RXT.GR α g) hconv hx0
    simpa only [Work.Construction.Ftau, Work.FTS.Galerkin.slice] using h
  have hv : ∀ x ∈ Set.Ioo (z / 2) (2 * z),
      Filter.Tendsto (fun n => -(Work.Construction.L12dens (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (gn n) τ) x)) Filter.atTop
        (𝓝 (-(Work.Construction.L12dens (Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) x))) := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1, hz]
    have h := dens_tendsto (β := Work.FTS.Regularity.pExp α) hβ hβ1 hCw h4 hbd
      (h := Work.FTS.RegExportIface.RXT.GR α g) hconv hx0
    exact h.neg
  exact Work.FTS_RegExport.RXR1.hasDerivAt_of_tendsto_deriv (a := z / 2) (b := 2 * z)
    (by linarith) hder hvdiff hM hL hu hv z ⟨by linarith, by linarith⟩

end Work.FTS_RegExport.RXT.Sys.L12FKaux
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.L12_limit_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Sys.L12FKaux

/-- **Uniform bound of `L₁₂` on a fake-time horizon.**

`L₁₂` is a *limit* (`L12_tendsto`) of the `L₁₂` of the approximating profiles
`F(n) = F_* + slice (gn n) τ`, and each approximant obeys the elementary bound
`abs_L12_Fstar_add_le` with the constant `Cw = Cd · (C₀ · (pExp α)²)`, where `Cd` is the constant
of the interior weighted `L^∞`–`ℋ⁴` trade-off `RXA1w.abs_mixed_le_HkNorm_C4_w_proved`: the
reference part of the profile contributes `2·pExp α`, the perturbation part `3(π/2)·Cw·3`.
Neither constant depends on `τ` (only the class-`C` membership and the `ℋ⁴`-smallness
`Xn (slice (gn n) τ) ≤ C₀·(pExp α)²`, both uniform on `[0,T]`, are used), so the bound transfers
to the limit along `n → ∞`.  (This is the third clause of `L12FK_family_jets`, isolated.)

The same argument is used elsewhere in the workspace (`L12FK_family_jets`), where the third clause
of the conclusion is exactly this estimate. -/
theorem L12_limit_bound {α C₀ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hA : Work.FTS.FinalV2.LimApprox (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ z : ℝ, 0 < z →
      |Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) τ) z| ≤ C := by
  obtain ⟨gn, B, L, hC, hLip, hjet, hmu⟩ := hA T hT
  have hβ : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hβ1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  obtain ⟨Cd, hCd0, hCd⟩ := Work.FTS_RegExport.RXA1w.abs_mixed_le_HkNorm_C4_w_proved hβ hβ1
  have hmem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
  have hC0β : 0 ≤ C₀ * (Work.FTS.Regularity.pExp α) ^ 2 :=
    le_trans (Work.Spaces.HkNorm_nonneg (Work.FTS.Regularity.pExp α) 4
        (Work.FTS.Galerkin.slice (gn 0) 0)) (hC 0 0 hmem0).2.1
  refine ⟨2 * Work.FTS.Regularity.pExp α
      + 3 * (Real.pi / 2) * (Cd * (C₀ * (Work.FTS.Regularity.pExp α) ^ 2)) * 3, ?_, ?_⟩
  · have h1 : 0 ≤ Cd * (C₀ * (Work.FTS.Regularity.pExp α) ^ 2) := mul_nonneg hCd0 hC0β
    nlinarith [hβ, h1, Real.pi_pos]
  · intro τ hτ z hz
    -- the standing slot bound of the approximants, uniform in `n`
    have hbd : ∀ (n : ℕ) (k : ℕ), k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.DzIter k (Work.FTS.Galerkin.slice (gn n) τ) z θ|
          ≤ (Cd * (C₀ * (Work.FTS.Regularity.pExp α) ^ 2))
            * Work.FTS_RegExport.RXT.Sys.L12FKaux.SW z := by
      intro n k hk z θ hz' h0 h1
      have hcl := (hC n τ hτ).1
      have h1' := hCd _ (hcl.reg.forall 4) (Work.FTS.ClassC.classC_hkMem_four hcl)
        (Work.FTS.ClassC.bdryTraces_mono (by norm_num) hcl.tr) k 0 (by omega) z θ hz' h0 h1
      rw [Work.Spaces.mixed_zero_right] at h1'
      have h2 : Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4
          (Work.FTS.Galerkin.slice (gn n) τ)
          ≤ C₀ * (Work.FTS.Regularity.pExp α) ^ 2 := (hC n τ hτ).2.1
      calc |Work.Spaces.DzIter k (Work.FTS.Galerkin.slice (gn n) τ) z θ|
          ≤ Cd * Work.FTS_RegExport.RXT.Sys.L12FKaux.SW z
              * Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4
                (Work.FTS.Galerkin.slice (gn n) τ) := h1'
        _ ≤ Cd * Work.FTS_RegExport.RXT.Sys.L12FKaux.SW z
              * (C₀ * (Work.FTS.Regularity.pExp α) ^ 2) :=
            mul_le_mul_of_nonneg_left h2
              (mul_nonneg hCd0 (Work.FTS_RegExport.RXT.Sys.L12FKaux.SW_nonneg hz'.le))
        _ = (Cd * (C₀ * (Work.FTS.Regularity.pExp α) ^ 2))
              * Work.FTS_RegExport.RXT.Sys.L12FKaux.SW z := by ring
    -- pointwise convergence of the slices to those of the limit family `GR α g`
    have hconv : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
        Filter.Tendsto (fun n => Work.FTS.Galerkin.slice (gn n) τ z θ) Filter.atTop
          (nhds (Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) τ z θ)) := by
      intro z θ hzθ
      have h := hjet τ hτ 0 0 (by norm_num) z θ hzθ
      have hGR := Work.FTS_RegExport.RXT.ftau_GR_of_quad (α := α) (g := g) hτ.1 hzθ.1
        hzθ.2.1.le hzθ.2.2.le
      simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_zero,
        Work.FTS.Galerkin.slice_apply, hGR] using h
    -- pass to the limit in `L₁₂`
    have htend := Work.FTS_RegExport.RXT.Sys.L12FKaux.L12_tendsto
      (β := Work.FTS.Regularity.pExp α) hβ hβ1 (mul_nonneg hCd0 hC0β)
      (fun n => (hC n τ hτ).1.reg.forall 4) hbd hconv hz
    refine le_of_tendsto htend.abs (Filter.Eventually.of_forall fun n => ?_)
    exact Work.FTS_RegExport.RXT.Sys.L12FKaux.abs_L12_Fstar_add_le
      (β := Work.FTS.Regularity.pExp α) hβ hβ1 (mul_nonneg hCd0 hC0β)
      ((hC n τ hτ).1.reg.forall 4) (Work.FTS.ClassC.classC_hkMem_four (hC n τ hτ).1)
      (fun k hk => hbd n k hk) hz

end Work.FTS_RegExport.RXT.Sys.L12FKaux

end
end
