import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.GalFields.RHS.HkSum
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.Nonlinear.Open.Row15
import Submission.Work.FTS.Nonlinear.Open.Row18
import Submission.Work.FTS.Nonlinear.Open.Row25Aux
import Submission.Work.FTS.Nonlinear.Pieces.RNP.RNP24.dzdIter_FK_eq_qang
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.Pgs
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.OpenPkg.Pieces4
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongEps.SupPort.classC_sup_le
import Submission.Work.FTS.StrongPersist.H6Rows.NZaux.L12AddFstar
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSlotInt
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsRadAux.aestronglyMeasurable_slotSum
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundR
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.TransportS.T2Sup.GenSlot
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_RegExport.RXA1w.Helpers
import Submission.Work.FTS_RegExport.RXT.Sys.abs_L12dens_Fstar_add_le
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_RegExport.THL.vopPert_theta_holder
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.Spaces.SmoothCompact_HkMem
-- ===== merged: Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnNCoreUnif =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.ClassCRHS

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin Work.Spaces

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

theorem nb_data_unifΦ {α : ℝ} (hαmem : α ∈ Set.Ioc 0 1) {C₀ B Ce Cs C1 C2 : ℝ}
    (hC1 : 0 < C1) (hC2 : 0 < C2)
    (hatoms1 : Work.FTS.VocabO.HQo α 4
        (fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ) ∧
      Xn α (fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ) ≤ C1 ∧
      Work.FTS.VocabO.HQo α 4
        (fun z θ => z / (1 + z) * Dth (Work.Construction.Fstar α) z θ) ∧
      Xn α
        (fun z θ => z / (1 + z) * Dth (Work.Construction.Fstar α) z θ) ≤ C1 ∧
      Work.FTS.VocabO.HQo α 4
        (fun z θ => z / (1 + z) * Dz (Work.Construction.Fstar α) z θ) ∧
      Xn α
        (fun z θ => z / (1 + z) * Dz (Work.Construction.Fstar α) z θ) ≤ C1)
    (hatoms2 : Work.FTS.VocabO.HQo α 4
        (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
          * Dth (Work.Construction.Fstar α) z θ) ∧
      Xn α
        (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
          * Dth (Work.Construction.Fstar α) z θ) ≤ C2 ∧
      Work.FTS.VocabO.HQo α 4
        (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
          * Work.Construction.Fstar α z θ) ∧
      Xn α
        (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
          * Work.Construction.Fstar α z θ) ≤ C2) :
    ∃ Kbig : ℝ, 0 < Kbig ∧ ∀ {Φs : Fn} {w Φg : Fn},
      Work.FTS.ClassC.ClassC α w → Xn α w ≤ C₀ * α ^ 2 →
      Work.Spaces.HkNorm α 6 w ≤ B →
      Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.VocabO2.StarPkgo2 α Cs Φs →
      (∀ k ∈ Finset.range 20, Work.FTS.EllipticEst.SmoothOpen (NBlk α w Φs Φg k)) ∧
      (∀ k ∈ Finset.range 20, HkMem α 4 (NBlk α w Φs Φg k) ∧
        Xn α (NBlk α w Φs Φg k) ≤ Kbig) ∧
      (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
        Work.Construction.N α (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ) z θ
          = ∑ k ∈ Finset.range 20, NBlk α w Φs Φg k z θ) := by
  have hα0 : 0 < α := hαmem.1
  have hα1 : α ≤ 1 := hαmem.2
  obtain ⟨Cprod, hCprod, hprodfield⟩ := Work.FTS.OpenPkg.prod_field
  obtain ⟨Cw, hCw, hwfield⟩ := Work.FTS.OpenPkg.wprod_field_winf
  obtain ⟨Cfk, hCfk, hfkfield⟩ := Work.FTS.OpenPkg.fkH_field
  obtain ⟨Cphi, hCphi, hphifield⟩ := Work.FTS.NonlinRows.NRow10aux.mul_phi_Hk
  obtain ⟨Cang, hCang, hangfield⟩ := Work.FTS.StrongPersist.L3Rhs.ang_mul_HkSq_le 4
  obtain ⟨CFS, hCFS, hFSW⟩ := Work.FTS.Nonlinear.FstarPkg.Fstar_W
  obtain ⟨CDth, hCDth, hDthW⟩ := Work.FTS.Nonlinear.FstarPkg.DthFstar_W
  obtain ⟨CDz, hCDz, hDzW⟩ := Work.FTS.Nonlinear.FstarPkg.DzFstar_W
  obtain ⟨Bsin, hBsin, hSinInt, hSinB, hSinIt⟩ :=
    Work.FTS.Nonlinear.Pieces.RNP.RNP24.angProfile_sinSq
  have hPR : ∀ f g : Fn, Work.FTS.VocabO.HQo α 4 f → Work.FTS.VocabO.HQo α 4 g →
      HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Xn α (fun z θ => f z θ * g z θ)
        ≤ Cprod * α ^ (-(1 / 2 : ℝ)) * Xn α f * Xn α g := hprodfield α hα0 hα1
  have hWR : ∀ f g : Fn, Work.FTS.EllipticEst.SmoothOpen f → WlInfMem α 4 f →
      Work.FTS.VocabO.HQo α 4 g →
      HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Xn α (fun z θ => f z θ * g z θ)
        ≤ Cw * α ^ (-(1 / 2 : ℝ)) * WlInf α 4 f * Xn α g := hwfield α hα0 hα1
  set aR : ℝ := max Ce 0 * max C₀ 0 * α ^ 2 with haRdef
  set aW : ℝ := max C₀ 0 * α ^ 2 with haWdef
  set aB : ℝ := max B 0 with haBdef
  set aRS : ℝ := max Cs 0 * α with haRSdef
  set aCFS : ℝ := CFS * α with haCFSdef
  set aCDth : ℝ := CDth * α ^ 2 with haCDthdef
  set aCDz : ℝ := CDz * α with haCDzdef
  set aFKw : ℝ := Cfk * max C₀ 0 * α ^ 2 with haFKwdef
  set aφw : ℝ := Cphi * aW with haφwdef
  set aφB : ℝ := Cphi * aB with haφBdef
  set aKer : ℝ := 200 * (2 * α) with haKerdef
  set Csin : ℝ := Real.sqrt (Cang * Bsin ^ 2) with hCsidef
  have haRnn : 0 ≤ aR := by rw [haRdef]; positivity
  have haWnn : 0 ≤ aW := by rw [haWdef]; positivity
  have haBnn : 0 ≤ aB := le_max_right _ _
  have haRSnn : 0 ≤ aRS := by rw [haRSdef]; positivity
  have haCFSnn : 0 ≤ aCFS := by rw [haCFSdef]; positivity
  have haCDthnn : 0 ≤ aCDth := by rw [haCDthdef]; positivity
  have haCDznn : 0 ≤ aCDz := by rw [haCDzdef]; positivity
  have haFKwnn : 0 ≤ aFKw := by rw [haFKwdef]; positivity
  have haφwnn : 0 ≤ aφw := by rw [haφwdef]; positivity
  have haφBnn : 0 ≤ aφB := by rw [haφBdef]; positivity
  have haKernn : 0 ≤ aKer := by rw [haKerdef]; positivity
  have hCsinpos : 0 < Csin := by rw [hCsidef]; positivity
  set T : ℕ → ℝ := fun k => match k with
    | 0 => |(2 : ℝ)| * Cprod * α ^ (-(1 / 2 : ℝ)) * aR * aW
    | 1 => |(2 : ℝ)| * Cw * α ^ (-(1 / 2 : ℝ)) * aCFS * aR
    | 2 => |(2 : ℝ)| * Cw * α ^ (-(1 / 2 : ℝ)) * aRS * aφw
    | 3 => |(2 : ℝ)| * Cw * α ^ (-(1 / 2 : ℝ)) * aRS * C1
    | 4 => |(-2 : ℝ)| * Cprod * α ^ (-(1 / 2 : ℝ)) * aR * aB
    | 5 => |(-2 : ℝ)| * Cw * α ^ (-(1 / 2 : ℝ)) * aCDth * aR
    | 6 => |(-2 : ℝ)| * Cw * α ^ (-(1 / 2 : ℝ)) * aRS * aφB
    | 7 => |(-2 : ℝ)| * Cw * α ^ (-(1 / 2 : ℝ)) * aRS * C1
    | 8 => |(-(2 * α))| * Cprod * α ^ (-(1 / 2 : ℝ)) * aR * aB
    | 9 => |(-(2 * α))| * Cw * α ^ (-(1 / 2 : ℝ)) * aCDz * aR
    | 10 => |(-(2 * α))| * Cw * α ^ (-(1 / 2 : ℝ)) * aRS * aφB
    | 11 => |(-(2 * α))| * Cw * α ^ (-(1 / 2 : ℝ)) * aRS * C1
    | 12 => |(-(1 / 2))| * Cprod * α ^ (-(1 / 2 : ℝ)) * aFKw * aB
    | 13 => |(-(1 / 2))| * Cw * α ^ (-(1 / 2 : ℝ)) * aCDth * aFKw
    | 14 => |(1 / 2)| * Cw * α ^ (-(1 / 2 : ℝ)) * aKer * aB
    | 15 => (1 / 2) * C2
    | 16 => Csin * (|(1 : ℝ)| * Cprod * α ^ (-(1 / 2 : ℝ)) * aFKw * aW)
    | 17 => Csin * (|(1 : ℝ)| * Cw * α ^ (-(1 / 2 : ℝ)) * aCFS * aFKw)
    | 18 => Csin * (|(1 : ℝ)| * Cw * α ^ (-(1 / 2 : ℝ)) * aKer * aW)
    | _ => Csin * C2 with hTdef
  set Kbig : ℝ := 1 + ∑ k ∈ Finset.range 20, T k with hKbigdef
  have hTnn : ∀ k ∈ Finset.range 20, 0 ≤ T k := by
    intro k hk
    have hk20 : k < 20 := Finset.mem_range.mp hk
    interval_cases k <;> simp only [hTdef] <;> positivity
  have hKbigpos : 0 < Kbig := by
    rw [hKbigdef]; linarith [Finset.sum_nonneg hTnn]
  have hbE : ∀ k : ℕ, k < 20 → ∀ x : ℝ, x = T k → x ≤ Kbig := by
    intro k hk20 x hx
    rw [hx, hKbigdef]
    linarith [Finset.single_le_sum hTnn (Finset.mem_range.mpr hk20)]
  refine ⟨Kbig, hKbigpos, ?_⟩
  intro Φs w Φg hw hXw hB hell hstar
  have hsw : Work.FTS.VocabO.StarPkgo α Cs Φs := hstar.toStarPkgo
  have hmem4w : HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 4 (by norm_num) hw.mem
  have hmem5w : HkMem α 5 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 5 (by norm_num) hw.mem
  have hmem6w : HkMem α 6 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 6 (by norm_num) hw.mem
  have hqow : Work.FTS.VocabO.HQo α 4 w := ⟨hw.reg, hmem4w⟩
  have hXw2 : Xn α w ≤ max C₀ 0 * α ^ 2 :=
    le_trans hXw (mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (by positivity))
  have hXw3 : Xn α w ≤ aW := by rw [haWdef]; exact hXw2
  have hDthwmem : HkMem α 4 (Dth w) :=
    Work.FTS.IPGen.HkMem_Dth_le (by linarith) hw.reg hmem5w
  have hDzwmem : HkMem α 4 (Dz w) :=
    Work.FTS.IPGen.HkMem_Dz_le hw.reg hmem5w
  have hXDthw : Xn α (Dth w) ≤ aB := by
    rw [haBdef]
    refine le_trans (Work.FTS.GalFields.Xn_Dth_le_Xn5 hα0 hmem5w) ?_
    exact le_trans (Work.FTS.StrongLWP.HkNorm_mono_of_mem (by norm_num) hmem6w)
      (le_trans hB (le_max_left B 0))
  have hXDzw : Xn α (Dz w) ≤ aB := by
    rw [haBdef]
    refine le_trans (Work.FTS.GalFields.Xn_Dz_le_Xn5 hα0 hw.reg hmem5w) ?_
    exact le_trans (Work.FTS.StrongLWP.HkNorm_mono_of_mem (by norm_num) hmem6w)
      (le_trans hB (le_max_left B 0))
  set R : Fn := Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg) with hRdef
  set Uc : Fn := fun z θ =>
    Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α w Φg) z θ / Work.Construction.s2 θ
    with hUcdef
  set Vc : Fn := Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg) with hVcdef
  set Rs : Fn := fun z θ =>
    (z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ with hRsdef
  set Us : Fn := fun z θ => (z + 1) / z *
    (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Work.Construction.s2 θ)
    with hUsdef
  set Vs : Fn := fun z θ =>
    (z + 1) / z * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ with hVsdef
  set Dthw : Fn := Dth w with hDthwdef
  set Dzw : Fn := Dz w with hDzwdef
  set DthFs : Fn := Dth (Work.Construction.Fstar α) with hDthFsdef
  set DzFs : Fn := Dz (Work.Construction.Fstar α) with hDzFsdef
  set FW : Fn := fun z θ => Work.Construction.Fstar α z θ with hFWdef
  set FKw : Fn := fun z _ => Work.Construction.FK w z with hFKwdef
  set FKneg : Fn := fun z _ => (-(2 * α)) * hKer z with hFKnegdef
  set phiw : Fn := fun z θ => z / (1 + z) * w z θ with hphiwdef
  set phiDthw : Fn := fun z θ => z / (1 + z) * Dth w z θ with hphiDthwdef
  set phiDzw : Fn := fun z θ => z / (1 + z) * Dz w z θ with hphiDzwdef
  set phiFs : Fn := fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ with hphiFsdef
  set phiDthFs : Fn := fun z θ => z / (1 + z) * Dth (Work.Construction.Fstar α) z θ
    with hphiDthFsdef
  set phiDzFs : Fn := fun z θ => z / (1 + z) * Dz (Work.Construction.Fstar α) z θ
    with hphiDzFsdef
  set prodFKFS : Fn := fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
    * Dth (Work.Construction.Fstar α) z θ with hprodFKFSdef
  have hFWsm : Work.FTS.EllipticEst.SmoothOpen FW := by
    rw [hFWdef]
    exact Work.FTS.EllipticEst.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  have hDthFssm : Work.FTS.EllipticEst.SmoothOpen DthFs := by
    rw [hDthFsdef]; exact hFWsm.Dth
  have hDzFssm : Work.FTS.EllipticEst.SmoothOpen DzFs := by rw [hDzFsdef]; exact hFWsm.Dz
  have hDthwsm : Work.FTS.EllipticEst.SmoothOpen Dthw := by rw [hDthwdef]; exact hw.reg.Dth
  have hDzwsm : Work.FTS.EllipticEst.SmoothOpen Dzw := by rw [hDzwdef]; exact hw.reg.Dz
  have hRssm : Work.FTS.EllipticEst.SmoothOpen Rs := by
    rw [hRsdef]; exact smoothOpen_Rs_of_star hα0 hα1 hsw
  have hUssm : Work.FTS.EllipticEst.SmoothOpen Us := by
    rw [hUsdef]; exact smoothOpen_Us_of_star hα0 hα1 hsw
  have hVssm : Work.FTS.EllipticEst.SmoothOpen Vs := by
    rw [hVsdef]; exact smoothOpen_Vs_of_star hα0 hα1 hsw
  have hKphi : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z / (1 + z)) := smoothOpen_zdiv
  have hphiwsm : Work.FTS.EllipticEst.SmoothOpen phiw := by
    rw [hphiwdef]; exact smoothOpen_phi_mul hw.reg
  have hphiDthwsm : Work.FTS.EllipticEst.SmoothOpen phiDthw := by
    rw [hphiDthwdef]; exact smoothOpen_phi_mul hDthwsm
  have hphiDzwsm : Work.FTS.EllipticEst.SmoothOpen phiDzw := by
    rw [hphiDzwdef]; exact smoothOpen_phi_mul hDzwsm
  have hphiFssm : Work.FTS.EllipticEst.SmoothOpen phiFs := by
    rw [hphiFsdef]; exact smoothOpen_phi_mul hFWsm
  have hphiDthFssm : Work.FTS.EllipticEst.SmoothOpen phiDthFs := by
    rw [hphiDthFsdef]; exact smoothOpen_phi_mul hDthFssm
  have hphiDzFssm : Work.FTS.EllipticEst.SmoothOpen phiDzFs := by
    rw [hphiDzFsdef]; exact smoothOpen_phi_mul hDzFssm
  have hFKwsm : Work.FTS.EllipticEst.SmoothOpen FKw := by
    rw [hFKwdef]; exact smoothOpen_FKw_of_classC hw
  have hFKnegsm : Work.FTS.EllipticEst.SmoothOpen FKneg := by
    rw [hFKnegdef]; exact smoothOpen_FKneg α
  have hXR : Xn α R ≤ aR := by
    rw [hRdef, haRdef]; exact Xn_Rop_le hw hell hXw
  have hqoR : Work.FTS.VocabO.HQo α 4 R := hell.R.1
  have hXUc : Xn α Uc ≤ aR := by
    rw [hUcdef, haRdef]; exact Xn_UopDiv_le hw hell hXw
  have hqoUc : Work.FTS.VocabO.HQo α 4 Uc := hell.U.1
  have hXVc : Xn α Vc ≤ aR := by
    rw [hVcdef, haRdef]; exact Xn_Vop_le hw hell hXw
  have hqoVc : Work.FTS.VocabO.HQo α 4 Vc := hell.V.1
  have hRsWle : WlInf α 4 Rs ≤ aRS := by
    rw [hRsdef, haRSdef]; exact WlInf_Rs_le hα0 hstar
  have hUsWle : WlInf α 4 Us ≤ aRS := by
    rw [hUsdef, haRSdef]; exact WlInf_Us_le hα0 hstar
  have hVsWle : WlInf α 4 Vs ≤ aRS := by
    rw [hVsdef, haRSdef]; exact WlInf_Vs_le hα0 hstar
  have hFsW : WlInfMem α 4 FW ∧ WlInf α 4 FW ≤ aCFS := by
    obtain ⟨hm, hb⟩ := hFSW α hα0 hα1
    exact ⟨by rw [hFWdef]; exact hm, by rw [hFWdef, haCFSdef]; exact hb⟩
  have hDthFsW : WlInfMem α 4 DthFs ∧ WlInf α 4 DthFs ≤ aCDth := by
    obtain ⟨hm, hb⟩ := hDthW α hα0 hα1
    exact ⟨by rw [hDthFsdef]; exact hm, by rw [hDthFsdef, haCDthdef]; exact hb⟩
  have hDzFsW : WlInfMem α 4 DzFs ∧ WlInf α 4 DzFs ≤ aCDz := by
    obtain ⟨hm, hb⟩ := hDzW α hα0 hα1
    exact ⟨by rw [hDzFsdef]; exact hm, by rw [hDzFsdef, haCDzdef]; exact hb⟩
  have hFKnegW : WlInfMem α 4 FKneg ∧ WlInf α 4 FKneg ≤ aKer := by
    obtain ⟨hm, hb⟩ := hKerNeg_data α hα0
    exact ⟨by rw [hFKnegdef]; exact hm, by rw [hFKnegdef, haKerdef]; exact hb⟩
  have hqoDthw : Work.FTS.VocabO.HQo α 4 Dthw := ⟨hDthwsm, hDthwmem⟩
  have hqoDzw : Work.FTS.VocabO.HQo α 4 Dzw := ⟨hDzwsm, hDzwmem⟩
  have hphiwD : HkMem α 4 phiw ∧ Xn α phiw ≤ aφw := by
    rw [hphiwdef, haφwdef]
    exact phi_mul_data hCphi (fun g hg => hphifield (g := g) hα0 hα1 hg) hqow hXw3
  have hqophiw : Work.FTS.VocabO.HQo α 4 phiw := ⟨hphiwsm, hphiwD.1⟩
  have hphiDthwD : HkMem α 4 phiDthw ∧ Xn α phiDthw ≤ aφB := by
    rw [hphiDthwdef, haφBdef]
    exact phi_mul_data hCphi (fun g hg => hphifield (g := g) hα0 hα1 hg) hqoDthw hXDthw
  have hqophiDthw : Work.FTS.VocabO.HQo α 4 phiDthw := ⟨hphiDthwsm, hphiDthwD.1⟩
  have hphiDzwD : HkMem α 4 phiDzw ∧ Xn α phiDzw ≤ aφB := by
    rw [hphiDzwdef, haφBdef]
    exact phi_mul_data hCphi (fun g hg => hphifield (g := g) hα0 hα1 hg) hqoDzw hXDzw
  have hqophiDzw : Work.FTS.VocabO.HQo α 4 phiDzw := ⟨hphiDzwsm, hphiDzwD.1⟩
  have hFKwD : HkMem α 4 FKw ∧ Xn α FKw ≤ aFKw := by
    rw [hFKwdef, haFKwdef]
    exact FKw_data hXw (fun g hg hl => hfkfield α hα0 hα1 g hg hl) hqow hw.l12 hCfk
  have hqoFKw : Work.FTS.VocabO.HQo α 4 FKw := ⟨hFKwsm, hFKwD.1⟩
  have hp0 := mulHQo (c := 2) (C := R) (G := w) hα0 hCprod hPR haRnn haWnn hqoR hqow hXR hXw3
  have hp1 := mulW (c := 2) (F := FW) (G := R) hα0 hCw hWR haCFSnn haRnn
    hFWsm hFsW.1 hFsW.2 hqoR hXR
  have hp2 := mulW (c := 2) (F := Rs) (G := phiw) hα0 hCw hWR haRSnn haφwnn
    hRssm hstar.RW.1 hRsWle hqophiw hphiwD.2
  have hp3 := mulW (c := 2) (F := Rs) (G := phiFs) hα0 hCw hWR haRSnn (le_of_lt hC1)
    hRssm hstar.RW.1 hRsWle hatoms1.1 hatoms1.2.1
  have hp4 := mulHQo (c := -2) (C := Uc) (G := Dthw) hα0 hCprod hPR haRnn haBnn
    hqoUc hqoDthw hXUc hXDthw
  have hp5 := mulW (c := -2) (F := DthFs) (G := Uc) hα0 hCw hWR haCDthnn haRnn
    hDthFssm hDthFsW.1 hDthFsW.2 hqoUc hXUc
  have hp6 := mulW (c := -2) (F := Us) (G := phiDthw) hα0 hCw hWR haRSnn haφBnn
    hUssm hstar.UszW.1 hUsWle hqophiDthw hphiDthwD.2
  have hp7 := mulW (c := -2) (F := Us) (G := phiDthFs) hα0 hCw hWR haRSnn (le_of_lt hC1)
    hUssm hstar.UszW.1 hUsWle hatoms1.2.2.1 hatoms1.2.2.2.1
  have hp8 := mulHQo (c := (-(2 * α))) (C := Vc) (G := Dzw) hα0 hCprod hPR haRnn haBnn
    hqoVc hqoDzw hXVc hXDzw
  have hp9 := mulW (c := (-(2 * α))) (F := DzFs) (G := Vc) hα0 hCw hWR haCDznn haRnn
    hDzFssm hDzFsW.1 hDzFsW.2 hqoVc hXVc
  have hp10 := mulW (c := (-(2 * α))) (F := Vs) (G := phiDzw) hα0 hCw hWR haRSnn haφBnn
    hVssm hstar.VzW.1 hVsWle hqophiDzw hphiDzwD.2
  have hp11 := mulW (c := (-(2 * α))) (F := Vs) (G := phiDzFs) hα0 hCw hWR haRSnn
    (le_of_lt hC1) hVssm hstar.VzW.1 hVsWle hatoms1.2.2.2.2.1 hatoms1.2.2.2.2.2
  have hp12 := mulHQo (c := (-(1 / 2))) (C := FKw) (G := Dthw) hα0 hCprod hPR
    haFKwnn haBnn hqoFKw hqoDthw hFKwD.2 hXDthw
  have hp13 := mulW (c := (-(1 / 2))) (F := DthFs) (G := FKw) hα0 hCw hWR haCDthnn haFKwnn
    hDthFssm hDthFsW.1 hDthFsW.2 hqoFKw hFKwD.2
  have hp14 := mulW (c := (1 / 2)) (F := FKneg) (G := Dthw) hα0 hCw hWR haKernn haBnn
    hFKnegsm hFKnegW.1 hFKnegW.2 hqoDthw hXDthw
  have hp16i := mulHQo (c := 1) (C := FKw) (G := w) hα0 hCprod hPR haFKwnn haWnn
    hqoFKw hqow hFKwD.2 hXw3
  have hp17i := mulW (c := 1) (F := FW) (G := FKw) hα0 hCw hWR haCFSnn haFKwnn
    hFWsm hFsW.1 hFsW.2 hqoFKw hFKwD.2
  have hp18i := mulW (c := 1) (F := FKneg) (G := w) hα0 hCw hWR haKernn haWnn
    hFKnegsm hFKnegW.1 hFKnegW.2 hqow hXw3
  have hSinMul : ∀ G : Fn, Work.FTS.EllipticEst.SmoothOpen G → HkMem α 4 G →
      HkMem α 4 (fun z θ => -(Real.sin θ) ^ 2 * G z θ) ∧
      Xn α (fun z θ => -(Real.sin θ) ^ 2 * G z θ)
        ≤ Csin * Xn α G := by
    intro G hGs hGm
    have h := hangfield α hα0 hα1 (fun θ => -(Real.sin θ) ^ 2) Bsin hBsin
      Work.FTS.Nonlinear.Open.row25_smoothOpen_neg_sinSq
      (fun θ hθ => hSinB θ hθ) (fun i hi hi4 θ hθ => hSinIt i hi hi4 θ hθ) G hGs hGm
    obtain ⟨hm, hsq⟩ := h
    refine ⟨hm, ?_⟩
    refine le_trans (Real.sqrt_le_sqrt hsq) ?_
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ Cang * Bsin ^ 2), hCsidef]
    rfl
  have hp16 : HkMem α 4 (fun z θ => -(Real.sin θ) ^ 2 * (FKw z θ * w z θ)) ∧
      Xn α (fun z θ => -(Real.sin θ) ^ 2 * (FKw z θ * w z θ))
        ≤ Csin * Xn α (fun z θ => FKw z θ * w z θ) :=
    hSinMul (fun z θ => FKw z θ * w z θ)
      (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hFKwsm hw.reg)
      (by simpa only [one_mul] using hp16i.1)
  have hp17 : HkMem α 4 (fun z θ => -(Real.sin θ) ^ 2 * (FW z θ * FKw z θ)) ∧
      Xn α (fun z θ => -(Real.sin θ) ^ 2 * (FW z θ * FKw z θ))
        ≤ Csin * Xn α (fun z θ => FW z θ * FKw z θ) :=
    hSinMul (fun z θ => FW z θ * FKw z θ)
      (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hFWsm hFKwsm)
      (by simpa only [one_mul] using hp17i.1)
  have hp19 := hSinMul _ hatoms2.2.2.1.1 hatoms2.2.2.1.2
  have heq18 : (fun z θ => (-1) * (-(Real.sin θ) ^ 2
        * ((-(2 * α)) * hKer z * w z θ)))
      = fun z θ => -(Real.sin θ) ^ 2 * (Work.Construction.FK (Work.Construction.Fstar α) z
        * w z θ) := by
    funext z θ
    rw [Work.FTS.Nonlin.FK_Fstar hα0 hα1, hKer_apply]
    ring
  have hp18 : HkMem α 4 (fun z θ => -(Real.sin θ) ^ 2 * (FKneg z θ * w z θ)) ∧
      Xn α (fun z θ => -(Real.sin θ) ^ 2 * (FKneg z θ * w z θ))
        ≤ Csin * Xn α (fun z θ => FKneg z θ * w z θ) :=
    hSinMul (fun z θ => FKneg z θ * w z θ)
      (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hFKnegsm hw.reg)
      (by simpa only [one_mul] using hp18i.1)
  have hM0 : HkMem α 4 (NBlk α w Φs Φg 0) := by simpa only [NBlk] using hp0.1
  have hM1 : HkMem α 4 (NBlk α w Φs Φg 1) := by simpa only [NBlk] using hp1.1
  have hM2 : HkMem α 4 (NBlk α w Φs Φg 2) := by simpa only [NBlk] using hp2.1
  have hM3 : HkMem α 4 (NBlk α w Φs Φg 3) := by simpa only [NBlk] using hp3.1
  have hM4 : HkMem α 4 (NBlk α w Φs Φg 4) := by simpa only [NBlk] using hp4.1
  have hM5 : HkMem α 4 (NBlk α w Φs Φg 5) := by simpa only [NBlk] using hp5.1
  have hM6 : HkMem α 4 (NBlk α w Φs Φg 6) := by simpa only [NBlk] using hp6.1
  have hM7 : HkMem α 4 (NBlk α w Φs Φg 7) := by simpa only [NBlk] using hp7.1
  have hM8 : HkMem α 4 (NBlk α w Φs Φg 8) := by simpa only [NBlk] using hp8.1
  have hM9 : HkMem α 4 (NBlk α w Φs Φg 9) := by simpa only [NBlk] using hp9.1
  have hM10 : HkMem α 4 (NBlk α w Φs Φg 10) := by simpa only [NBlk] using hp10.1
  have hM11 : HkMem α 4 (NBlk α w Φs Φg 11) := by simpa only [NBlk] using hp11.1
  have hM12 : HkMem α 4 (NBlk α w Φs Φg 12) := by simpa only [NBlk] using hp12.1
  have hM13 : HkMem α 4 (NBlk α w Φs Φg 13) := by simpa only [NBlk] using hp13.1
  have hM14 : HkMem α 4 (NBlk α w Φs Φg 14) := by simpa only [NBlk] using hp14.1
  have hM15 : HkMem α 4 (NBlk α w Φs Φg 15) :=
    Work.FTS.LocData.HkMem_const_mul α 4 (-(1 / 2)) hatoms2.1.2
  have hM16 : HkMem α 4 (NBlk α w Φs Φg 16) := by simpa only [NBlk] using hp16.1
  have hM17 : HkMem α 4 (NBlk α w Φs Φg 17) := by simpa only [NBlk] using hp17.1
  have hM18 : HkMem α 4 (NBlk α w Φs Φg 18) := by
    rw [show NBlk α w Φs Φg 18 = fun z θ => -(Real.sin θ) ^ 2
      * (Work.Construction.FK (Work.Construction.Fstar α) z * w z θ) from by simp only [NBlk]]
    rw [← heq18]
    exact Work.FTS.LocData.HkMem_const_mul α 4 (-1) hp18.1
  have hM19 : HkMem α 4 (NBlk α w Φs Φg 19) := by simpa only [NBlk] using hp19.1
  have hB0 : Xn α (NBlk α w Φs Φg 0) ≤ Kbig :=
    le_trans (by simpa only [NBlk] using hp0.2) (hbE 0 (by decide) _ (by simp only [hTdef]))
  have hB1 : Xn α (NBlk α w Φs Φg 1) ≤ Kbig :=
    le_trans (by simpa only [NBlk] using hp1.2) (hbE 1 (by decide) _ (by simp only [hTdef]))
  have hB2 : Xn α (NBlk α w Φs Φg 2) ≤ Kbig :=
    le_trans (by simpa only [NBlk] using hp2.2) (hbE 2 (by decide) _ (by simp only [hTdef]))
  have hB3 : Xn α (NBlk α w Φs Φg 3) ≤ Kbig :=
    le_trans (by simpa only [NBlk] using hp3.2) (hbE 3 (by decide) _ (by simp only [hTdef]))
  have hB4 : Xn α (NBlk α w Φs Φg 4) ≤ Kbig :=
    le_trans (by simpa only [NBlk] using hp4.2) (hbE 4 (by decide) _ (by simp only [hTdef]))
  have hB5 : Xn α (NBlk α w Φs Φg 5) ≤ Kbig :=
    le_trans (by simpa only [NBlk] using hp5.2) (hbE 5 (by decide) _ (by simp only [hTdef]))
  have hB6 : Xn α (NBlk α w Φs Φg 6) ≤ Kbig :=
    le_trans (by simpa only [NBlk] using hp6.2) (hbE 6 (by decide) _ (by simp only [hTdef]))
  have hB7 : Xn α (NBlk α w Φs Φg 7) ≤ Kbig :=
    le_trans (by simpa only [NBlk] using hp7.2) (hbE 7 (by decide) _ (by simp only [hTdef]))
  have hB8 : Xn α (NBlk α w Φs Φg 8) ≤ Kbig :=
    le_trans (by simpa only [NBlk] using hp8.2) (hbE 8 (by decide) _ (by simp only [hTdef]))
  have hB9 : Xn α (NBlk α w Φs Φg 9) ≤ Kbig :=
    le_trans (by simpa only [NBlk] using hp9.2) (hbE 9 (by decide) _ (by simp only [hTdef]))
  have hB10 : Xn α (NBlk α w Φs Φg 10) ≤ Kbig :=
    le_trans (by simpa only [NBlk] using hp10.2) (hbE 10 (by decide) _ (by simp only [hTdef]))
  have hB11 : Xn α (NBlk α w Φs Φg 11) ≤ Kbig :=
    le_trans (by simpa only [NBlk] using hp11.2) (hbE 11 (by decide) _ (by simp only [hTdef]))
  have hB12 : Xn α (NBlk α w Φs Φg 12) ≤ Kbig :=
    le_trans (by simpa only [NBlk] using hp12.2) (hbE 12 (by decide) _ (by simp only [hTdef]))
  have hB13 : Xn α (NBlk α w Φs Φg 13) ≤ Kbig :=
    le_trans (by simpa only [NBlk] using hp13.2) (hbE 13 (by decide) _ (by simp only [hTdef]))
  have hB14 : Xn α (NBlk α w Φs Φg 14) ≤ Kbig :=
    le_trans (by simpa only [NBlk] using hp14.2) (hbE 14 (by decide) _ (by simp only [hTdef]))
  have hB15 : Xn α (NBlk α w Φs Φg 15) ≤ Kbig := by
    rw [show NBlk α w Φs Φg 15 = fun z θ => (-(1 / 2)) * prodFKFS z θ from by
      simp only [NBlk, hprodFKFSdef]]
    rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul, show |(-(1 / 2) : ℝ)| = 1 / 2 from by
      norm_num]
    refine le_trans (mul_le_mul_of_nonneg_left hatoms2.2.1 (by norm_num : (0 : ℝ) ≤ 1 / 2))
      (hbE 15 (by decide) _ (by simp only [hTdef]))
  have hB16 : Xn α (NBlk α w Φs Φg 16) ≤ Kbig :=
    le_trans (by simpa only [NBlk] using hp16.2)
      (le_trans (mul_le_mul_of_nonneg_left (by simpa only [one_mul] using hp16i.2) hCsinpos.le)
        (hbE 16 (by decide) _ (by simp only [hTdef])))
  have hB17 : Xn α (NBlk α w Φs Φg 17) ≤ Kbig :=
    le_trans (by simpa only [NBlk] using hp17.2)
      (le_trans (mul_le_mul_of_nonneg_left (by simpa only [one_mul] using hp17i.2) hCsinpos.le)
        (hbE 17 (by decide) _ (by simp only [hTdef])))
  have hB18 : Xn α (NBlk α w Φs Φg 18) ≤ Kbig := by
    rw [show NBlk α w Φs Φg 18 = fun z θ => -(Real.sin θ) ^ 2
      * (Work.Construction.FK (Work.Construction.Fstar α) z * w z θ) from by simp only [NBlk]]
    rw [← heq18, Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul,
      show |(-1 : ℝ)| = 1 from by norm_num, one_mul]
    exact le_trans hp18.2 (le_trans
      (mul_le_mul_of_nonneg_left (by simpa only [one_mul] using hp18i.2) hCsinpos.le)
      (hbE 18 (by decide) _ (by simp only [hTdef])))
  have hB19 : Xn α (NBlk α w Φs Φg 19) ≤ Kbig :=
    le_trans (by simpa only [NBlk] using hp19.2)
      (le_trans (mul_le_mul_of_nonneg_left hatoms2.2.2.2 hCsinpos.le) (hbE 19 (by decide) _ (by simp only [hTdef])))
  have hL : ∀ z : ℝ, 0 < z → Work.Construction.L12 (Work.Construction.Ftot α w) z
      = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 w z :=
    fun z hz => Work.FTS.StrongPersist.H6Rows.NZaux.L12AddFstar hα0 hα1 hw.reg hmem4w z hz
  have hFK : ∀ z : ℝ, 0 < z → Work.Construction.FK (Work.Construction.Ftot α w) z
      = Work.Construction.FK (Work.Construction.Fstar α) z + Work.Construction.FK w z :=
    fun z hz => Work.FTS.GalFields.RHS.FK_add_of_slices (a := Work.Construction.Fstar α) (b := w)
      (ne_of_gt hz) (Work.Stability.integrableOn_slice_Fstar α hα0 z)
      (Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hw.reg hmem4w hz)
  have hL12d : ∀ z : ℝ, 0 < z → DifferentiableAt ℝ (fun z' => Work.Construction.L12 w z') z :=
    fun z hz => Work.FTS.StrongEps.EComparison.differentiableAt_L12_of_Vop (ne_of_gt hα0)
      (F := w) (Ψ := Φg) hell.smooth hell.V.1.1 hz
  have hsplit := Work.FTS.NonlinRows.Rl1.splitOpen (α := α) (g := w) (Φs := Φs) (Φg := Φg)
    hα0 hα1 hw.reg hstar.smooth hell.smooth hL hFK hL12d
  refine ⟨NBlk_smooth hα0 hα1 hw hell hstar, ?_, ?_⟩
  · intro k hk
    have hk20 : k < 20 := Finset.mem_range.mp hk
    interval_cases k <;>
      first
        | exact ⟨hM0, hB0⟩ | exact ⟨hM1, hB1⟩ | exact ⟨hM2, hB2⟩ | exact ⟨hM3, hB3⟩
        | exact ⟨hM4, hB4⟩ | exact ⟨hM5, hB5⟩ | exact ⟨hM6, hB6⟩ | exact ⟨hM7, hB7⟩
        | exact ⟨hM8, hB8⟩ | exact ⟨hM9, hB9⟩ | exact ⟨hM10, hB10⟩ | exact ⟨hM11, hB11⟩
        | exact ⟨hM12, hB12⟩ | exact ⟨hM13, hB13⟩ | exact ⟨hM14, hB14⟩ | exact ⟨hM15, hB15⟩
        | exact ⟨hM16, hB16⟩ | exact ⟨hM17, hB17⟩ | exact ⟨hM18, hB18⟩ | exact ⟨hM19, hB19⟩
  · intro z θ hq
    obtain ⟨hz, hθ0, hθ1⟩ := hq
    rw [hsplit z θ ⟨hz, hθ0, hθ1⟩, ← PB_sum_eq α w Φs Φg z θ]
    exact Finset.sum_congr rfl
      (fun k hk => PB_eq_NBlk hα0 hα1 w Φs Φg k hk z θ hz hθ0 hθ1)

end Work.FTS.StrongEps.ClassCRHS
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.N4C.PairingT.RowInputs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.N4C

open Work.FTS.Galerkin (Fn)
open Work.FTS.VocabO (HQo)
open Work.FTS.Nonlin

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **The honest per-piece table of §8.**  Field for field this is `Open2.RowInputs2'`, with the
`HkMem α 4`-hypotheses on the first arguments replaced by the honest class `GoodO α = HQo α 4`
(interior `C^∞` plus honesty), which is what the `N4ExtraH` interface consumes. -/
structure RowInputsTO (IP : ℝ → Fn → Fn → ℝ) (α C : ℝ) (g Φs Φg : Fn) : Prop where
  r1 : GoodO α (N0fix α) ∧ Xn α (N0fix α) ≤ C * α ^ 2
  r2 : GoodO α (N03g α g) ∧ Xn α (N03g α g) ≤ C * (α ^ (-(1 : ℝ)) * Xn α g ^ 2)
  r3 : GoodO α (N04aF α g) ∧ Xn α (N04aF α g) ≤ C * (Real.sqrt α * Xn α g)
  r4 : GoodO α (N04bF α g) ∧ |IP α (N04bF α g) g| ≤ C * (α ^ (-(3 / 2 : ℝ)) * Xn α g ^ 3)
  r5 : GoodO α (N05aF α g) ∧ Xn α (N05aF α g) ≤ C * (Real.sqrt α * Xn α g)
  r6 : GoodO α (N05bF α g) ∧ |IP α (N05bF α g) g| ≤ C * (α ^ (-(1 / 2 : ℝ)) * Xn α g ^ 3)
  r7 : GoodO α (N06F α g) ∧ |IP α (N06F α g) g| ≤ C * (Real.sqrt α * Xn α g ^ 2)
  r8 : GoodO α (N1gg α g Φg) ∧ Xn α (N1gg α g Φg) ≤ C * (α ^ (-(1 / 2 : ℝ)) * Xn α g ^ 2)
  r9 : GoodO α (N1gs α g Φg) ∧ Xn α (N1gs α g Φg) ≤ C * (Real.sqrt α * Xn α g)
  r10 : GoodO α (N1sg α Φs g) ∧ Xn α (N1sg α Φs g) ≤ C * (Real.sqrt α * Xn α g)
  r11 : GoodO α (N1ss α Φs) ∧ Xn α (N1ss α Φs) ≤ C * α ^ 2
  r12 : GoodO α (N2gg α g Φg) ∧ |IP α (N2gg α g Φg) g| ≤ C * (α ^ (-(1 / 2 : ℝ)) * Xn α g ^ 3)
  r13 : GoodO α (N2gs α g Φg) ∧ Xn α (N2gs α g Φg) ≤ C * (α ^ (3 / 2 : ℝ) * Xn α g)
  r14 : GoodO α (N2sg α Φs g) ∧ |IP α (N2sg α Φs g) g| ≤ C * (Real.sqrt α * Xn α g ^ 2)
  r15 : GoodO α (N2ss α Φs) ∧ Xn α (N2ss α Φs) ≤ C * α ^ 2
  r16 : GoodO α (N3gg α g Φg) ∧ |IP α (N3gg α g Φg) g| ≤ C * Xn α g ^ 3
  r17 : GoodO α (N3gs α g Φg) ∧ Xn α (N3gs α g Φg) ≤ C * (α ^ (3 / 2 : ℝ) * Xn α g)
  r18 : GoodO α (N3sg α Φs g) ∧ |IP α (N3sg α Φs g) g| ≤ C * (α ^ (3 / 2 : ℝ) * Xn α g ^ 2)
  r19 : GoodO α (N3ss α Φs) ∧ Xn α (N3ss α Φs) ≤ C * α ^ 3
  r20 : GoodO α (N4gg α g) ∧ |IP α (N4gg α g) g| ≤ C * (α ^ (-(1 / 2 : ℝ)) * Xn α g ^ 3)
  r21 : GoodO α (N4gs α g) ∧ Xn α (N4gs α g) ≤ C * (α ^ (3 / 2 : ℝ) * Xn α g)
  r22 : GoodO α (N4sg α g) ∧ |IP α (N4sg α g) g| ≤ C * (Real.sqrt α * Xn α g ^ 2)
  r23 : GoodO α (N4ss α) ∧ Xn α (N4ss α) ≤ C * α ^ 3
  r24 : GoodO α (N5gg g) ∧ Xn α (N5gg g) ≤ C * Xn α g ^ 2
  r25 : GoodO α (N5gs α g) ∧ GoodO α (N5sg α g) ∧
    Xn α (N5gs α g) + Xn α (N5sg α g) ≤ C * (Real.sqrt α * Xn α g)
  r26 : GoodO α (N5ss α) ∧ Xn α (N5ss α) ≤ C * α ^ 2
  rak : GoodO α (Work.Construction.AK α) ∧ Xn α (Work.Construction.AK α) ≤ C
  rl0 : |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α g) g) 0|
    ≤ C * (α ^ 2 + Real.sqrt α * Xn α g + α ^ (-(3 / 2 : ℝ)) * Xn α g ^ 2)
  rl1 : |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α g)
      (fun z θ => Φs z θ + Φg z θ)) 0|
    ≤ C * (α ^ 2 + Real.sqrt α * Xn α g + α ^ (-(3 / 2 : ℝ)) * Xn α g ^ 2)
  rl2 : |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)) 0| ≤ C * Xn α g
  hN0 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
    Work.Construction.N0 α (Work.Construction.Ftot α g) g z θ
      = N0fix α z θ + (N03g α g z θ + N04aF α g z θ + N04bF α g z θ
          + N05aF α g z θ + N05bF α g z θ + N06F α g z θ)
  hN : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
    Work.Construction.N α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ) z θ
      = (N1gg α g Φg z θ + N1gs α g Φg z θ + N1sg α Φs g z θ + N1ss α Φs z θ)
        + (N2gg α g Φg z θ + N2gs α g Φg z θ + N2sg α Φs g z θ + N2ss α Φs z θ)
        + (N3gg α g Φg z θ + N3gs α g Φg z θ + N3sg α Φs g z θ + N3ss α Φs z θ)
        + (N4gg α g z θ + N4gs α g z θ + N4sg α g z θ + N4ss α z θ)
        + (N5gg g z θ + N5gs α g z θ + N5sg α g z θ + N5ss α z θ)
  hNs : ∀ μ : ℝ, μ ≠ -1 → ∀ z θ,
    Work.Construction.Nstar μ (Work.Construction.lamfun μ) g z θ = NstarLam μ g z θ
  hkN0 : GoodO α (Work.Construction.N0 α (Work.Construction.Ftot α g) g)
  hkN : GoodO α (Work.Construction.N α (Work.Construction.Ftot α g)
    (fun z θ => Φs z θ + Φg z θ))
  hkDz : GoodO α (Work.Spaces.Dz g)

/-- **The honest per-piece table from the honest row table.** -/
theorem rowInputsTO_of_rows {IP : ℝ → Fn → Fn → ℝ} {α₂ Ce Cs α C K₁ K₂ K₃ : ℝ} {g Φs Φg : Fn}
    (hα : 0 < α) (hα1 : α ≤ 1) (hαα₂ : α ≤ α₂)
    (hgC : Work.FTS.ClassC.ClassC α g) (hco : Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α g)
    (hell : Work.FTS.VocabO.EllPkgGo α Ce g Φg)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hrowsN0 : Work.FTS.Nonlinear.Pieces.N0Rows IP α K₁ g Φs Φg)
    (hrowsN : Work.FTS.VocabO2.NRows2 IP α K₂ g Φs Φg)
    (hrowsAux : Work.FTS.Nonlinear.Pieces.AuxRows IP α K₃ g Φs Φg)
    (hK1 : K₁ ≤ C) (hK2 : K₂ ≤ C) (hK3 : K₃ ≤ C)
    (hk : Work.FTS.OpenPkg.PiecesHk α g Φs Φg)
    (hspl : Work.FTS.NonlinRows.SplitsData α g Φs Φg)
    (hsmN0 : Work.FTS.EllipticEst.SmoothOpen (N0fix α) ∧
      Work.FTS.EllipticEst.SmoothOpen (N03g α g) ∧
      Work.FTS.EllipticEst.SmoothOpen (N04aF α g) ∧
      Work.FTS.EllipticEst.SmoothOpen (N04bF α g) ∧
      Work.FTS.EllipticEst.SmoothOpen (N05aF α g) ∧
      Work.FTS.EllipticEst.SmoothOpen (N05bF α g) ∧
      Work.FTS.EllipticEst.SmoothOpen (N06F α g))
    (hsmN : Work.FTS.EllipticEst.SmoothOpen (N1gg α g Φg) ∧
      Work.FTS.EllipticEst.SmoothOpen (N1gs α g Φg) ∧
      Work.FTS.EllipticEst.SmoothOpen (N1sg α Φs g) ∧
      Work.FTS.EllipticEst.SmoothOpen (N1ss α Φs) ∧
      Work.FTS.EllipticEst.SmoothOpen (N2gg α g Φg) ∧
      Work.FTS.EllipticEst.SmoothOpen (N2gs α g Φg) ∧
      Work.FTS.EllipticEst.SmoothOpen (N2sg α Φs g) ∧
      Work.FTS.EllipticEst.SmoothOpen (N2ss α Φs) ∧
      Work.FTS.EllipticEst.SmoothOpen (N3gg α g Φg) ∧
      Work.FTS.EllipticEst.SmoothOpen (N3gs α g Φg) ∧
      Work.FTS.EllipticEst.SmoothOpen (N3sg α Φs g) ∧
      Work.FTS.EllipticEst.SmoothOpen (N3ss α Φs) ∧
      Work.FTS.EllipticEst.SmoothOpen (N4gg α g) ∧
      Work.FTS.EllipticEst.SmoothOpen (N4gs α g) ∧
      Work.FTS.EllipticEst.SmoothOpen (N4sg α g) ∧
      Work.FTS.EllipticEst.SmoothOpen (N4ss α) ∧
      Work.FTS.EllipticEst.SmoothOpen (N5gg g) ∧
      Work.FTS.EllipticEst.SmoothOpen (N5gs α g) ∧
      Work.FTS.EllipticEst.SmoothOpen (N5sg α g) ∧
      Work.FTS.EllipticEst.SmoothOpen (N5ss α)) :
    RowInputsTO IP α C g Φs Φg := by
  obtain ⟨hs0, hs1, hs2⟩ := hspl
  obtain ⟨m1, m2, m3, m4, m5, m6, m7⟩ := hsmN0
  obtain ⟨m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23,
    m24, m25, m26, m27⟩ := hsmN
  have hα0 : (0 : ℝ) ≤ α := hα.le
  have hX0 : (0 : ℝ) ≤ Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hsq0 : (0 : ℝ) ≤ Real.sqrt α := Real.sqrt_nonneg α
  have hX2 : (0 : ℝ) ≤ Xn α g ^ 2 := pow_nonneg hX0 2
  have hX3 : (0 : ℝ) ≤ Xn α g ^ 3 := pow_nonneg hX0 3
  have hr1 : (0 : ℝ) ≤ α ^ (-(1 : ℝ)) := Real.rpow_nonneg hα0 _
  have hr12 : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα0 _
  have hr32 : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hα0 _
  have h32 : (0 : ℝ) ≤ α ^ (3 / 2 : ℝ) := Real.rpow_nonneg hα0 _
  refine
    { r1 := ⟨⟨m1, hk.p1⟩, le_trans hrowsN0.r1 (mul_le_mul_of_nonneg_right hK1 (pow_nonneg hα0 2))⟩
      r2 := ⟨⟨m2, hk.p2⟩,
        le_trans hrowsN0.r2 (mul_le_mul_of_nonneg_right hK1 (mul_nonneg hr1 hX2))⟩
      r3 := ⟨⟨m3, hk.p3⟩,
        le_trans hrowsN0.r3 (mul_le_mul_of_nonneg_right hK1 (mul_nonneg hsq0 hX0))⟩
      r4 := ⟨⟨m4, hk.p4⟩,
        le_trans hrowsN0.r4 (mul_le_mul_of_nonneg_right hK1 (mul_nonneg hr32 hX3))⟩
      r5 := ⟨⟨m5, hk.p5⟩,
        le_trans hrowsN0.r5 (mul_le_mul_of_nonneg_right hK1 (mul_nonneg hsq0 hX0))⟩
      r6 := ⟨⟨m6, hk.p6⟩,
        le_trans hrowsN0.r6 (mul_le_mul_of_nonneg_right hK1 (mul_nonneg hr12 hX3))⟩
      r7 := ⟨⟨m7, hk.p7⟩,
        le_trans hrowsN0.r7 (mul_le_mul_of_nonneg_right hK1 (mul_nonneg hsq0 hX2))⟩
      r8 := ⟨⟨m8, hk.p8⟩,
        le_trans hrowsN.r8 (mul_le_mul_of_nonneg_right hK2 (mul_nonneg hr12 hX2))⟩
      r9 := ⟨⟨m9, hk.p9⟩,
        le_trans hrowsN.r9 (mul_le_mul_of_nonneg_right hK2 (mul_nonneg hsq0 hX0))⟩
      r10 := ⟨⟨m10, hk.p10⟩,
        le_trans hrowsN.r10 (mul_le_mul_of_nonneg_right hK2 (mul_nonneg hsq0 hX0))⟩
      r11 := ⟨⟨m11, hk.p11⟩,
        le_trans hrowsN.r11 (mul_le_mul_of_nonneg_right hK2 (pow_nonneg hα0 2))⟩
      r12 := ⟨⟨m12, hk.p12⟩,
        le_trans hrowsN.r12 (mul_le_mul_of_nonneg_right hK2 (mul_nonneg hr12 hX3))⟩
      r13 := ⟨⟨m13, hk.p13⟩,
        le_trans hrowsN.r13 (mul_le_mul_of_nonneg_right hK2 (mul_nonneg h32 hX0))⟩
      r14 := ⟨⟨m14, hk.p14⟩,
        le_trans hrowsN.r14 (mul_le_mul_of_nonneg_right hK2 (mul_nonneg hsq0 hX2))⟩
      r15 := ⟨⟨m15, hk.p15⟩,
        le_trans hrowsN.r15 (mul_le_mul_of_nonneg_right hK2 (pow_nonneg hα0 2))⟩
      r16 := ⟨⟨m16, hk.p16⟩, le_trans hrowsN.r16 (mul_le_mul_of_nonneg_right hK2 hX3)⟩
      r17 := ⟨⟨m17, hk.p17⟩,
        le_trans hrowsN.r17 (mul_le_mul_of_nonneg_right hK2 (mul_nonneg h32 hX0))⟩
      r18 := ⟨⟨m18, hk.p18⟩,
        le_trans hrowsN.r18 (mul_le_mul_of_nonneg_right hK2 (mul_nonneg h32 hX2))⟩
      r19 := ⟨⟨m19, hk.p19⟩,
        le_trans hrowsN.r19 (mul_le_mul_of_nonneg_right hK2 (pow_nonneg hα0 3))⟩
      r20 := ⟨⟨m20, hk.p20⟩,
        le_trans hrowsN.r20 (mul_le_mul_of_nonneg_right hK2 (mul_nonneg hr12 hX3))⟩
      r21 := ⟨⟨m21, hk.p21⟩,
        le_trans hrowsN.r21 (mul_le_mul_of_nonneg_right hK2 (mul_nonneg h32 hX0))⟩
      r22 := ⟨⟨m22, hk.p22⟩,
        le_trans hrowsN.r22 (mul_le_mul_of_nonneg_right hK2 (mul_nonneg hsq0 hX2))⟩
      r23 := ⟨⟨m23, hk.p23⟩,
        le_trans hrowsN.r23 (mul_le_mul_of_nonneg_right hK2 (pow_nonneg hα0 3))⟩
      r24 := ⟨⟨m24, hk.p24⟩, le_trans hrowsN.r24 (mul_le_mul_of_nonneg_right hK2 hX2)⟩
      r25 := ⟨⟨m25, hk.p25⟩, ⟨m26, hk.p26⟩,
        le_trans hrowsN.r25 (mul_le_mul_of_nonneg_right hK2 (mul_nonneg hsq0 hX0))⟩
      r26 := ⟨⟨m27, hk.p27⟩,
        le_trans hrowsN.r26 (mul_le_mul_of_nonneg_right hK2 (pow_nonneg hα0 2))⟩
      rak := ⟨⟨Work.FTS.StrongPersist.AK_smoothO α, hk.pAK⟩,
        le_trans hrowsAux.rak hK3⟩
      rl0 := le_trans hrowsAux.rl0 (mul_le_mul_of_nonneg_right hK3 (by positivity))
      rl1 := le_trans hrowsAux.rl1 (mul_le_mul_of_nonneg_right hK3 (by positivity))
      rl2 := le_trans hrowsAux.rl2 (mul_le_mul_of_nonneg_right hK3 hX0)
      hN0 := hs0
      hN := hs1
      hNs := hs2
      hkN0 := ⟨Work.FTS.StrongEps.ClassCRHS.SmoothOpenRHS hα hα1 hgC hell hstar |>.2.2.2.1,
        hk.pN0⟩
      hkN := ⟨Work.FTS.StrongEps.ClassCRHS.SmoothOpenRHS hα hα1 hgC hell hstar |>.2.2.2.2,
        hk.pN⟩
      hkDz := ⟨hgC.reg.Dz, hk.pDz⟩ }

/-- **The shared context of the honest §8 assembly**: the `IP`-interface `N4ExtraH`, the ranges
of `α`, the class-`C` data (whose coercivity field supplies the `D_z`-self-pairing), the honest
row table and the constant bookkeeping.  This is the honest analogue of `Open2.BlkCtx`. -/
structure BlkCtxO (IP : ℝ → Fn → Fn → ℝ) (α₂ Ct K₀ C C₀ α : ℝ) (g Φs Φg : Fn) : Prop where
  hE : N4ExtraH IP α₂ Ct
  hα : 0 < α
  hαα₂ : α ≤ α₂
  hα1 : α ≤ 1
  hgC : Work.FTS.ClassC.ClassC α g
  hco : Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α g
  hR : RowInputsTO IP α C g Φs Φg
  hCt : 0 < Ct
  hK₀pos : 0 < K₀
  hK₀Ct : Ct ≤ K₀
  hK₀one : 1 ≤ K₀
  hC : 0 < C
  hbigK : K₀ * (C + 1) ≤ C₀ * C

namespace BlkCtxO

variable {IP : ℝ → Fn → Fn → ℝ} {α₂ Ct K₀ C C₀ α : ℝ} {g Φs Φg : Fn}

theorem hαIoc (h : BlkCtxO IP α₂ Ct K₀ C C₀ α g Φs Φg) : α ∈ Set.Ioc 0 α₂ :=
  ⟨h.hα, h.hαα₂⟩

theorem hg4 (h : BlkCtxO IP α₂ Ct K₀ C C₀ α g Φs Φg) : HQo α 4 g :=
  classC_hqo4 h.hgC

theorem hreg5 (h : BlkCtxO IP α₂ Ct K₀ C C₀ α g Φs Φg) :
    Work.FTS.StrongEps.EpsE4Thr.RegQo α 5 g := h.hco.1

end BlkCtxO

/-- **The per-piece bound from an `ℋ⁴`-estimate**, honest version of `Open2.pieceBd`. -/
theorem pieceBdO {IP : ℝ → Fn → Fn → ℝ} {α₂ Ct K₀ C α : ℝ} {g : Fn}
    (hE : N4ExtraH IP α₂ Ct) (hαIoc : α ∈ Set.Ioc 0 α₂) (hg : HQo α 4 g) (hCt : 0 < Ct)
    (hK₀Ct : Ct ≤ K₀) (hX0 : 0 ≤ Xn α g) (hPbd0 : 0 ≤ Pbd α (Xn α g)) (hC : 0 < C)
    (f : Fn) (B : ℝ) (hf : Xn α f ≤ C * B) (hB : B * Xn α g ≤ Pbd α (Xn α g))
    (hk : HQo α 4 f) :
    |IP α f g| ≤ K₀ * (C + 1) * Pbd α (Xn α g) := by
  set X := Xn α g with hXdef
  have hK₀pos : 0 < K₀ := lt_of_lt_of_le hCt hK₀Ct
  have h1 : |IP α f g| ≤ Ct * Xn α f * X := hE.cs α hαIoc f g hk hg
  have h2 : Ct * Xn α f * X ≤ Ct * (C * B) * X :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf hCt.le) hX0
  have h3 : Ct * (C * B) * X = Ct * C * (B * X) := by ring
  have h4 : Ct * C * (B * X) ≤ Ct * C * Pbd α X :=
    mul_le_mul_of_nonneg_left hB (by positivity)
  have h5 : Ct * C * Pbd α X ≤ K₀ * C * Pbd α X :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK₀Ct hC.le) hPbd0
  have h6 : K₀ * C * Pbd α X ≤ K₀ * (C + 1) * Pbd α X := by
    have h := mul_le_mul_of_nonneg_right (by linarith : C ≤ C + 1) hPbd0
    nlinarith [h, hK₀pos.le, hPbd0]
  linarith [h1, h2, h3.le, h3.ge, h4, h5, h6]

/-- **The per-piece bound from a direct pairing estimate**, honest version of
`Open2.pieceDir`. -/
theorem pieceDirO {IP : ℝ → Fn → Fn → ℝ} {K₀ C α : ℝ} {g : Fn}
    (f : Fn) (m : ℝ) (hf : |IP α f g| ≤ C * m) (hm : m ≤ Pbd α (Xn α g))
    (hPbd0 : 0 ≤ Pbd α (Xn α g)) (hC : 0 < C) (hK₀one : 1 ≤ K₀) :
    |IP α f g| ≤ K₀ * (C + 1) * Pbd α (Xn α g) := by
  set X := Xn α g with hXdef
  have h1 : C * m ≤ C * Pbd α X := mul_le_mul_of_nonneg_left hm hC.le
  have h2 : C * Pbd α X ≤ K₀ * C * Pbd α X := by
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK₀one hC.le) hPbd0
    nlinarith [h]
  have h3 : K₀ * C * Pbd α X ≤ K₀ * (C + 1) * Pbd α X := by
    have h := mul_le_mul_of_nonneg_right (by linarith : C ≤ C + 1) hPbd0
    nlinarith [h, hPbd0]
  linarith [hf, h1, h2, h3]

end Work.FTS.StrongEps.E4R3.N4C
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.N4C.rows.rowsN2b =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology

namespace Work.FTS.StrongEps.E4R3.N4C.rows

open Work.FTS.Galerkin (Fn)
open Work.FTS.VocabO (HQo)
open Work.FTS.Nonlinear.Open

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Row 14: `N₂^{sg} = -2·𝒰(Φ̃_*)·∂_θg` -/

/-- **Row 14 of the honest §8 table** (pairing bound only): for every honest context,

  `|IP α (N₂^{sg} α Φs g) g| ≤ K·√α·(Xn α g)²`.

Constant `K = 2·(CW·(Ct·max Cs 0)) + 1`, with `CW` the constant of
`OpenPkg.WDp_le_WlInf`. -/
theorem rowN2sgHon (IP : ℝ → Fn → Fn → ℝ) {α₂ Ci Ct Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α Ce : ℝ} {g Φs Φg : Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      |IP α (Work.FTS.Nonlin.N2sg α Φs g) g|
        ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2) := by
  obtain ⟨CW, hCW0, hCW⟩ := Work.FTS.OpenPkg.WDp_le_WlInf
  obtain ⟨hCt, _hα₂⟩ := hE.pos
  refine ⟨2 * (CW * (Ct * max Cs 0)) + 1, ?_, ?_⟩
  · have h1 : 0 ≤ CW * (Ct * max Cs 0) :=
      mul_nonneg hCW0.le (mul_nonneg hCt.le (le_max_right Cs 0))
    linarith
  · intro α Ce g Φs Φg hctx
    have hα : 0 < α := hctx.hα
    have hα1 : α ≤ 1 := hctx.hα1
    have hαα₂ : α ≤ α₂ := hctx.hαα₂
    have hαIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
    have hs2 : Work.FTS.VocabO2.StarPkgo2 α Cs Φs := hctx.hs
    have hs : Work.FTS.VocabO.StarPkgo α Cs Φs := hs2.toStarPkgo
    have hSmG : Work.FTS.EllipticEst.SmoothOpen g := hctx.hSmoothOpen
    have hqo4 : HQo α 4 g := hctx.hqo4
    have hmem4 : Work.Spaces.HkMem α 4 g := hctx.hkMem4
    have hmem5 : Work.Spaces.HkMem α 5 g := hctx.hkMem5
    have hdec : Work.Spaces.DecayAll 4 g := hctx.hdecay
    -- the coefficient `Ǔ = 𝒰(Φ̃_*)/sin 2θ` priced by `StarPkgo2.UsW`
    set Uv : Fn := fun z θ =>
      Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Work.Construction.s2 θ with hUv
    have hUvmem : Work.Spaces.WlInfMem α 4 Uv := by
      rw [hUv]; exact hs2.UsW.1
    have hUvle : Work.Spaces.WlInf α 4 Uv ≤ Cs * α := by
      rw [hUv]; exact hs2.UsW.2
    have hΦ : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.PhiTs α Φs) :=
      Work.FTS.NonlinRows.NRow10aux.smoothOpen_PhiTs hα hα1 hs
    have hUopsm : Work.FTS.EllipticEst.SmoothOpen
        (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) := by
      rw [Work.FTS.EllipticEst.Uop_eq]
      exact Work.FTS.EllipticEst.smoothOpen_Uop hΦ
    have hUvsm : Work.FTS.EllipticEst.SmoothOpen Uv := by
      rw [hUv]
      exact Work.FTS.EllipticEst.RPFresh.smoothOpen_div_sin hUopsm
    -- `D_θg` is honest
    have hDthSm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth g) := hSmG.Dth
    have hDthMem : Work.Spaces.HkMem α 4 (Work.Spaces.Dth g) := hctx.hkMemDth
    have hDthHQo : HQo α 4 (Work.Spaces.Dth g) := ⟨hDthSm, hDthMem⟩
    -- the honest product `Ǔ · D_θg`, by the `𝒲^{4,∞}`-product rule
    have hprod := hN.wprod α hαIoc Uv (Work.Spaces.Dth g) hUvsm hUvmem hDthHQo
    have hUvDth : HQo α 4 (fun z θ => Uv z θ * Work.Spaces.Dth g z θ) :=
      ⟨Work.FTS.StrongPersist.H6Pair6Aux.so_mul hUvsm hDthSm, hprod.1⟩
    have hUvDth2 : HQo α 4 (fun z θ => -2 * (Uv z θ * Work.Spaces.Dth g z θ)) :=
      Work.FTS.StrongEps.E4R3.N4C.goodO_const_mul (-2) hUvDth
    -- `Ǔ·D_θg = 𝒰(Φ̃_*)·∂_θg` on the open quadrant (both sides vanish at `θ = 0, π/2`)
    have hpt : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Work.Spaces.Iθ,
        (fun z θ => -2 * (Uv z θ * Work.Spaces.Dth g z θ)) z θ
          = Work.FTS.Nonlin.N2sg α Φs g z θ := by
      intro z _hz θ hθ
      have hv1 : Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z 0 = 0 := hs.vanishU.1 z
      have hv2 : Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z (Real.pi / 2) = 0 :=
        hs.vanishU.2 z
      have hsin : Real.sin (2 * (Real.pi / 2)) = 0 := by
        rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
      simp only [hUv, Work.FTS.Nonlin.N2sg, Work.Spaces.Dth, Work.Spaces.pth,
        Work.Construction.s2]
      rcases eq_or_lt_of_le hθ.1 with h0 | hpos
      · subst h0
        simp [hv1]
      · rcases eq_or_lt_of_le hθ.2 with hpi | hlt
        · subst hpi
          simp [hv2, hsin]
        · have hsne : Real.sin (2 * θ) ≠ 0 :=
            ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith)
              (by linarith [Real.pi_pos]))
          field_simp
    -- the honest class of `N₂^{sg}`
    have hN2sgQo : HQo α 4 (Work.FTS.Nonlin.N2sg α Φs g) :=
      Work.FTS.StrongEps.E4R3.N4C.goodO_of_eqOn_Qd hUvDth2
        (fun z θ hQd => hpt z hQd.1 θ ⟨le_of_lt hQd.2.1, le_of_lt hQd.2.2⟩)
    -- `WlInfMem` gives the `D`-sup membership, with the pointwise constant `200`
    have hWdMem : Work.FTS.VocabO.WDMem 4 Uv := by
      intro b j hbj
      refine ⟨200 * Work.Spaces.WlInf α 4 Uv, ?_⟩
      intro z θ hz hθ hθ2
      exact Work.FTS.OpenPkg.mixed_le_WlInf_200 hα hα1 hUvsm hUvmem hbj hz ⟨hθ, hθ2⟩
    -- the honest transport clause for a `D`-sup coefficient
    have ht4 := hE.t4 α hαIoc Uv g hUvsm hWdMem hSmG hmem4 hmem5 hdec
    have hWDp : Work.FTS.VocabO.WDp 4 Uv ≤ CW * Work.Spaces.WlInf α 4 Uv :=
      hCW α Uv hα hα1 hUvsm hUvmem
    have hXg : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
    have hsqrt : α ^ (-(1 / 2 : ℝ)) * α = Real.sqrt α := by
      rw [Real.sqrt_eq_rpow]
      have h := Real.rpow_add hα (-(1 / 2 : ℝ)) (1 : ℝ)
      rw [Real.rpow_one, show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] at h
      exact h.symm
    -- the pairing at the honest representative
    have hIPval : IP α (Work.FTS.Nonlin.N2sg α Φs g) g
        = -2 * IP α (fun z θ => Uv z θ * Work.Spaces.Dth g z θ) g := by
      have hsm := hE.smul α hαIoc (-2) (fun z θ => Uv z θ * Work.Spaces.Dth g z θ) g
        hUvDth hqo4
      have hcg := hE.congr α hαIoc (Work.FTS.Nonlin.N2sg α Φs g)
        (fun z θ => -2 * (Uv z θ * Work.Spaces.Dth g z θ)) g hN2sgQo hUvDth2 hqo4
        (fun z θ hQd => (hpt z hQd.1 θ ⟨le_of_lt hQd.2.1, le_of_lt hQd.2.2⟩).symm)
      rw [hcg, hsm]
    have hWlL : Work.Spaces.WlInf α 4 Uv ≤ max Cs 0 * α :=
      le_trans hUvle (mul_le_mul_of_nonneg_right (le_max_left Cs 0) hα.le)
    have hWDpL : Work.FTS.VocabO.WDp 4 Uv ≤ CW * (max Cs 0 * α) :=
      le_trans hWDp (mul_le_mul_of_nonneg_left hWlL hCW0.le)
    have hIPb : |IP α (fun z θ => Uv z θ * Work.Spaces.Dth g z θ) g|
        ≤ CW * Ct * max Cs 0 * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2) := by
      refine le_trans ht4 ?_
      have hA : 0 ≤ Ct * α ^ (-(1 / 2 : ℝ)) :=
        mul_nonneg hCt.le (Real.rpow_nonneg hα.le _)
      have hstep : Ct * α ^ (-(1 / 2 : ℝ)) * Work.FTS.VocabO.WDp 4 Uv
            * Work.FTS.Nonlin.Xn α g ^ 2
          ≤ Ct * α ^ (-(1 / 2 : ℝ)) * (CW * (max Cs 0 * α))
            * Work.FTS.Nonlin.Xn α g ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWDpL hA) (sq_nonneg _)
      refine le_trans hstep (le_of_eq ?_)
      rw [show Ct * α ^ (-(1 / 2 : ℝ)) * (CW * (max Cs 0 * α)) * Work.FTS.Nonlin.Xn α g ^ 2
          = CW * Ct * max Cs 0 * (α ^ (-(1 / 2 : ℝ)) * α)
            * Work.FTS.Nonlin.Xn α g ^ 2 from by ring, hsqrt]
      ring
    have hfin : 2 * |IP α (fun z θ => Uv z θ * Work.Spaces.Dth g z θ) g|
        ≤ (2 * (CW * (Ct * max Cs 0)) + 1)
          * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2) := by
      have hX2nn : 0 ≤ Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2 :=
        mul_nonneg (Real.sqrt_nonneg α) (sq_nonneg _)
      calc 2 * |IP α (fun z θ => Uv z θ * Work.Spaces.Dth g z θ) g|
          ≤ 2 * (CW * Ct * max Cs 0 * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2)) :=
            mul_le_mul_of_nonneg_left hIPb (by norm_num)
        _ = 2 * (CW * (Ct * max Cs 0)) * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2) := by ring
        _ ≤ (2 * (CW * (Ct * max Cs 0)) + 1)
              * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2) := by
            refine mul_le_mul_of_nonneg_right ?_ hX2nn
            linarith
    calc |IP α (Work.FTS.Nonlin.N2sg α Φs g) g|
        = |(-2) * IP α (fun z θ => Uv z θ * Work.Spaces.Dth g z θ) g| := by rw [hIPval]
      _ = 2 * |IP α (fun z θ => Uv z θ * Work.Spaces.Dth g z θ) g| := by
            rw [abs_mul, abs_of_neg (by norm_num : (-2 : ℝ) < 0)]; ring
      _ ≤ _ := hfin

/-! ## Row 15: `N₂^{ss} = -2·𝒰(Φ̃_*)·∂_θF_*` -/

/-- **Row 15 of the honest §8 table** (norm bound only): for every honest context,

  `Xn α (N₂^{ss} α Φs) ≤ K·α²`.

The proof is that of `Work.FTS.Nonlinear.Open.Row15` verbatim (the frozen proof never uses the
Galerkin class of `g` nor the `N4Extra'` clauses): it factors the piece as
`ψ(z)·(2·C15 α θ·G15 α Φs z θ)` and feeds the two pointwise families of
`Nonlinear.Open.Row15Aux.Bound` into `NonlinRows.wtoHQ_of_pointwise_open`, with the
`𝒲^{4,∞}`-coefficient `G15 α Φs` priced by the field `StarPkgo2.UszW`. -/
theorem rowN2ssHon (IP : ℝ → Fn → Fn → ℝ) {α₂ Ci Ct Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α Ce : ℝ} {g Φs Φg : Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N2ss α Φs) ≤ K * α ^ 2 := by
  obtain ⟨Cw, hCw, hwto⟩ := Work.FTS.NonlinRows.wtoHQ_of_pointwise_open
  obtain ⟨Cpsi, hCpsipos, hpsib⟩ := Work.FTS.NonlinRows.pzIter_psi15_le
  obtain ⟨KA, hKApos, hKAb0⟩ := dthU_iter_A15_flat_le
  obtain ⟨KB, hKBpos, hKBb0⟩ := dthU_iter_A15_weight_le
  refine ⟨Cw * (10 ^ 7 * Cpsi * (KA + KB + 1) + 1) * (max Cs 0) + 1, ?_, ?_⟩
  · have h1 : (0 : ℝ) < 10 ^ 7 * Cpsi * (KA + KB + 1) + 1 := by positivity
    have h2 : 0 ≤ Cw * (10 ^ 7 * Cpsi * (KA + KB + 1) + 1) * max Cs 0 :=
      mul_nonneg (mul_nonneg hCw.le h1.le) (le_max_right Cs 0)
    linarith
  · intro α Ce g Φs Φg hctx
    have hα : 0 < α := hctx.hα
    have hα1 : α ≤ 1 := hctx.hα1
    have hs2 : Work.FTS.VocabO2.StarPkgo2 α Cs Φs := hctx.hs
    have hs : Work.FTS.VocabO.StarPkgo α Cs Φs := hs2.toStarPkgo
    have hGm : Work.Spaces.WlInfMem α 4 (Work.FTS.NonlinRows.G15 α Φs) := hs2.UszW.1
    have hGle : Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs) ≤ Cs * α := hs2.UszW.2
    have hΛ : 0 ≤ Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs) :=
      Work.FTS.H2.WlInf_nonneg hGm
    have hΛle : Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs) ≤ max Cs 0 * α :=
      le_trans hGle (mul_le_mul_of_nonneg_right (le_max_left Cs 0) hα.le)
    obtain ⟨hSO, hAfam, hBfam⟩ := row15_pointwise hα hα1 hs hKApos.le hKBpos.le hCpsipos
      (fun c m hcm hm z hz θ => hpsib c m hcm hm z hz θ)
      (fun a ha θ hθ => hKAb0 α hα hα1 a ha θ hθ)
      (fun a ha θ hθ => hKBb0 α hα hα1 a ha θ hθ)
      (Work.FTS.NonlinRows.smoothOpen_G15 hα hα1 hs) hGm
    set CW : ℝ := 10 ^ 7 * Cpsi * (KA + KB + 1) + 1 with hCW
    set Λ : ℝ := Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs) with hΛdef
    set W : ℝ := CW * α * Λ with hWdef
    have hCW0 : 0 < CW := by rw [hCW]; positivity
    have hW0 : 0 ≤ W := by
      rw [hWdef]; exact mul_nonneg (mul_nonneg hCW0.le hα.le) hΛ
    obtain ⟨_hmem, hxn⟩ := hwto α (Work.FTS.Nonlin.N2ss α Φs) W hα hα1 hW0 hSO
      (fun m hm z hz θ hθ => by
        have := hAfam m hm z hz θ hθ
        rwa [hWdef, hCW, hΛdef] at this)
      (fun i l hi hli z hz θ hθ => by
        have := hBfam i l hi hli z hz θ hθ
        rwa [hWdef, hCW, hΛdef] at this)
    have hX : W ≤ CW * (max Cs 0) * α ^ 2 := by
      rw [hWdef, hΛdef]
      have hstep : α * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)
          ≤ α * (max Cs 0 * α) := mul_le_mul_of_nonneg_left hΛle hα.le
      calc CW * α * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)
          = CW * (α * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)) := by ring
        _ ≤ CW * (α * (max Cs 0 * α)) := mul_le_mul_of_nonneg_left hstep hCW0.le
        _ = CW * (max Cs 0) * α ^ 2 := by ring
    have h1 : Cw * W ≤ Cw * (CW * (max Cs 0) * α ^ 2) :=
      mul_le_mul_of_nonneg_left hX hCw.le
    have h2 : Cw * (CW * (max Cs 0) * α ^ 2)
        ≤ (Cw * (10 ^ 7 * Cpsi * (KA + KB + 1) + 1) * (max Cs 0) + 1) * α ^ 2 := by
      rw [hCW]
      have h4 : (0 : ℝ) ≤ Cw * (10 ^ 7 * Cpsi * (KA + KB + 1) + 1) * max Cs 0 :=
        mul_nonneg (mul_nonneg hCw.le (by positivity)) (le_max_right Cs 0)
      have h5 : 0 ≤ α ^ 2 := sq_nonneg α
      nlinarith
    exact hxn.trans (h1.trans h2)

/-! ## The target -/

theorem rowsN2b (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      |IP α (Work.FTS.Nonlin.N2sg α Φs g) g| ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N2ss α Φs) ≤ K * α ^ 2 := by
  obtain ⟨K1, hK1, h1⟩ := rowN2sgHon IP hN hE
  obtain ⟨K2, hK2, h2⟩ := rowN2ssHon IP hN hE
  refine ⟨max K1 K2, lt_of_lt_of_le hK1 (le_max_left K1 K2), ?_⟩
  intro α g Φs Φg hctx
  refine ⟨?_, ?_⟩
  · refine (h1 hctx).trans (mul_le_mul_of_nonneg_right (le_max_left K1 K2) ?_)
    exact mul_nonneg (Real.sqrt_nonneg α) (sq_nonneg _)
  · exact (h2 hctx).trans (mul_le_mul_of_nonneg_right (le_max_right K1 K2) (sq_nonneg α))

end Work.FTS.StrongEps.E4R3.N4C.rows
end
-- ===== merged: Submission.Work.FTS.StrongEps.smoothOpen_epsWP =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Submission/Work/FTS/StrongEps/smoothOpen_epsWP.lean`

**Target.** `Work.FTS.StrongEps.smoothOpen_epsWP`: the pre-mollified right-hand side

  `epsWP α ρ ε Φs E g s = 𝓛_{Γ}^{T}(slice (JfamP ρ ε g) s) + gRHS(μ̄,λ, F_* + slice (JfamP ρ ε g) s,
   slice (PsiCan Φs E (JfamP ρ ε g)) s, slice (JfamP ρ ε g) s)`

of the `P₀`-corrected `ε`-scheme is `C^∞` on the open quadrant `(0,∞) × (0,π/2)`, for every
fake time `s ∈ [0,T]`, **assuming**

* `hC` : the projected slices `slice (JfamP ρ ε g) s` lie in the class `ClassC α` (i.e. they are
  open-quadrant smooth and `ℋ^{10}`-honest),
* `hEll` : the elliptic solution operator `E` returns an `EllPkgGo`-package at the class-`C`
  profiles,
* `hstar` : the star package `StarPkgo2 α Cs Φs` of the datum `Φs`.

## The proof

`epsWP = dynLin + dynRHS` definitionally, so it suffices to treat the two summands.

* **The linear part** `dynLin = -𝓛_Γ^T(w)`, `w := slice (JfamP ρ ε g) s`: the third conjunct of
  `ClassCRHS.SmoothOpenRHS` (the module that assembles the atoms of the right-hand side from the
  class-`C` data) is exactly `SmoothOpen (𝓛_Γ^T w)`.
* **The nonlinear part** `dynRHS`: here the useful general form is
  `smoothOpen_gRHS_gen`, whose hypotheses are the *atoms* of `gRHS` in exactly the shape in which
  `SmoothOpenRHS` delivers them: `F = F_* + w`, `Φ = Φs + E w = slice (PsiCan Φs E (JfamP …)) s`,
  the radial moments `L₁₂(w)`, `L₁₂(F)`, `FK(F)`, and the three transported coefficients
  `ℛ(Φ̃)`, `𝒰(Φ̃)`, `𝒱(Φ̃)` of the residual `Φ̃ = PhiTil α F Φ`.  The last three are produced here
  from `SmoothOpen (PhiTil α F Φ)` (which is `Φ - (1/(4α))·sin 2θ ·L₁₂(F)`) with
  `smoothOpen_Rop` / `EllipticEst.smoothOpen_Uop` / `smoothOpen_Vop`.

Everything is `SmoothOpen`-API plus definitional unfolding: `Ftau α (JfamP ρ ε g) s` and
`Ftot α (slice (JfamP ρ ε g) s)` are the same function, `slice (PsiCan Φs E (JfamP ρ ε g)) s` is
`fun z θ => Φs z θ + E (slice (JfamP ρ ε g) s) z θ`, and `gRHS`/`muDyn`/`lamDyn` unfold to the
`dynRHS` of `Work.FTS.Galerkin`.
-/

namespace Work.FTS.StrongEps

open Work.FTS.EllipticEst (SmoothOpen)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **The nonlinear part of the `P₀`-corrected `ε`-scheme is `C^∞` on the open quadrant.**

This is `smoothOpen_gRHS_gen` at the profile `F = F_* + w` and the stream function
`Φs + E w`, where `w := slice (JfamP ρ ε g) s` is the projected slice at the fake time `s`; the
modulation constants `μ̄`, `λ` are irrelevant (they are numbers).  All atoms come from
`ClassCRHS.SmoothOpenRHS`; the coefficient atoms `ℛ`, `𝒰`, `𝒱` are built here from the
open-quadrant smoothness of the residual `PhiTil α F Φ`. -/
theorem smoothOpen_dynRHS_of_classC {α Ce Cs ε : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam} {s : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hw : Work.FTS.ClassC.ClassC α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s))
    (hell : Work.FTS.VocabO.EllPkgGo α Ce
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s)
      (E (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s)))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    SmoothOpen
      (Work.FTS.Galerkin.dynRHS α (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g))
        (Work.FTS.StrongEps.JfamP ρ ε g) s) := by
  -- ### the atoms of the right-hand side, in `SmoothOpen` normal form
  obtain ⟨hL12F, hFKF, hLG, hN0, hN⟩ :=
    Work.FTS.StrongEps.ClassCRHS.SmoothOpenRHS hα0 hα1 hw hell hstar
  -- the radial moment of the perturbation (`N₀` is evaluated at `w`, not at `F`)
  have hL12w : SmoothOpen (fun z _ => Work.Construction.L12
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s) z) :=
    Work.FTS.NonlinRows.smoothOpen_L12_radial hα0 hell.smooth hell.V.1.1
  -- the full profile `F = F_* + w` and the stream function `Φs + E w`
  have hF : SmoothOpen
      (Work.Construction.Ftot α (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s)) :=
    Work.FTS.NonlinRows.smoothOpen_add
      (Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)) hw.reg
  have hPhi : SmoothOpen
      (fun z θ => Φs z θ + E (Work.FTS.Galerkin.slice
        (Work.FTS.StrongEps.JfamP ρ ε g) s) z θ) :=
    Work.FTS.NonlinRows.smoothOpen_add hstar.smooth hell.smooth
  -- ### the residual `Φ̃ = Φ - Θ = Φ - (1/(4α))·sin 2θ·L₁₂(F)`
  have hTheta : SmoothOpen (fun z θ => (1 / (4 * α)) * Work.Construction.s2 θ
      * Work.Construction.L12 (Work.Construction.Ftot α
          (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s)) z) :=
    Work.FTS.NonlinRows.smoothOpen_mul
      (Work.FTS.NonlinRows.smoothOpen_const_mul (1 / (4 * α))
        Work.FTS.GalFields.RHS.smoothOpen_sin_two) hL12F
  have hPsi : SmoothOpen (Work.Construction.PhiTil α (Work.Construction.Ftot α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s))
      (fun z θ => Φs z θ + E (Work.FTS.Galerkin.slice
        (Work.FTS.StrongEps.JfamP ρ ε g) s) z θ)) :=
    hPhi.sub hTheta
  -- ### the three transported coefficients `ℛ`, `𝒰`, `𝒱` of `Φ̃`
  have hR : SmoothOpen (Work.Construction.Rop α (Work.Construction.PhiTil α
      (Work.Construction.Ftot α (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s))
      (fun z θ => Φs z θ + E (Work.FTS.Galerkin.slice
        (Work.FTS.StrongEps.JfamP ρ ε g) s) z θ))) :=
    Work.FTS.NonlinRows.smoothOpen_Rop hPsi
  have hU : SmoothOpen (Work.Construction.Uop α (Work.Construction.PhiTil α
      (Work.Construction.Ftot α (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s))
      (fun z θ => Φs z θ + E (Work.FTS.Galerkin.slice
        (Work.FTS.StrongEps.JfamP ρ ε g) s) z θ))) :=
    Work.FTS.EllipticEst.smoothOpen_Uop hPsi
  have hV : SmoothOpen (Work.Construction.Vop (Work.Construction.PhiTil α
      (Work.Construction.Ftot α (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s))
      (fun z θ => Φs z θ + E (Work.FTS.Galerkin.slice
        (Work.FTS.StrongEps.JfamP ρ ε g) s) z θ))) :=
    Work.FTS.NonlinRows.smoothOpen_Vop hPsi
  -- ### assembly: the general form of the right-hand side, at the modulation constants
  exact smoothOpen_gRHS_gen (α := α)
    (μ := Work.FTS.Galerkin.muDyn α
      (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g))
      (Work.FTS.StrongEps.JfamP ρ ε g) s)
    (lam := Work.FTS.Galerkin.lamDyn α
      (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g))
      (Work.FTS.StrongEps.JfamP ρ ε g) s)
    (F := Work.Construction.Ftot α (Work.FTS.Galerkin.slice
      (Work.FTS.StrongEps.JfamP ρ ε g) s))
    (Φ := fun z θ => Φs z θ + E (Work.FTS.Galerkin.slice
      (Work.FTS.StrongEps.JfamP ρ ε g) s) z θ)
    (gg := Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s)
    hF hw.reg hL12w hFKF hR hU hV

theorem smoothOpen_epsWP {α C₀ Ce Cs T : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam} {ε : ℝ}
    (hα : α ∈ Set.Ioc 0 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hC : ∀ s ∈ Set.Icc 0 T, Work.FTS.ClassC.ClassC α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s)) :
    ∀ s ∈ Set.Icc 0 T, Work.FTS.EllipticEst.SmoothOpen
      (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s) := by
  intro s hs
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  -- the projected slice at the fake time `s` is in the class `C`, and `E` returns its package
  have hw : Work.FTS.ClassC.ClassC α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s) := hC s hs
  have hell : Work.FTS.VocabO.EllPkgGo α Ce
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s)
      (E (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s)) := (hEll _ hw).1
  -- the linear part `dynLin = -𝓛_Γ^T(w)`
  have hlin : SmoothOpen (Work.FTS.Galerkin.dynLin α (Work.FTS.StrongEps.JfamP ρ ε g) s) :=
    (Work.FTS.StrongEps.ClassCRHS.SmoothOpenRHS hα0 hα1 hw hell hstar).2.2.1.neg
  -- the nonlinear part `dynRHS`
  have hdyn : SmoothOpen (Work.FTS.Galerkin.dynRHS α
      (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g))
      (Work.FTS.StrongEps.JfamP ρ ε g) s) :=
    smoothOpen_dynRHS_of_classC hα0 hα1 hw hell hstar
  -- `epsWP` is definitionally the sum of the two
  exact Work.FTS.NonlinRows.smoothOpen_add hlin hdyn

end Work.FTS.StrongEps
end
