import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.GalFields.RHS.HkSum
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.Nonlinear.Open.Row25Aux
import Submission.Work.FTS.Nonlinear.Pieces.RNP.RNP24.dzdIter_FK_eq_qang
import Submission.Work.FTS.OpenPkg.Pieces4
import Submission.Work.FTS.OpenPkg.prod_field
import Submission.Work.FTS.StrongEps.SupPort.classC_sup_le
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.H6Row6.fkFacts7
import Submission.Work.FTS.StrongPersist.H6Rows.NZaux.L12AddFstar
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsNstarBlock
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsRadAux.aestronglyMeasurable_slotSum
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundCore
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundE
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundR
import Submission.Work.FTS.StrongPersist.Star6
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.TransportS.T2Sup.GenSlot
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_RegExport.RXA1w.Helpers
import Submission.Work.FTS_RegExport.RXT.Sys.abs_L12dens_Fstar_add_le
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_z
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_RegExport.THL.vopPert_theta_holder
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
-- ===== merged: Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnNCore =====
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

theorem nb_data {α : ℝ} (hαmem : α ∈ Set.Ioc 0 1) {C₀ B Ce Cs C1 C2 : ℝ} {Φs : Fn}
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
    ∃ Kbig : ℝ, 0 < Kbig ∧ ∀ {w Φg : Fn},
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
  intro w Φg hw hXw hB hell hstar
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
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.NB4Aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `N_aux.NB4Aux` — the α-absorption helpers for the level-`4` pricing of `blkN`

This file is the toolbox for the per-piece `ℋ⁴`-pricing of the twenty pieces
`Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k` (the `b4` field of `BData α w K (blkN …)`).

The two product rules of the tree have an explicit `α ^ (-1/2)` in front:

* `Work.FTS.OpenPkg.prod_field`: `Xn α (f·g) ≤ Cp·α^{-1/2}·Xn α f·Xn α g`;
* `Work.FTS.OpenPkg.wprod_field_winf`: `Xn α (f·g) ≤ Cw·α^{-1/2}·WlInf α 4 f·Xn α g`.

In every one of the twenty pieces one of the two factors is *`α`-small* — its price carries a
genuine factor `α` (`α¹` for the `𝒲^{4,∞}` star coefficients `Cs·α` and the `hKer` atom `400α`,
`α²` for the perturbed coefficients `Ce·C₀·α²`, the `φ`-multiplications and `FK w`).  So the
`α^{-1/2}` is absorbed:

  `α^{-1/2} · (b·α^s) ≤ b`  for `α ∈ (0,1]`, `s ≥ 1`.

That is the content of `mulQo_absorb` and `mulW_absorb` below: they take the price of the
coefficient in the *normalized* form `bA · α ^ s` (`s ≥ 1`, `bA` independent of `α`) together with
the price `Q` of the factor, and return a bound with the α-free constant `|c|·Cprod·bA·Q`
respectively `|c|·Cw·bF·Q`.

`Xn_w_slots_le` records the three prices of the `w`-slots met in the pieces that *do* grow with
`HkNorm α 5 w` (the shifted slots `D_θw`, `D_zw`, and `w` itself).

`exists_neg_sinSq_mul` is the `-sin²θ`-multiplication used by the pieces 16–19.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The absorption of the `α^{-1/2}` of the product rule against an `α`-small coefficient:
`α^{-1/2}·α^s ≤ 1` for `α ∈ (0,1]`, `s ≥ 1`. -/
theorem rpow_neg_half_mul_nat_le_one {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {s : ℕ} (hs : 1 ≤ s) :
    α ^ (-(1 / 2 : ℝ)) * α ^ s ≤ 1 := by
  have h1 : α ^ (-(1 / 2 : ℝ)) * α ^ s = α ^ (-(1 / 2 : ℝ) + (s : ℝ)) := by
    rw [← Real.rpow_natCast α s, ← Real.rpow_add hα]
  rw [h1]
  refine Real.rpow_le_one hα.le hα1 ?_
  have hs' : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  linarith

/-- **The `ℋ⁴`-product rule with an `α`-small `ℋ⁴`-coefficient.**  If `Xn α A ≤ bA · α^s` with
`s ≥ 1` and `Xn α P ≤ Q`, then `c·(A·P)` is `ℋ⁴`-honest with `Xn α (c·(A·P)) ≤ |c|·Cprod·bA·Q`:
the `α^{-1/2}` of `prod_field` is absorbed by the `α`-smallness of `A`. -/
theorem mulQo_absorb {α Cprod : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCprod : 0 < Cprod)
    (hfield : ∀ f g : Fn, Work.FTS.VocabO.HQo α 4 f → Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ Cprod * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g)
    {c bA Q : ℝ} {s : ℕ} (hs : 1 ≤ s) (hbA : 0 ≤ bA) (hQ : 0 ≤ Q)
    {A P : Fn} (hA : Work.FTS.VocabO.HQo α 4 A) (hP : Work.FTS.VocabO.HQo α 4 P)
    (hAb : Work.FTS.Nonlin.Xn α A ≤ bA * α ^ s) (hPb : Work.FTS.Nonlin.Xn α P ≤ Q) :
    Work.Spaces.HkMem α 4 (fun z θ => c * (A z θ * P z θ)) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => c * (A z θ * P z θ)) ≤ |c| * Cprod * bA * Q := by
  obtain ⟨hm, hb⟩ :=
    Work.FTS.StrongEps.ClassCRHS.mulHQo hα hCprod hfield
      (mul_nonneg hbA (by positivity)) (by positivity) hA hP hAb hPb
  refine ⟨hm, ?_⟩
  refine le_trans hb ?_
  have hkey := rpow_neg_half_mul_nat_le_one hα hα1 hs
  have hstep : |c| * Cprod * α ^ (-(1 / 2 : ℝ)) * (bA * α ^ s) * Q
      = (|c| * Cprod * bA * Q) * (α ^ (-(1 / 2 : ℝ)) * α ^ s) := by ring
  rw [hstep]
  simpa using mul_le_of_le_one_right
    (mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg c) hCprod.le) hbA) hQ) hkey

/-- **The `ℋ⁴`-product rule with an `α`-small `𝒲^{4,∞}`-coefficient.**  The `WlInf`-analogue of
`mulQo_absorb`, through `wprod_field_winf`. -/
theorem mulW_absorb {α Cw : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCw : 0 < Cw)
    (hfield : ∀ f g : Fn, Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 4 f →
      Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ Cw * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f * Work.FTS.Nonlin.Xn α g)
    {c bF Q : ℝ} {s : ℕ} (hs : 1 ≤ s) (hbF : 0 ≤ bF) (hQ : 0 ≤ Q)
    {F G : Fn} (hFs : Work.FTS.EllipticEst.SmoothOpen F) (hFm : Work.Spaces.WlInfMem α 4 F)
    (hG : Work.FTS.VocabO.HQo α 4 G)
    (hFb : Work.Spaces.WlInf α 4 F ≤ bF * α ^ s) (hGb : Work.FTS.Nonlin.Xn α G ≤ Q) :
    Work.Spaces.HkMem α 4 (fun z θ => c * (F z θ * G z θ)) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => c * (F z θ * G z θ)) ≤ |c| * Cw * bF * Q := by
  obtain ⟨hm, hb⟩ :=
    Work.FTS.StrongEps.ClassCRHS.mulW hα hCw hfield
      (mul_nonneg hbF (by positivity)) (by positivity) hFs hFm hFb hG hGb
  refine ⟨hm, ?_⟩
  refine le_trans hb ?_
  have hkey := rpow_neg_half_mul_nat_le_one hα hα1 hs
  have hstep : |c| * Cw * α ^ (-(1 / 2 : ℝ)) * (bF * α ^ s) * Q
      = (|c| * Cw * bF * Q) * (α ^ (-(1 / 2 : ℝ)) * α ^ s) := by ring
  rw [hstep]
  simpa using mul_le_of_le_one_right
    (mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg c) hCw.le) hbF) hQ) hkey

/-- **The three `w`-slot prices**: `w`, `D_θw = sin(2θ)∂_θw` and `D_zw` are all priced by
`1 + HkNorm α 5 w` (`w` by monotonicity of the level, the other two by the level-shift theorems
`Xn_Dth_le_Xn5`/`Xn_Dz_le_Xn5`). -/
theorem Xn_w_slots_le {α : ℝ} {w : Fn} (hα : 0 < α) (hreg : Work.FTS.EllipticEst.SmoothOpen w)
    (hm5 : Work.Spaces.HkMem α 5 w) :
    Work.FTS.Nonlin.Xn α w ≤ 1 + Work.Spaces.HkNorm α 5 w ∧
      Work.FTS.Nonlin.Xn α (Work.Spaces.Dth w) ≤ 1 + Work.Spaces.HkNorm α 5 w ∧
      Work.FTS.Nonlin.Xn α (Work.Spaces.Dz w) ≤ 1 + Work.Spaces.HkNorm α 5 w := by
  have hmono : Work.Spaces.HkSq α 4 w ≤ Work.Spaces.HkSq α 5 w :=
    Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (Nat.le_succ 4) hm5
  have h4 : Work.FTS.Nonlin.Xn α w ≤ Work.Spaces.HkNorm α 5 w := by
    show Real.sqrt (Work.Spaces.HkSq α 4 w) ≤ Real.sqrt (Work.Spaces.HkSq α 5 w)
    exact Real.sqrt_le_sqrt hmono
  have h5 : Work.FTS.Nonlin.Xn α (Work.Spaces.Dth w) ≤ Work.Spaces.HkNorm α 5 w :=
    Work.FTS.GalFields.Xn_Dth_le_Xn5 hα hm5
  have h6 : Work.FTS.Nonlin.Xn α (Work.Spaces.Dz w) ≤ Work.Spaces.HkNorm α 5 w :=
    Work.FTS.GalFields.Xn_Dz_le_Xn5 hα hreg hm5
  have hnn : 0 ≤ Work.Spaces.HkNorm α 5 w := Real.sqrt_nonneg _
  exact ⟨by linarith, by linarith, by linarith⟩

/-- **Angular multiplication by `-sin²θ`** in `ℋ⁴`, with an `α`-free constant, at level `4`
(the profile `θ ↦ -sin²θ` is bounded by `192` on `Iθ` with all `D_θ`-iterates up to order `4`
bounded by `192·sin 2θ`). -/
theorem exists_neg_sinSq_mul :
    ∃ C : ℝ, 0 < C ∧ ∀ ⦃α : ℝ⦄, 0 < α → α ≤ 1 → ∀ ⦃f : Fn⦄,
      Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.VocabO.HQo α 4 f →
      Work.Spaces.HkMem α 4 (fun z θ => -(Real.sin θ) ^ 2 * f z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => -(Real.sin θ) ^ 2 * f z θ)
        ≤ C * Work.FTS.Nonlin.Xn α f := by
  obtain ⟨Cang, hCang, hang⟩ := Work.FTS.StrongPersist.L3Rhs.ang_mul_HkSq_le 4
  obtain ⟨Bsin, hBsin, -, hBB, hBit⟩ :=
    Work.FTS.Nonlinear.Pieces.RNP.RNP24.angProfile_sinSq
  have hCsin_pos : 0 < Real.sqrt (Cang * Bsin ^ 2) := Real.sqrt_pos.2 (by positivity)
  refine ⟨Real.sqrt (Cang * Bsin ^ 2), hCsin_pos, ?_⟩
  intro α hα hα1 f hfs hfm
  have hmem := hang α hα hα1 (fun θ => -(Real.sin θ) ^ 2) Bsin hBsin
    Work.FTS.Nonlinear.Open.row25_smoothOpen_neg_sinSq (fun θ hθ => hBB θ hθ)
    (fun i hi hi4 θ hθ => hBit i hi hi4 θ hθ) f hfs hfm.2
  obtain ⟨hm, hsq⟩ := hmem
  refine ⟨hm, ?_⟩
  have hann : 0 ≤ Cang * Bsin ^ 2 := by positivity
  calc Work.FTS.Nonlin.Xn α (fun z θ => -(Real.sin θ) ^ 2 * f z θ)
      = Real.sqrt (Work.Spaces.HkSq α 4 (fun z θ => -(Real.sin θ) ^ 2 * f z θ)) := rfl
    _ ≤ Real.sqrt (Cang * Bsin ^ 2 * Work.Spaces.HkSq α 4 f) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (Cang * Bsin ^ 2) * Work.Spaces.HkNorm α 4 f := by
        rw [Real.sqrt_mul hann, Work.Spaces.HkNorm]
    _ = Real.sqrt (Cang * Bsin ^ 2) * Work.FTS.Nonlin.Xn α f := rfl

/-! ## Two convenience lemmas for the `K · (1 + HkNorm α 5 w)` pricing -/

/-- `1 ≤ 1 + HkNorm α 5 w`. -/
theorem one_le_one_add_HkNorm5 {α : ℝ} {w : Fn} :
    (1 : ℝ) ≤ 1 + Work.Spaces.HkNorm α 5 w := by
  have h : (0 : ℝ) ≤ Work.Spaces.HkNorm α 5 w := by
    rw [Work.Spaces.HkNorm]; exact Real.sqrt_nonneg _
  linarith

/-- `0 ≤ 1 + HkNorm α 5 w`. -/
theorem zero_le_G {α : ℝ} {w : Fn} : (0 : ℝ) ≤ 1 + Work.Spaces.HkNorm α 5 w :=
  le_trans zero_le_one one_le_one_add_HkNorm5

/-- **Weakening a constant bound to `K·(1 + HkNorm α 5 w)`.** -/
theorem le_mul_G {α : ℝ} {w : Fn} {x K : ℝ} (h : x ≤ K) (hK : 0 ≤ K) :
    x ≤ K * (1 + Work.Spaces.HkNorm α 5 w) := by
  calc x ≤ K := h
    _ = K * 1 := (mul_one K).symm
    _ ≤ K * (1 + Work.Spaces.HkNorm α 5 w) :=
        mul_le_mul_of_nonneg_left one_le_one_add_HkNorm5 hK

/-- `C·α^s ≤ C` for `α ∈ (0,1]`, `0 ≤ C`. -/
theorem mul_pow_le_self {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) {C : ℝ} (hC : 0 ≤ C) (s : ℕ) :
    C * α ^ s ≤ C := by
  have h1 : α ^ s ≤ (1 : ℝ) ^ s := pow_le_pow_left₀ hα0.le hα1 s
  simp only [one_pow] at h1
  calc C * α ^ s ≤ C * 1 := mul_le_mul_of_nonneg_left h1 hC
    _ = C := mul_one C

/-! ## The pricing context of the twenty pieces

`NB4Ctx C C₀ Ce Cs α Φs w Φg` collects, at a single `α`-free constant `C ≥ 1`, all the
factor/coefficient data consumed by the twenty per-piece estimates of `NBlk`:

* the two product rules, normalized (`Cprod`, `Cw ≤ C`);
* the three `w`-slots, priced by `1 + HkNorm α 5 w`, and the three `φ = z/(1+z)`-scaled ones,
  priced by `C·(1 + HkNorm α 5 w)`;
* the perturbed coefficients `Rop Φ̃_g`, `Uop Φ̃_g/sin 2θ`, `Vop Φ̃_g` and `FK w`, each
  `α²`-small (`≤ C·α²`) — this is the smallness that absorbs the `α^{-1/2}` of the product rules;
* `-(2α)·hKer` and the three `(z+1)/z`-weighted star coefficients, each `𝒲^{4,∞}`-small
  (`≤ C·α`);
* the fixed `F_*`-atoms (`F_*`, `D_θF_*`, `D_zF_*` with `𝒲^{4,∞}`-prices `Cα`, `Cα²`, `Cα`), the
  three `φ`-scaled `F_*`-atoms and the two fixed `FK(F_*)`-products (priced by the constant `C`);
* the `-sin²θ`-multiplication.

`NB4Ctx` is designed so that every piece `NBlk k` is priced by a single application of
`mulQo_absorb`/`mulW_absorb` (resp. of `hSinMul`), with the *factor*'s price passed in as the
`Q`-argument. -/
structure NB4Ctx (C : ℝ) (C₀ Ce Cs : ℝ) (α : ℝ) (Φs w Φg : Fn) : Prop where
  hα0 : 0 < α
  hα1 : α ≤ 1
  hCpos : 0 < C
  hCone : 1 ≤ C
  /-- the `ℋ⁴ × ℋ⁴` product rule, with the α-free constant `C` -/
  hPQo : ∀ f g : Fn, Work.FTS.VocabO.HQo α 4 f → Work.FTS.VocabO.HQo α 4 g →
    Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
    Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
      ≤ C * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g
  /-- the `𝒲^{4,∞} × ℋ⁴` product rule, with the α-free constant `C` -/
  hPW : ∀ f g : Fn, Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 4 f →
    Work.FTS.VocabO.HQo α 4 g →
    Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
    Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
      ≤ C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f * Work.FTS.Nonlin.Xn α g
  -- the `w`-slots
  wqo : Work.FTS.VocabO.HQo α 4 w
  dthwqo : Work.FTS.VocabO.HQo α 4 (Work.Spaces.Dth w)
  dzwqo : Work.FTS.VocabO.HQo α 4 (Work.Spaces.Dz w)
  wX : Work.FTS.Nonlin.Xn α w ≤ 1 + Work.Spaces.HkNorm α 5 w
  dthwX : Work.FTS.Nonlin.Xn α (Work.Spaces.Dth w) ≤ 1 + Work.Spaces.HkNorm α 5 w
  dzwX : Work.FTS.Nonlin.Xn α (Work.Spaces.Dz w) ≤ 1 + Work.Spaces.HkNorm α 5 w
  phiwqo : Work.FTS.VocabO.HQo α 4 (fun z θ => z / (1 + z) * w z θ)
  phiDthwqo : Work.FTS.VocabO.HQo α 4 (fun z θ => z / (1 + z) * Work.Spaces.Dth w z θ)
  phiDzwqo : Work.FTS.VocabO.HQo α 4 (fun z θ => z / (1 + z) * Work.Spaces.Dz w z θ)
  phiwX : Work.FTS.Nonlin.Xn α (fun z θ => z / (1 + z) * w z θ)
    ≤ C * (1 + Work.Spaces.HkNorm α 5 w)
  phiDthwX : Work.FTS.Nonlin.Xn α (fun z θ => z / (1 + z) * Work.Spaces.Dth w z θ)
    ≤ C * (1 + Work.Spaces.HkNorm α 5 w)
  phiDzwX : Work.FTS.Nonlin.Xn α (fun z θ => z / (1 + z) * Work.Spaces.Dz w z θ)
    ≤ C * (1 + Work.Spaces.HkNorm α 5 w)
  -- the perturbed coefficients (`α²`-small)
  Rsm : Work.FTS.EllipticEst.SmoothOpen
    (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg))
  Rqo : Work.FTS.VocabO.HQo α 4 (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg))
  RX : Work.FTS.Nonlin.Xn α (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg)) ≤ C * α ^ 2
  Usm : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
    Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α w Φg) z θ / Work.Construction.s2 θ)
  Uqo : Work.FTS.VocabO.HQo α 4 (fun z θ =>
    Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α w Φg) z θ / Work.Construction.s2 θ)
  UX : Work.FTS.Nonlin.Xn α (fun z θ =>
    Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α w Φg) z θ / Work.Construction.s2 θ) ≤ C * α ^ 2
  Vsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg))
  Vqo : Work.FTS.VocabO.HQo α 4 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg))
  VX : Work.FTS.Nonlin.Xn α (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg)) ≤ C * α ^ 2
  FKwsm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.FK w z)
  FKwqo : Work.FTS.VocabO.HQo α 4 (fun z _ => Work.Construction.FK w z)
  FKwX : Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.FK w z) ≤ C * α ^ 2
  -- `-(2α)·hKer` (`α`-small, `𝒲^{4,∞}`)
  FKnegsm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => (-(2 * α)) * Work.Spaces.hKer z)
  FKnegWm : Work.Spaces.WlInfMem α 4 (fun z _ => (-(2 * α)) * Work.Spaces.hKer z)
  FKnegW : Work.Spaces.WlInf α 4 (fun z _ => (-(2 * α)) * Work.Spaces.hKer z) ≤ C * α
  -- the three `(z+1)/z`-weighted star coefficients (`α`-small, `𝒲^{4,∞}`)
  Rssm : Work.FTS.EllipticEst.SmoothOpen
    (fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ)
  RsWm : Work.Spaces.WlInfMem α 4
    (fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ)
  RsW : Work.Spaces.WlInf α 4
    (fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ) ≤ C * α
  Ussm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => (z + 1) / z *
    (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Work.Construction.s2 θ))
  UsWm : Work.Spaces.WlInfMem α 4 (fun z θ => (z + 1) / z *
    (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Work.Construction.s2 θ))
  UsW : Work.Spaces.WlInf α 4 (fun z θ => (z + 1) / z *
    (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Work.Construction.s2 θ)) ≤ C * α
  Vssm : Work.FTS.EllipticEst.SmoothOpen
    (fun z θ => (z + 1) / z * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ)
  VsWm : Work.Spaces.WlInfMem α 4
    (fun z θ => (z + 1) / z * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ)
  VsW : Work.Spaces.WlInf α 4
    (fun z θ => (z + 1) / z * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ) ≤ C * α
  -- the fixed `F_*`-atoms
  FWsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α)
  FWWm : Work.Spaces.WlInfMem α 4 (Work.Construction.Fstar α)
  FWW : Work.Spaces.WlInf α 4 (Work.Construction.Fstar α) ≤ C * α
  DthFssm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth (Work.Construction.Fstar α))
  DthFsWm : Work.Spaces.WlInfMem α 4 (Work.Spaces.Dth (Work.Construction.Fstar α))
  DthFsW : Work.Spaces.WlInf α 4 (Work.Spaces.Dth (Work.Construction.Fstar α)) ≤ C * α ^ 2
  DzFssm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz (Work.Construction.Fstar α))
  DzFsWm : Work.Spaces.WlInfMem α 4 (Work.Spaces.Dz (Work.Construction.Fstar α))
  DzFsW : Work.Spaces.WlInf α 4 (Work.Spaces.Dz (Work.Construction.Fstar α)) ≤ C * α
  -- the three `φ`-scaled `F_*`-atoms
  phiFsqo : Work.FTS.VocabO.HQo α 4
    (fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ)
  phiFsX : Work.FTS.Nonlin.Xn α (fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ) ≤ C
  phiDthFsqo : Work.FTS.VocabO.HQo α 4
    (fun z θ => z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ)
  phiDthFsX : Work.FTS.Nonlin.Xn α
    (fun z θ => z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ≤ C
  phiDzFsqo : Work.FTS.VocabO.HQo α 4
    (fun z θ => z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ)
  phiDzFsX : Work.FTS.Nonlin.Xn α
    (fun z θ => z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ≤ C
  -- the fixed `FK(F_*)`-atom and its two products
  FKFSsm : Work.FTS.EllipticEst.SmoothOpen
    (fun z _ => Work.Construction.FK (Work.Construction.Fstar α) z)
  FKFSWm : Work.Spaces.WlInfMem α 4
    (fun z _ => Work.Construction.FK (Work.Construction.Fstar α) z)
  FKFSW : Work.Spaces.WlInf α 4
    (fun z _ => Work.Construction.FK (Work.Construction.Fstar α) z) ≤ C * α
  prodFKDthFSqo : Work.FTS.VocabO.HQo α 4 (fun z θ =>
    Work.Construction.FK (Work.Construction.Fstar α) z
      * Work.Spaces.Dth (Work.Construction.Fstar α) z θ)
  prodFKDthFSX : Work.FTS.Nonlin.Xn α (fun z θ =>
    Work.Construction.FK (Work.Construction.Fstar α) z
      * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ≤ C
  prodFKFSqo : Work.FTS.VocabO.HQo α 4 (fun z θ =>
    Work.Construction.FK (Work.Construction.Fstar α) z * Work.Construction.Fstar α z θ)
  prodFKFSX : Work.FTS.Nonlin.Xn α (fun z θ =>
    Work.Construction.FK (Work.Construction.Fstar α) z * Work.Construction.Fstar α z θ) ≤ C
  /-- angular multiplication by `-sin²θ` -/
  hSinMul : ∀ g : Fn, Work.FTS.EllipticEst.SmoothOpen g → Work.FTS.VocabO.HQo α 4 g →
    Work.Spaces.HkMem α 4 (fun z θ => -(Real.sin θ) ^ 2 * g z θ) ∧
    Work.FTS.Nonlin.Xn α (fun z θ => -(Real.sin θ) ^ 2 * g z θ) ≤ C * Work.FTS.Nonlin.Xn α g

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.N4C.PairingT.smoothOpen_pieces_N =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.N4C.PairingT

open Work.FTS.EllipticEst (SmoothOpen)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Local closure helpers for the products occurring in the pieces -/

/-- `c·A·B`. -/
private theorem so_c2 (c : ℝ) {A B : ℝ → ℝ → ℝ} (hA : SmoothOpen A) (hB : SmoothOpen B) :
    SmoothOpen (fun z θ => c * A z θ * B z θ) :=
  Work.FTS.StrongPersist.H6Pair6Aux.so_mul
    (Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul c hA) hB

/-- `c·A·B·C`. -/
private theorem so_c3 (c : ℝ) {A B C : ℝ → ℝ → ℝ} (hA : SmoothOpen A) (hB : SmoothOpen B)
    (hC : SmoothOpen C) : SmoothOpen (fun z θ => c * A z θ * B z θ * C z θ) :=
  Work.FTS.StrongPersist.H6Pair6Aux.so_mul
    (Work.FTS.StrongPersist.H6Pair6Aux.so_mul
      (Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul c hA) hB) hC

/-- `A·B·C`. -/
private theorem so_three {A B C : ℝ → ℝ → ℝ} (hA : SmoothOpen A) (hB : SmoothOpen B)
    (hC : SmoothOpen C) : SmoothOpen (fun z θ => A z θ * B z θ * C z θ) :=
  Work.FTS.StrongPersist.H6Pair6Aux.so_mul
    (Work.FTS.StrongPersist.H6Pair6Aux.so_mul hA hB) hC

/-- `-sin²θ` as a function of `θ` alone. -/
private theorem so_negSinSq : SmoothOpen (fun _ (θ : ℝ) => -(Real.sin θ) ^ 2) :=
  Work.FTS.StrongPersist.H6Pair6Aux.so_snd ((Real.contDiff_sin.pow 2).neg)

/-! ## The target -/

theorem smoothOpen_pieces_N {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {Cs Ce : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn}
    (hg : Work.FTS.ClassC.ClassC α g) (hell : Work.FTS.VocabO.EllPkgGo α Ce g Φg)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N1gg α g Φg) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N1gs α g Φg) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N1sg α Φs g) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N1ss α Φs) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N2gg α g Φg) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N2gs α g Φg) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N2sg α Φs g) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N2ss α Φs) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N3gg α g Φg) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N3gs α g Φg) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N3sg α Φs g) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N3ss α Φs) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N4gg α g) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N4gs α g) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N4sg α g) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N4ss α) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N5gg g) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N5gs α g) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N5sg α g) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N5ss α) := by
  have A : Work.FTS.StrongEps.E4R3.N4C.AtomsO α g Φs Φg :=
    atomsO_of_ctx hα hα1 hg hell hstar
  -- the atoms
  have hG : SmoothOpen g := A.sg
  have hFs : SmoothOpen (Work.Construction.Fstar α) := A.sFs
  have hFKg := A.sFKg
  have hFKFs := A.sFKFs
  have hRg : SmoothOpen (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg)) := A.sRg
  have hUg : SmoothOpen (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg)) := A.sUg
  have hVg : SmoothOpen (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg)) := A.sVg
  have hRs : SmoothOpen (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) := A.sRs
  have hUs : SmoothOpen (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) := A.sUs
  have hVs : SmoothOpen (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) := A.sVs
  -- the derived atoms
  have hPG : SmoothOpen (Work.Spaces.pth g) := hG.pth
  have hPFs : SmoothOpen (Work.Spaces.pth (Work.Construction.Fstar α)) := hFs.pth
  have hDzG : SmoothOpen (Work.Spaces.Dz g) := hG.Dz
  have hDzFs : SmoothOpen (Work.Spaces.Dz (Work.Construction.Fstar α)) := hFs.Dz
  have hDthG : SmoothOpen (Work.Spaces.Dth g) := hG.Dth
  have hS2 : SmoothOpen (fun _ (θ : ℝ) => Work.Construction.s2 θ) := smoothOpen_s2
  have hSinSq : SmoothOpen (fun _ (θ : ℝ) => -(Real.sin θ) ^ 2) := so_negSinSq
  -- the twenty pieces
  have p1 : SmoothOpen (Work.FTS.Nonlin.N1gg α g Φg) := by
    unfold Work.FTS.Nonlin.N1gg
    exact so_c2 2 hRg hG
  have p2 : SmoothOpen (Work.FTS.Nonlin.N1gs α g Φg) := by
    unfold Work.FTS.Nonlin.N1gs
    exact so_c2 2 hRg hFs
  have p3 : SmoothOpen (Work.FTS.Nonlin.N1sg α Φs g) := by
    unfold Work.FTS.Nonlin.N1sg
    exact so_c2 2 hRs hG
  have p4 : SmoothOpen (Work.FTS.Nonlin.N1ss α Φs) := by
    unfold Work.FTS.Nonlin.N1ss
    exact so_c2 2 hRs hFs
  have p5 : SmoothOpen (Work.FTS.Nonlin.N2gg α g Φg) := by
    unfold Work.FTS.Nonlin.N2gg
    exact so_c2 (-2) hUg hPG
  have p6 : SmoothOpen (Work.FTS.Nonlin.N2gs α g Φg) := by
    unfold Work.FTS.Nonlin.N2gs
    exact so_c2 (-2) hUg hPFs
  have p7 : SmoothOpen (Work.FTS.Nonlin.N2sg α Φs g) := by
    unfold Work.FTS.Nonlin.N2sg
    exact so_c2 (-2) hUs hPG
  have p8 : SmoothOpen (Work.FTS.Nonlin.N2ss α Φs) := by
    unfold Work.FTS.Nonlin.N2ss
    exact so_c2 (-2) hUs hPFs
  have p9 : SmoothOpen (Work.FTS.Nonlin.N3gg α g Φg) := by
    unfold Work.FTS.Nonlin.N3gg
    exact so_c2 (-2 * α) hVg hDzG
  have p10 : SmoothOpen (Work.FTS.Nonlin.N3gs α g Φg) := by
    unfold Work.FTS.Nonlin.N3gs
    exact so_c2 (-2 * α) hVg hDzFs
  have p11 : SmoothOpen (Work.FTS.Nonlin.N3sg α Φs g) := by
    unfold Work.FTS.Nonlin.N3sg
    exact so_c2 (-2 * α) hVs hDzG
  have p12 : SmoothOpen (Work.FTS.Nonlin.N3ss α Φs) := by
    unfold Work.FTS.Nonlin.N3ss
    exact so_c2 (-2 * α) hVs hDzFs
  have p13 : SmoothOpen (Work.FTS.Nonlin.N4gg α g) := by
    unfold Work.FTS.Nonlin.N4gg
    exact so_c2 (-(1 / 2)) hFKg hDthG
  have p14 : SmoothOpen (Work.FTS.Nonlin.N4gs α g) := by
    unfold Work.FTS.Nonlin.N4gs
    exact so_c3 (-(1 / 2)) hS2 hFKg hPFs
  have p15 : SmoothOpen (Work.FTS.Nonlin.N4sg α g) := by
    unfold Work.FTS.Nonlin.N4sg
    exact so_c2 (-(1 / 2)) hFKFs hDthG
  have p16 : SmoothOpen (Work.FTS.Nonlin.N4ss α) := by
    unfold Work.FTS.Nonlin.N4ss
    exact so_c3 (-(1 / 2)) hS2 hFKFs hPFs
  have p17 : SmoothOpen (Work.FTS.Nonlin.N5gg g) := by
    unfold Work.FTS.Nonlin.N5gg
    exact so_three hSinSq hFKg hG
  have p18 : SmoothOpen (Work.FTS.Nonlin.N5gs α g) := by
    unfold Work.FTS.Nonlin.N5gs
    exact so_three hSinSq hFKg hFs
  have p19 : SmoothOpen (Work.FTS.Nonlin.N5sg α g) := by
    unfold Work.FTS.Nonlin.N5sg
    exact so_three hSinSq hFKFs hG
  have p20 : SmoothOpen (Work.FTS.Nonlin.N5ss α) := by
    unfold Work.FTS.Nonlin.N5ss
    exact so_three hSinSq hFKFs hFs
  exact ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18,
    p19, p20⟩

end Work.FTS.StrongEps.E4R3.N4C.PairingT
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.N4C.PairingT.smoothOpen_pieces_N0 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.N4C.PairingT

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.StrongEps.E4R3.N4C
open Work.FTS.EllipticEst (SmoothOpen)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Negation preserves `SmoothOpen`.  (The library's `so_const_mul (-1)` produces
`fun z θ => -1 * f z θ`, which is only propositionally equal to `fun z θ => -f z θ`, and the
product rule below needs the latter shape.) -/
theorem so_neg {f : ℝ → ℝ → ℝ} (hf : SmoothOpen f) :
    SmoothOpen (fun z θ => -f z θ) :=
  SmoothOpen.congr (Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul (-1) hf)
    (fun z θ _ _ _ => by ring)

theorem smoothOpen_pieces_N0 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {Cs Ce : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn}
    (hg : Work.FTS.ClassC.ClassC α g) (hell : Work.FTS.VocabO.EllPkgGo α Ce g Φg)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N0fix α) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N03g α g) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N04aF α g) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N04bF α g) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N05aF α g) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N05bF α g) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N06F α g) := by
  -- the twelve smoothness atoms of the §8 assembly
  have hA := atomsO_of_ctx hα hα1 hg hell hstar
  -- the angular factors
  have hs2 : SmoothOpen (fun _ (θ : ℝ) => Work.Construction.s2 θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_snd Work.FTS.StrongPersist.H6Pair6Aux.contDiff_s2
  have hc2m : SmoothOpen (fun _ (θ : ℝ) => Work.Construction.c2m θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_snd Work.FTS.StrongPersist.H6Pair6Aux.contDiff_c2m
  -- the derivatives of the two profiles
  have hpF : SmoothOpen (Work.Spaces.pth (Work.Construction.Fstar α)) :=
    SmoothOpen.pth hA.sFs
  have hDzF : SmoothOpen (Work.Spaces.Dz (Work.Construction.Fstar α)) :=
    SmoothOpen.Dz hA.sFs
  have hpg : SmoothOpen (Work.Spaces.pth g) := SmoothOpen.pth hA.sg
  have hDzg : SmoothOpen (Work.Spaces.Dz g) := SmoothOpen.Dz hA.sg
  -- the negated angular factor, in the `-c2m` shape
  have hnc2m : SmoothOpen (fun z (θ : ℝ) => -Work.Construction.c2m θ) := so_neg hc2m
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `N0fix α = I^{N₀}_1 + I^{N₀}_2`
    refine SmoothOpen.congr (f := fun z θ =>
        (3 / (2 * α)) * Work.Construction.s2 θ
          * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.pth (Work.Construction.Fstar α) z θ
        + (-Work.Construction.c2m θ) * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ?_ ?_
    · exact Work.FTS.StrongPersist.H6Pair6Aux.so_add
        (Work.FTS.StrongPersist.H6Pair6Aux.so_mul
          (Work.FTS.StrongPersist.H6Pair6Aux.so_mul
            (Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul (3 / (2 * α)) hs2) hA.sLFs)
          hpF)
        (Work.FTS.StrongPersist.H6Pair6Aux.so_mul
          (Work.FTS.StrongPersist.H6Pair6Aux.so_mul hnc2m hA.sLFs) hDzF)
    · intro z θ hz hθ hθ2
      simp only [Work.FTS.Nonlin.N0fix, Work.Construction.N01, Work.Construction.N02]
  · -- `N03g α g = I^{N₀}_3 = (1/α) L₁₂(g) g`
    refine SmoothOpen.congr (f := fun z θ =>
        (1 / α) * Work.Construction.L12 g z * g z θ) ?_ ?_
    · exact Work.FTS.StrongPersist.H6Pair6Aux.so_mul
        (Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul (1 / α) hA.sLg) hA.sg
    · intro z θ hz hθ hθ2
      simp only [Work.FTS.Nonlin.N03g, Work.Construction.N03]
  · -- `N04aF α g = (3/(2α)) sin 2θ L₁₂(g) ∂_θF_*`
    refine SmoothOpen.congr (f := fun z θ => (3 / (2 * α)) * Work.Construction.s2 θ
        * Work.Construction.L12 g z * Work.Spaces.pth (Work.Construction.Fstar α) z θ) ?_ ?_
    · exact Work.FTS.StrongPersist.H6Pair6Aux.so_mul
        (Work.FTS.StrongPersist.H6Pair6Aux.so_mul
          (Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul (3 / (2 * α)) hs2) hA.sLg) hpF
    · intro z θ hz hθ hθ2
      simp only [Work.FTS.Nonlin.N04aF, Work.Construction.N04a]
  · -- `N04bF α g = (3/(2α)) sin 2θ L₁₂(g) ∂_θg`
    refine SmoothOpen.congr (f := fun z θ => (3 / (2 * α)) * Work.Construction.s2 θ
        * Work.Construction.L12 g z * Work.Spaces.pth g z θ) ?_ ?_
    · exact Work.FTS.StrongPersist.H6Pair6Aux.so_mul
        (Work.FTS.StrongPersist.H6Pair6Aux.so_mul
          (Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul (3 / (2 * α)) hs2) hA.sLg) hpg
    · intro z θ hz hθ hθ2
      simp only [Work.FTS.Nonlin.N04bF, Work.Construction.N04b]
  · -- `N05aF α g = -c2m(θ) L₁₂(g) D_zF_*`
    refine SmoothOpen.congr (f := fun z θ => (-Work.Construction.c2m θ)
        * Work.Construction.L12 g z * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ?_ ?_
    · exact Work.FTS.StrongPersist.H6Pair6Aux.so_mul
        (Work.FTS.StrongPersist.H6Pair6Aux.so_mul hnc2m hA.sLg) hDzF
    · intro z θ hz hθ hθ2
      simp only [Work.FTS.Nonlin.N05aF, Work.Construction.N05a]
  · -- `N05bF α g = -c2m(θ) L₁₂(g) D_zg`
    refine SmoothOpen.congr (f := fun z θ => (-Work.Construction.c2m θ)
        * Work.Construction.L12 g z * Work.Spaces.Dz g z θ) ?_ ?_
    · exact Work.FTS.StrongPersist.H6Pair6Aux.so_mul
        (Work.FTS.StrongPersist.H6Pair6Aux.so_mul hnc2m hA.sLg) hDzg
    · intro z θ hz hθ hθ2
      simp only [Work.FTS.Nonlin.N05bF, Work.Construction.N05b]
  · -- `N06F α g = -c2m(θ) L₁₂(F_*) D_zg`
    refine SmoothOpen.congr (f := fun z θ => (-Work.Construction.c2m θ)
        * Work.Construction.L12 (Work.Construction.Fstar α) z
        * Work.Spaces.Dz g z θ) ?_ ?_
    · exact Work.FTS.StrongPersist.H6Pair6Aux.so_mul
        (Work.FTS.StrongPersist.H6Pair6Aux.so_mul hnc2m hA.sLFs) hDzg
    · intro z θ hz hθ hθ2
      simp only [Work.FTS.Nonlin.N06F, Work.Construction.N06]

end Work.FTS.StrongEps.E4R3.N4C.PairingT
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux2.prof_cont_moments =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux2

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The two moments `L₁₂(F_* + w)` and `FK(F_* + w)` are `C^∞` on the open quadrant for a
profile `w` of the class `ClassC α`** — with no elliptic data at all.

This is the `ClassC`-native version of the first two conjuncts of
`ClassCRHS.SmoothOpenRHS`: the elliptic package `hell` is *not* used, because

* `z ↦ L₁₂(w)(z)` is `C^∞` on `(0,∞)` from `ClassC.reg` + `ClassC.mem` alone
  (`ClassCRHS.smoothOpen_L12_radial_classC`), while the older route went through
  `smoothOpen_L12_radial` and the elliptic field `hell`;
* `z ↦ FK(w)(z) = 3 F_*(w)(z)` is radial smooth from `ClassC.fsm` alone
  (`RXT.velPert_FK_eq`), no elliptic data either;
* the `F_*`-halves are explicit (`smoothOpen_L12_Fstar_rad`, `smoothOpen_FK_Fstar_rad`), and the
  two halves add by `NZaux.L12AddFstar` respectively `GalFields.RHS.FK_add_of_slices`. -/
theorem prof_cont_moments {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {w : ℝ → ℝ → ℝ}
    (hw : Work.FTS.ClassC.ClassC α w) :
    Work.FTS.EllipticEst.SmoothOpen
        (fun z (_ : ℝ) => Work.Construction.L12 (Work.Construction.Ftot α w) z) ∧
      Work.FTS.EllipticEst.SmoothOpen
        (fun z (_ : ℝ) => Work.Construction.FK (Work.Construction.Ftot α w) z) := by
  -- the `ℋ⁴`-honesty of `w`, from the `ℋ⁷`-honesty of the class
  have hmem4 : Work.Spaces.HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 4 (by norm_num) hw.mem
  -- `SmoothOpen (z ↦ L₁₂(w)(z))`: no elliptic data needed
  have hL12w : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.L12 w z) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC hα hw
  -- `SmoothOpen (z ↦ FK(w)(z))`: `FK F = 3 F_*(F)`, so only `ClassC.fsm` is used
  have hFKw : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.FK w z) := by
    have hr : ∀ n : ℕ, ContDiffOn ℝ n (fun z : ℝ => 3 * Work.Elliptic.Fstar w z)
        (Set.Ioi 0) :=
      fun n => contDiffOn_const.mul (hw.fsm n)
    have hmain := Work.FTS.NonlinRows.smoothOpen_radial
      (r := fun z : ℝ => 3 * Work.Elliptic.Fstar w z) hr
    refine hmain.congr ?_
    rintro z θ _ _ _
    exact (Work.FTS_RegExport.RXT.velPert_FK_eq w z).symm
  -- the two `F_*`-moments are explicit
  have hL12F : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.L12 (Work.Construction.Fstar α) z) :=
    Work.FTS.GalFields.RHS.smoothOpen_L12_Fstar_rad α hα hα1
  have hFKF : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.FK (Work.Construction.Fstar α) z) :=
    Work.FTS.GalFields.RHS.smoothOpen_FK_Fstar_rad α hα hα1
  constructor
  · -- the first moment `L₁₂(F_* + w)`
    refine (Work.FTS.NonlinRows.smoothOpen_add hL12F hL12w).congr ?_
    rintro z θ hz _ _
    exact (Work.FTS.StrongPersist.H6Rows.NZaux.L12AddFstar hα hα1 hw.reg hmem4 z hz).symm
  · -- the second moment `FK(F_* + w)`
    refine (Work.FTS.NonlinRows.smoothOpen_add hFKF hFKw).congr ?_
    rintro z θ hz _ _
    exact (Work.FTS.GalFields.RHS.FK_add_of_slices
      (a := Work.Construction.Fstar α) (b := w) (ne_of_gt hz)
      (Work.Stability.integrableOn_slice_Fstar α hα z)
      (Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hw.reg hmem4 hz)).symm

end Work.FTS.StrongEps.E5Aux2
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.AtomsW5 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5.Atoms

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The three star coefficients -/

/-- **The three star coefficients at level `5`**, as `𝒲^{5,∞}`-valued atoms.  The constant may
depend on `Cs6` and `α`, but not on `Φs`. -/
theorem WAtomsStar5 : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {Cs6 : ℝ},
    ∃ a : ℝ, 0 < a ∧ ∀ {Φs : Fn}, Work.FTS.StrongPersist.StarPkg6 α Cs6 Φs →
      (Work.FTS.EllipticEst.SmoothOpen (fun z θ => (z + 1) / z
          * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ) ∧
        Work.Spaces.WlInfMem α 5 (fun z θ => (z + 1) / z
          * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ) ∧
        Work.Spaces.WlInf α 5 (fun z θ => (z + 1) / z
          * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ) ≤ a) ∧
      (Work.FTS.EllipticEst.SmoothOpen (fun z θ => (z + 1) / z
          * (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
            / Work.Construction.s2 θ)) ∧
        Work.Spaces.WlInfMem α 5 (fun z θ => (z + 1) / z
          * (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
            / Work.Construction.s2 θ)) ∧
        Work.Spaces.WlInf α 5 (fun z θ => (z + 1) / z
          * (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
            / Work.Construction.s2 θ)) ≤ a) ∧
      (Work.FTS.EllipticEst.SmoothOpen (fun z θ => (z + 1) / z
          * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ) ∧
        Work.Spaces.WlInfMem α 5 (fun z θ => (z + 1) / z
          * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ) ∧
        Work.Spaces.WlInf α 5 (fun z θ => (z + 1) / z
          * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ) ≤ a) := by
  intro α hαI Cs6
  have hα0 : 0 < α := hαI.1
  have hα1 : α ≤ 1 := hαI.2
  refine ⟨|Cs6 * α| + 1, by positivity, fun {Φs} hstar => ?_⟩
  have hsw : Work.FTS.VocabO.StarPkgo α Cs6 Φs := hstar.toStarPkgo2.toStarPkgo
  have h1 := Work.FTS.StrongPersist.StarPkg6.RW6_mem hstar
  have h1b := Work.FTS.StrongPersist.StarPkg6.RW6_bd hstar
  have h2 := Work.FTS.StrongPersist.StarPkg6.UszW6_mem hstar
  have h2b := Work.FTS.StrongPersist.StarPkg6.UszW6_bd hstar
  have h3 := Work.FTS.StrongPersist.StarPkg6.VzW6_mem hstar
  have h3b := Work.FTS.StrongPersist.StarPkg6.VzW6_bd hstar
  obtain ⟨h1m, h1l⟩ := WlInfMem_mono (α := α) (l := 6) (l' := 5) (by norm_num) h1
  obtain ⟨h2m, h2l⟩ := WlInfMem_mono (α := α) (l := 6) (l' := 5) (by norm_num) h2
  obtain ⟨h3m, h3l⟩ := WlInfMem_mono (α := α) (l := 6) (l' := 5) (by norm_num) h3
  have hCs : Cs6 * α ≤ |Cs6 * α| + 1 := by linarith [le_abs_self (Cs6 * α)]
  exact ⟨⟨Work.FTS.StrongEps.ClassCRHS.smoothOpen_Rs_of_star hα0 hα1 hsw, h1m,
      le_trans (le_trans h1l h1b) hCs⟩,
    ⟨Work.FTS.StrongEps.ClassCRHS.smoothOpen_Us_of_star hα0 hα1 hsw, h2m,
      le_trans (le_trans h2l h2b) hCs⟩,
    ⟨Work.FTS.StrongEps.ClassCRHS.smoothOpen_Vs_of_star hα0 hα1 hsw, h3m,
      le_trans (le_trans h3l h3b) hCs⟩⟩

/-! ## The four fixed profiles -/

/-- **The four fixed `𝒲^{5,∞}`-priced profiles at level `5`.** -/
theorem WAtomsFixed5 : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 →
    ∃ a : ℝ, 0 < a ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) ∧
        Work.Spaces.WlInfMem α 5 (Work.Construction.Fstar α) ∧
        Work.Spaces.WlInf α 5 (Work.Construction.Fstar α) ≤ a) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth (Work.Construction.Fstar α)) ∧
        Work.Spaces.WlInfMem α 5 (Work.Spaces.Dth (Work.Construction.Fstar α)) ∧
        Work.Spaces.WlInf α 5 (Work.Spaces.Dth (Work.Construction.Fstar α)) ≤ a) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz (Work.Construction.Fstar α)) ∧
        Work.Spaces.WlInfMem α 5 (Work.Spaces.Dz (Work.Construction.Fstar α)) ∧
        Work.Spaces.WlInf α 5 (Work.Spaces.Dz (Work.Construction.Fstar α)) ≤ a) ∧
      (Work.FTS.EllipticEst.SmoothOpen (fun z _ => (-(2 * α)) * Work.Spaces.hKer z) ∧
        Work.Spaces.WlInfMem α 5 (fun z _ => (-(2 * α)) * Work.Spaces.hKer z) ∧
        Work.Spaces.WlInf α 5 (fun z _ => (-(2 * α)) * Work.Spaces.hKer z) ≤ a) := by
  intro α hαI
  have hα0 : 0 < α := hαI.1
  have hα1 : α ≤ 1 := hαI.2
  obtain ⟨C1, hC1, hF⟩ := Work.FTS.StrongPersist.Fstar_W6
  obtain ⟨C2, hC2, hDF⟩ := Work.FTS.StrongPersist.DthFstar_W6
  obtain ⟨C3, hC3, hDZ⟩ := Work.FTS.StrongPersist.DzFstar_W6
  obtain ⟨C4, hC4, hK⟩ := hKerConstWlInf_l 5
  obtain ⟨hFm, hFl⟩ := hF α hα0 hα1
  obtain ⟨hDFm, hDFl⟩ := hDF α hα0 hα1
  obtain ⟨hDZm, hDZl⟩ := hDZ α hα0 hα1
  obtain ⟨hKm, hKl⟩ := hK α (-(2 * α))
  obtain ⟨hF5m, hF5l⟩ := WlInfMem_mono (α := α) (l := 6) (l' := 5) (by norm_num) hFm
  obtain ⟨hDF5m, hDF5l⟩ := WlInfMem_mono (α := α) (l := 6) (l' := 5) (by norm_num) hDFm
  obtain ⟨hDZ5m, hDZ5l⟩ := WlInfMem_mono (α := α) (l := 6) (l' := 5) (by norm_num) hDZm
  have hFsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.EllipticEst.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  have h1nn : 0 ≤ C1 * α := mul_nonneg hC1.le hα0.le
  have h2nn : 0 ≤ C2 * α ^ 2 := mul_nonneg hC2.le (sq_nonneg α)
  have h3nn : 0 ≤ C3 * α := mul_nonneg hC3.le hα0.le
  have h4nn : 0 ≤ C4 * |-(2 * α)| := mul_nonneg hC4.le (abs_nonneg _)
  refine ⟨C1 * α + C2 * α ^ 2 + C3 * α + C4 * |-(2 * α)| + 1, by linarith, ?_, ?_, ?_, ?_⟩
  · exact ⟨hFsm, hF5m, le_trans hF5l (by linarith)⟩
  · exact ⟨hFsm.Dth, hDF5m, le_trans hDF5l (by linarith)⟩
  · exact ⟨hFsm.Dz, hDZ5m, le_trans hDZ5l (by linarith)⟩
  · exact ⟨Work.FTS.StrongEps.ClassCRHS.smoothOpen_FKneg α, hKm, le_trans hKl (by linarith)⟩

end Work.FTS.StrongEps.H5.Atoms
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.HAtoms5 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5.Atoms

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- **Multiplication by `φ z = z/(1+z)` preserves `ℋ⁵`-honesty**, with the universal constant
of `H5.phiAtoms5`. -/
theorem phiHQo5 : ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ}, 0 < α → α ≤ 1 → ∀ {g : Fn},
    Work.FTS.VocabO.HQo α 5 g →
    Work.FTS.VocabO.HQo α 5 (fun z θ => z / (1 + z) * g z θ) ∧
    Work.Spaces.HkNorm α 5 (fun z θ => z / (1 + z) * g z θ)
      ≤ C * Work.Spaces.HkNorm α 5 g := by
  obtain ⟨C, hC, hphi⟩ := Work.FTS.StrongEps.H5.phiAtoms5
  refine ⟨C, hC, fun {α} hα hα1 {g} hg => ⟨⟨?_, (hphi α hα hα1 g hg).1⟩,
    (hphi α hα hα1 g hg).2⟩⟩
  simpa [Work.FTS.NonlinRows.NRow10aux.phiF]
    using Work.FTS.OpenPkg.smoothOpen_sepMul
      (Work.FTS.NonlinRows.NRow10aux.phiSelf_smoothOpen) hg.1

/-- **The `ℋ⁵`-honest atoms of the level-`5` `N`-block.** -/
theorem HAtoms5 : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {C₀ B Ce : ℝ},
    ∃ a : ℝ, 0 < a ∧ ∀ {w Φg : Fn},
      Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      Work.Spaces.HkNorm α 6 w ≤ B → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
      (Work.FTS.VocabO.HQo α 5 (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg)) ∧
        Work.Spaces.HkNorm α 5 (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg)) ≤ a) ∧
      (Work.FTS.VocabO.HQo α 5 (fun z θ => Work.Construction.Uop α
          (Work.FTS.Nonlin.PhiTg α w Φg) z θ / Work.Construction.s2 θ) ∧
        Work.Spaces.HkNorm α 5 (fun z θ => Work.Construction.Uop α
          (Work.FTS.Nonlin.PhiTg α w Φg) z θ / Work.Construction.s2 θ) ≤ a) ∧
      (Work.FTS.VocabO.HQo α 5 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg)) ∧
        Work.Spaces.HkNorm α 5 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg)) ≤ a) ∧
      (Work.FTS.VocabO.HQo α 5 w ∧ Work.Spaces.HkNorm α 5 w ≤ a) ∧
      (Work.FTS.VocabO.HQo α 5 (Work.Spaces.Dth w) ∧
        Work.Spaces.HkNorm α 5 (Work.Spaces.Dth w) ≤ a) ∧
      (Work.FTS.VocabO.HQo α 5 (Work.Spaces.Dz w) ∧
        Work.Spaces.HkNorm α 5 (Work.Spaces.Dz w) ≤ a) ∧
      (Work.FTS.VocabO.HQo α 5 (fun z _ => Work.Construction.FK w z) ∧
        Work.Spaces.HkNorm α 5 (fun z _ => Work.Construction.FK w z) ≤ a) ∧
      (Work.FTS.VocabO.HQo α 5 (fun z θ => z / (1 + z) * w z θ) ∧
        Work.Spaces.HkNorm α 5 (fun z θ => z / (1 + z) * w z θ) ≤ a) ∧
      (Work.FTS.VocabO.HQo α 5 (fun z θ => z / (1 + z) * Work.Spaces.Dth w z θ) ∧
        Work.Spaces.HkNorm α 5 (fun z θ => z / (1 + z) * Work.Spaces.Dth w z θ) ≤ a) ∧
      (Work.FTS.VocabO.HQo α 5 (fun z θ => z / (1 + z) * Work.Spaces.Dz w z θ) ∧
        Work.Spaces.HkNorm α 5 (fun z θ => z / (1 + z) * Work.Spaces.Dz w z θ) ≤ a) := by
  intro α hαI C₀ B Ce
  have hα0 : 0 < α := hαI.1
  have hα1 : α ≤ 1 := hαI.2
  obtain ⟨Cphi, hCphi, hphi⟩ := phiHQo5
  obtain ⟨CFK, Xi, Cpow, hCFK, hXi, hCpow, hfk⟩ := Work.FTS.StrongPersist.H6Row6.fkFacts7
  have hXiRnn : 0 ≤ Xi * α ^ (-Cpow) :=
    mul_nonneg hXi.le (Real.rpow_pos_of_pos hα0 _).le
  set B0 : ℝ := max B 0 with hB0def
  have hB0nn : 0 ≤ B0 := by rw [hB0def]; exact le_max_right _ _
  set A1 : ℝ := |Ce| * B0 with hA1def
  set A2 : ℝ := Xi * α ^ (-Cpow) * B0 + 1 with hA2def
  set A3 : ℝ := Cphi * B0 with hA3def
  have hA1nn : 0 ≤ A1 := by rw [hA1def]; exact mul_nonneg (abs_nonneg _) hB0nn
  have hA2nn : 0 ≤ A2 := by
    rw [hA2def]; linarith [mul_nonneg hXiRnn hB0nn]
  have hA3nn : 0 ≤ A3 := by rw [hA3def]; exact mul_nonneg hCphi.le hB0nn
  refine ⟨A1 + A2 + A3 + B0 + 1, by linarith, ?_⟩
  intro w Φg hw hXw hX6 hell
  have hX6' : Work.Spaces.HkNorm α 6 w ≤ B0 :=
    le_trans hX6 (by rw [hB0def]; exact le_max_left _ _)
  have hb0 : ∀ {x : ℝ}, x ≤ B0 → x ≤ A1 + A2 + A3 + B0 + 1 := by
    intro x hx; linarith [hA1nn, hA2nn, hA3nn]
  have hb1 : ∀ {x : ℝ}, x ≤ |Ce| * B0 → x ≤ A1 + A2 + A3 + B0 + 1 := by
    intro x hx; rw [← hA1def] at hx; linarith [hA2nn, hA3nn, hB0nn]
  have hb2 : ∀ {x : ℝ}, x ≤ Xi * α ^ (-Cpow) * B0 → x ≤ A1 + A2 + A3 + B0 + 1 := by
    intro x hx
    have h2 : Xi * α ^ (-Cpow) * B0 ≤ A2 := by rw [hA2def]; linarith
    linarith [hA1nn, hA3nn, hB0nn]
  have hb3 : ∀ {x : ℝ}, x ≤ Cphi * B0 → x ≤ A1 + A2 + A3 + B0 + 1 := by
    intro x hx; rw [← hA3def] at hx; linarith [hA1nn, hA2nn, hB0nn]
  -- ### the `ℋ⁶`-data of `w`
  have hmem6w : Work.Spaces.HkMem α 6 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 6 (by norm_num) hw.mem
  have hqo6w : Work.FTS.VocabO.HQo α 6 w := ⟨hw.reg, hmem6w⟩
  -- ### the three elliptic coefficients, from `EllPkgK α 6`
  have hell' : ∀ {A : Fn}, Work.FTS.VocabO.HQo α 6 A →
      Work.Spaces.HkNorm α 6 A ≤ Ce * Work.Spaces.HkNorm α 6 w →
      Work.FTS.VocabO.HQo α 5 A ∧ Work.Spaces.HkNorm α 5 A ≤ A1 + A2 + A3 + B0 + 1 := by
    intro A hQA hb6
    refine ⟨⟨hQA.1, Work.FTS.OpenPkg.HkMem_mono_open hQA.1 5 (by norm_num) hQA.2⟩, hb1 ?_⟩
    calc Work.Spaces.HkNorm α 5 A ≤ Work.Spaces.HkNorm α 6 A :=
          Work.FTS.StrongLWP.HkNorm_mono_of_mem (by norm_num) hQA.2
      _ ≤ Ce * Work.Spaces.HkNorm α 6 w := hb6
      _ ≤ |Ce| * B0 :=
          le_trans (mul_le_mul_of_nonneg_right (le_abs_self Ce)
            (Work.Spaces.HkNorm_nonneg α 6 w)) (mul_le_mul_of_nonneg_left hX6' (abs_nonneg Ce))
  have hR := hell' hell.R.1 hell.R.2
  have hU := hell' hell.U.1 hell.U.2
  have hV := hell' hell.V.1 hell.V.2
  -- ### `w` and its two first derivatives
  have hwB : Work.Spaces.HkNorm α 5 w ≤ B0 :=
    le_trans (Work.FTS.StrongLWP.HkNorm_mono_of_mem (by norm_num) hmem6w) hX6'
  have hw5 : Work.FTS.VocabO.HQo α 5 w ∧ Work.Spaces.HkNorm α 5 w ≤ A1 + A2 + A3 + B0 + 1 :=
    ⟨⟨hw.reg, Work.FTS.OpenPkg.HkMem_mono_open hw.reg 5 (by norm_num) hmem6w⟩, hb0 hwB⟩
  have hDzB : Work.Spaces.HkNorm α 5 (Work.Spaces.Dz w) ≤ B0 := by
    refine le_trans (Real.sqrt_le_sqrt (Work.FTS.CoercivityFix.Transfer.HkSq_Dz_le_Q0Sm α 5
      (Work.FTS.StrongPersist.q0Sm_of_smoothOpen hw.reg 6) hmem6w)) ?_
    exact le_trans (Work.FTS.StrongLWP.HkNorm_mono_of_mem (by norm_num) hmem6w) hX6'
  have hDz5 : Work.FTS.VocabO.HQo α 5 (Work.Spaces.Dz w) ∧
      Work.Spaces.HkNorm α 5 (Work.Spaces.Dz w) ≤ A1 + A2 + A3 + B0 + 1 :=
    ⟨⟨hw.reg.Dz, Work.FTS.IPGen.HkMem_Dz_le hqo6w.1 hqo6w.2⟩, hb0 hDzB⟩
  have hDthB : Work.Spaces.HkNorm α 5 (Work.Spaces.Dth w) ≤ B0 := by
    refine le_trans (Real.sqrt_le_sqrt
      (Work.FTS.CoercivityStep.Norm.HkSq_Dth_le α hα0 5 hmem6w)) ?_
    exact le_trans (Work.FTS.StrongLWP.HkNorm_mono_of_mem (by norm_num) hmem6w) hX6'
  have hDth5 : Work.FTS.VocabO.HQo α 5 (Work.Spaces.Dth w) ∧
      Work.Spaces.HkNorm α 5 (Work.Spaces.Dth w) ≤ A1 + A2 + A3 + B0 + 1 :=
    ⟨⟨hw.reg.Dth, Work.FTS.IPGen.HkMem_Dth_le (by linarith) hqo6w.1 hqo6w.2⟩, hb0 hDthB⟩
  -- ### the angular moment `FK w`
  have hfkfacts := hfk hα0 hα1 w hqo6w hw.mem hw.l12
  have hFKsmo : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.FK w z) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_FKw_of_classC hw
  have hFKmem6 : Work.Spaces.HkMem α 6 (fun z _ => Work.Construction.FK w z) :=
    hfkfacts.2.2.2.1
  have hFKbd6 : Work.Spaces.HkNorm α 6 (fun z _ => Work.Construction.FK w z)
      ≤ Xi * α ^ (-Cpow) * Work.Spaces.HkNorm α 6 w := hfkfacts.2.2.2.2.1
  have hFK5 : Work.FTS.VocabO.HQo α 5 (fun z _ => Work.Construction.FK w z) ∧
      Work.Spaces.HkNorm α 5 (fun z _ => Work.Construction.FK w z) ≤ A1 + A2 + A3 + B0 + 1 := by
    refine ⟨⟨hFKsmo, Work.FTS.OpenPkg.HkMem_mono_open hFKsmo 5 (by norm_num) hFKmem6⟩,
      hb2 ?_⟩
    calc Work.Spaces.HkNorm α 5 (fun z _ => Work.Construction.FK w z)
        ≤ Work.Spaces.HkNorm α 6 (fun z _ => Work.Construction.FK w z) :=
          Work.FTS.StrongLWP.HkNorm_mono_of_mem (by norm_num) hFKmem6
      _ ≤ Xi * α ^ (-Cpow) * Work.Spaces.HkNorm α 6 w := hFKbd6
      _ ≤ Xi * α ^ (-Cpow) * B0 := mul_le_mul_of_nonneg_left hX6' hXiRnn
  -- ### the three `φ`-scaled atoms
  obtain ⟨hphiwm, hphiwb⟩ := hphi hα0 hα1 hw5.1
  obtain ⟨hphiDthm, hphiDthb⟩ := hphi hα0 hα1 hDth5.1
  obtain ⟨hphiDzm, hphiDzb⟩ := hphi hα0 hα1 hDz5.1
  exact ⟨hR, hU, hV, hw5, hDth5, hDz5, hFK5,
    ⟨hphiwm, hb3 (le_trans hphiwb (mul_le_mul_of_nonneg_left hwB hCphi.le))⟩,
    ⟨hphiDthm, hb3 (le_trans hphiDthb (mul_le_mul_of_nonneg_left hDthB hCphi.le))⟩,
    ⟨hphiDzm, hb3 (le_trans hphiDzb (mul_le_mul_of_nonneg_left hDzB hCphi.le))⟩⟩

end Work.FTS.StrongEps.H5.Atoms
end
end
