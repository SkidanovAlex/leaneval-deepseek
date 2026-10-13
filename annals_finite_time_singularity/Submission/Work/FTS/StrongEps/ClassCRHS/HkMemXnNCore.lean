import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.GalFields.Norm.Basic
import Submission.Work.FTS.StrongPersist.L3Rhs.c2m_mul_HkSq_le
import Submission.Work.FTS.Nonlinear.Pieces.RNP.RNP24.angProfile_sinSq
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.Nonlinear.Open.Row25Aux
import Submission.Work.FTS.StrongEps.EComparison.EllPkgClsVop
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row22
import Submission.Work.FTS.OpenPkg.fkH_field
import Submission.Work.FTS.GalFields.RHS.HkSum
import Submission.Work.FTS.NonlinRows.Rl1.splitOpen
import Submission.Work.FTS.NonlinRows.NRow10aux.mul_phi_Hk
import Submission.Work.FTS.GalFields.RHS.smoothOpen_N_Ftot_gal
import Submission.Work.FTS.StrongPersist.H6Rows.NZaux.L12AddFstar
import Submission.Work.FTS.StrongLWP.Basic
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.StrongEps.ClassCRHS.SmoothOpenRHS
import Submission.Work.FTS.IPGen.OpenBasic
import Submission.Work.FTS.LocData.SmoothQuad_Fstar
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnNDefs
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnNAux
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnNIdent

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
