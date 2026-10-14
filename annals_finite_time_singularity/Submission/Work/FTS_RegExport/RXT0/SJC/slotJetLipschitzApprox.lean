import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.OpenPkg.Pieces4
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS.StrongEps.SupPort.classC_sup_le
import Submission.Work.FTS.StrongPersist.L3Rhs.N3ssPriced
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsRadAux.aestronglyMeasurable_slotSum
import Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.Star6
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_MuLamOK.Conversion
import Submission.Work.FTS_RegExport.RXB.l12_aux
import Submission.Work.FTS_RegExport.RXT.C2Radial
import Submission.Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto
import Submission.Work.FTS_RegExport.RXT.Slots.v2_paramC2
import Submission.Work.FTS_RegExport.RXT.Slots.v2_theta_sup_uniform
import Submission.Work.FTS_RegExport.RXT.Slots.v2_velPert
import Submission.Work.FTS_RegExport.RXT.SysAux.bR_decomp
import Submission.Work.FTS_RegExport.RXT.SysAux.pertSlot_lip_approx
import Submission.Work.FTS_RegExport.RXT.st1_stdata
import Submission.Work.FTS_RegExport.RXT.velPert
import Submission.Work.FTS_RegExport.RXT.velVanish2
import Submission.Work.FTS_RegExport.RXT.velVanish2Aux
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_RegExport.THL.angular_L2_noTrace
import Submission.Work.FTS_RegExport.THL.vopPert_theta_holder
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_majorant
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.FTS.StrongEps.EpsZero.ClassCHk.NMemAux2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsZero.ClassCHk

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

open Work.FTS.Galerkin (Fn)

/-!
# `NMemAux2` — the `N₃`, `N₄`, `N₅` pieces of the split of `N`

The remaining twelve pieces `N₃^{gg} … N₅^{ss}` of `Work.FTS.Nonlin.Defs`, each proved
`ℋ⁴`-honest and `C⁴` on the open quadrant (`Work.FTS.OpenPkg.Good`).  See
`Work.FTS.StrongEps.EpsZero.ClassCHk.NMemAux` for the helpers and the first eight pieces.
-/

variable {α Ce Cs : ℝ} {w Φs Φg : Fn}

/-- `N₃^{gg} = -2α 𝒱(Φ̃_g)·D_z w`. -/
theorem good_N3gg (hα : 0 < α) (hα1 : α ≤ 1)
    (hw : Work.FTS.ClassC.ClassC α w) (hell : Work.FTS.VocabO.EllPkgGo α Ce w Φg) :
    Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N3gg α w Φg) := by
  obtain ⟨Cp, _, hprod⟩ := Work.FTS.OpenPkg.prod_field
  have hmem5 : Work.Spaces.HkMem α 5 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 5 (by norm_num) hw.mem
  have hDzQ : Work.FTS.VocabO.HQo α 4 (Work.Spaces.Dz w) :=
    ⟨hw.reg.Dz, Work.FTS.EllipticEst.UopHk.HkMem_Dz_of_smoothOpen α 4 hw.reg hmem5⟩
  have h1 : Work.Spaces.HkMem α 4 (fun z θ =>
      Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg) z θ * Work.Spaces.Dz w z θ) :=
    (hprod α hα hα1 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg))
      (Work.Spaces.Dz w) hell.V.1 hDzQ).1
  have hsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N3gg α w Φg) :=
    (so_mul (Work.FTS.NonlinRows.smoothOpen_const_mul (-2 * α)
      (Work.FTS.NonlinRows.Rl1.smoothOpen_Vop_open
        (Work.FTS.GalFields.RHS.Sharp.smoothOpen_PhiTil hα hell))) hw.reg.Dz).congr
      (fun z θ _ _ _ => by simp only [Work.FTS.Nonlin.N3gg, Work.FTS.Nonlin.PhiTg]; try ring_nf)
  exact ⟨hsm.forall 4, Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4
    (Work.FTS.LocData.HkMem_const_mul α 4 (-2 * α) h1)
    (fun z _ θ _ => by simp only [Work.FTS.Nonlin.N3gg, Work.FTS.Nonlin.PhiTg]; try ring_nf)⟩

/-- `N₃^{gs} = -2α 𝒱(Φ̃_g)·D_zF_*`. -/
theorem good_N3gs (hα : 0 < α) (hα1 : α ≤ 1)
    (hell : Work.FTS.VocabO.EllPkgGo α Ce w Φg) :
    Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N3gs α w Φg) := by
  obtain ⟨Cwv, _, hwprod⟩ := Work.FTS.OpenPkg.wprod_field_winf
  obtain ⟨_, _, hDzFW⟩ := Work.FTS.Nonlinear.FstarPkg.DzFstar_W
  have hFsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α
  have h1 : Work.Spaces.HkMem α 4 (fun z θ =>
      Work.Spaces.Dz (Work.Construction.Fstar α) z θ *
        Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg) z θ) :=
    (hwprod α hα hα1 (Work.Spaces.Dz (Work.Construction.Fstar α))
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg)) hFsm.Dz
      (hDzFW α hα hα1).1 hell.V.1).1
  have hsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N3gs α w Φg) :=
    (so_mul (Work.FTS.NonlinRows.smoothOpen_const_mul (-2 * α)
      (Work.FTS.NonlinRows.Rl1.smoothOpen_Vop_open
        (Work.FTS.GalFields.RHS.Sharp.smoothOpen_PhiTil hα hell))) hFsm.Dz).congr
      (fun z θ _ _ _ => by simp only [Work.FTS.Nonlin.N3gs, Work.FTS.Nonlin.PhiTg]; try ring_nf)
  exact ⟨hsm.forall 4, Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4
    (Work.FTS.LocData.HkMem_const_mul α 4 (-2 * α) h1)
    (fun z _ θ _ => by simp only [Work.FTS.Nonlin.N3gs, Work.FTS.Nonlin.PhiTg]; try ring_nf)⟩

/-- `N₃^{sg} = -2α 𝒱(Φ̃_*)·D_z w = -2α·(((z+1)/z)𝒱(Φ̃_*))·((z/(1+z))D_z w)`. -/
theorem good_N3sg (hα : 0 < α) (hα1 : α ≤ 1)
    (hw : Work.FTS.ClassC.ClassC α w) (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N3sg α Φs w) := by
  obtain ⟨Cwv, _, hwprod⟩ := Work.FTS.OpenPkg.wprod_field_winf
  obtain ⟨Cm, _, hmulphi⟩ := Work.FTS.NonlinRows.NRow10aux.mul_phi_Hk
  have hmem5 : Work.Spaces.HkMem α 5 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 5 (by norm_num) hw.mem
  have hDzQ : Work.FTS.VocabO.HQo α 4 (Work.Spaces.Dz w) :=
    ⟨hw.reg.Dz, Work.FTS.EllipticEst.UopHk.HkMem_Dz_of_smoothOpen α 4 hw.reg hmem5⟩
  have hPhi : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.PhiTs α Φs) :=
    Work.FTS.NonlinRows.NRow10aux.smoothOpen_PhiTs hα hα1 hstar.toStarPkgo
  have hreg := Work.FTS.PhiStar.StarPkgo2Aux.FieldRegularity α (Work.FTS.Nonlin.PhiTs α Φs) hPhi
  have hH1sm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (z + 1) / z * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ) :=
    hreg.2.2.1
  have hH1W : Work.Spaces.WlInfMem α 4
      (fun z θ => (z + 1) / z * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ) :=
    hstar.VzW.1
  have hH2sm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z / (1 + z) * Work.Spaces.Dz w z θ) :=
    so_mul so_zdiv hDzQ.1
  have hH2mem : Work.Spaces.HkMem α 4 (fun z θ => z / (1 + z) * Work.Spaces.Dz w z θ) :=
    (hmulphi hα hα1 hDzQ).1
  have h1 : Work.Spaces.HkMem α 4 (fun z θ =>
      ((z + 1) / z * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ)
        * (z / (1 + z) * Work.Spaces.Dz w z θ)) :=
    (hwprod α hα hα1 _ _ hH1sm hH1W ⟨hH2sm, hH2mem⟩).1
  have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.Nonlin.N3sg α Φs w z θ
        = (-2 * α) * (((z + 1) / z * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ)
              * (z / (1 + z) * Work.Spaces.Dz w z θ)) := by
    intro z θ hz hθ hlt
    have hz0 : z ≠ 0 := ne_of_gt hz
    have h1z : (1 : ℝ) + z ≠ 0 := by linarith
    have hkey : (z + 1) / z * (z / (1 + z)) = (1 : ℝ) := by
      field_simp
      ring
    simp only [Work.FTS.Nonlin.N3sg]
    calc -2 * α * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ
          * Work.Spaces.Dz w z θ
        = (-2 * α) * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ
            * Work.Spaces.Dz w z θ * ((z + 1) / z * (z / (1 + z))) := by rw [hkey]; ring
      _ = (-2 * α) * (((z + 1) / z * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ)
            * (z / (1 + z) * Work.Spaces.Dz w z θ)) := by ring
  have hsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N3sg α Φs w) :=
    (Work.FTS.NonlinRows.smoothOpen_const_mul (-2 * α) (so_mul hH1sm hH2sm)).congr
      (fun z θ hz hθ hlt => (hpt z θ hz hθ hlt).symm)
  refine ⟨hsm.forall 4, ?_⟩
  exact Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4
    (Work.FTS.LocData.HkMem_const_mul α 4 (-2 * α) h1)
    (fun z hz θ hθ => (hpt z θ hz hθ.1 hθ.2).symm)

/-- `N₃^{**} = -2α 𝒱(Φ̃_*)·D_zF_*` (priced row 19). -/
theorem good_N3ss (hα : 0 < α) (hα1 : α ≤ 1)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N3ss α Φs) := by
  obtain ⟨_, _, hrow⟩ := Work.FTS.StrongPersist.L3Rhs.N3ssPriced
  have hPhi : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.PhiTs α Φs) :=
    Work.FTS.NonlinRows.NRow10aux.smoothOpen_PhiTs hα hα1 hstar.toStarPkgo
  have hFsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α
  have hsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N3ss α Φs) :=
    (so_mul (Work.FTS.NonlinRows.smoothOpen_const_mul (-2 * α)
      (Work.FTS.NonlinRows.Rl1.smoothOpen_Vop_open hPhi)) hFsm.Dz).congr
      (fun z θ _ _ _ => by simp only [Work.FTS.Nonlin.N3ss]; try ring_nf)
  exact ⟨hsm.forall 4, (hrow α ⟨hα, hα1⟩ Cs Φs hstar).1⟩

/-- `N₄^{gg} = -(1/2) FK(w)·D_θ w`. -/
theorem good_N4gg (hα : 0 < α) (hα1 : α ≤ 1)
    (hw : Work.FTS.ClassC.ClassC α w) :
    Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N4gg α w) := by
  obtain ⟨Cp, _, hprod⟩ := Work.FTS.OpenPkg.prod_field
  obtain ⟨Cf, _, hfkH⟩ := Work.FTS.OpenPkg.fkH_field
  have hmem4 : Work.Spaces.HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 4 (by norm_num) hw.mem
  have hmem5 : Work.Spaces.HkMem α 5 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 5 (by norm_num) hw.mem
  have hFKQ : Work.FTS.VocabO.HQo α 4 (fun z _ => Work.Construction.FK w z) :=
    ⟨so_FKw hw, (hfkH α hα hα1 w ⟨hw.reg, hmem4⟩ hw.l12).1⟩
  have hDthQ : Work.FTS.VocabO.HQo α 4 (Work.Spaces.Dth w) :=
    ⟨hw.reg.Dth, Work.FTS.StrongEps.ClassCRHS.hkMem_Dth_of_smoothOpen hα 4 hw.reg hmem5⟩
  have h1 : Work.Spaces.HkMem α 4 (fun z θ =>
      Work.Construction.FK w z * Work.Spaces.Dth w z θ) :=
    (hprod α hα hα1 (fun z _ => Work.Construction.FK w z) (Work.Spaces.Dth w)
      hFKQ hDthQ).1
  have hsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N4gg α w) :=
    (so_mul (Work.FTS.NonlinRows.smoothOpen_const_mul (-(1 / 2)) (so_FKw hw))
      hw.reg.Dth).congr
      (fun z θ _ _ _ => by simp only [Work.FTS.Nonlin.N4gg]; try ring_nf)
  exact ⟨hsm.forall 4, Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4
    (Work.FTS.LocData.HkMem_const_mul α 4 (-(1 / 2)) h1)
    (fun z _ θ _ => by simp only [Work.FTS.Nonlin.N4gg]; try ring_nf)⟩

/-- `N₄^{gs} = -(1/2) FK(w)·D_θF_*`. -/
theorem good_N4gs (hα : 0 < α) (hα1 : α ≤ 1)
    (hw : Work.FTS.ClassC.ClassC α w) :
    Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N4gs α w) := by
  obtain ⟨Cwv, _, hwprod⟩ := Work.FTS.OpenPkg.wprod_field_winf
  obtain ⟨Cf, _, hfkH⟩ := Work.FTS.OpenPkg.fkH_field
  obtain ⟨_, _, hDthFW⟩ := Work.FTS.Nonlinear.FstarPkg.DthFstar_W
  have hmem4 : Work.Spaces.HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 4 (by norm_num) hw.mem
  have hFsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α
  have hFKQ : Work.FTS.VocabO.HQo α 4 (fun z _ => Work.Construction.FK w z) :=
    ⟨so_FKw hw, (hfkH α hα hα1 w ⟨hw.reg, hmem4⟩ hw.l12).1⟩
  have h1 : Work.Spaces.HkMem α 4 (fun z θ =>
      Work.Spaces.Dth (Work.Construction.Fstar α) z θ * Work.Construction.FK w z) :=
    (hwprod α hα hα1 (Work.Spaces.Dth (Work.Construction.Fstar α))
      (fun z _ => Work.Construction.FK w z) hFsm.Dth (hDthFW α hα hα1).1 hFKQ).1
  have hsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N4gs α w) :=
    (so_mul (so_mul (Work.FTS.NonlinRows.smoothOpen_const_mul (-(1 / 2))
      (Work.FTS.GalFields.RHS.smoothOpen_sin_two)) (so_FKw hw)) hFsm.pth).congr
      (fun z θ _ _ _ => by
        simp only [Work.FTS.Nonlin.N4gs, Work.Construction.s2, Work.Spaces.Dth]; try ring_nf)
  exact ⟨hsm.forall 4, Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4
    (Work.FTS.LocData.HkMem_const_mul α 4 (-(1 / 2)) h1)
    (fun z _ θ _ => by
      simp only [Work.FTS.Nonlin.N4gs, Work.Construction.s2, Work.Spaces.Dth]; try ring_nf)⟩

/-- `N₄^{sg} = -(1/2) FK(F_*)·D_θ w = -α·(hKer·D_θ w)`. -/
theorem good_N4sg (hα : 0 < α) (hα1 : α ≤ 1)
    (hw : Work.FTS.ClassC.ClassC α w) :
    Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N4sg α w) := by
  obtain ⟨Cwv, _, hwprod⟩ := Work.FTS.OpenPkg.wprod_field_winf
  have hmem5 : Work.Spaces.HkMem α 5 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 5 (by norm_num) hw.mem
  have hker := Work.FTS.Nonlinear.Pieces.RNP.hKerConstWlInf α (2 * α)
  have hkersm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => 2 * α * Work.Spaces.hKer z) :=
    Work.FTS.NonlinRows.hKerConst_smoothOpen (2 * α)
  have hDthQ : Work.FTS.VocabO.HQo α 4 (Work.Spaces.Dth w) :=
    ⟨hw.reg.Dth, Work.FTS.StrongEps.ClassCRHS.hkMem_Dth_of_smoothOpen hα 4 hw.reg hmem5⟩
  have h1 : Work.Spaces.HkMem α 4 (fun z θ =>
      (2 * α * Work.Spaces.hKer z) * Work.Spaces.Dth w z θ) :=
    (hwprod α hα hα1 (fun z _ => 2 * α * Work.Spaces.hKer z) (Work.Spaces.Dth w)
      hkersm hker.1 hDthQ).1
  have hsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N4sg α w) :=
    (so_mul (Work.FTS.NonlinRows.smoothOpen_const_mul (-(1 / 2))
      (Work.FTS.GalFields.RHS.smoothOpen_FK_Fstar_rad α hα hα1)) hw.reg.Dth).congr
      (fun z θ _ _ _ => by simp only [Work.FTS.Nonlin.N4sg]; try ring_nf)
  refine ⟨hsm.forall 4, ?_⟩
  refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4
    (Work.FTS.LocData.HkMem_const_mul α 4 (-(1 / 2)) h1) (fun z hz θ hθ => ?_)
  have hFK := Work.FTS.Nonlinear.FstarPkg.FK_Fstar (α := α) (z := z) hα hα1
  simp only [Work.FTS.Nonlin.N4sg]
  rw [hFK, Work.Spaces.hKer_apply]
  ring_nf

/-- `N₄^{**} = -(1/2) sin(2θ) FK(F_*) ∂_θF_*` (priced row 23). -/
theorem good_N4ss (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N4ss α) := by
  obtain ⟨_, _, hrow⟩ := Work.FTS.StrongPersist.L3Rhs.N4ssPriced
  have hFsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α
  have hsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N4ss α) :=
    (so_mul (so_mul (Work.FTS.NonlinRows.smoothOpen_const_mul (-(1 / 2))
      (Work.FTS.GalFields.RHS.smoothOpen_sin_two))
      (Work.FTS.GalFields.RHS.smoothOpen_FK_Fstar_rad α hα hα1)) hFsm.pth).congr
      (fun z θ _ _ _ => by simp only [Work.FTS.Nonlin.N4ss, Work.Construction.s2]; try ring_nf)
  exact ⟨hsm.forall 4, (hrow α ⟨hα, hα1⟩).1⟩

/-- `N₅^{gg} = -sin²θ·FK(w)·w`. -/
theorem good_N5gg (hα : 0 < α) (hα1 : α ≤ 1)
    (hw : Work.FTS.ClassC.ClassC α w) :
    Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N5gg w) := by
  obtain ⟨Cp, _, hprod⟩ := Work.FTS.OpenPkg.prod_field
  obtain ⟨Cf, _, hfkH⟩ := Work.FTS.OpenPkg.fkH_field
  obtain ⟨Ca, _, hang⟩ := Work.FTS.OpenPkg.angmul_field
  obtain ⟨Bs, hBs, hasm, hab, hdab⟩ := angSq_data
  have hmem4 : Work.Spaces.HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 4 (by norm_num) hw.mem
  have hFKQ : Work.FTS.VocabO.HQo α 4 (fun z _ => Work.Construction.FK w z) :=
    ⟨so_FKw hw, (hfkH α hα hα1 w ⟨hw.reg, hmem4⟩ hw.l12).1⟩
  have h2 : Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.FK w z * w z θ) :=
    (hprod α hα hα1 (fun z _ => Work.Construction.FK w z) w hFKQ ⟨hw.reg, hmem4⟩).1
  have h2sm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.FK w z * w z θ) := so_mul (so_FKw hw) hw.reg
  have h3 := hang α hα hα1 (fun θ => -((Real.sin θ) ^ 2))
    (fun z θ => Work.Construction.FK w z * w z θ) Bs hasm hab hdab h2sm h2
  have hsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N5gg w) :=
    (so_mul (so_mul (Work.FTS.NonlinRows.smoothOpen_const_mul (-1)
      (Work.FTS.GalFields.RHS.smoothOpen_sin_sq)) (so_FKw hw)) hw.reg).congr
      (fun z θ _ _ _ => by simp only [Work.FTS.Nonlin.N5gg]; try ring_nf)
  exact ⟨hsm.forall 4, Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 h3.1
    (fun z _ θ _ => by simp only [Work.FTS.Nonlin.N5gg]; try ring_nf)⟩

/-- `N₅^{gs} = -sin²θ·FK(w)·F_*`. -/
theorem good_N5gs (hα : 0 < α) (hα1 : α ≤ 1)
    (hw : Work.FTS.ClassC.ClassC α w) :
    Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N5gs α w) := by
  obtain ⟨Cwv, _, hwprod⟩ := Work.FTS.OpenPkg.wprod_field_winf
  obtain ⟨Cf, _, hfkH⟩ := Work.FTS.OpenPkg.fkH_field
  obtain ⟨Ca, _, hang⟩ := Work.FTS.OpenPkg.angmul_field
  obtain ⟨Bs, hBs, hasm, hab, hdab⟩ := angSq_data
  have hmem4 : Work.Spaces.HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 4 (by norm_num) hw.mem
  have hFsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α
  obtain ⟨_, _, hFstarW⟩ := Work.FTS.Nonlinear.FstarPkg.Fstar_W
  have hFKQ : Work.FTS.VocabO.HQo α 4 (fun z _ => Work.Construction.FK w z) :=
    ⟨so_FKw hw, (hfkH α hα hα1 w ⟨hw.reg, hmem4⟩ hw.l12).1⟩
  have h2 : Work.Spaces.HkMem α 4 (fun z θ =>
      Work.Construction.Fstar α z θ * Work.Construction.FK w z) :=
    (hwprod α hα hα1 (Work.Construction.Fstar α) (fun z _ => Work.Construction.FK w z)
      hFsm (hFstarW α hα hα1).1 hFKQ).1
  have h2sm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.Fstar α z θ * Work.Construction.FK w z) :=
    so_mul hFsm (so_FKw hw)
  have h3 := hang α hα hα1 (fun θ => -((Real.sin θ) ^ 2))
    (fun z θ => Work.Construction.Fstar α z θ * Work.Construction.FK w z) Bs hasm hab hdab
    h2sm h2
  have hsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N5gs α w) :=
    (so_mul (so_mul (Work.FTS.NonlinRows.smoothOpen_const_mul (-1)
      (Work.FTS.GalFields.RHS.smoothOpen_sin_sq)) (so_FKw hw)) hFsm).congr
      (fun z θ _ _ _ => by simp only [Work.FTS.Nonlin.N5gs]; try ring_nf)
  exact ⟨hsm.forall 4, Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 h3.1
    (fun z _ θ _ => by simp only [Work.FTS.Nonlin.N5gs]; try ring_nf)⟩

/-- `N₅^{sg} = -sin²θ·FK(F_*)·w = -2α·sin²θ·(hKer·w)`. -/
theorem good_N5sg (hα : 0 < α) (hα1 : α ≤ 1)
    (hw : Work.FTS.ClassC.ClassC α w) :
    Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N5sg α w) := by
  obtain ⟨Cwv, _, hwprod⟩ := Work.FTS.OpenPkg.wprod_field_winf
  obtain ⟨Ca, _, hang⟩ := Work.FTS.OpenPkg.angmul_field
  obtain ⟨Bs, hBs, hasm, hab, hdab⟩ := angSq_data
  have hmem4 : Work.Spaces.HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 4 (by norm_num) hw.mem
  have hker := Work.FTS.Nonlinear.Pieces.RNP.hKerConstWlInf α 1
  have hkersm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => 1 * Work.Spaces.hKer z) :=
    Work.FTS.NonlinRows.hKerConst_smoothOpen 1
  have h1 : Work.Spaces.HkMem α 4 (fun z θ => (1 * Work.Spaces.hKer z) * w z θ) :=
    (hwprod α hα hα1 (fun z _ => 1 * Work.Spaces.hKer z) w hkersm hker.1
      ⟨hw.reg, hmem4⟩).1
  have h1sm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => (1 * Work.Spaces.hKer z) * w z θ) :=
    so_mul hkersm hw.reg
  have h2 : Work.Spaces.HkMem α 4 (fun z θ => (2 * α) * ((1 * Work.Spaces.hKer z) * w z θ)) :=
    Work.FTS.LocData.HkMem_const_mul α 4 (2 * α) h1
  have h2sm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (2 * α) * ((1 * Work.Spaces.hKer z) * w z θ)) :=
    Work.FTS.NonlinRows.smoothOpen_const_mul (2 * α) h1sm
  have h3 := hang α hα hα1 (fun θ => -((Real.sin θ) ^ 2))
    (fun z θ => (2 * α) * ((1 * Work.Spaces.hKer z) * w z θ)) Bs hasm hab hdab h2sm h2
  have hsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N5sg α w) :=
    (so_mul (so_mul (Work.FTS.NonlinRows.smoothOpen_const_mul (-1)
      (Work.FTS.GalFields.RHS.smoothOpen_sin_sq))
      (Work.FTS.GalFields.RHS.smoothOpen_FK_Fstar_rad α hα hα1)) hw.reg).congr
      (fun z θ _ _ _ => by simp only [Work.FTS.Nonlin.N5sg]; try ring_nf)
  refine ⟨hsm.forall 4, ?_⟩
  refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 h3.1 (fun z hz θ hθ => ?_)
  have hFK := Work.FTS.Nonlinear.FstarPkg.FK_Fstar (α := α) (z := z) hα hα1
  simp only [Work.FTS.Nonlin.N5sg]
  rw [hFK, Work.Spaces.hKer_apply]
  ring_nf

/-- `N₅^{**} = -sin²θ FK(F_*) F_*` (priced row 26). -/
theorem good_N5ss (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N5ss α) := by
  obtain ⟨_, _, hrow⟩ := Work.FTS.StrongPersist.L3Rhs.N5ssPriced
  have hFsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α
  have hsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N5ss α) :=
    (so_mul (so_mul (Work.FTS.NonlinRows.smoothOpen_const_mul (-1)
      (Work.FTS.GalFields.RHS.smoothOpen_sin_sq))
      (Work.FTS.GalFields.RHS.smoothOpen_FK_Fstar_rad α hα hα1)) hFsm).congr
      (fun z θ _ _ _ => by simp only [Work.FTS.Nonlin.N5ss]; try ring_nf)
  exact ⟨hsm.forall 4, (hrow α ⟨hα, hα1⟩).1⟩

end Work.FTS.StrongEps.EpsZero.ClassCHk
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.SmoothK5 =====
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
set_option linter.unusedVariables false

/-- **`SmoothOpen` of the twenty `NBlk` pieces**, for `EllPkgK α 6` elliptic data. -/
theorem NBlk_smoothK {α Ce Cs6 : ℝ} {w Φs Φg : Fn} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hw : Work.FTS.ClassC.ClassC α w) (hell : Work.FTS.ClassC.EllPkgK α 6 Ce w Φg)
    (hstar : Work.FTS.StrongPersist.StarPkg6 α Cs6 Φs) :
    ∀ k ∈ Finset.range 20,
      Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k) := by
  have hsw : Work.FTS.VocabO.StarPkgo α Cs6 Φs := hstar.toStarPkgo2.toStarPkgo
  have hRsm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg)) := hell.R.1.1
  have hUcsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α w Φg) z θ / Work.Construction.s2 θ) :=
    hell.U.1.1
  have hVcsm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg)) := hell.V.1.1
  have hRssm : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      (z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_Rs_of_star hα0 hα1 hsw
  have hUssm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => (z + 1) / z *
      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Work.Construction.s2 θ)) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_Us_of_star hα0 hα1 hsw
  have hVssm : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      (z + 1) / z * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_Vs_of_star hα0 hα1 hsw
  have hFWsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Construction.Fstar α z θ) :=
    Work.FTS.EllipticEst.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  have hDthFssm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.Dth (Work.Construction.Fstar α)) := hFWsm.Dth
  have hDzFssm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.Dz (Work.Construction.Fstar α)) := hFWsm.Dz
  have hDthwsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth w) := hw.reg.Dth
  have hDzwsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz w) := hw.reg.Dz
  have hFKesm : Work.FTS.EllipticEst.SmoothOpen
      (fun z _ => Work.Construction.FK (Work.Construction.Fstar α) z) :=
    Work.FTS.GalFields.RHS.smoothOpen_FK_Fstar_rad α hα0 hα1
  have hFKws : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.FK w z) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_FKw_of_classC hw
  have hFKnegsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z _ : ℝ => (-(2 * α)) * Work.Spaces.hKer z) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_FKneg α
  have hSinSq : Work.FTS.EllipticEst.SmoothOpen (fun x θ : ℝ => -Real.sin θ ^ 2) :=
    Work.FTS.Nonlinear.Open.row25_smoothOpen_neg_sinSq
  have hG : ∀ (A B : Fn), Work.FTS.EllipticEst.SmoothOpen A →
      Work.FTS.EllipticEst.SmoothOpen B →
      Work.FTS.EllipticEst.SmoothOpen (fun z θ => A z θ * B z θ) :=
    fun A B hA hB => Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hA hB
  have hC : ∀ (c : ℝ) (A : Fn), Work.FTS.EllipticEst.SmoothOpen A →
      Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * A z θ) :=
    fun c A hA => Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl c hA
  have hpw := hG (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg)) w hRsm hw.reg
  have hps := hG (fun z θ => Work.Construction.Fstar α z θ)
    (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg)) hFWsm hRsm
  have hphiw : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z / (1 + z) * w z θ) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_phi_mul hw.reg
  have hphiFs : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_phi_mul hFWsm
  have hphiDthw : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z / (1 + z) * Work.Spaces.Dth w z θ) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_phi_mul (hw.reg.Dth)
  have hphiDzw : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z / (1 + z) * Work.Spaces.Dz w z θ) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_phi_mul (hw.reg.Dz)
  have hphiDthFs : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_phi_mul hFWsm.Dth
  have hphiDzFs : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_phi_mul hFWsm.Dz
  intro k hk
  have hk20 : k < 20 := Finset.mem_range.mp hk
  interval_cases k
  · simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]; exact hC 2 _ hpw
  · simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]; exact hC 2 _ hps
  · simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]; exact hC 2 _ (hG _ _ hRssm hphiw)
  · simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]; exact hC 2 _ (hG _ _ hRssm hphiFs)
  · simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]; exact hC (-2) _ (hG _ _ hUcsm hDthwsm)
  · simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]; exact hC (-2) _ (hG _ _ hDthFssm hUcsm)
  · simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]; exact hC (-2) _ (hG _ _ hUssm hphiDthw)
  · simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]; exact hC (-2) _ (hG _ _ hUssm hphiDthFs)
  · simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]; exact hC (-(2 * α)) _ (hG _ _ hVcsm hDzwsm)
  · simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]; exact hC (-(2 * α)) _ (hG _ _ hDzFssm hVcsm)
  · simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]; exact hC (-(2 * α)) _ (hG _ _ hVssm hphiDzw)
  · simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]; exact hC (-(2 * α)) _ (hG _ _ hVssm hphiDzFs)
  · simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]; exact hC (-(1 / 2)) _ (hG _ _ hFKws hDthwsm)
  · simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]; exact hC (-(1 / 2)) _ (hG _ _ hDthFssm hFKws)
  · simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]; exact hC (1 / 2) _ (hG _ _ hFKnegsm hDthwsm)
  · simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]; exact hC (-(1 / 2)) _ (hG _ _ hFKesm hDthFssm)
  · simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]
    exact hG _ _ hSinSq (hG _ _ hFKws hw.reg)
  · simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]
    exact hG _ _ hSinSq (hG _ _ hFWsm hFKws)
  · simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]
    exact hG _ _ hSinSq (hG _ _ hFKesm hw.reg)
  · simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]
    exact hG _ _ hSinSq (hG _ _ hFKesm hFWsm)

/-- **`SmoothOpen (N α (F_*+w) (Φs+Φg))`** for `EllPkgK α 6` elliptic data (conjunct 5 of
`ClassCRHS.SmoothOpenRHS`, transcribed). -/
theorem SmoothOpenN_K {α Ce Cs6 : ℝ} {Φs w Φg : Fn}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hw : Work.FTS.ClassC.ClassC α w)
    (hell : Work.FTS.ClassC.EllPkgK α 6 Ce w Φg)
    (hstar : Work.FTS.StrongPersist.StarPkg6 α Cs6 Φs) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.N α (Work.Construction.Ftot α w)
      (fun z θ => Φs z θ + Φg z θ)) := by
  have hmem4 : Work.Spaces.HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 4 (by norm_num) hw.mem
  have hL12w : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.L12 w z) :=
    Work.FTS.NonlinRows.smoothOpen_L12_radial hα hell.smooth hell.V.1.1
  have hFKw : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.FK w z) := by
    have hfs : Work.FTS.EllipticEst.SmoothOpen
        (fun z (_ : ℝ) => Work.Elliptic.Fstar w z) :=
      Work.FTS.NonlinRows.smoothOpen_radial (r := Work.Elliptic.Fstar w) hw.fsm
    refine (Work.FTS.NonlinRows.smoothOpen_const_mul 3 hfs).congr ?_
    intro z _ hz _ _
    exact (Work.FTS_RegExport.RXT.velPert_FK_eq w z).symm
  have hL12F : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.L12 (Work.Construction.Fstar α) z) :=
    Work.FTS.GalFields.RHS.smoothOpen_L12_Fstar_rad α hα hα1
  have hFKF : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.FK (Work.Construction.Fstar α) z) :=
    Work.FTS.GalFields.RHS.smoothOpen_FK_Fstar_rad α hα hα1
  have hL12tot : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.L12 (Work.Construction.Ftot α w) z) :=
    (Work.FTS.NonlinRows.smoothOpen_add hL12F hL12w).congr (by
      intro z _ hz _ _
      exact (Work.FTS.StrongPersist.H6Rows.NZaux.L12AddFstar hα hα1 hw.reg hmem4 z hz).symm)
  have hFKadd : ∀ z : ℝ, 0 < z → Work.Construction.FK (Work.Construction.Ftot α w) z
      = Work.Construction.FK (Work.Construction.Fstar α) z + Work.Construction.FK w z := by
    intro z hz
    exact Work.FTS.GalFields.RHS.FK_add_of_slices
      (a := Work.Construction.Fstar α) (b := w) (ne_of_gt hz)
      (Work.Stability.integrableOn_slice_Fstar α hα z)
      (Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hw.reg hmem4 hz)
  have hFKtot : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.FK (Work.Construction.Ftot α w) z) :=
    (Work.FTS.NonlinRows.smoothOpen_add hFKF hFKw).congr (by
      intro z _ hz _ _
      exact (hFKadd z hz).symm)
  have hΦ : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Φs z θ + Φg z θ) :=
    Work.FTS.NonlinRows.smoothOpen_add hstar.smooth hell.smooth
  have hTheta : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (1 / (4 * α)) * (Real.sin (2 * θ)
        * Work.Construction.L12 (Work.Construction.Ftot α w) z)) :=
    Work.FTS.NonlinRows.smoothOpen_const_mul (1 / (4 * α))
      (Work.FTS.NonlinRows.smoothOpen_mul
        (Work.FTS.GalFields.RHS.smoothOpen_sin_two) hL12tot)
  have hPsi_eq : Work.Construction.PhiTil α (Work.Construction.Ftot α w)
        (fun z θ => Φs z θ + Φg z θ)
      = fun z θ => (Φs z θ + Φg z θ)
        - (1 / (4 * α)) * (Real.sin (2 * θ)
          * Work.Construction.L12 (Work.Construction.Ftot α w) z) := by
    funext z θ
    simp only [Work.Construction.PhiTil, Work.Construction.Theta, Work.Construction.s2]
    ring
  have hPsi : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.PhiTil α (Work.Construction.Ftot α w)
        (fun z θ => Φs z θ + Φg z θ)) :=
    hPsi_eq ▸ (Work.FTS.NonlinRows.smoothOpen_sub hΦ hTheta)
  have hRop := Work.FTS.NonlinRows.smoothOpen_Rop (α := α) hPsi
  have hUop : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Ftot α w)
        (fun z θ => Φs z θ + Φg z θ))) :=
    Work.FTS.EllipticEst.smoothOpen_Uop hPsi
  have hVop := Work.FTS.NonlinRows.smoothOpen_Vop hPsi
  have hF : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Ftot α w) :=
    Work.FTS.NonlinRows.smoothOpen_add
      (Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)) hw.reg
  have hpthF := Work.FTS.EllipticEst.SmoothOpen.pth hF
  have hDzF := Work.FTS.EllipticEst.SmoothOpen.Dz hF
  have t1 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (2 * Work.Construction.Rop α (Work.Construction.PhiTil α
          (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ)) z θ)
        * Work.Construction.Ftot α w z θ) :=
    Work.FTS.NonlinRows.smoothOpen_mul
      (Work.FTS.NonlinRows.smoothOpen_const_mul 2 hRop) hF
  have t2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (2 * Work.Construction.Uop α (Work.Construction.PhiTil α
          (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ)) z θ)
        * Work.Spaces.pth (Work.Construction.Ftot α w) z θ) :=
    Work.FTS.NonlinRows.smoothOpen_mul
      (Work.FTS.NonlinRows.smoothOpen_const_mul 2 hUop) hpthF
  have t3 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => ((2 * α) * Work.Construction.Vop (Work.Construction.PhiTil α
          (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ)) z θ)
        * Work.Spaces.Dz (Work.Construction.Ftot α w) z θ) :=
    Work.FTS.NonlinRows.smoothOpen_mul
      (Work.FTS.NonlinRows.smoothOpen_const_mul (2 * α) hVop) hDzF
  have t4 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (((1 / 2) * Real.sin (2 * θ)) * Work.Construction.FK
          (Work.Construction.Ftot α w) z)
        * Work.Spaces.pth (Work.Construction.Ftot α w) z θ) :=
    Work.FTS.NonlinRows.smoothOpen_mul
      (Work.FTS.NonlinRows.smoothOpen_mul
        (Work.FTS.NonlinRows.smoothOpen_const_mul (1 / 2)
          (Work.FTS.GalFields.RHS.smoothOpen_sin_two)) hFKtot) hpthF
  have t5 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Ftot α w) z)
        * Work.Construction.Ftot α w z θ) :=
    Work.FTS.NonlinRows.smoothOpen_mul
      (Work.FTS.NonlinRows.smoothOpen_mul
        (Work.FTS.GalFields.RHS.smoothOpen_sin_sq) hFKtot) hF
  have hmain : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => 2 * Work.Construction.Rop α (Work.Construction.PhiTil α
            (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ)) z θ
          * Work.Construction.Ftot α w z θ
        - 2 * Work.Construction.Uop α (Work.Construction.PhiTil α
            (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ)) z θ
          * Work.Spaces.pth (Work.Construction.Ftot α w) z θ
        - 2 * α * Work.Construction.Vop (Work.Construction.PhiTil α
            (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ)) z θ
          * Work.Spaces.Dz (Work.Construction.Ftot α w) z θ
        - (1 / 2) * Real.sin (2 * θ) * Work.Construction.FK (Work.Construction.Ftot α w) z
          * Work.Spaces.pth (Work.Construction.Ftot α w) z θ
        - Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Ftot α w) z
          * Work.Construction.Ftot α w z θ) :=
    Work.FTS.NonlinRows.smoothOpen_sub
      (Work.FTS.NonlinRows.smoothOpen_sub
        (Work.FTS.NonlinRows.smoothOpen_sub
          (Work.FTS.NonlinRows.smoothOpen_sub t1 t2) t3) t4) t5
  change Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => 2 * Work.Construction.Rop α (Work.Construction.PhiTil α
            (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ)) z θ
          * Work.Construction.Ftot α w z θ
        - 2 * Work.Construction.Uop α (Work.Construction.PhiTil α
            (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ)) z θ
          * Work.Spaces.pth (Work.Construction.Ftot α w) z θ
        - 2 * α * Work.Construction.Vop (Work.Construction.PhiTil α
            (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ)) z θ
          * Work.Spaces.Dz (Work.Construction.Ftot α w) z θ
        - (1 / 2) * Work.Construction.s2 θ * Work.Construction.FK
            (Work.Construction.Ftot α w) z
          * Work.Spaces.pth (Work.Construction.Ftot α w) z θ
        - Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Ftot α w) z
          * Work.Construction.Ftot α w z θ)
  exact hmain

end Work.FTS.StrongEps.H5
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.pth_vop_pert_tendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.pth_vop_pert_tendsto` — the `∂_θ`-jet of `𝒱(Φ̃_n)` converges

For the perturbation residual `Φ̃(τ) = PhiTil (pExp α) (g(τ)) (E (g(τ)))` of the dynamic
modulation, the angular transport coefficient `𝒱(Φ̃) = ∂_θΦ̃ - tan θ · Φ̃` is bounded (in
`pth_vop_slot_bd`) by `max Ce 0 · α^{-1/2} · (max C₀ 0 · α²)`.  The liminf step of that bound is
taken along the class-`C` approximating sequence `gn` of the `LimApprox` clause of `DynOK'`,
and it needs exactly the statement proved here: for every point `(z,θ)` of the open quadrant
(`z > 0`, `0 < θ < π/2`) the `∂_θ`-jets of the coefficients
`𝒱(Φ̃_n)` — with `Φ̃_n = PhiTil (pExp α) (gn n (τ)) (E (gn n (τ)))` — converge to the
`∂_θ`-jet of the limit coefficient `𝒱(Φ̃)`.

## Route

1. `∂_θ𝒱(Φ̃) = D_θ(𝒱(Φ̃))/sin 2θ` on the open quadrant (`D_θ = sin 2θ · ∂_θ`), so it suffices
   to prove the convergence of the mixed jet `D_z^0 D_θ^1` of the *function*
   `(z,θ) ↦ 𝒱(Φ̃_n)(z,θ)`;
2. that is the `(j,i) = (0,1)` instance of the slot-convergence theorem
   `Slots.v2_SlotJetsTendsto`, whose hypotheses are the `C³`-regularity of the residuals and the
   convergence of their mixed jets up to order `3`;
3. the jets of the residual split as the difference of the jets of `E(gn n(τ))` and of
   `Θ(gn n(τ)) = (1/(4α)) sin 2θ · L₁₂(gn n(τ))`:
   * the `E`-jets converge by the limit closure `EllLimOK3` at order `3` (the limit clause of
     `LimApprox` at order `4` supplies its hypotheses), and `E` of the *approximants* is `C³`
     because `EllLimOK3` may also be applied to the constant sequence `n ↦ gn n(τ)` with itself
     as limit (a constant sequence converges trivially);
   * the `Θ`-jets converge by `Slots.v2_thetaJetsTendsto` from the convergence of the `D_z`-jets
     of `L₁₂(gn n(τ))` (`Slots.v2_L12DzIterTendsto`, whose pointwise bound is the trace-free
     `ℋ⁴ → L^∞` trade-off `RXA1w.abs_mixed_le_HkNorm_C4_w_proved`); the `C³`-regularity of `Θ`
     of a class-`C` datum is `ClassC.fsm` fed into `contDiffOn_three_L12`;
4. the `C³`-regularity of the *limit* residual is `pert_tilde_contDiffOn`, and that of `Θ` of
   the limit is obtained by subtraction from the former and `E` of the limit.
-/

namespace Work.FTS_RegExport.RXT.Sys

open scoped Real Topology
open Set Filter

set_option autoImplicit false

open Work.FTS.Galerkin (Fn Fam slice)

/-- `D_z^0D_θ^1f = sin(2θ)·∂_θf`: the plain `θ`-derivative is the mixed jet divided by
`sin(2θ)`. -/
private theorem pth_eq_mixed_zero_one_div {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hs : Real.sin (2 * θ) ≠ 0) :
    Work.Spaces.pth f z θ = Work.Spaces.mixed 0 1 f z θ / Real.sin (2 * θ) := by
  rw [show Work.Spaces.mixed 0 1 f z θ = Real.sin (2 * θ) * Work.Spaces.pth f z θ from by
    simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_succ,
      Work.Spaces.DthIter_zero, Work.Spaces.Dth]]
  field_simp

theorem pth_vop_pert_tendsto {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) S)
    {gn : ℕ → Work.FTS.Galerkin.Fam} {B : ℝ}
    (hApprox : ∀ n, ∀ σ ∈ Set.Icc (0 : ℝ) S,
      Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice (gn n) σ) ∧
      Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice (gn n) σ)
        ≤ C₀ * (Work.FTS.Regularity.pExp α) ^ 2 ∧
      Work.FTS.StrongGlobal.Xn6 (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice (gn n) σ) ≤ B)
    (hJet : ∀ σ ∈ Set.Icc (0 : ℝ) S, ∀ j i : ℕ, j + i ≤ 4 → ∀ z θ : ℝ,
      (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n => Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (gn n) σ) z θ)
        Filter.atTop (nhds (Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g σ) z θ))) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Filter.Tendsto (fun n => Work.Spaces.pth (Work.Construction.Vop (fun z θ =>
          Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice (gn n) τ)
            (E (Work.FTS.Galerkin.slice (gn n) τ)) z θ)) z θ)
        Filter.atTop
        (nhds (Work.Spaces.pth (Work.Construction.Vop (fun z θ =>
          Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice g τ)
            (E (Work.FTS.Galerkin.slice g τ)) z θ)) z θ)) := by
  have hαG : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  have hτ0 : (0 : ℝ) ≤ τ := hτ.1
  -- ## the data of the limit slice
  have hF4 : ContDiffOn ℝ 4 (Function.uncurry (slice g τ)) Work.FTS.EllipticEst.Q0 :=
    hOK.1.1.c4 τ hτ0
  -- ## the regularity of the class-`C` approximants
  have hReg : ∀ n : ℕ,
      ContDiffOn ℝ 4 (Function.uncurry (slice (gn n) τ)) Work.FTS.EllipticEst.Q0 ∧
      Work.Spaces.HkMem (Work.FTS.Regularity.pExp α) 4 (slice (gn n) τ) ∧
      Work.FTS.Nonlin.BdryTraces (Work.FTS.Regularity.pExp α) 4 (slice (gn n) τ) ∧
      Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4 (slice (gn n) τ)
        ≤ max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2 := by
    intro n
    obtain ⟨hCn, hXn, _⟩ := hApprox n τ hτ
    have h2 : C₀ * (Work.FTS.Regularity.pExp α) ^ 2
        ≤ max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (sq_nonneg _)
    exact ⟨hCn.reg.of_le (by norm_num),
      Work.FTS.IPGen.HkMem_mono_le hCn.reg 4 (by norm_num) hCn.mem,
      hCn.bdry_le_six (by norm_num), le_trans hXn h2⟩
  -- ## the `E`-jets of the limit slice (order `3`); `E` of the limit is `C³`
  obtain ⟨_hBsl, hElim3, hEconv⟩ := hEL3 (fun n => slice (gn n) τ) (slice g τ) B
    (fun n => (hApprox n τ hτ).1) (fun n => (hApprox n τ hτ).2.2) hF4
    (fun j i hji z' θ' hzθ => hJet τ hτ j i hji z' θ' hzθ)
  -- ## `E` of the approximants is `C³` (the constant-sequence instance of `EllLimOK3`)
  have hΦ3c : ∀ n : ℕ, ContDiffOn ℝ 3
      (Function.uncurry (fun z θ => E (slice (gn n) τ) z θ)) Work.FTS.EllipticEst.Q0 := by
    intro n
    exact (hEL3 (fun _ => slice (gn n) τ) (slice (gn n) τ) B
      (fun _ => (hApprox n τ hτ).1) (fun _ => (hApprox n τ hτ).2.2)
      (hReg n).1
      (fun j i hji z' θ' hzθ => tendsto_const_nhds)).2.1
  -- ## `Θ` of a class-`C` datum is `C³` (all-order smoothness of the angular moment)
  have hΘ3 : ∀ n : ℕ, ContDiffOn ℝ 3 (Function.uncurry
      (Work.Construction.Theta (Work.FTS.Regularity.pExp α) (slice (gn n) τ)))
      Work.FTS.EllipticEst.Q0 := by
    intro n
    refine velPert_contDiffOn_Theta (α := Work.FTS.Regularity.pExp α) ?_
    refine contDiffOn_three_L12 ?_
    have h1 : ContDiffOn ℝ 2 (fun z => 3 * Work.Elliptic.Fstar (slice (gn n) τ) z) (Set.Ioi 0) :=
      contDiffOn_const.mul ((hApprox n τ hτ).1.fsm 2)
    refine h1.congr fun z' _ => ?_
    rw [velPert_FK_eq]
  -- ## the residual `Φ̃_n = E(gn n(τ)) - Θ(gn n(τ))` is `C³`
  have hΞ3 : ∀ n : ℕ, ContDiffOn ℝ 3 (Function.uncurry (fun z θ =>
      Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
        (E (slice (gn n) τ)) z θ)) Work.FTS.EllipticEst.Q0 := by
    intro n
    refine ((hΦ3c n).sub (hΘ3 n)).congr fun p _ => ?_
    rcases p with ⟨z', θ'⟩
    simp only [Function.uncurry, Pi.sub_apply, Work.Construction.PhiTil]
  -- ## the limit residual and `Θ` of the limit
  have hΞ3lim : ContDiffOn ℝ 3 (Function.uncurry (fun z θ =>
      Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
        (E (slice g τ)) z θ)) Work.FTS.EllipticEst.Q0 :=
    pert_tilde_contDiffOn hα hα13 hEL3 hOK τ hτ0
  have hΘ3lim : ContDiffOn ℝ 3 (Function.uncurry
      (Work.Construction.Theta (Work.FTS.Regularity.pExp α) (slice g τ)))
      Work.FTS.EllipticEst.Q0 := by
    refine ((hElim3.sub hΞ3lim)).congr fun p _ => ?_
    rcases p with ⟨z', θ'⟩
    simp only [Function.uncurry, Pi.sub_apply, Work.Construction.PhiTil]
    ring
  -- ## the trace-free `ℋ⁴ → L^∞` trade-off for the approximants
  obtain ⟨CA1, hCA10, hA1⟩ := Work.FTS_RegExport.RXA1w.abs_mixed_le_HkNorm_C4_w_proved hαG hαG1
  -- ## the `D_z`-jets of `L₁₂` converge
  have hL12jets : ∀ j : ℕ, j ≤ 3 → ∀ z' : ℝ, 0 < z' →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.DzIter j
          (fun z _ => Work.Construction.L12 (slice (gn n) τ) z) z' 0) Filter.atTop
        (nhds (Work.Spaces.DzIter j
          (fun z _ => Work.Construction.L12 (slice g τ) z) z' 0)) := by
    intro j hj z' hz'
    refine Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto
      (C0 := CA1 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2))
      (F := fun n => slice (gn n) τ) (G := slice g τ) (by positivity) ?_ hF4 ?_ ?_ j hj z' hz'
    · intro n; exact (hReg n).1
    · intro n b a hba z'' θ'' hz'' hθ'' hθ''2
      have h1 := hA1 (slice (gn n) τ) (hReg n).1 (hReg n).2.1 (hReg n).2.2.1 b a hba
        z'' θ'' hz'' hθ'' hθ''2
      have h2 : Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4 (slice (gn n) τ)
          ≤ max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2 := (hReg n).2.2.2
      have hA0 : 0 ≤ CA1 * (z'' ^ ((3 : ℝ) / 2) / (1 + z'') ^ 2) :=
        mul_nonneg hCA10 (div_nonneg (Real.rpow_nonneg hz''.le _) (by positivity))
      calc |Work.Spaces.mixed b a (slice (gn n) τ) z'' θ''|
          ≤ CA1 * (z'' ^ ((3 : ℝ) / 2) / (1 + z'') ^ 2)
              * Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4 (slice (gn n) τ) := h1
        _ ≤ CA1 * (z'' ^ ((3 : ℝ) / 2) / (1 + z'') ^ 2)
              * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) :=
            mul_le_mul_of_nonneg_left h2 hA0
        _ = CA1 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2)
              * (z'' ^ ((3 : ℝ) / 2) / (1 + z'') ^ 2) := by ring
    · intro b a hab z'' θ'' hz'' hθ'' hθ''2
      exact hJet τ hτ b a (by omega) z'' θ'' ⟨hz'', hθ'', hθ''2⟩
  -- ## the `Θ`-jets converge
  have hΘconv := Work.FTS_RegExport.RXT.Slots.v2_thetaJetsTendsto
    (α := Work.FTS.Regularity.pExp α) (F := fun n => slice (gn n) τ) (G := slice g τ) hL12jets
  -- ## the residual jets converge (difference of the two families)
  have hΞconv : ∀ b a : ℕ, a + b ≤ 3 → ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed b a (fun z θ =>
          Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
            (E (slice (gn n) τ)) z θ) z' θ') Filter.atTop
        (nhds (Work.Spaces.mixed b a (fun z θ =>
          Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
            (E (slice g τ)) z θ) z' θ')) := by
    intro b a hba z' θ' hz' hθ' hθ'2
    have hfun : (fun n : ℕ => Work.Spaces.mixed b a (fun z θ =>
          Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
            (E (slice (gn n) τ)) z θ) z' θ')
        = fun n : ℕ => Work.Spaces.mixed b a (fun z θ => E (slice (gn n) τ) z θ) z' θ'
            - Work.Spaces.mixed b a (fun z θ =>
                Work.Construction.Theta (Work.FTS.Regularity.pExp α)
                  (slice (gn n) τ) z θ) z' θ' := by
      funext n
      exact velPert_mixed_sub_three (b := b) (a := a) hba (hΦ3c n) (hΘ3 n) hz' hθ' hθ'2
    have hlim : Work.Spaces.mixed b a (fun z θ =>
          Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
            (E (slice g τ)) z θ) z' θ'
        = Work.Spaces.mixed b a (fun z θ => E (slice g τ) z θ) z' θ'
            - Work.Spaces.mixed b a (fun z θ =>
                Work.Construction.Theta (Work.FTS.Regularity.pExp α)
                  (slice g τ) z θ) z' θ' :=
      velPert_mixed_sub_three (b := b) (a := a) hba hElim3 hΘ3lim hz' hθ' hθ'2
    rw [hfun, hlim]
    exact (hEconv b a (by omega) z' θ' ⟨hz', hθ', hθ'2⟩).sub
      (hΘconv b a (by omega) z' θ' hz' hθ' hθ'2)
  -- ## the mixed jets of the transport coefficient `𝒱(Φ̃)`
  have hslot := Work.FTS_RegExport.RXT.Slots.v2_SlotJetsTendsto (α := Work.FTS.Regularity.pExp α)
    (Ξ := fun n => fun z θ => Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
      (slice (gn n) τ) (E (slice (gn n) τ)) z θ)
    (Ξlim := fun z θ => Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
      (slice g τ) (E (slice g τ)) z θ) hΞ3 hΞ3lim hΞconv
  -- ## the plain `∂_θ`-jet
  intro z θ hz hθ hθ2
  have hs : Real.sin (2 * θ) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
  have hVop := (hslot 0 1 (by norm_num) z θ hz hθ hθ2).2.1
  have e1 : (fun n : ℕ => Work.Spaces.pth (Work.Construction.Vop (fun z θ =>
      Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
        (E (slice (gn n) τ)) z θ)) z θ)
      = fun n : ℕ => Work.Spaces.mixed 0 1 (Work.Construction.Vop (fun z θ =>
      Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
        (E (slice (gn n) τ)) z θ)) z θ / Real.sin (2 * θ) := by
    funext n
    exact pth_eq_mixed_zero_one_div hs
  have e2 : Work.Spaces.pth (Work.Construction.Vop (fun z θ =>
      Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
        (E (slice g τ)) z θ)) z θ
      = Work.Spaces.mixed 0 1 (Work.Construction.Vop (fun z θ =>
      Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
        (E (slice g τ)) z θ)) z θ / Real.sin (2 * θ) := pth_eq_mixed_zero_one_div hs
  rw [e1, e2]
  exact hVop.div_const _

end Work.FTS_RegExport.RXT.Sys
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.slot_tau_cont_alpha =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Set Filter
open scoped Topology Real

namespace Work.FTS_RegExport.RXT.Sys

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-!
# `Work.FTS_RegExport.RXT.Sys.slot_tau_cont_alpha`

**C3 of the `Sys/coeff_jets` plan**: the three transport slots `ℛ(Φ̃_τ)`, `𝒱(Φ̃_τ)`,
`𝒰(Φ̃_τ)/sin 2θ` of the modulated residual `Φ̃_τ = PhiTil (pExp α) (F_* + g(τ)) (Φs + E(g(τ)))`
depend continuously on the fake time `τ` on every horizon `[0,S]`, at every point `(z,θ)` of the
open quadrant.

The route (documented in `Submission/Work/FTS_RegExport/RXT/Sys/NOTES_coeff_jets.md`):

* on the open quadrant the residual splits as `Φ̃_τ = Φ̃_* + Ξ_τ` with `Φ̃_* = PhiTil F_* Φs`
  independent of `τ` (`v2_phiTil_split`) and `Ξ_τ = PhiTil (g(τ)) (E(g(τ)))`; the three slots are
  additive on the quadrant (`v2_rop_add_at`/`v2_vop_add_at`/`v2_uop_div_add_at`), so it suffices to
  treat `Ξ_τ`;
* `Ξ_τ` is approximated by the class-`C` sequence `Ξ_n(τ) = PhiTil (g_n(τ)) (E(g_n(τ)))` of the
  `LimApprox` clause of `DynOK'`; each `Ξ_n` is *uniformly Lipschitz in* `τ`
  (`SysAux.pertSlot_lip_approx`, from `EllPkgGo` applied to the class-`C` difference
  `g_n(τ) - g_n(τ')`) and converges pointwise (`SysAux.pertSlot_tendsto`);
* the two combine (`lipschitz_of_approx`) into a Lipschitz bound in `τ` for the limit slots, hence
  continuity.
-/

/-- **A uniformly Lipschitz sequence with a pointwise limit has a Lipschitz limit**: if every
`A n` satisfies `|A n τ - A n τ'| ≤ K|τ - τ'|` on `[0,S]` and `A n τ → Alim τ` for every
`τ ∈ [0,S]`, then `Alim` satisfies the same Lipschitz bound. -/
theorem lipschitz_of_approx {A : ℕ → ℝ → ℝ} {Alim : ℝ → ℝ} {S K : ℝ}
    (hLip : ∀ n (τ : ℝ), τ ∈ Set.Icc 0 S → ∀ τ' ∈ Set.Icc 0 S,
      |A n τ - A n τ'| ≤ K * |τ - τ'|)
    (hconv : ∀ τ ∈ Set.Icc (0:ℝ) S,
      Filter.Tendsto (fun n => A n τ) Filter.atTop (nhds (Alim τ))) :
    ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S, |Alim τ - Alim τ'| ≤ K * |τ - τ'| := by
  intro τ hτ τ' hτ'
  have h1 : Filter.Tendsto (fun n => |A n τ - A n τ'|) Filter.atTop
      (nhds (|Alim τ - Alim τ'|)) :=
    ((hconv τ hτ).sub (hconv τ' hτ')).abs
  exact le_of_tendsto' h1 (fun n => hLip n τ hτ τ' hτ')

theorem slot_tau_cont_alpha {α Ce C₀ Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hμ : Work.FTS.RegExportIface.ClockBd α Φs E g) :
    ∀ S > 0, ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ContinuousOn (fun τ => Work.FTS_RegExport.RXT.v2_SlotR α
          (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ) z θ) (Set.Icc 0 S) ∧
      ContinuousOn (fun τ => Work.FTS_RegExport.RXT.v2_SlotV α
          (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ) z θ) (Set.Icc 0 S) ∧
      ContinuousOn (fun τ => Work.FTS_RegExport.RXT.v2_SlotU α
          (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ) z θ) (Set.Icc 0 S) := by
  intro S hS z θ hz hθ hθ2
  have hαG : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  obtain ⟨gn, B, L, hAppx, hLipC, hJetC, _hμc⟩ := hOK.2 S hS
  -- the two children: the uniform Lipschitz bound and the pointwise convergence
  obtain ⟨K, hK0, hB⟩ := Work.FTS_RegExport.RXT.SysAux.pertSlot_lip_approx
    (α := α) (Ce := Ce) (L := L) (E := E) hα hα13 hEll
    (fun n τ hτ => (hAppx n τ hτ).1) (fun n τ hτ τ' hτ' => hLipC n τ hτ τ' hτ')
  have hC : ∀ τ ∈ Set.Icc (0:ℝ) S,
      (Filter.Tendsto (fun n : ℕ => Work.Construction.Rop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
            (E (slice (gn n) τ))) z θ) Filter.atTop
        (nhds (Work.Construction.Rop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
            (E (slice g τ))) z θ))) ∧
      (Filter.Tendsto (fun n : ℕ => Work.Construction.Vop
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
            (E (slice (gn n) τ))) z θ) Filter.atTop
        (nhds (Work.Construction.Vop
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
            (E (slice g τ))) z θ))) ∧
      (Filter.Tendsto (fun n : ℕ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
            (E (slice (gn n) τ))) z θ / Real.sin (2 * θ)) Filter.atTop
        (nhds (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
            (E (slice g τ))) z θ / Real.sin (2 * θ)))) :=
    fun τ hτ => Work.FTS_RegExport.RXT.SysAux.pertSlot_tendsto
      (α := α) (Ce := Ce) (C₀ := C₀) (Φs := Φs) (E := E) (g := g)
      hα hα13 hEll hEL3 hOK hS hAppx hJetC hτ z θ hz hθ hθ2
  -- ## regularity of the split pieces
  have hStar3 : ContDiffOn ℝ 3 (Function.uncurry (v2_PhiStar α Φs))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.PhiStar.CoreAux.fields_smooth hαG hαG1 hStar.smooth).1.of_le
      (by simp [Work.Stability.smoothOrder])
  have hStar1 : ContDiffOn ℝ 1 (Function.uncurry (v2_PhiStar α Φs))
      Work.FTS.EllipticEst.Q0 := hStar3.of_le (by norm_num)
  have hTheta3 : ∀ τ : ℝ, 0 ≤ τ → ContDiffOn ℝ 3 (Function.uncurry
      (Work.Construction.Theta (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ))) Work.FTS.EllipticEst.Q0 := by
    intro τ hτ
    refine Work.FTS_RegExport.RXT.velPert_contDiffOn_Theta
      (α := Work.FTS.Regularity.pExp α) ?_
    refine Work.FTS_RegExport.RXT.contDiffOn_three_L12 ?_
    obtain ⟨C, _hC0, hCb⟩ := Work.FTS_RegExport.RXT.Ftau_bounds
      (Φs := Φs) (E := E) hα hα13 hOK τ hτ
    exact Work.FTS_RegExport.RXT.contDiffOn_two_integral_Itheta (φ := Work.Spaces.K)
      Work.FTS_RegExport.RXT.v2_continuousOn_K_Iθ
      (Work.FTS_RegExport.RXT.contDiffOn_Ftau_Q0 (Φs := Φs) (E := E) hα hα13 hOK τ hτ)
      (fun z₁ θ₁ hz₁ hθ₁ hθ₁2 => ⟨(hCb z₁ θ₁ hz₁ hθ₁ hθ₁2).1,
        (hCb z₁ θ₁ hz₁ hθ₁ hθ₁2).2.1, (hCb z₁ θ₁ hz₁ hθ₁ hθ₁2).2.2⟩)
  have hFull3 : ∀ τ : ℝ, 0 ≤ τ → ContDiffOn ℝ 3 (Function.uncurry (v2_PhiT α Φs E g τ))
      Work.FTS.EllipticEst.Q0 := by
    intro τ hτ
    have hP := Work.FTS_RegExport.RXT.contDiffOn_slice_PhiR_Q0
      (α := α) (C₀ := C₀) (Cs := Cs) hEL3 hStar hOK τ hτ
    exact hP.sub (hTheta3 τ hτ)
  have hPert3 : ∀ τ : ℝ, 0 ≤ τ → ContDiffOn ℝ 3 (Function.uncurry (v2_PhiPert α E g τ))
      Work.FTS.EllipticEst.Q0 := by
    intro τ hτ
    refine ((hFull3 τ hτ).sub hStar3).congr ?_
    intro p hp
    obtain ⟨z₁, θ₁⟩ := p
    simp only [Function.uncurry]
    linarith [v2_phiTil_split (C₀ := C₀) hα hα13 hOK hτ z₁ θ₁ hp]
  have hPert1 : ∀ τ : ℝ, 0 ≤ τ → ContDiffOn ℝ 1 (Function.uncurry (v2_PhiPert α E g τ))
      Work.FTS.EllipticEst.Q0 := fun τ hτ => (hPert3 τ hτ).of_le (by norm_num)
  -- ## the split identities of the three slots at `(z,θ)`
  have hsplitFun : ∀ τ : ℝ, 0 ≤ τ → Work.FTS_RegExport.RXR5.AgreeOnQ (v2_PhiT α Φs E g τ)
      (v2_PhiStar α Φs + v2_PhiPert α E g τ) := fun τ hτ z₁ θ₁ hz₁ hθ₁ hθ₁2 =>
    v2_phiTil_split (C₀ := C₀) hα hα13 hOK hτ z₁ θ₁
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz₁, hθ₁, hθ₁2⟩)
  have hsplitR : ∀ τ ∈ Set.Icc (0:ℝ) S, v2_SlotR α (v2_PhiT α Φs E g τ) z θ
      = v2_SlotR α (v2_PhiStar α Φs) z θ + v2_SlotR α (v2_PhiPert α E g τ) z θ := by
    intro τ hτ
    show Work.Construction.Rop (Work.FTS.Regularity.pExp α) (v2_PhiT α Φs E g τ) z θ
      = Work.Construction.Rop (Work.FTS.Regularity.pExp α) (v2_PhiStar α Φs) z θ
        + Work.Construction.Rop (Work.FTS.Regularity.pExp α) (v2_PhiPert α E g τ) z θ
    rw [Work.FTS_RegExport.RXR5.Rop_congr_of_agreeOnQ (α := Work.FTS.Regularity.pExp α)
      (h := hsplitFun τ hτ.1) hz hθ hθ2]
    exact v2_rop_add_at hStar1 (hPert1 τ hτ.1) ⟨hz, hθ, hθ2⟩
  have hsplitV : ∀ τ ∈ Set.Icc (0:ℝ) S, v2_SlotV α (v2_PhiT α Φs E g τ) z θ
      = v2_SlotV α (v2_PhiStar α Φs) z θ + v2_SlotV α (v2_PhiPert α E g τ) z θ := by
    intro τ hτ
    show Work.Construction.Vop (v2_PhiT α Φs E g τ) z θ
      = Work.Construction.Vop (v2_PhiStar α Φs) z θ
        + Work.Construction.Vop (v2_PhiPert α E g τ) z θ
    rw [Work.FTS_RegExport.RXR5.Vop_congr_of_agreeOnQ (h := hsplitFun τ hτ.1) hz hθ hθ2]
    exact v2_vop_add_at hStar1 (hPert1 τ hτ.1) ⟨hz, hθ, hθ2⟩
  have hsplitU : ∀ τ ∈ Set.Icc (0:ℝ) S, v2_SlotU α (v2_PhiT α Φs E g τ) z θ
      = v2_SlotU α (v2_PhiStar α Φs) z θ + v2_SlotU α (v2_PhiPert α E g τ) z θ := by
    intro τ hτ
    show Work.Construction.Uop (Work.FTS.Regularity.pExp α) (v2_PhiT α Φs E g τ) z θ
        / Real.sin (2 * θ)
      = Work.Construction.Uop (Work.FTS.Regularity.pExp α) (v2_PhiStar α Φs) z θ
          / Real.sin (2 * θ)
        + Work.Construction.Uop (Work.FTS.Regularity.pExp α) (v2_PhiPert α E g τ) z θ
          / Real.sin (2 * θ)
    rw [Work.FTS_RegExport.RXR5.Uop_congr_of_agreeOnQ (α := Work.FTS.Regularity.pExp α)
      (h := hsplitFun τ hτ.1) hz hθ hθ2]
    exact v2_uop_div_add_at (αG := Work.FTS.Regularity.pExp α) hStar1 (hPert1 τ hτ.1)
      ⟨hz, hθ, hθ2⟩
  -- ## the Lipschitz bound for the limit slot families
  have hLR : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
      |Work.Construction.Rop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
            (E (slice g τ))) z θ
        - Work.Construction.Rop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ')
            (E (slice g τ'))) z θ| ≤ K * |τ - τ'| :=
    lipschitz_of_approx (A := fun n τ => Work.Construction.Rop (Work.FTS.Regularity.pExp α)
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
          (E (slice (gn n) τ))) z θ)
      (Alim := fun τ => Work.Construction.Rop (Work.FTS.Regularity.pExp α)
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
          (E (slice g τ))) z θ)
      (fun n τ hτ τ' hτ' => (hB n τ hτ τ' hτ' z θ hz hθ hθ2).1)
      (fun τ hτ => (hC τ hτ).1)
  have hLV : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
      |Work.Construction.Vop
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
            (E (slice g τ))) z θ
        - Work.Construction.Vop
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ')
            (E (slice g τ'))) z θ| ≤ K * |τ - τ'| :=
    lipschitz_of_approx (A := fun n τ => Work.Construction.Vop
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
          (E (slice (gn n) τ))) z θ)
      (Alim := fun τ => Work.Construction.Vop
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
          (E (slice g τ))) z θ)
      (fun n τ hτ τ' hτ' => (hB n τ hτ τ' hτ' z θ hz hθ hθ2).2.1)
      (fun τ hτ => (hC τ hτ).2.1)
  have hLU : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
      |Work.Construction.Uop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
            (E (slice g τ))) z θ / Real.sin (2 * θ)
        - Work.Construction.Uop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ')
            (E (slice g τ'))) z θ / Real.sin (2 * θ)| ≤ K * |τ - τ'| :=
    lipschitz_of_approx (A := fun n τ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
          (E (slice (gn n) τ))) z θ / Real.sin (2 * θ))
      (Alim := fun τ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
          (E (slice g τ))) z θ / Real.sin (2 * θ))
      (fun n τ hτ τ' hτ' => (hB n τ hτ τ' hτ' z θ hz hθ hθ2).2.2)
      (fun τ hτ => (hC τ hτ).2.2)
  -- ## continuity of a Lipschitz family on `[0,S]`
  have hcontaux : ∀ (P : ℝ → ℝ) (hP : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
        |P τ - P τ'| ≤ K * |τ - τ'|),
      ContinuousOn P (Set.Icc 0 S) := by
    intro P hP τ₀ hτ₀
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    refine ⟨ε / (K + 1), by positivity, fun τ hτ hd => ?_⟩
    have hK1 : (0:ℝ) < K + 1 := by linarith
    have hb := hP τ hτ τ₀ hτ₀
    rw [Real.dist_eq] at hd ⊢
    have h2 : K * |τ - τ₀| ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left (le_of_lt hd) hK0
    have h3 : K * (ε / (K + 1)) < ε := by
      rw [← mul_div_assoc, div_lt_iff₀ hK1]
      nlinarith [hε, hK0]
    linarith
  refine ⟨?_, ?_, ?_⟩
  · refine ContinuousOn.congr (f := fun τ => v2_SlotR α (v2_PhiStar α Φs) z θ
        + v2_SlotR α (v2_PhiPert α E g τ) z θ) ?_ (fun τ hτ => hsplitR τ hτ)
    have hP : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
        |v2_SlotR α (v2_PhiPert α E g τ) z θ - v2_SlotR α (v2_PhiPert α E g τ') z θ|
          ≤ K * |τ - τ'| := by
      intro τ hτ τ' hτ'
      simpa only [v2_SlotR, v2_PhiPert] using hLR τ hτ τ' hτ'
    exact continuousOn_const.add (hcontaux _ hP)
  · refine ContinuousOn.congr (f := fun τ => v2_SlotV α (v2_PhiStar α Φs) z θ
        + v2_SlotV α (v2_PhiPert α E g τ) z θ) ?_ (fun τ hτ => hsplitV τ hτ)
    have hP : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
        |v2_SlotV α (v2_PhiPert α E g τ) z θ - v2_SlotV α (v2_PhiPert α E g τ') z θ|
          ≤ K * |τ - τ'| := by
      intro τ hτ τ' hτ'
      simpa only [v2_SlotV, v2_PhiPert] using hLV τ hτ τ' hτ'
    exact continuousOn_const.add (hcontaux _ hP)
  · refine ContinuousOn.congr (f := fun τ => v2_SlotU α (v2_PhiStar α Φs) z θ
        + v2_SlotU α (v2_PhiPert α E g τ) z θ) ?_ (fun τ hτ => hsplitU τ hτ)
    have hP : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
        |v2_SlotU α (v2_PhiPert α E g τ) z θ - v2_SlotU α (v2_PhiPert α E g τ') z θ|
          ≤ K * |τ - τ'| := by
      intro τ hτ τ' hτ'
      simpa only [v2_SlotU, v2_PhiPert] using hLU τ hτ τ' hτ'
    exact continuousOn_const.add (hcontaux _ hP)

end Work.FTS_RegExport.RXT.Sys
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT0.SJC.slotJetLipschitzApprox =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT0.SJC

open scoped Real Topology
open Set Filter
open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.Regularity (pExp)
set_option autoImplicit false
variable {α Ce C₀ : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}

/-! ## Joint (in `τ`) Lipschitz approximation of the order-`≤ 2` jets of the three slots

`RXT.SysAux.pertSlot_lip_approx` gives the `τ`-Lipschitz modulus of the three slots
`Rop Φ̃`, `Vop Φ̃`, `Uop Φ̃ / sin 2θ` themselves.  Here we upgrade it to every mixed jet
`D_z^j D_θ^i`, `j + i ≤ 2`: the difference of the two `τ`-slices telescopes into the
difference slice `Δ = slice τ - slice τ'`, whose slot is controlled by the pair
`EllPkgGo` (`HkNorm α 4 (slot Δ) ≤ Ce · Xn α Δ`) together with the *trace-free weighted*
`ℋ⁴ → L^∞` trade-off `v2_hkMem_pointwise_min`
(`|mixed j i Q z θ| ≤ Ct · min z 1 · HkNorm α 4 Q`). -/

/-- `D_θ`-iterates only see the values on the open quadrant. -/
private theorem DthIter_congr_Q0_pt {u v : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → u z θ = v z θ) (i : ℕ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DthIter i u z θ = Work.Spaces.DthIter i v z θ := by
  induction i with
  | zero => intro z θ hz h1 h2; exact h z θ hz h1 h2
  | succ n ih =>
      intro z θ hz h1 h2
      have hEq : Set.EqOn (Function.uncurry (Work.Spaces.DthIter n u))
          (Function.uncurry (Work.Spaces.DthIter n v)) Work.FTS.EllipticEst.Q0 := by
        intro p hp
        obtain ⟨hz', h1', h2'⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
        exact ih p.1 p.2 hz' h1' h2'
      have hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
        Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, h1, h2⟩
      have hpth : Work.Spaces.pth (Work.Spaces.DthIter n u) z θ
          = Work.Spaces.pth (Work.Spaces.DthIter n v) z θ :=
        Work.Spaces.pth_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEq hp
      simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth]
      rw [hpth]

/-- `mixed` only sees the values on the open quadrant. -/
private theorem mixed_congr_Q0_pt {u v : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → u z θ = v z θ) (j i : ℕ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed j i u z θ = Work.Spaces.mixed j i v z θ :=
  fun z θ hz h1 h2 =>
    Work.FTS.EllipticEst.SmoothOpen.DzIter_congr
      (F := Work.Spaces.DthIter i u) (G := Work.Spaces.DthIter i v)
      (DthIter_congr_Q0_pt h i) j z θ hz h1 h2

theorem slotJetLipschitzApprox
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (pExp α) u →
      Work.FTS.Final.EllPkgGo (pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (pExp α) 6 Ce u (E u))
    {gn : ℕ → Fam} {L S : ℝ} (hS : 0 < S)
    (hCl : ∀ n : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) S,
      Work.FTS.ClassC.ClassC (pExp α) (slice (gn n) τ))
    (hLip : ∀ n : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ τ' ∈ Set.Icc (0 : ℝ) S,
      Work.FTS.Nonlin.Xn (pExp α) (slice (gn n) τ - slice (gn n) τ') ≤ L * |τ - τ'|) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ τ' ∈ Set.Icc (0 : ℝ) S,
      ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (|Work.Spaces.mixed j i (Work.Construction.Rop (pExp α)
            (Work.Construction.PhiTil (pExp α) (slice (gn n) τ) (E (slice (gn n) τ)))) z θ
          - Work.Spaces.mixed j i (Work.Construction.Rop (pExp α)
            (Work.Construction.PhiTil (pExp α) (slice (gn n) τ') (E (slice (gn n) τ')))) z θ|
        ≤ K * |τ - τ'|) ∧
      (|Work.Spaces.mixed j i (Work.Construction.Vop
            (Work.Construction.PhiTil (pExp α) (slice (gn n) τ) (E (slice (gn n) τ)))) z θ
          - Work.Spaces.mixed j i (Work.Construction.Vop
            (Work.Construction.PhiTil (pExp α) (slice (gn n) τ') (E (slice (gn n) τ')))) z θ|
        ≤ K * |τ - τ'|) ∧
      (|Work.Spaces.mixed j i (fun z θ => Work.Construction.Uop (pExp α)
            (Work.Construction.PhiTil (pExp α) (slice (gn n) τ) (E (slice (gn n) τ))) z θ
            / Real.sin (2 * θ)) z θ
          - Work.Spaces.mixed j i (fun z θ => Work.Construction.Uop (pExp α)
            (Work.Construction.PhiTil (pExp α) (slice (gn n) τ') (E (slice (gn n) τ'))) z θ
            / Real.sin (2 * θ)) z θ| ≤ K * |τ - τ'|) := by
  have hαG : 0 < pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  obtain ⟨Ct, hCt0, hCt⟩ := Work.FTS_RegExport.RXT.v2_hkMem_pointwise_min hαG hαG1
  refine ⟨Ct * max Ce 0 * max L 0,
    mul_nonneg (mul_nonneg hCt0 (le_max_right _ _)) (le_max_right _ _), ?_⟩
  intro n τ hτ τ' hτ' j i hji z θ hz hθ hθ2
  have hCu : Work.FTS.ClassC.ClassC (pExp α) (slice (gn n) τ) := hCl n τ hτ
  have hCv : Work.FTS.ClassC.ClassC (pExp α) (slice (gn n) τ') := hCl n τ' hτ'
  set Δ : Fn := fun z θ => slice (gn n) τ z θ - slice (gn n) τ' z θ with hΔ
  have hCΔ : Work.FTS.ClassC.ClassC (pExp α) Δ :=
    Work.FTS.StrongEps.EComparison.classC_sub hCu hCv
  set Xu : Fn := Work.Construction.PhiTil (pExp α)
    (slice (gn n) τ) (E (slice (gn n) τ)) with hXu
  set Xv : Fn := Work.Construction.PhiTil (pExp α)
    (slice (gn n) τ') (E (slice (gn n) τ')) with hXv
  set Xd : Fn := Work.Construction.PhiTil (pExp α) Δ (E Δ) with hXd
  obtain ⟨hGo, _hK6⟩ := hEll Δ hCΔ
  obtain ⟨hGu, _⟩ := hEll (slice (gn n) τ) hCu
  obtain ⟨hGv, _⟩ := hEll (slice (gn n) τ') hCv
  have hSXd : Work.FTS.EllipticEst.SmoothOpen Xd :=
    Work.FTS.GalFields.RHS.Sharp.smoothOpen_PhiTil hαG hGo
  have hSXv : Work.FTS.EllipticEst.SmoothOpen Xv :=
    Work.FTS.GalFields.RHS.Sharp.smoothOpen_PhiTil hαG hGv
  have hXn0 : 0 ≤ Work.FTS.Nonlin.Xn (pExp α) Δ :=
    Work.Spaces.HkNorm_nonneg _ _ _
  have hXnΔ : Work.FTS.Nonlin.Xn (pExp α) Δ ≤ max L 0 * |τ - τ'| := by
    refine le_trans (hLip n τ hτ τ' hτ') ?_
    exact mul_le_mul_of_nonneg_right (le_max_left L 0) (abs_nonneg _)
  -- ## the pointwise telescoping of the residues
  have hpot : ∀ z' θ' : ℝ, 0 < z' → Xu z' θ' = Xd z' θ' + Xv z' θ' := by
    intro z' θ' hz'
    have hL : Work.Construction.L12 Δ z'
        = Work.Construction.L12 (slice (gn n) τ) z'
          - Work.Construction.L12 (slice (gn n) τ') z' :=
      Work.FTS.StrongEps.EComparison.L12_sub_HkMem hCu.reg hCv.reg
        (Work.FTS.ClassC.classC_hkMem_four hCu) (Work.FTS.ClassC.classC_hkMem_four hCv)
        z' hz'.le
    have hE' : E Δ z' θ'
        = E (slice (gn n) τ) z' θ'
          - E (slice (gn n) τ') z' θ' := by
      have h2 : E Δ = E (slice (gn n) τ)
          - E (slice (gn n) τ') := by
        rw [hΔ]
        exact map_sub E _ _
      exact congrFun (congrFun h2 z') θ'
    rw [hXu, hXd, hXv]
    unfold Work.Construction.PhiTil Work.Construction.Theta
    rw [hL, hE']
    ring
  -- ## the pointwise additivity of the three slots on `Q0`
  have hR_id : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      Work.Construction.Rop (pExp α) Xu z' θ'
        = Work.Construction.Rop (pExp α) Xd z' θ'
          + Work.Construction.Rop (pExp α) Xv z' θ' := by
    intro z' θ' hz' h1 h2
    calc Work.Construction.Rop (pExp α) Xu z' θ'
        = Work.Construction.Rop (pExp α) (fun z θ => Xd z θ + Xv z θ) z' θ' :=
          Work.FTS.GalFields.RHS.Sharp.Rop_congr_Q0
            (f := Xu) (g := fun z θ => Xd z θ + Xv z θ)
            (fun z θ hz'' _ _ => hpot z θ hz'') z' θ' hz' h1 h2
      _ = Work.Construction.Rop (pExp α) Xd z' θ'
            + Work.Construction.Rop (pExp α) Xv z' θ' :=
          Work.FTS.GalFields.RHS.Sharp.Rop_add_Q0 hSXd hSXv z' θ' hz' h1 h2
  have hV_id : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      Work.Construction.Vop Xu z' θ'
        = Work.Construction.Vop Xd z' θ' + Work.Construction.Vop Xv z' θ' := by
    intro z' θ' hz' h1 h2
    calc Work.Construction.Vop Xu z' θ'
        = Work.Construction.Vop (fun z θ => Xd z θ + Xv z θ) z' θ' :=
          Work.FTS.GalFields.RHS.Sharp.Vop_congr_Q0
            (f := Xu) (g := fun z θ => Xd z θ + Xv z θ)
            (fun z θ hz'' _ _ => hpot z θ hz'') z' θ' hz' h1 h2
      _ = Work.Construction.Vop Xd z' θ' + Work.Construction.Vop Xv z' θ' :=
          Work.FTS.GalFields.RHS.Sharp.Vop_add_Q0 hSXd hSXv z' θ' hz' h1 h2
  have hU_id : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      Work.Construction.Uop (pExp α) Xu z' θ' / Real.sin (2 * θ')
        = Work.Construction.Uop (pExp α) Xd z' θ' / Real.sin (2 * θ')
          + Work.Construction.Uop (pExp α) Xv z' θ' / Real.sin (2 * θ') := by
    intro z' θ' hz' h1 h2
    have hc : Work.Construction.Uop (pExp α) Xu z' θ'
        = Work.Construction.Uop (pExp α) (fun z θ => Xd z θ + Xv z θ) z' θ' :=
      Work.FTS.GalFields.RHS.Sharp.Uop_congr_Q0
        (f := Xu) (g := fun z θ => Xd z θ + Xv z θ)
        (fun z θ hz'' _ _ => hpot z θ hz'') z' θ' hz' h1 h2
    have ha := Work.FTS.GalFields.RHS.Sharp.Uop_add_Q0 (α := pExp α) hSXd hSXv z' θ' hz' h1 h2
    rw [hc, ha]
    ring
  -- ## the abstract slot bound: the trade-off bound on the difference slot
  have hji' : i + j ≤ 2 := by omega
  have key : ∀ (Sl : Fn → Fn) (P Q : Fn),
      Work.FTS.EllipticEst.SmoothOpen (Sl Q) → Work.FTS.EllipticEst.SmoothOpen (Sl P) →
      (∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
        Sl Xu z' θ' = Sl Q z' θ' + Sl P z' θ') →
      ContDiffOn ℝ 4 (Function.uncurry (Sl Q)) Work.FTS.EllipticEst.Q0 →
      Work.Spaces.HkMem (pExp α) 4 (Sl Q) →
      Work.Spaces.HkNorm (pExp α) 4 (Sl Q) ≤ max Ce 0 * Work.FTS.Nonlin.Xn (pExp α) Δ →
      |Work.Spaces.mixed j i (Sl Xu) z θ - Work.Spaces.mixed j i (Sl P) z θ|
        ≤ Ct * max Ce 0 * max L 0 * |τ - τ'| := by
    intro Sl P Q hSQ hSP hsum hcd hmem hnorm
    have hsplit : Work.Spaces.mixed j i (Sl Xu) z θ
        = Work.Spaces.mixed j i (Sl Q) z θ + Work.Spaces.mixed j i (Sl P) z θ := by
      rw [mixed_congr_Q0_pt (u := Sl Xu) (v := fun z θ => Sl Q z θ + Sl P z θ)
        (fun z θ hz' h1 h2 => hsum z θ hz' h1 h2) j i z θ hz hθ hθ2]
      exact Work.FTS.EllipticEst.SmoothOpen.mixed_add hSQ hSP j i z θ hz hθ hθ2
    have hpt := hCt (Sl Q) hcd hmem j i hji' z θ hz hθ hθ2
    have hN0 : 0 ≤ Work.Spaces.HkNorm (pExp α) 4 (Sl Q) :=
      Work.Spaces.HkNorm_nonneg _ _ _
    have hstep : Ct * min z 1 * Work.Spaces.HkNorm (pExp α) 4 (Sl Q)
        ≤ Ct * (max Ce 0 * (max L 0 * |τ - τ'|)) := by
      have h1 : Ct * min z 1 ≤ Ct * 1 :=
        mul_le_mul_of_nonneg_left (min_le_right z 1) hCt0
      calc Ct * min z 1 * Work.Spaces.HkNorm (pExp α) 4 (Sl Q)
          ≤ (Ct * 1) * Work.Spaces.HkNorm (pExp α) 4 (Sl Q) :=
            mul_le_mul_of_nonneg_right h1 hN0
        _ ≤ Ct * (max Ce 0 * Work.FTS.Nonlin.Xn (pExp α) Δ) := by
            rw [mul_one]
            exact mul_le_mul_of_nonneg_left hnorm hCt0
        _ ≤ Ct * (max Ce 0 * (max L 0 * |τ - τ'|)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hXnΔ (le_max_right Ce 0)) hCt0
    calc |Work.Spaces.mixed j i (Sl Xu) z θ - Work.Spaces.mixed j i (Sl P) z θ|
        = |Work.Spaces.mixed j i (Sl Q) z θ| := by rw [hsplit, add_sub_cancel_right]
      _ ≤ Ct * min z 1 * Work.Spaces.HkNorm (pExp α) 4 (Sl Q) := hpt
      _ ≤ Ct * (max Ce 0 * (max L 0 * |τ - τ'|)) := hstep
      _ = Ct * max Ce 0 * max L 0 * |τ - τ'| := by ring
  -- ## the bound of the three difference slots
  have hRb : |Work.Spaces.mixed j i (Work.Construction.Rop (pExp α) Xu) z θ
      - Work.Spaces.mixed j i (Work.Construction.Rop (pExp α) Xv) z θ|
      ≤ Ct * max Ce 0 * max L 0 * |τ - τ'| :=
    key (Work.Construction.Rop (pExp α)) Xv Xd hGo.R.1.1 hGv.R.1.1 hR_id
      (hGo.R.1.1.forall 4) hGo.R.1.2
      (le_trans hGo.R.2 (mul_le_mul_of_nonneg_right (le_max_left Ce 0) hXn0))
  have hVb : |Work.Spaces.mixed j i (Work.Construction.Vop Xu) z θ
      - Work.Spaces.mixed j i (Work.Construction.Vop Xv) z θ|
      ≤ Ct * max Ce 0 * max L 0 * |τ - τ'| :=
    key Work.Construction.Vop Xv Xd hGo.V.1.1 hGv.V.1.1 hV_id
      (hGo.V.1.1.forall 4) hGo.V.1.2
      (le_trans hGo.V.2 (mul_le_mul_of_nonneg_right (le_max_left Ce 0) hXn0))
  have hUb : |Work.Spaces.mixed j i (fun z θ => Work.Construction.Uop (pExp α) Xu z θ
        / Real.sin (2 * θ)) z θ
      - Work.Spaces.mixed j i (fun z θ => Work.Construction.Uop (pExp α) Xv z θ
        / Real.sin (2 * θ)) z θ|
      ≤ Ct * max Ce 0 * max L 0 * |τ - τ'| :=
    key (fun X => fun z θ => Work.Construction.Uop (pExp α) X z θ / Real.sin (2 * θ))
      Xv Xd
      (by simpa only [Work.Construction.s2] using hGo.U.1.1)
      (by simpa only [Work.Construction.s2] using hGv.U.1.1)
      hU_id
      (hGo.U.1.1.forall 4) hGo.U.1.2
      (le_trans hGo.U.2 (mul_le_mul_of_nonneg_right (le_max_left Ce 0) hXn0))
  refine ⟨?_, ?_, ?_⟩
  · calc |Work.Spaces.mixed j i (Work.Construction.Rop (pExp α)
          (Work.Construction.PhiTil (pExp α) (slice (gn n) τ) (E (slice (gn n) τ)))) z θ
        - Work.Spaces.mixed j i (Work.Construction.Rop (pExp α)
          (Work.Construction.PhiTil (pExp α) (slice (gn n) τ') (E (slice (gn n) τ')))) z θ|
        = |Work.Spaces.mixed j i (Work.Construction.Rop (pExp α) Xu) z θ
            - Work.Spaces.mixed j i (Work.Construction.Rop (pExp α) Xv) z θ| := by
          rw [hXu, hXv]
      _ ≤ Ct * max Ce 0 * max L 0 * |τ - τ'| := hRb
  · calc |Work.Spaces.mixed j i (Work.Construction.Vop
          (Work.Construction.PhiTil (pExp α) (slice (gn n) τ) (E (slice (gn n) τ)))) z θ
        - Work.Spaces.mixed j i (Work.Construction.Vop
          (Work.Construction.PhiTil (pExp α) (slice (gn n) τ') (E (slice (gn n) τ')))) z θ|
        = |Work.Spaces.mixed j i (Work.Construction.Vop Xu) z θ
            - Work.Spaces.mixed j i (Work.Construction.Vop Xv) z θ| := by
          rw [hXu, hXv]
      _ ≤ Ct * max Ce 0 * max L 0 * |τ - τ'| := hVb
  · calc |Work.Spaces.mixed j i (fun z θ => Work.Construction.Uop (pExp α)
          (Work.Construction.PhiTil (pExp α) (slice (gn n) τ) (E (slice (gn n) τ))) z θ
          / Real.sin (2 * θ)) z θ
        - Work.Spaces.mixed j i (fun z θ => Work.Construction.Uop (pExp α)
          (Work.Construction.PhiTil (pExp α) (slice (gn n) τ') (E (slice (gn n) τ'))) z θ
          / Real.sin (2 * θ)) z θ|
        = |Work.Spaces.mixed j i (fun z θ => Work.Construction.Uop (pExp α) Xu z θ
            / Real.sin (2 * θ)) z θ
          - Work.Spaces.mixed j i (fun z θ => Work.Construction.Uop (pExp α) Xv z θ
            / Real.sin (2 * θ)) z θ| := by
          rw [hXu, hXv]
      _ ≤ Ct * max Ce 0 * max L 0 * |τ - τ'| := hUb

end Work.FTS_RegExport.RXT0.SJC
end
