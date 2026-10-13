import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.EpsZero.ClassCHk.NMemAux
import Submission.Work.FTS.OpenPkg.fkH_field
import Submission.Work.FTS.OpenPkg.angmul_field
import Submission.Work.FTS.NonlinRows.Rl1.splitOpen
import Submission.Work.FTS.GalFields.RHS.smoothOpen_N_Ftot_gal
import Submission.Work.FTS.StrongPersist.L3Rhs.N3ssPriced
import Submission.Work.FTS.StrongPersist.L3Rhs.N4ssPriced
import Submission.Work.FTS.StrongPersist.L3Rhs.N5ssPriced

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
