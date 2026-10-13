import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.NB4Aux
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnNAux
import Submission.Work.FTS.StrongEps.ClassCRHS.StarAtomsScaled
import Submission.Work.FTS.StrongEps.ClassCRHS.StarAtomsFK
import Submission.Work.FTS.NonlinRows.NRow10aux.mul_phi_Hk
import Submission.Work.FTS.OpenPkg.fkH_field
import Submission.Work.FTS.GalFields.RHS.smoothOpen_N_Ftot_gal
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.OpenPkg.prod_field
import Submission.Work.FTS.OpenPkg.wprod_field_winf

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux

open Work.FTS.Galerkin (Fn)
open scoped Real Topology

set_option maxHeartbeats 1600000

theorem N_b4_ctx (C₀ Ce Cs : ℝ) : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ (Φs w Φg : ℝ → ℝ → ℝ),
    Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
    Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.NB4Ctx C C₀ Ce Cs α Φs w Φg := by
  obtain ⟨Cprod, hCprodpos, hprod⟩ := Work.FTS.OpenPkg.prod_field
  obtain ⟨Cw, hCwpos, hwp⟩ := Work.FTS.OpenPkg.wprod_field_winf
  obtain ⟨Cfk, hCfkpos, hfkfield⟩ := Work.FTS.OpenPkg.fkH_field
  obtain ⟨Cphi, hCphipos, hphifield⟩ := Work.FTS.NonlinRows.NRow10aux.mul_phi_Hk
  obtain ⟨Csin, hCsinpos, hsinfield⟩ := exists_neg_sinSq_mul
  obtain ⟨CFS, hCFSpos, hFSW⟩ := Work.FTS.Nonlinear.FstarPkg.Fstar_W
  obtain ⟨CDth, hCDthpos, hDthW⟩ := Work.FTS.Nonlinear.FstarPkg.DthFstar_W
  obtain ⟨CDz, hCDzpos, hDzW⟩ := Work.FTS.Nonlinear.FstarPkg.DzFstar_W
  obtain ⟨Catom, hCatompos, hatom⟩ := Work.FTS.StrongEps.ClassCRHS.StarAtomsScaled
  obtain ⟨Cfka, hCfkapos, hfka⟩ := Work.FTS.StrongEps.ClassCRHS.StarAtomsFK
  set C : ℝ := 500 + Cprod + Cw + Cfk + Cphi + Csin + CFS + CDth + CDz + Catom + Cfka
    + max Ce 0 * max C₀ 0 + Cfk * max C₀ 0 + max Cs 0 with hCdef
  have hRnn : (0 : ℝ) ≤ max Ce 0 * max C₀ 0 := by positivity
  have hFknn : (0 : ℝ) ≤ Cfk * max C₀ 0 := by positivity
  have hCsnn : (0 : ℝ) ≤ max Cs 0 := le_max_right _ _
  have hCpos : 0 < C := by rw [hCdef]; linarith
  have hCone : 1 ≤ C := by rw [hCdef]; linarith
  have hCprod_le : Cprod ≤ C := by rw [hCdef]; linarith
  have hCw_le : Cw ≤ C := by rw [hCdef]; linarith
  have hCfk_le : Cfk ≤ C := by rw [hCdef]; linarith
  have hCphi_le : Cphi ≤ C := by rw [hCdef]; linarith
  have hCsin_le : Csin ≤ C := by rw [hCdef]; linarith
  have hCFS_le : CFS ≤ C := by rw [hCdef]; linarith
  have hCDth_le : CDth ≤ C := by rw [hCdef]; linarith
  have hCDz_le : CDz ≤ C := by rw [hCdef]; linarith
  have hCatom_le : Catom ≤ C := by rw [hCdef]; linarith
  have hCfka_le : Cfka ≤ C := by rw [hCdef]; linarith
  have hR_le : max Ce 0 * max C₀ 0 ≤ C := by rw [hCdef]; linarith
  have hFk2_le : Cfk * max C₀ 0 ≤ C := by rw [hCdef]; linarith
  have hCs_le : max Cs 0 ≤ C := by rw [hCdef]; linarith
  have h400 : (400 : ℝ) ≤ C := by rw [hCdef]; linarith
  refine ⟨C, hCpos, ?_⟩
  intro α hαI Φs w Φg hw hXw hell hstar
  obtain ⟨hα0, hα1⟩ := Set.mem_Ioc.mp hαI
  have hsqα : (0 : ℝ) ≤ α ^ 2 := sq_nonneg α
  have hrpow : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα0.le _
  -- ## the two product rules at the single constant `C`
  have hPQo : ∀ f g : Fn, Work.FTS.VocabO.HQo α 4 f → Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ C * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g := by
    intro f g hf hg
    obtain ⟨hm, hb⟩ := hprod α hα0 hα1 f g hf hg
    refine ⟨hm, ?_⟩
    have h1 : Cprod * α ^ (-(1 / 2 : ℝ)) ≤ C * α ^ (-(1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_right hCprod_le hrpow
    exact le_trans hb (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
  have hPW : ∀ f g : Fn, Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 4 f →
      Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f * Work.FTS.Nonlin.Xn α g := by
    intro f g hfs hfm hg
    obtain ⟨hm, hb⟩ := hwp α hα0 hα1 f g hfs hfm hg
    refine ⟨hm, ?_⟩
    have hWnn : 0 ≤ Work.Spaces.WlInf α 4 f := Work.Spaces.WlInf_nonneg α 4 f hfm
    have h1 : Cw * α ^ (-(1 / 2 : ℝ)) ≤ C * α ^ (-(1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_right hCw_le hrpow
    exact le_trans hb (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h1 hWnn) (Real.sqrt_nonneg _))
  -- ## the `w`-slots
  have hmem4w : Work.Spaces.HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 4 (by norm_num) hw.mem
  have hmem5w : Work.Spaces.HkMem α 5 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 5 (by norm_num) hw.mem
  have hqow : Work.FTS.VocabO.HQo α 4 w := ⟨hw.reg, hmem4w⟩
  have hDthwmem : Work.Spaces.HkMem α 4 (Work.Spaces.Dth w) :=
    Work.FTS.IPGen.HkMem_Dth_le (by linarith) hw.reg hmem5w
  have hDzwmem : Work.Spaces.HkMem α 4 (Work.Spaces.Dz w) :=
    Work.FTS.IPGen.HkMem_Dz_le hw.reg hmem5w
  have hqoDthw : Work.FTS.VocabO.HQo α 4 (Work.Spaces.Dth w) := ⟨hw.reg.Dth, hDthwmem⟩
  have hqoDzw : Work.FTS.VocabO.HQo α 4 (Work.Spaces.Dz w) := ⟨hw.reg.Dz, hDzwmem⟩
  obtain ⟨hwX, hdthwX, hdzwX⟩ := Xn_w_slots_le hα0 hw.reg hmem5w
  -- ## the three `φ = z/(1+z)`-scaled `w`-slots
  have hphiField : ∀ g : Fn, Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => z / (1 + z) * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => z / (1 + z) * g z θ) ≤ Cphi * Work.FTS.Nonlin.Xn α g :=
    fun g hg => hphifield hα0 hα1 hg
  have hphiwD := Work.FTS.StrongEps.ClassCRHS.phi_mul_data hCphipos hphiField hqow hwX
  have hphiDthwD :=
    Work.FTS.StrongEps.ClassCRHS.phi_mul_data hCphipos hphiField hqoDthw hdthwX
  have hphiDzwD := Work.FTS.StrongEps.ClassCRHS.phi_mul_data hCphipos hphiField hqoDzw hdzwX
  have hphiwqo : Work.FTS.VocabO.HQo α 4 (fun z θ => z / (1 + z) * w z θ) :=
    ⟨Work.FTS.StrongEps.ClassCRHS.smoothOpen_phi_mul hw.reg, hphiwD.1⟩
  have hphiDthwqo : Work.FTS.VocabO.HQo α 4 (fun z θ => z / (1 + z) * Work.Spaces.Dth w z θ) :=
    ⟨Work.FTS.StrongEps.ClassCRHS.smoothOpen_phi_mul hw.reg.Dth, hphiDthwD.1⟩
  have hphiDzwqo : Work.FTS.VocabO.HQo α 4 (fun z θ => z / (1 + z) * Work.Spaces.Dz w z θ) :=
    ⟨Work.FTS.StrongEps.ClassCRHS.smoothOpen_phi_mul hw.reg.Dz, hphiDzwD.1⟩
  have hphiwX : Work.FTS.Nonlin.Xn α (fun z θ => z / (1 + z) * w z θ)
      ≤ C * (1 + Work.Spaces.HkNorm α 5 w) := by
    refine le_trans hphiwD.2 ?_
    exact mul_le_mul_of_nonneg_right hCphi_le (zero_le_G (α := α) (w := w))
  have hphiDthwX : Work.FTS.Nonlin.Xn α
      (fun z θ => z / (1 + z) * Work.Spaces.Dth w z θ)
      ≤ C * (1 + Work.Spaces.HkNorm α 5 w) := by
    refine le_trans hphiDthwD.2 ?_
    exact mul_le_mul_of_nonneg_right hCphi_le (zero_le_G (α := α) (w := w))
  have hphiDzwX : Work.FTS.Nonlin.Xn α
      (fun z θ => z / (1 + z) * Work.Spaces.Dz w z θ)
      ≤ C * (1 + Work.Spaces.HkNorm α 5 w) := by
    refine le_trans hphiDzwD.2 ?_
    exact mul_le_mul_of_nonneg_right hCphi_le (zero_le_G (α := α) (w := w))
  -- ## the three perturbed coefficients of `EllPkgGo`
  have hRsm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg)) := hell.R.1.1
  have hRqo : Work.FTS.VocabO.HQo α 4
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg)) := hell.R.1
  have hRX : Work.FTS.Nonlin.Xn α
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg)) ≤ C * α ^ 2 :=
    le_trans (Work.FTS.StrongEps.ClassCRHS.Xn_Rop_le hw hell hXw)
      (mul_le_mul_of_nonneg_right hR_le hsqα)
  have hUsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α w Φg) z θ / Work.Construction.s2 θ) :=
    hell.U.1.1
  have hUqo : Work.FTS.VocabO.HQo α 4 (fun z θ =>
      Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α w Φg) z θ / Work.Construction.s2 θ) :=
    hell.U.1
  have hUX : Work.FTS.Nonlin.Xn α (fun z θ =>
      Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α w Φg) z θ / Work.Construction.s2 θ)
      ≤ C * α ^ 2 :=
    le_trans (Work.FTS.StrongEps.ClassCRHS.Xn_UopDiv_le hw hell hXw)
      (mul_le_mul_of_nonneg_right hR_le hsqα)
  have hVsm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg)) := hell.V.1.1
  have hVqo : Work.FTS.VocabO.HQo α 4
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg)) := hell.V.1
  have hVX : Work.FTS.Nonlin.Xn α
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg)) ≤ C * α ^ 2 :=
    le_trans (Work.FTS.StrongEps.ClassCRHS.Xn_Vop_le hw hell hXw)
      (mul_le_mul_of_nonneg_right hR_le hsqα)
  -- ## the `FK w`-atom
  have hFKwsm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.FK w z) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_FKw_of_classC hw
  have hFKwD : Work.Spaces.HkMem α 4 (fun z _ => Work.Construction.FK w z) ∧
      Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.FK w z) ≤ Cfk * max C₀ 0 * α ^ 2 :=
    Work.FTS.StrongEps.ClassCRHS.FKw_data hXw
      (fun g hg hl => hfkfield α hα0 hα1 g hg hl) hqow hw.l12 hCfkpos
  have hFKwqo : Work.FTS.VocabO.HQo α 4 (fun z _ => Work.Construction.FK w z) :=
    ⟨hFKwsm, hFKwD.1⟩
  have hFKwX : Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.FK w z) ≤ C * α ^ 2 :=
    le_trans hFKwD.2 (mul_le_mul_of_nonneg_right hFk2_le hsqα)
  -- ## the `-(2α)·hKer`-atom
  have hFKnegsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z _ => (-(2 * α)) * Work.Spaces.hKer z) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_FKneg α
  have hFKnegD := Work.FTS.StrongEps.ClassCRHS.hKerNeg_data α hα0
  have hFKnegWm : Work.Spaces.WlInfMem α 4
      (fun z _ => (-(2 * α)) * Work.Spaces.hKer z) := hFKnegD.1
  have hFKnegW : Work.Spaces.WlInf α 4 (fun z _ => (-(2 * α)) * Work.Spaces.hKer z)
      ≤ C * α := by
    refine le_trans hFKnegD.2 ?_
    rw [show 200 * (2 * α) = 400 * α from by ring]
    exact mul_le_mul_of_nonneg_right h400 hα0.le
  -- ## the star coefficients
  have hstar2 : Work.FTS.VocabO2.StarPkgo2 α Cs Φs := hstar.toStarPkgo2
  have hsw : Work.FTS.VocabO.StarPkgo α Cs Φs := hstar2.toStarPkgo
  have hRssm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_Rs_of_star hα0 hα1 hsw
  have hRsWm : Work.Spaces.WlInfMem α 4
      (fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ) :=
    hstar2.RW.1
  have hRsW : Work.Spaces.WlInf α 4
      (fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ)
      ≤ C * α :=
    le_trans (Work.FTS.StrongEps.ClassCRHS.WlInf_Rs_le hα0 hstar2)
      (mul_le_mul_of_nonneg_right hCs_le hα0.le)
  have hUssm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => (z + 1) / z *
      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Work.Construction.s2 θ)) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_Us_of_star hα0 hα1 hsw
  have hUsWm : Work.Spaces.WlInfMem α 4 (fun z θ => (z + 1) / z *
      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Work.Construction.s2 θ)) :=
    hstar2.UszW.1
  have hUsW : Work.Spaces.WlInf α 4 (fun z θ => (z + 1) / z *
      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Work.Construction.s2 θ))
      ≤ C * α :=
    le_trans (Work.FTS.StrongEps.ClassCRHS.WlInf_Us_le hα0 hstar2)
      (mul_le_mul_of_nonneg_right hCs_le hα0.le)
  have hVssm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (z + 1) / z * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_Vs_of_star hα0 hα1 hsw
  have hVsWm : Work.Spaces.WlInfMem α 4
      (fun z θ => (z + 1) / z * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ) :=
    hstar2.VzW.1
  have hVsW : Work.Spaces.WlInf α 4
      (fun z θ => (z + 1) / z * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ)
      ≤ C * α :=
    le_trans (Work.FTS.StrongEps.ClassCRHS.WlInf_Vs_le hα0 hstar2)
      (mul_le_mul_of_nonneg_right hCs_le hα0.le)
  -- ## the fixed `F_*`-atoms
  have hFWsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.EllipticEst.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  have hDthFssm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.Dth (Work.Construction.Fstar α)) := hFWsm.Dth
  have hDzFssm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.Dz (Work.Construction.Fstar α)) := hFWsm.Dz
  obtain ⟨hFWWm, hFWW⟩ := hFSW α hα0 hα1
  obtain ⟨hDthFsWm, hDthFsW⟩ := hDthW α hα0 hα1
  obtain ⟨hDzFsWm, hDzFsW⟩ := hDzW α hα0 hα1
  -- ## the three `φ`-scaled `F_*`-atoms
  obtain ⟨hphiFsqo, hphiFsX0, hphiDthFsqo, hphiDthFsX0, hphiDzFsqo, hphiDzFsX0⟩ :=
    hatom α hαI
  -- ## the two fixed `FK(F_*)`-products
  obtain ⟨hprodFKDthFSqo, hprodFKDthFSX0, hprodFKFSqo, hprodFKFSX0⟩ := hfka α hαI
  -- ## the atom `FK(F_*)` itself
  have hFKFSsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z _ => Work.Construction.FK (Work.Construction.Fstar α) z) :=
    Work.FTS.GalFields.RHS.smoothOpen_FK_Fstar_rad α hα0 hα1
  have hFKeq : ∀ z : ℝ, -1 < z → ∀ θ : ℝ,
      Work.Construction.FK (Work.Construction.Fstar α) z = (2 * α) * Work.Spaces.hKer z := by
    intro z _ θ
    rw [Work.FTS.Nonlin.FK_Fstar hα0 hα1, Work.Spaces.hKer_apply]
    ring
  have hkerC := Work.FTS.Nonlinear.Pieces.RNP.hKerConstWlInf α (2 * α)
  have hcongr := Work.FTS.Nonlinear.FstarPkg.WlInf_congr
    (f := fun z _ => Work.Construction.FK (Work.Construction.Fstar α) z)
    (g := fun z θ => (2 * α) * Work.Spaces.hKer z) hFKeq α 4
  have hFKFSWm : Work.Spaces.WlInfMem α 4
      (fun z _ => Work.Construction.FK (Work.Construction.Fstar α) z) :=
    hcongr.2.mpr hkerC.1
  have hFKFSW : Work.Spaces.WlInf α 4
      (fun z _ => Work.Construction.FK (Work.Construction.Fstar α) z) ≤ C * α := by
    rw [hcongr.1]
    refine le_trans hkerC.2 ?_
    rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * α),
      show 200 * (2 * α) = 400 * α from by ring]
    exact mul_le_mul_of_nonneg_right h400 hα0.le
  -- ## the `-sin²θ`-multiplication
  have hSinMul : ∀ g : Fn, Work.FTS.EllipticEst.SmoothOpen g → Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => -(Real.sin θ) ^ 2 * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => -(Real.sin θ) ^ 2 * g z θ)
        ≤ C * Work.FTS.Nonlin.Xn α g := by
    intro g hgs hgm
    obtain ⟨hm, hb⟩ := hsinfield hα0 hα1 hgs hgm
    exact ⟨hm, le_trans hb (mul_le_mul_of_nonneg_right hCsin_le (Real.sqrt_nonneg _))⟩
  exact
    { hα0 := hα0
    , hα1 := hα1
    , hCpos := hCpos
    , hCone := hCone
    , hPQo := hPQo
    , hPW := hPW
    , wqo := hqow
    , dthwqo := hqoDthw
    , dzwqo := hqoDzw
    , wX := hwX
    , dthwX := hdthwX
    , dzwX := hdzwX
    , phiwqo := hphiwqo
    , phiDthwqo := hphiDthwqo
    , phiDzwqo := hphiDzwqo
    , phiwX := hphiwX
    , phiDthwX := hphiDthwX
    , phiDzwX := hphiDzwX
    , Rsm := hRsm
    , Rqo := hRqo
    , RX := hRX
    , Usm := hUsm
    , Uqo := hUqo
    , UX := hUX
    , Vsm := hVsm
    , Vqo := hVqo
    , VX := hVX
    , FKwsm := hFKwsm
    , FKwqo := hFKwqo
    , FKwX := hFKwX
    , FKnegsm := hFKnegsm
    , FKnegWm := hFKnegWm
    , FKnegW := hFKnegW
    , Rssm := hRssm
    , RsWm := hRsWm
    , RsW := hRsW
    , Ussm := hUssm
    , UsWm := hUsWm
    , UsW := hUsW
    , Vssm := hVssm
    , VsWm := hVsWm
    , VsW := hVsW
    , FWsm := hFWsm
    , FWWm := hFWWm
    , FWW := le_trans hFWW (mul_le_mul_of_nonneg_right hCFS_le hα0.le)
    , DthFssm := hDthFssm
    , DthFsWm := hDthFsWm
    , DthFsW := le_trans hDthFsW (mul_le_mul_of_nonneg_right hCDth_le hsqα)
    , DzFssm := hDzFssm
    , DzFsWm := hDzFsWm
    , DzFsW := le_trans hDzFsW (mul_le_mul_of_nonneg_right hCDz_le hα0.le)
    , phiFsqo := hphiFsqo
    , phiFsX := le_trans hphiFsX0 hCatom_le
    , phiDthFsqo := hphiDthFsqo
    , phiDthFsX := le_trans hphiDthFsX0 hCatom_le
    , phiDzFsqo := hphiDzFsqo
    , phiDzFsX := le_trans hphiDzFsX0 hCatom_le
    , FKFSsm := hFKFSsm
    , FKFSWm := hFKFSWm
    , FKFSW := hFKFSW
    , prodFKDthFSqo := hprodFKDthFSqo
    , prodFKDthFSX := le_trans hprodFKDthFSX0 hCfka_le
    , prodFKFSqo := hprodFKFSqo
    , prodFKFSX := le_trans hprodFKFSX0 hCfka_le
    , hSinMul := hSinMul }

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux
