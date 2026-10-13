import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.GalFields.Defs
import Submission.Work.FTS.GalFields.RHS.HkSum
import Submission.Work.FTS.GalFields.Norm.Basic
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.Nonlinear.Open.Row1
import Submission.Work.FTS.Nonlinear.Open.Row2
import Submission.Work.FTS.Nonlinear.Open.Row3
import Submission.Work.FTS.Nonlinear.Open.Row4
import Submission.Work.FTS.Nonlinear.Open.Row5
import Submission.Work.FTS.Nonlinear.Open.Row6
import Submission.Work.FTS.Nonlinear.Open.Row7
import Submission.Work.FTS.Nonlinear.Open.Splits
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0
import Submission.Work.FTS.NonlinRows.NRow1_7Aux
import Submission.Work.FTS.CoercivityFix.QuadPorts.RegQ_dz
import Submission.Work.FTS.Nonlinear.N4Fields.angmul_field_smooth
import Submission.Work.FTS.FinalClock.L12LinearSub
import Submission.Work.FTS.GalBasis.cc.L12_add_of_HkMem
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_Dth_le
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_mono_le
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.StrongLWP.Basic
import Submission.Work.FTS.Nonlinear.FstarPkg.DthFstar_W
import Submission.Work.FTS.Nonlinear.FstarPkg.DzFstar_W
import Submission.Work.FTS.Nonlinear.FstarPkg.c2m_L12Fstar_W
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.MuFix.MufunS

import Submission.Work.FTS.GalFields.RHS.sharpN0_defs
import Submission.Work.FTS.GalFields.RHS.sharpN0_hkMem
import Submission.Work.FTS.GalFields.RHS.sharpN0_piecesA
import Submission.Work.FTS.GalFields.RHS.sharpN0_piecesB
import Submission.Work.FTS.GalFields.RHS.sharpN0_sums

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end


noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.RHS

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

theorem sharp_N0_diff {α α₂ Ci Ct Ce Cs : ℝ}
    {IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {EllSol : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hell : ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.Nonlin.GalClass α g →
      Work.FTS.VocabO.EllPkgGo α Ce g (EllSol g))
    (hEllSub : ∀ g g' : Work.FTS.Galerkin.Fn,
      EllSol (fun z θ => g z θ - g' z θ) = fun z θ => EllSol g z θ - EllSol g' z θ)
    (hα : 0 < α) (hαα₂ : α ≤ α₂) :
    ∃ K : ℝ, 0 < K ∧ ∀ g g' h : Work.FTS.Galerkin.Fn,
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.GalClass α g' →
      Work.FTS.Nonlin.GalClass α h →
      (∀ z θ, h z θ = g z θ - g' z θ) → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
          Work.Construction.N0 α (Work.Construction.Ftot α g) g z θ
            - Work.Construction.N0 α (Work.Construction.Ftot α g') g' z θ) ∧
      Work.Spaces.HkMem α 4 (fun z θ =>
          Work.Construction.N0 α (Work.Construction.Ftot α g) g z θ
            - Work.Construction.N0 α (Work.Construction.Ftot α g') g' z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ =>
          Work.Construction.N0 α (Work.Construction.Ftot α g) g z θ
            - Work.Construction.N0 α (Work.Construction.Ftot α g') g' z θ)
        ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
            * Work.FTS.GalFields.Xn5 α h ∧
      |Work.Construction.L12
          (Work.Construction.N0 α (Work.Construction.Ftot α g) g) 0
        - Work.Construction.L12
          (Work.Construction.N0 α (Work.Construction.Ftot α g') g') 0|
        ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
            * Work.FTS.GalFields.Xn5 α h := by
  obtain ⟨K1, hK1, row1⟩ := Work.FTS.Nonlinear.Open.Row1 IP hN hE
  obtain ⟨K2, hK2, row2⟩ := Work.FTS.Nonlinear.Open.Row2 IP hN hE
  obtain ⟨K3, hK3, row3⟩ := Work.FTS.Nonlinear.Open.Row3 IP hN hE
  obtain ⟨K4, hK4, row4⟩ := Work.FTS.Nonlinear.Open.Row4 IP hN hE
  obtain ⟨K5, hK5, row5⟩ := Work.FTS.Nonlinear.Open.Row5 IP hN hE
  obtain ⟨K6, hK6, row6⟩ := Work.FTS.Nonlinear.Open.Row6 IP hN hE
  obtain ⟨K7, hK7, row7⟩ := Work.FTS.Nonlinear.Open.Row7 IP hN hE
  obtain ⟨CF, hCF, hFstarW⟩ := Work.FTS.Nonlinear.FstarPkg.DthFstar_W
  obtain ⟨Cdz, hCdz, hDzstarW⟩ := Work.FTS.Nonlinear.FstarPkg.DzFstar_W
  obtain ⟨Cw, hCw, hWstar⟩ := Work.FTS.Nonlinear.FstarPkg.c2m_L12Fstar_W
  have hCi : 0 < Ci := hN.pos.1
  have hK0 : 0 ≤ ksum α Ci CF Cdz Cw := ksum_nonneg hα hCi hCF hCdz hCw
  set K : ℝ := 1024 * (1 + Ci) * ksum α Ci CF Cdz Cw + 1 with hK
  have hKpos : 0 < K := by rw [hK]; nlinarith
  refine ⟨K, hKpos, ?_⟩
  intro g g' h hg hg' hh hdiff hα1
  have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  set D : ℝ → ℝ → ℝ := fun z θ =>
    Work.Construction.N0 α (Work.Construction.Ftot α g) g z θ
      - Work.Construction.N0 α (Work.Construction.Ftot α g') g' z θ with hD

  -- ## the datum and the fixed profile
  have hFstarSm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α
  have hLFstarSm : Work.FTS.EllipticEst.SmoothOpen
      (fun z _ => Work.Construction.L12 (Work.Construction.Fstar α) z) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_L12_Fstar α
  have hDthFstarSm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.Dth (Work.Construction.Fstar α)) := hFstarSm.Dth
  have hDzFstarSm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.Dz (Work.Construction.Fstar α)) := hFstarSm.Dz
  have hc2mSm : Work.FTS.EllipticEst.SmoothOpen
      (fun _ (θ : ℝ) => Work.Construction.c2m θ) := smoothOpen_c2m_ang
  have hs2Sm : Work.FTS.EllipticEst.SmoothOpen
      (fun _ (θ : ℝ) => Work.Construction.s2 θ) := smoothOpen_sin_two_ang
  have hgsm : Work.FTS.EllipticEst.SmoothOpen g :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad hg.reg.1
  have hg'sm : Work.FTS.EllipticEst.SmoothOpen g' :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad hg'.reg.1
  have hhsm : Work.FTS.EllipticEst.SmoothOpen h :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad hh.reg.1
  have hDthhSm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth h) := hhsm.Dth
  have hDz'hSm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz g') := hg'sm.Dz
  have hDzhSm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz h) := hhsm.Dz
  -- honesty of the `D`-derivatives
  have hDthhMem : Work.Spaces.HkMem α 4 (Work.Spaces.Dth h) :=
    Work.FTS.CoercivityFix.E2Bound.HkMem_dth_of_RegQ_ge α 4 (by linarith)
      (Work.FTS.LocDataExt.RegQ_mono (by norm_num) hh.reg)
  have hDz'hMem : Work.Spaces.HkMem α 4 (Work.Spaces.Dz g') :=
    Work.FTS.CoercivityFix.QuadPorts.HkMem_Dz_quad α 4 hg'.reg.1
      (Work.FTS.OpenPkg.galClass_HkMem5 hg')
  have hDzhMem : Work.Spaces.HkMem α 4 (Work.Spaces.Dz h) :=
    Work.FTS.CoercivityFix.QuadPorts.HkMem_Dz_quad α 4 hh.reg.1
      (Work.FTS.OpenPkg.galClass_HkMem5 hh)
  -- the `L₁₂`-factors
  have hellg := hell g hg
  have hellg' := hell g' hg'
  have hLgSm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 g z) :=
    Work.FTS.NonlinRows.smoothOpen_L12_radial hα hellg.smooth hellg.V.1.1
  have hLg'Sm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 g' z) :=
    Work.FTS.NonlinRows.smoothOpen_L12_radial hα hellg'.smooth hellg'.V.1.1
  have hLhSm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 h z) :=
    Work.FTS.NonlinRows.smoothOpen_L12_radial hα (hell h hh).smooth
      (hell h hh).V.1.1
  have hLgMem : Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.L12 g z) :=
    (hN.l12H α hIoc g (Work.FTS.OpenPkg.HQo_of_RegQ (Work.FTS.Nonlin.galClass_regQ4 hg))
      hg.l12).1
  have hLgXn : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 g z)
      ≤ Ci * Work.FTS.Nonlin.Xn α g :=
    (hN.l12H α hIoc g (Work.FTS.OpenPkg.HQo_of_RegQ (Work.FTS.Nonlin.galClass_regQ4 hg))
      hg.l12).2
  have hLg'Mem : Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.L12 g' z) :=
    (hN.l12H α hIoc g' (Work.FTS.OpenPkg.HQo_of_RegQ (Work.FTS.Nonlin.galClass_regQ4 hg'))
      hg'.l12).1
  have hLhMem : Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.L12 h z) :=
    (hN.l12H α hIoc h (Work.FTS.OpenPkg.HQo_of_RegQ (Work.FTS.Nonlin.galClass_regQ4 hh))
      hh.l12).1
  have hLhXn : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 h z)
      ≤ Ci * Work.FTS.GalFields.Xn5 α h := by
    have h1 : Work.FTS.Nonlin.Xn α h ≤ Work.FTS.GalFields.Xn5 α h :=
      Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 5) (k' := 4) (by norm_num)
        (Work.FTS.OpenPkg.galClass_HkMem5 hh)
    have h2 := (hN.l12H α hIoc h
      (Work.FTS.OpenPkg.HQo_of_RegQ (Work.FTS.Nonlin.galClass_regQ4 hh)) hh.l12).2
    calc Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 h z)
        ≤ Ci * Work.FTS.Nonlin.Xn α h := h2
      _ ≤ Ci * Work.FTS.GalFields.Xn5 α h := by
          exact mul_le_mul_of_nonneg_left h1 (le_of_lt hCi)
  -- the `ℋ⁵`-comparisons
  have hXg5 : Work.FTS.Nonlin.Xn α g ≤ Work.FTS.GalFields.Xn5 α g :=
    Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 5) (k' := 4) (by norm_num)
      (Work.FTS.OpenPkg.galClass_HkMem5 hg)
  have hXg'5 : Work.FTS.Nonlin.Xn α g' ≤ Work.FTS.GalFields.Xn5 α g' :=
    Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 5) (k' := 4) (by norm_num)
      (Work.FTS.OpenPkg.galClass_HkMem5 hg')
  have hXh5 : Work.FTS.Nonlin.Xn α h ≤ Work.FTS.GalFields.Xn5 α h :=
    Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 5) (k' := 4) (by norm_num)
      (Work.FTS.OpenPkg.galClass_HkMem5 hh)
  have hDthhXn : Work.FTS.Nonlin.Xn α (Work.Spaces.Dth h) ≤ Work.FTS.GalFields.Xn5 α h :=
    Work.FTS.GalFields.Xn_Dth_le_Xn5 hα (Work.FTS.OpenPkg.galClass_HkMem5 hh)
  have hDz'hXn : Work.FTS.Nonlin.Xn α (Work.Spaces.Dz g') ≤ Work.FTS.GalFields.Xn5 α g' :=
    Work.FTS.GalFields.Xn_Dz_le_Xn5 hα hg'sm (Work.FTS.OpenPkg.galClass_HkMem5 hg')
  have hDzhXn : Work.FTS.Nonlin.Xn α (Work.Spaces.Dz h) ≤ Work.FTS.GalFields.Xn5 α h :=
    Work.FTS.GalFields.Xn_Dz_le_Xn5 hα hhsm (Work.FTS.OpenPkg.galClass_HkMem5 hh)
  have hDthg'Xn : Work.FTS.Nonlin.Xn α (Work.Spaces.Dth g') ≤ Work.FTS.GalFields.Xn5 α g' :=
    Work.FTS.GalFields.Xn_Dth_le_Xn5 hα (Work.FTS.OpenPkg.galClass_HkMem5 hg')
  have hZh0 : 0 ≤ Work.FTS.GalFields.Xn5 α h := Work.Spaces.HkNorm_nonneg α 5 h
  have hXg50 : 0 ≤ Work.FTS.GalFields.Xn5 α g := Work.Spaces.HkNorm_nonneg α 5 g
  have hXg'50 : 0 ≤ Work.FTS.GalFields.Xn5 α g' := Work.Spaces.HkNorm_nonneg α 5 g'
  -- the angular hypotheses for `c2m`
  have hc2mB : ∀ θ ∈ Work.Spaces.Iθ, |Work.Construction.c2m θ| ≤ 1000 :=
    fun θ _ => abs_c2m_le_thousand θ
  have hc2mIt : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Construction.c2m θ') 0 θ|
        ≤ 1000 * Real.sin (2 * θ) :=
    fun i hi hi4 θ hθ => DthIter_c2m_le_sin i hi hi4 θ hθ
  -- ## the auxiliary bounds of the three pieces
  have hA1 := sharpN0_piecesA (α := α) (α₂ := α₂) (Ci := Ci) hN hIoc hα hα1 hg hg' hgsm hg'sm
    hhsm hh hLgSm hLg'Sm hLhSm hLgMem hLg'Mem hLhMem hLgXn hLhXn hXg5 hXh5 hXg'5 hDthhSm hDthhMem
    hDthhXn hDthg'Xn hDz'hSm hDz'hMem hDz'hXn hDzhSm hDzhMem hDzhXn hZh0 hLFstarSm hDthFstarSm
    hDzFstarSm hc2mSm CF Cdz Cw hCF hCdz hCw (hFstarW α hα hα1) (hDzstarW α hα hα1)
    (hWstar α hα hα1)
  obtain ⟨h1, h2, h3, h4, h5, hs1, hs2, hs3, hs4, hs5⟩ := hA1
  have hA2 := sharpN0_piecesB (α := α) (α₂ := α₂) (Ci := Ci) hN hIoc hα hα1 hg hg' hgsm hg'sm
    hhsm hLgSm hLg'Sm hLhSm hLgMem hLg'Mem hLhMem hLgXn hLhXn hXg5 hXh5 hXg'5 hDthhSm hDthhMem hDthhXn
    hDthg'Xn hDz'hSm hDz'hMem hDz'hXn hDzhSm hDzhMem hDzhXn hZh0 hLFstarSm hDthFstarSm hDzFstarSm
    hc2mSm CF Cdz Cw hCF hCdz hCw (hFstarW α hα hα1) (hDzstarW α hα hα1)
    (hWstar α hα hα1)
  obtain ⟨h6, h7, h8, h9, hs6, hs7, hs8, hs9⟩ := hA2
  have hA3 := sharpN0_sums (α := α) (Ci := Ci) hα hCi CF Cdz Cw hCF hCdz hCw h1 h2 h3 h4 h5 h6 h7
    h8 h9 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9
  obtain ⟨hRmem, hRsm, hRx⟩ := hA3

  -- ## the pointwise identity `N₀(g) - N₀(g') = R1` on the open quadrant
  have hSplitg := (Work.FTS.Nonlinear.Open.Splits IP hN hE hα hα1 hαα₂ hg hstar (hell g hg)).1
  have hSplitg' := (Work.FTS.Nonlinear.Open.Splits IP hN hE hα hα1 hαα₂ hg' hstar (hell g' hg')).1
  have hhfun : (fun z θ => g z θ - g' z θ) = h := by
    funext z θ
    exact (hdiff z θ).symm
  have hDelta_eq : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → D z θ = Rsum α g g' h z θ := by
    intro z θ hz hθ0 hθ1
    have hzθ : (z, θ) ∈ Work.Construction.Qd := ⟨hz, ⟨hθ0, hθ1⟩⟩
    have hgh : ∀ z' θ', g z' θ' = g' z' θ' + h z' θ' := by
      intro z' θ'
      have := hdiff z' θ'
      linarith
    have hLadd : Work.Construction.L12 g z
        = Work.Construction.L12 g' z + Work.Construction.L12 h z := by
      have h := L12_sub_eq_of_smoothOpen hgsm hg'sm
        (Work.FTS.OpenPkg.galClass_HkMem4 hg) (Work.FTS.OpenPkg.galClass_HkMem4 hg')
        z (le_of_lt hz)
      rw [hhfun] at h
      linarith
    have hpzadd : Work.Spaces.pz g z θ = Work.Spaces.pz g' z θ + Work.Spaces.pz h z θ :=
      pz_add_of_smoothOpen hg'sm hhsm hgh z θ hz hθ0 hθ1
    have hpthadd : Work.Spaces.pth g z θ = Work.Spaces.pth g' z θ + Work.Spaces.pth h z θ :=
      pth_add_of_smoothOpen hg'sm hhsm hgh z θ hz hθ0 hθ1
    have h3 : Work.FTS.Nonlin.N03g α g z θ
        = Work.FTS.Nonlin.N03g α g' z θ + (P1 α g h z θ + P2 α g' h z θ) := by
      unfold P1 P2
      simp only [Work.FTS.Nonlin.N03g, Work.Construction.N03]
      rw [hgh z θ, hLadd]
      ring
    have h4a : Work.FTS.Nonlin.N04aF α g z θ
        = Work.FTS.Nonlin.N04aF α g' z θ + P3 α h z θ := by
      unfold P3
      simp only [Work.FTS.Nonlin.N04aF, Work.Construction.N04a, Work.Construction.s2,
        Work.Spaces.Dth]
      rw [hLadd]
      ring
    have h4b : Work.FTS.Nonlin.N04bF α g z θ
        = Work.FTS.Nonlin.N04bF α g' z θ + (P4 α g h z θ + P5 α g' h z θ) := by
      unfold P4 P5
      simp only [Work.FTS.Nonlin.N04bF, Work.Construction.N04b, Work.Construction.s2,
        Work.Spaces.Dth]
      rw [hpthadd, hLadd]
      ring
    have h5a : Work.FTS.Nonlin.N05aF α g z θ
        = Work.FTS.Nonlin.N05aF α g' z θ + P6 α h z θ := by
      unfold P6
      simp only [Work.FTS.Nonlin.N05aF, Work.Construction.N05a]
      rw [hLadd]
      ring
    have h5b : Work.FTS.Nonlin.N05bF α g z θ
        = Work.FTS.Nonlin.N05bF α g' z θ + (P7 α g h z θ + P8 α g' h z θ) := by
      unfold P7 P8
      simp only [Work.FTS.Nonlin.N05bF, Work.Construction.N05b, Work.Spaces.Dz]
      rw [hLadd, hpzadd]
      ring
    have h6 : Work.FTS.Nonlin.N06F α g z θ
        = Work.FTS.Nonlin.N06F α g' z θ + P9 α h z θ := by
      unfold P9
      simp only [Work.FTS.Nonlin.N06F, Work.Construction.N06, Work.Spaces.Dz]
      rw [hpzadd]
      ring
    change Work.Construction.N0 α (Work.Construction.Ftot α g) g z θ
        - Work.Construction.N0 α (Work.Construction.Ftot α g') g' z θ
        = Rsum α g g' h z θ
    rw [hSplitg z θ hzθ, hSplitg' z θ hzθ]
    rw [h3, h4a, h4b, h5a, h5b, h6]
    simp only [Rsum, Pi.add_apply]
    ring
  have hDsm : Work.FTS.EllipticEst.SmoothOpen D := by
    rw [hD]
    exact Work.FTS.EllipticEst.smoothOpen_sub
      (Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0 hα hgsm hLgSm)
      (Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0 hα hg'sm hLg'Sm)
  have hDmem : Work.Spaces.HkMem α 4 D := Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4
    hRmem
    (fun z hz θ hθ => (hDelta_eq z θ hz hθ.1 hθ.2).symm)
  have hDSq : Work.Spaces.HkSq α 4 D = Work.Spaces.HkSq α 4 (Rsum α g g' h) :=
    Work.FTS.EllipticEst.HkSq_congr_open α 4 hDelta_eq
  have hDX : Work.FTS.Nonlin.Xn α D = Work.FTS.Nonlin.Xn α (Rsum α g g' h) := by
    show Real.sqrt (Work.Spaces.HkSq α 4 D)
      = Real.sqrt (Work.Spaces.HkSq α 4 (Rsum α g g' h))
    rw [hDSq]
  have hXnD : Work.FTS.Nonlin.Xn α D ≤ 1024 * ksum α Ci CF Cdz Cw * TOf α g g' h := by
    rw [hDX]
    exact hRx
  -- the `ℋ⁴`-honesty of the two `N₀`-blocks (for the `L₁₂`-linearity at `z = 0`)
  have hN0gmem : Work.Spaces.HkMem α 4
      (Work.Construction.N0 α (Work.Construction.Ftot α g) g) :=
    hkMem_N0_of_rows hα hgsm hLgSm
      (row1 (α := α) (g := g) (Φs := Φs) (Φg := EllSol g) hα hα1 hαα₂ hg hstar.toStarPkgo
        hellg).1
      (row2 (α := α) (g := g) (Φs := Φs) (Φg := EllSol g) hα hα1 hαα₂ hg hstar.toStarPkgo
        hellg).1
      (row3 (α := α) (g := g) (Φs := Φs) (Φg := EllSol g) hα hα1 hαα₂ hg hstar.toStarPkgo
        hellg).1
      (row4 (α := α) (g := g) (Φs := Φs) (Φg := EllSol g) hα hα1 hαα₂ hg hstar.toStarPkgo
        hellg).1
      (row5 (α := α) (g := g) (Φs := Φs) (Φg := EllSol g) hα hα1 hαα₂ hg hstar.toStarPkgo
        hellg).1
      (row6 (α := α) (g := g) (Φs := Φs) (Φg := EllSol g) hα hα1 hαα₂ hg hstar.toStarPkgo
        hellg).1
      (row7 (α := α) (g := g) (Φs := Φs) (Φg := EllSol g) hα hα1 hαα₂ hg hstar.toStarPkgo
        hellg).1
      hSplitg
  have hN0g'mem : Work.Spaces.HkMem α 4
      (Work.Construction.N0 α (Work.Construction.Ftot α g') g') :=
    hkMem_N0_of_rows hα hg'sm hLg'Sm
      (row1 (α := α) (g := g') (Φs := Φs) (Φg := EllSol g') hα hα1 hαα₂ hg' hstar.toStarPkgo
        hellg').1
      (row2 (α := α) (g := g') (Φs := Φs) (Φg := EllSol g') hα hα1 hαα₂ hg' hstar.toStarPkgo
        hellg').1
      (row3 (α := α) (g := g') (Φs := Φs) (Φg := EllSol g') hα hα1 hαα₂ hg' hstar.toStarPkgo
        hellg').1
      (row4 (α := α) (g := g') (Φs := Φs) (Φg := EllSol g') hα hα1 hαα₂ hg' hstar.toStarPkgo
        hellg').1
      (row5 (α := α) (g := g') (Φs := Φs) (Φg := EllSol g') hα hα1 hαα₂ hg' hstar.toStarPkgo
        hellg').1
      (row6 (α := α) (g := g') (Φs := Φs) (Φg := EllSol g') hα hα1 hαα₂ hg' hstar.toStarPkgo
        hellg').1
      (row7 (α := α) (g := g') (Φs := Φs) (Φg := EllSol g') hα hα1 hαα₂ hg' hstar.toStarPkgo
        hellg').1
      hSplitg'
  refine ⟨hDsm, hDmem, ?_, ?_⟩
  · refine le_trans hXnD ?_
    have hle : 1024 * ksum α Ci CF Cdz Cw ≤ K := by
      rw [hK]; nlinarith [hK0, hCi, mul_nonneg (le_of_lt hCi) hK0]
    calc 1024 * ksum α Ci CF Cdz Cw * TOf α g g' h
        ≤ K * TOf α g g' h :=
          mul_le_mul_of_nonneg_right hle (TOf_nonneg α g g' h)
      _ = K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
            * Work.FTS.GalFields.Xn5 α h := by rw [TOf, mul_assoc]
  · have hL12lin : Work.Construction.L12
        (Work.Construction.N0 α (Work.Construction.Ftot α g) g) 0
        - Work.Construction.L12
          (Work.Construction.N0 α (Work.Construction.Ftot α g') g') 0
        = Work.Construction.L12 (fun z θ =>
            Work.Construction.N0 α (Work.Construction.Ftot α g) g z θ
              - Work.Construction.N0 α (Work.Construction.Ftot α g') g' z θ) 0 :=
      L12_sub_eq_of_smoothOpen
        (Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0 hα hgsm hLgSm)
        (Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0 hα hg'sm hLg'Sm)
        hN0gmem hN0g'mem 0 (le_refl 0)
    rw [hL12lin, ← hD]
    have hzero := hN.l12zero α hIoc D ⟨hDsm, hDmem⟩
    have hle : Ci * (1024 * ksum α Ci CF Cdz Cw) ≤ K := by
      rw [hK]; nlinarith [hK0, hCi, mul_nonneg (le_of_lt hCi) hK0]
    refine le_trans hzero ?_
    calc Ci * Work.FTS.Nonlin.Xn α D
        ≤ Ci * (1024 * ksum α Ci CF Cdz Cw * TOf α g g' h) :=
          mul_le_mul_of_nonneg_left hXnD (le_of_lt hCi)
      _ = Ci * (1024 * ksum α Ci CF Cdz Cw) * TOf α g g' h := by ring
      _ ≤ K * TOf α g g' h :=
          mul_le_mul_of_nonneg_right hle (TOf_nonneg α g g' h)
      _ = K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
            * Work.FTS.GalFields.Xn5 α h := by rw [TOf, mul_assoc]


end Work.FTS.GalFields.RHS
