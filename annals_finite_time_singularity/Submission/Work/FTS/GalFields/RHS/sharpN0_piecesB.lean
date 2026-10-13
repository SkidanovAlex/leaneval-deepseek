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
import Submission.Work.FTS.GalFields.RHS.sharpN0_tof

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

/-- The `ℋ⁴`-honesty, size and smoothness of the pieces `P6` -- `P9` of the `N₀`-difference. -/
theorem sharpN0_piecesB {α α₂ Ci : ℝ} {g g' h : ℝ → ℝ → ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hIoc : α ∈ Set.Ioc 0 α₂) (hα : 0 < α) (hα1 : α ≤ 1)
    (hg : Work.FTS.Nonlin.GalClass α g) (hg' : Work.FTS.Nonlin.GalClass α g')
    (hgsm : Work.FTS.EllipticEst.SmoothOpen g)
    (hg'sm : Work.FTS.EllipticEst.SmoothOpen g')
    (hhsm : Work.FTS.EllipticEst.SmoothOpen h)
    (hLgSm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 g z))
    (hLg'Sm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 g' z))
    (hLhSm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 h z))
    (hLgMem : Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.L12 g z))
    (hLg'Mem : Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.L12 g' z))
    (hLhMem : Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.L12 h z))
    (hLgXn : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 g z)
      ≤ Ci * Work.FTS.Nonlin.Xn α g)
    (hLhXn : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 h z)
      ≤ Ci * Work.FTS.GalFields.Xn5 α h)
    (hXg5 : Work.FTS.Nonlin.Xn α g ≤ Work.FTS.GalFields.Xn5 α g)
    (hXh5 : Work.FTS.Nonlin.Xn α h ≤ Work.FTS.GalFields.Xn5 α h)
    (hXg'5 : Work.FTS.Nonlin.Xn α g' ≤ Work.FTS.GalFields.Xn5 α g')
    (hDthhSm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth h))
    (hDthhMem : Work.Spaces.HkMem α 4 (Work.Spaces.Dth h))
    (hDthhXn : Work.FTS.Nonlin.Xn α (Work.Spaces.Dth h) ≤ Work.FTS.GalFields.Xn5 α h)
    (hDthg'Xn : Work.FTS.Nonlin.Xn α (Work.Spaces.Dth g') ≤ Work.FTS.GalFields.Xn5 α g')
    (hDz'hSm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz g'))
    (hDz'hMem : Work.Spaces.HkMem α 4 (Work.Spaces.Dz g'))
    (hDz'hXn : Work.FTS.Nonlin.Xn α (Work.Spaces.Dz g') ≤ Work.FTS.GalFields.Xn5 α g')
    (hDzhSm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz h))
    (hDzhMem : Work.Spaces.HkMem α 4 (Work.Spaces.Dz h))
    (hDzhXn : Work.FTS.Nonlin.Xn α (Work.Spaces.Dz h) ≤ Work.FTS.GalFields.Xn5 α h)
    (hZh0 : 0 ≤ Work.FTS.GalFields.Xn5 α h)
    (hLFstarSm : Work.FTS.EllipticEst.SmoothOpen
      (fun z _ => Work.Construction.L12 (Work.Construction.Fstar α) z))
    (hDthFstarSm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.Dth (Work.Construction.Fstar α)))
    (hDzFstarSm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.Dz (Work.Construction.Fstar α)))
    (hc2mSm : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => Work.Construction.c2m θ))
    (CF Cdz Cw : ℝ) (hCF : 0 < CF) (hCdz : 0 < Cdz) (hCw : 0 < Cw)
    (hFstarW : Work.Spaces.WlInfMem α 4 (Work.Spaces.Dth (Work.Construction.Fstar α)) ∧
      Work.Spaces.WlInf α 4 (Work.Spaces.Dth (Work.Construction.Fstar α)) ≤ CF * α ^ 2)
    (hDzstarW : Work.Spaces.WlInfMem α 4 (Work.Spaces.Dz (Work.Construction.Fstar α)) ∧
      Work.Spaces.WlInf α 4 (Work.Spaces.Dz (Work.Construction.Fstar α)) ≤ Cdz * α)
    (hWstar : Work.Spaces.WlInfMem α 4 (fun z θ => Work.Construction.c2m θ
        * Work.Construction.L12 (Work.Construction.Fstar α) z) ∧
      Work.Spaces.WlInf α 4 (fun z θ => Work.Construction.c2m θ
        * Work.Construction.L12 (Work.Construction.Fstar α) z) ≤ Cw * α)
    : (Work.Spaces.HkMem α 4 (P6 α h) ∧ Work.FTS.Nonlin.Xn α (P6 α h)
          ≤ kA6 α Ci Cdz * TOf α g g' h)
      ∧ (Work.Spaces.HkMem α 4 (P7 α g h) ∧ Work.FTS.Nonlin.Xn α (P7 α g h)
          ≤ kA7 α Ci * TOf α g g' h)
      ∧ (Work.Spaces.HkMem α 4 (P8 α g' h) ∧ Work.FTS.Nonlin.Xn α (P8 α g' h)
          ≤ kA8 α Ci * TOf α g g' h)
      ∧ (Work.Spaces.HkMem α 4 (P9 α h) ∧ Work.FTS.Nonlin.Xn α (P9 α h)
          ≤ kA9 α Ci Cw * TOf α g g' h)
      ∧ Work.FTS.EllipticEst.SmoothOpen (P6 α h)
      ∧ Work.FTS.EllipticEst.SmoothOpen (P7 α g h)
      ∧ Work.FTS.EllipticEst.SmoothOpen (P8 α g' h)
      ∧ Work.FTS.EllipticEst.SmoothOpen (P9 α h) := by
  have hCi : 0 < Ci := hN.pos.1
  have h0g : (0 : ℝ) ≤ Work.FTS.GalFields.Xn5 α g := Work.Spaces.HkNorm_nonneg α 5 g
  have h0g' : (0 : ℝ) ≤ Work.FTS.GalFields.Xn5 α g' := Work.Spaces.HkNorm_nonneg α 5 g'
  have hs6 : Work.FTS.EllipticEst.SmoothOpen (P6 α h) := by
    unfold P6
    exact smoothOpen_neg' (Work.FTS.NonlinRows.smoothOpen_mul hc2mSm
      (Work.FTS.NonlinRows.smoothOpen_mul hDzFstarSm hLhSm))
  have h6 : Work.Spaces.HkMem α 4 (P6 α h) ∧ Work.FTS.Nonlin.Xn α (P6 α h) ≤ kA6 α Ci Cdz * TOf α g g' h := by
    have hw := hN.wprod α hIoc (Work.Spaces.Dz (Work.Construction.Fstar α))
      (fun z θ => Work.Construction.L12 h z) hDzFstarSm (hDzstarW).1
      ⟨hLhSm, hLhMem⟩
    have huSm : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => Work.Spaces.Dz (Work.Construction.Fstar α) z θ
          * Work.Construction.L12 h z) :=
      Work.FTS.NonlinRows.smoothOpen_mul hDzFstarSm hLhSm
    have hang6 := Cangdef_spec.2 α (fun z θ => Work.Spaces.Dz (Work.Construction.Fstar α) z θ
        * Work.Construction.L12 h z) hα hα1 huSm hw.1
    refine ⟨?_, ?_⟩
    · unfold P6
      exact Work.FTS.StrongPersist.L3Rhs.HkMem_neg α 4 hang6.1
    · have hnegXn : Work.FTS.Nonlin.Xn α (P6 α h) = Work.FTS.Nonlin.Xn α
          (fun z θ => Work.Construction.c2m θ * (Work.Spaces.Dz (Work.Construction.Fstar α) z θ
            * Work.Construction.L12 h z)) := by
        unfold P6
        show Work.Spaces.HkNorm α 4 (-(fun z θ => Work.Construction.c2m θ
            * (Work.Spaces.Dz (Work.Construction.Fstar α) z θ
              * Work.Construction.L12 h z))) = _
        rw [Work.FTS.EllipticEst.HkNorm_neg]
      rw [hnegXn]
      have hC0 : (0 : ℝ) ≤ Cangdef := Cangdef_pos.le
      have hstep : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.c2m θ
            * (Work.Spaces.Dz (Work.Construction.Fstar α) z θ * Work.Construction.L12 h z))
          ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * (Cdz * α)
              * (Ci * Work.FTS.GalFields.Xn5 α h)) := by
        have h1 := Xn_le_of_HkSq_le hC0 hang6.2
        refine le_trans h1 ?_
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hA0 : (0 : ℝ) ≤ Ci * α ^ (-(1 / 2 : ℝ)) := by positivity
        refine le_trans hw.2 ?_
        calc Ci * α ^ (-(1 / 2 : ℝ))
              * Work.Spaces.WlInf α 4 (Work.Spaces.Dz (Work.Construction.Fstar α))
              * Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 h z)
            ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Cdz * α)
              * Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 h z) :=
              mul_le_mul (mul_le_mul_of_nonneg_left (hDzstarW).2 hA0) (le_refl _)
                (Work.Spaces.HkNorm_nonneg α 4 (fun z θ => Work.Construction.L12 h z))
                (mul_nonneg hA0 (by positivity))
          _ ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Cdz * α)
              * (Ci * Work.FTS.GalFields.Xn5 α h) :=
              mul_le_mul_of_nonneg_left hLhXn (mul_nonneg hA0 (by positivity))
      refine le_trans hstep ?_
      rw [kA6, TOf]
      have h1' : (1 : ℝ) ≤ 1 + Work.FTS.GalFields.Xn5 α g
          + Work.FTS.GalFields.Xn5 α g' := by linarith
      exact tof_mul_left_le' (Real.sqrt_nonneg Cangdef) (by positivity)
        (le_of_lt hCi) hZh0 h1'
  have hs7 : Work.FTS.EllipticEst.SmoothOpen (P7 α g h) := by
    unfold P7
    exact smoothOpen_neg' (Work.FTS.NonlinRows.smoothOpen_mul hc2mSm
      (Work.FTS.NonlinRows.smoothOpen_mul hLgSm hDzhSm))
  have h7 : Work.Spaces.HkMem α 4 (P7 α g h) ∧ Work.FTS.Nonlin.Xn α (P7 α g h) ≤ kA7 α Ci * TOf α g g' h := by
    have hprod := hN.prod α hIoc (fun z θ => Work.Construction.L12 g z) (Work.Spaces.Dz h)
      ⟨hLgSm, hLgMem⟩ ⟨hDzhSm, hDzhMem⟩
    have hang7 := Cangdef_spec.2 α (fun z θ => Work.Construction.L12 g z
        * Work.Spaces.Dz h z θ) hα hα1 (Work.FTS.NonlinRows.smoothOpen_mul hLgSm hDzhSm) hprod.1
    refine ⟨?_, ?_⟩
    · unfold P7
      exact Work.FTS.StrongPersist.L3Rhs.HkMem_neg α 4 hang7.1
    · have hnegXn : Work.FTS.Nonlin.Xn α (P7 α g h) = Work.FTS.Nonlin.Xn α
          (fun z θ => Work.Construction.c2m θ
            * (Work.Construction.L12 g z * Work.Spaces.Dz h z θ)) := by
        unfold P7
        show Work.Spaces.HkNorm α 4 (-(fun z θ => Work.Construction.c2m θ
            * (Work.Construction.L12 g z * Work.Spaces.Dz h z θ))) = _
        rw [Work.FTS.EllipticEst.HkNorm_neg]
      rw [hnegXn]
      have hC0 : (0 : ℝ) ≤ Cangdef := Cangdef_pos.le
      have hstep : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.c2m θ
            * (Work.Construction.L12 g z * Work.Spaces.Dz h z θ))
          ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ))
              * (Ci * Work.FTS.Nonlin.Xn α g) * Work.FTS.GalFields.Xn5 α h) := by
        have h1 := Xn_le_of_HkSq_le hC0 hang7.2
        refine le_trans h1 ?_
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hA0 : (0 : ℝ) ≤ Ci * α ^ (-(1 / 2 : ℝ)) := by positivity
        refine le_trans hprod.2 ?_
        calc Ci * α ^ (-(1 / 2 : ℝ))
              * Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 g z)
              * Work.FTS.Nonlin.Xn α (Work.Spaces.Dz h)
            ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Ci * Work.FTS.Nonlin.Xn α g)
              * Work.FTS.Nonlin.Xn α (Work.Spaces.Dz h) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hLgXn hA0) (le_refl _)
                (Work.Spaces.HkNorm_nonneg α 4 (Work.Spaces.Dz h))
                (mul_nonneg hA0 (mul_nonneg (le_of_lt hCi) (Work.Spaces.HkNorm_nonneg α 4 g)))
          _ ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Ci * Work.FTS.Nonlin.Xn α g)
              * Work.FTS.GalFields.Xn5 α h :=
              mul_le_mul_of_nonneg_left hDzhXn
                (mul_nonneg hA0 (mul_nonneg (le_of_lt hCi)
                  (Work.Spaces.HkNorm_nonneg α 4 g)))
      refine le_trans hstep ?_
      rw [kA7, TOf]
      have h1' : Work.FTS.Nonlin.Xn α g ≤ 1 + Work.FTS.GalFields.Xn5 α g
          + Work.FTS.GalFields.Xn5 α g' := by linarith
      exact tof_mul_mix_le (Real.sqrt_nonneg Cangdef) (by positivity)
        (le_of_lt hCi) hZh0 h1'
  have hs8 : Work.FTS.EllipticEst.SmoothOpen (P8 α g' h) := by
    unfold P8
    exact smoothOpen_neg' (Work.FTS.NonlinRows.smoothOpen_mul hc2mSm
      (Work.FTS.NonlinRows.smoothOpen_mul hLhSm hDz'hSm))
  have h8 : Work.Spaces.HkMem α 4 (P8 α g' h) ∧ Work.FTS.Nonlin.Xn α (P8 α g' h) ≤ kA8 α Ci * TOf α g g' h := by
    have hprod := hN.prod α hIoc (fun z θ => Work.Construction.L12 h z) (Work.Spaces.Dz g')
      ⟨hLhSm, hLhMem⟩ ⟨hDz'hSm, hDz'hMem⟩
    have hang8 := Cangdef_spec.2 α (fun z θ => Work.Construction.L12 h z
        * Work.Spaces.Dz g' z θ) hα hα1 (Work.FTS.NonlinRows.smoothOpen_mul hLhSm hDz'hSm) hprod.1
    refine ⟨?_, ?_⟩
    · unfold P8
      exact Work.FTS.StrongPersist.L3Rhs.HkMem_neg α 4 hang8.1
    · have hnegXn : Work.FTS.Nonlin.Xn α (P8 α g' h) = Work.FTS.Nonlin.Xn α
          (fun z θ => Work.Construction.c2m θ
            * (Work.Construction.L12 h z * Work.Spaces.Dz g' z θ)) := by
        unfold P8
        show Work.Spaces.HkNorm α 4 (-(fun z θ => Work.Construction.c2m θ
            * (Work.Construction.L12 h z * Work.Spaces.Dz g' z θ))) = _
        rw [Work.FTS.EllipticEst.HkNorm_neg]
      rw [hnegXn]
      have hC0 : (0 : ℝ) ≤ Cangdef := Cangdef_pos.le
      have hstep : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.c2m θ
            * (Work.Construction.L12 h z * Work.Spaces.Dz g' z θ))
          ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ))
              * (Ci * Work.FTS.GalFields.Xn5 α h) * Work.FTS.GalFields.Xn5 α g') := by
        have h1 := Xn_le_of_HkSq_le hC0 hang8.2
        refine le_trans h1 ?_
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hA0 : (0 : ℝ) ≤ Ci * α ^ (-(1 / 2 : ℝ)) := by positivity
        refine le_trans hprod.2 ?_
        calc Ci * α ^ (-(1 / 2 : ℝ))
              * Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 h z)
              * Work.FTS.Nonlin.Xn α (Work.Spaces.Dz g')
            ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Ci * Work.FTS.GalFields.Xn5 α h)
              * Work.FTS.Nonlin.Xn α (Work.Spaces.Dz g') :=
              mul_le_mul (mul_le_mul_of_nonneg_left hLhXn hA0) (le_refl _)
                (Work.Spaces.HkNorm_nonneg α 4 (Work.Spaces.Dz g'))
                (mul_nonneg hA0 (by positivity))
          _ ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Ci * Work.FTS.GalFields.Xn5 α h)
              * Work.FTS.GalFields.Xn5 α g' :=
              mul_le_mul_of_nonneg_left hDz'hXn (mul_nonneg hA0 (by positivity))
      refine le_trans hstep ?_
      rw [kA8, TOf]
      have h1' : Work.FTS.GalFields.Xn5 α g' ≤ 1 + Work.FTS.GalFields.Xn5 α g
          + Work.FTS.GalFields.Xn5 α g' := by linarith
      exact tof_mul_mix_le' (Real.sqrt_nonneg Cangdef) (by positivity)
        (le_of_lt hCi) hZh0 h1'
  have hs9 : Work.FTS.EllipticEst.SmoothOpen (P9 α h) := by
    unfold P9
    exact smoothOpen_neg' (Work.FTS.NonlinRows.smoothOpen_mul
      (Work.FTS.NonlinRows.smoothOpen_mul hc2mSm hLFstarSm) hDzhSm)
  have h9 : Work.Spaces.HkMem α 4 (P9 α h) ∧ Work.FTS.Nonlin.Xn α (P9 α h) ≤ kA9 α Ci Cw * TOf α g g' h := by
    have hw := hN.wprod α hIoc
      (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z)
      (Work.Spaces.Dz h)
      (Work.FTS.NonlinRows.smoothOpen_mul hc2mSm hLFstarSm) (hWstar).1
      ⟨hDzhSm, hDzhMem⟩
    refine ⟨?_, ?_⟩
    · unfold P9
      exact Work.FTS.StrongPersist.L3Rhs.HkMem_neg α 4 hw.1
    · have hnegXn : Work.FTS.Nonlin.Xn α (P9 α h) = Work.FTS.Nonlin.Xn α
          (fun z θ => (Work.Construction.c2m θ
            * Work.Construction.L12 (Work.Construction.Fstar α) z)
            * Work.Spaces.Dz h z θ) := by
        unfold P9
        show Work.Spaces.HkNorm α 4 (-(fun z θ => (Work.Construction.c2m θ
            * Work.Construction.L12 (Work.Construction.Fstar α) z)
            * Work.Spaces.Dz h z θ)) = _
        rw [Work.FTS.EllipticEst.HkNorm_neg]
      rw [hnegXn]
      have hstep : Work.FTS.Nonlin.Xn α (fun z θ => (Work.Construction.c2m θ
            * Work.Construction.L12 (Work.Construction.Fstar α) z)
            * Work.Spaces.Dz h z θ)
          ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Cw * α) * Work.FTS.GalFields.Xn5 α h := by
        have hA0 : (0 : ℝ) ≤ Ci * α ^ (-(1 / 2 : ℝ)) := by positivity
        refine le_trans hw.2 ?_
        calc Ci * α ^ (-(1 / 2 : ℝ))
              * Work.Spaces.WlInf α 4 (fun z θ => Work.Construction.c2m θ
                * Work.Construction.L12 (Work.Construction.Fstar α) z)
              * Work.FTS.Nonlin.Xn α (Work.Spaces.Dz h)
            ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Cw * α)
              * Work.FTS.Nonlin.Xn α (Work.Spaces.Dz h) :=
              mul_le_mul (mul_le_mul_of_nonneg_left (hWstar).2 hA0) (le_refl _)
                (Work.Spaces.HkNorm_nonneg α 4 (Work.Spaces.Dz h))
                (mul_nonneg hA0 (by positivity))
          _ ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Cw * α) * Work.FTS.GalFields.Xn5 α h :=
              mul_le_mul_of_nonneg_left hDzhXn (mul_nonneg hA0 (by positivity))
      refine le_trans hstep ?_
      rw [kA9, TOf]
      have h1' : (1 : ℝ) ≤ 1 + Work.FTS.GalFields.Xn5 α g
          + Work.FTS.GalFields.Xn5 α g' := by linarith
      exact tof_mul_left_le_plain (by positivity) hZh0 h1'
  exact ⟨h6, h7, h8, h9, hs6, hs7, hs8, hs9⟩

end Work.FTS.GalFields.RHS
