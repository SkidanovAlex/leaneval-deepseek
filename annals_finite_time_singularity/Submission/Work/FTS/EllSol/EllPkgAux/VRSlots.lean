import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllSol.EllPkgAux.Slots
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.StrongEps.RhsCont
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS.StrongGlobal.Global
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.HkMem_mul_of_WlInf6_cd6
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.SolutionDelivery.DatumOdd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The linking identity (local copy) -/

/-- `ℛ(Ξ) = -2 sin²θ · (U(Ξ)/sin 2θ) + V(Ξ)` for `θ ∈ (0,π/2)`. -/
theorem rop_eq_uop_vop_point_cl {α : ℝ} {Ξ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    Work.Construction.Rop α Ξ z θ
      = -2 * Real.sin θ ^ 2
          * (Work.Construction.Uop α Ξ z θ / Work.Construction.s2 θ)
        + Work.Construction.Vop Ξ z θ := by
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ2⟩)
  have hsin : Real.sin θ ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith)
      (by linarith [hθ2, Real.pi_pos]))
  have hs2 : Work.Construction.s2 θ = 2 * Real.sin θ * Real.cos θ := by
    rw [Work.Construction.s2_eq, Real.sin_two_mul]
  rw [Work.Construction.Rop, Work.Construction.Uop, Work.Construction.Vop, Work.Spaces.pz,
    Work.Spaces.pth, Real.tan_eq_sin_div_cos, hs2]
  field_simp
  ring

/-! ## The `V`-slot -/

/-- The `V`-slot at level `4` over level-`7` solutions, from the level-`4` elliptic estimate
(clash-free copy). -/
theorem vopSlotLe4_cl
    (hEst : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllEstUnif 4 C) :
    ∃ C : ℝ, 0 < C ∧ VopSlotLe4 C := by
  obtain ⟨Cest, hCest0, hEst4⟩ := hEst
  obtain ⟨Csrc, hCsrc0, hSrc⟩ := Work.FTS.EllSol.VthAuxC.certC
  obtain ⟨CV, hCV0, hV⟩ :=
    Work.FTS.EllSol.PkgK5.vopTransferK5c 4 (by norm_num) (by norm_num)
  refine ⟨CV * (Cest * Csrc + 1), ?_, ?_⟩
  · have h : (0 : ℝ) < Cest * Csrc + 1 := by
      have := mul_pos hCest0 hCsrc0; linarith
    exact mul_pos hCV0 h
  intro α g Ψ hα hα4 hC hO
  have hα1 : α ≤ 1 := by linarith
  have hsol : Work.FTS.StrongGlobal.IsBslSolPos α g Ψ :=
    Work.FTS.StrongGlobal.IsBslSol.toPos hO.1
  have hsmo : Work.FTS.EllipticEst.SmoothOpen Ψ := hO.2.1
  have hw7 : Work.FTS.EllipticEst.TT.EllWeakPos α 7 (Work.Elliptic.orthSource g)
      (Work.FTS.EllExist.shiftSing α g Ψ) := hO.2.2
  have hw4 : Work.FTS.EllipticEst.TT.EllWeakPos α 4 (Work.Elliptic.orthSource g)
      (Work.FTS.EllSol.ellShift α g Ψ) :=
    Work.FTS.EllSol.PkgK5.EllWeakPos_descend (α := α) (K := 7) (l := 4) (by norm_num) hw7
  have hmemA : Work.Spaces.HkMem α 7
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.FTS.EllSol.ellShift α g Ψ) z θ) :=
    hw7.memA
  have hmemF6 : Work.Spaces.HkMem α 6 (Work.Elliptic.orthSource g) :=
    (Work.FTS.EllSol.PkgK5.EllWeakPos_descend (α := α) (K := 7) (l := 6)
      (by norm_num) hw7).memF
  obtain ⟨hVm, hVb⟩ :=
    hV α g Ψ hα hα4 hC hsol hsmo hw4 hmemA hmemF6
  obtain ⟨_hOrthSm, _hOrthMem, hOrthLe, _hBarSm, _hBarMem, _hBarLe⟩ :=
    hSrc α g hα hα1 hC
  have hell := hEst4 α (Work.Elliptic.orthSource g) (Work.FTS.EllSol.ellShift α g Ψ)
    hα hα4 hw4
  have hNgnn : 0 ≤ Work.Spaces.HkNorm α 4 g := Work.Spaces.HkNorm_nonneg α 4 g
  have hkey : α ^ 2 * Work.Spaces.HkNorm α 4
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.FTS.EllSol.ellShift α g Ψ) z θ)
      + Work.Spaces.HkNorm α 4 (Work.Spaces.pthIter 2 (Work.FTS.EllSol.ellShift α g Ψ))
      + Work.Spaces.HkNorm α 4 g
      ≤ (Cest * Csrc + 1) * Work.Spaces.HkNorm α 4 g := by
    have h2 : Cest * Work.Spaces.HkNorm α 4 (Work.Elliptic.orthSource g)
        ≤ Cest * Csrc * Work.Spaces.HkNorm α 4 g := by
      calc Cest * Work.Spaces.HkNorm α 4 (Work.Elliptic.orthSource g)
          ≤ Cest * (Csrc * Work.Spaces.HkNorm α 4 g) :=
            mul_le_mul_of_nonneg_left hOrthLe (le_of_lt hCest0)
        _ = Cest * Csrc * Work.Spaces.HkNorm α 4 g := by ring
    have hid : Cest * Csrc * Work.Spaces.HkNorm α 4 g + Work.Spaces.HkNorm α 4 g
        = (Cest * Csrc + 1) * Work.Spaces.HkNorm α 4 g := by ring
    linarith [hell, h2, hid]
  refine ⟨hVm, ?_⟩
  calc Work.Spaces.HkNorm α 4 (Work.Construction.Vop (Work.Construction.PhiTil α g Ψ))
      ≤ CV * (α ^ 2 * Work.Spaces.HkNorm α 4
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.FTS.EllSol.ellShift α g Ψ) z θ)
          + Work.Spaces.HkNorm α 4 (Work.Spaces.pthIter 2 (Work.FTS.EllSol.ellShift α g Ψ))
          + Work.Spaces.HkNorm α 4 g) := hVb
    _ ≤ CV * ((Cest * Csrc + 1) * Work.Spaces.HkNorm α 4 g) :=
        mul_le_mul_of_nonneg_left hkey (le_of_lt hCV0)
    _ = CV * (Cest * Csrc + 1) * Work.Spaces.HkNorm α 4 g := by ring

/-! ## The `ℛ`-slot -/

/-- The `ℛ`-slot at level `4` over level-`7` solutions, from the `U`- and `V`-slots
(clash-free copy). -/
theorem ropSlotLe4_cl
    (hU : ∃ C : ℝ, 0 < C ∧ UopSlotLe4 C)
    (hV : ∃ C : ℝ, 0 < C ∧ VopSlotLe4 C) :
    ∃ C : ℝ, 0 < C ∧ RopSlotLe4 C := by
  obtain ⟨CU, hCUpos, hU⟩ := hU
  obtain ⟨CV, hCVpos, hV⟩ := hV
  obtain ⟨Ca, hCapos, ha⟩ := Work.Blocks.HkMul_ang_le 4
  have hCU0 : (0 : ℝ) ≤ CU := le_of_lt hCUpos
  have hCV0 : (0 : ℝ) ≤ CV := le_of_lt hCVpos
  have hCa0 : (0 : ℝ) ≤ Ca := le_of_lt hCapos
  have hsCa0 : (0 : ℝ) ≤ Real.sqrt Ca := Real.sqrt_nonneg Ca
  refine ⟨Real.sqrt 2 * (2 * Real.sqrt Ca + 1) * (CU + CV), by positivity, ?_⟩
  intro α g Ψ hα hα4 hC hΨ
  have hα1 : α ≤ 1 := by linarith
  set Ξ : ℝ → ℝ → ℝ := Work.Construction.PhiTil α g Ψ with hΞdef
  set X : ℝ := Work.Spaces.HkNorm α 4 g with hXdef
  have hX0 : 0 ≤ X := Work.Spaces.HkNorm_nonneg α 4 g
  obtain ⟨hQHQo, hQb⟩ := hU α g Ψ hα hα4 hC hΨ
  obtain ⟨hVHQo, hVb⟩ := hV α g Ψ hα hα4 hC hΨ
  set Q : ℝ → ℝ → ℝ := fun z θ =>
    Work.Construction.Uop α Ξ z θ / Work.Construction.s2 θ with hQdef
  set Vf : ℝ → ℝ → ℝ := Work.Construction.Vop Ξ with hVdef
  set S : ℝ → ℝ → ℝ := fun z θ => Real.sin θ ^ 2 * Q z θ with hSdef
  set P : ℝ → ℝ → ℝ := fun z θ => (-2 : ℝ) * S z θ with hPdef
  have hQsmo : Work.FTS.EllipticEst.SmoothOpen Q := hQHQo.1
  have hQmem : Work.Spaces.HkMem α 4 Q := hQHQo.2
  have hVsmo : Work.FTS.EllipticEst.SmoothOpen Vf := hVHQo.1
  have hVmem : Work.Spaces.HkMem α 4 Vf := hVHQo.2
  have hSsmem : Work.Spaces.HkMem α 4 S :=
    ((ha α Q hα hα1 hQsmo).2.2 hQmem).2.2.1
  have hSsq : Work.Spaces.HkSq α 4 S ≤ Ca * Work.Spaces.HkSq α 4 Q :=
    ((ha α Q hα hα1 hQsmo).2.2 hQmem).2.2.2
  have hSsmo : Work.FTS.EllipticEst.SmoothOpen S :=
    Work.FTS.EllSol.SmoothOpen_mul_sin_sq_local hQsmo
  have hPsmo : Work.FTS.EllipticEst.SmoothOpen P := hSsmo.const_mul' (-2)
  have hPmem : Work.Spaces.HkMem α 4 P := by
    rw [hPdef]
    exact Work.FTS.LocData.HkMem_const_mul α 4 (-2) hSsmem
  have hsum_smo : Work.FTS.EllipticEst.SmoothOpen (fun z θ => P z θ + Vf z θ) :=
    Work.FTS.EllSol.SmoothOpen_add_local hPsmo hVsmo
  have hsum_mem : Work.Spaces.HkMem α 4 (fun z θ => P z θ + Vf z θ) :=
    Work.FTS.EllipticEst.HkMem_add_open hPsmo hVsmo hPmem hVmem
  have hAgree : Work.FTS.EllipticEst.AgreeOnQ (fun z θ => P z θ + Vf z θ)
      (Work.Construction.Rop α Ξ) := by
    intro z θ hz hθ0 hθ1
    rw [rop_eq_uop_vop_point_cl hθ0 hθ1]
    simp only [hPdef, hSdef, hQdef, hVdef]
    ring
  have hRopsmo : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Rop α Ξ) :=
    Work.FTS.EllipticEst.SmoothOpen.congr hsum_smo hAgree
  have hRopmem : Work.Spaces.HkMem α 4 (Work.Construction.Rop α Ξ) :=
    Work.FTS.EllipticEst.HkMem_agreeOnQ hRopsmo hAgree hsum_mem
  have hSnorm : Work.Spaces.HkNorm α 4 S ≤ Real.sqrt Ca * Work.Spaces.HkNorm α 4 Q := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, ← Real.sqrt_mul hCa0]
    exact Real.sqrt_le_sqrt hSsq
  have hPnorm : Work.Spaces.HkNorm α 4 P ≤ 2 * Work.Spaces.HkNorm α 4 S := by
    rw [hPdef, Work.FTS.EllipticEst.HkNorm_const_mul α 4 (-2) hSsmo.forall]
    norm_num
  have hQnorm : Work.Spaces.HkNorm α 4 Q ≤ CU * X := by
    rw [hXdef]
    exact hQb
  have hVnorm : Work.Spaces.HkNorm α 4 Vf ≤ CV * X := by
    rw [hXdef]
    exact hVb
  have htri : Work.Spaces.HkNorm α 4 (fun z θ => P z θ + Vf z θ)
      ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α 4 P + Work.Spaces.HkNorm α 4 Vf) :=
    Work.FTS.EllipticEst.HkNorm_add_le α 4 hPsmo.forall hVsmo.forall hPmem hVmem
  have hsqeq : Work.Spaces.HkSq α 4 (Work.Construction.Rop α Ξ)
      = Work.Spaces.HkSq α 4 (fun z θ => P z θ + Vf z θ) :=
    (Work.FTS.EllipticEst.HkSq_congr_open α 4 hAgree).symm
  have hnormRop : Work.Spaces.HkNorm α 4 (Work.Construction.Rop α Ξ)
      = Work.Spaces.HkNorm α 4 (fun z θ => P z θ + Vf z θ) := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, hsqeq]
  have hfinal : Real.sqrt 2 * (2 * (Real.sqrt Ca * (CU * X)) + CV * X)
      ≤ Real.sqrt 2 * (2 * Real.sqrt Ca + 1) * (CU + CV) * X := by
    have hcoef : 2 * Real.sqrt Ca * CU + CV ≤ (2 * Real.sqrt Ca + 1) * (CU + CV) := by
      have h0 : (0 : ℝ) ≤ 2 * Real.sqrt Ca * CV + CU := by nlinarith [hsCa0, hCU0, hCV0]
      nlinarith
    calc Real.sqrt 2 * (2 * (Real.sqrt Ca * (CU * X)) + CV * X)
        = Real.sqrt 2 * ((2 * Real.sqrt Ca * CU + CV) * X) := by ring
      _ ≤ Real.sqrt 2 * (((2 * Real.sqrt Ca + 1) * (CU + CV)) * X) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcoef hX0)
            (Real.sqrt_nonneg 2)
      _ = Real.sqrt 2 * (2 * Real.sqrt Ca + 1) * (CU + CV) * X := by ring
  refine ⟨⟨hRopsmo, hRopmem⟩, ?_⟩
  rw [hnormRop]
  calc Work.Spaces.HkNorm α 4 (fun z θ => P z θ + Vf z θ)
      ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α 4 P + Work.Spaces.HkNorm α 4 Vf) := htri
    _ ≤ Real.sqrt 2 * (2 * (Real.sqrt Ca * (CU * X)) + CV * X) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg 2)
        have h1 : Work.Spaces.HkNorm α 4 P ≤ 2 * (Real.sqrt Ca * (CU * X)) := by
          calc Work.Spaces.HkNorm α 4 P ≤ 2 * Work.Spaces.HkNorm α 4 S := hPnorm
            _ ≤ 2 * (Real.sqrt Ca * Work.Spaces.HkNorm α 4 Q) :=
                mul_le_mul_of_nonneg_left hSnorm (by norm_num)
            _ ≤ 2 * (Real.sqrt Ca * (CU * X)) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hQnorm hsCa0) (by norm_num)
        have h2 : Work.Spaces.HkNorm α 4 Vf ≤ CV * X := hVnorm
        linarith
    _ ≤ Real.sqrt 2 * (2 * Real.sqrt Ca + 1) * (CU + CV) * X := hfinal

end Work.FTS.EllSol.EllPkgAux
