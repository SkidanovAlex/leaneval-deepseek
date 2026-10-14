import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllExist.LevelK
import Submission.Work.FTS.EllSol.ClassC
import Submission.Work.FTS.EllSol.PkgK5.ropTransferK5c
import Submission.Work.FTS.EllSol.PkgK6.uopTransferKSharp
import Submission.Work.FTS.EllSol.PkgK6.vopTransferKSharp
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkStarPieces
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

namespace Work.FTS.EllSol

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The `ℛ`-slot at levels `2 ≤ k ≤ 6`

The same assembly as `PkgK5.ropTransferK5c`, but with the two *sharp* level-`k` siblings
(`PkgK6.uopTransferKSharp`, `PkgK6.vopTransferKSharp`, which ask for `ℋ^{k+2}` instead of
`ℋ^{k+3}`), so that it applies to the `ℋ⁸`-budget of `EllClassOk 8` at `k = 6`. -/

theorem ropTransferSharp (k : ℕ) (hk : 2 ≤ k) (hk6 : k ≤ 6) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (g Φg : Fn), 0 < α → α ≤ 1 / 4 →
      ClassC α g →
      Work.FTS.StrongGlobal.IsBslSolPos α g Φg →
      Work.FTS.EllipticEst.SmoothOpen Φg →
      Work.FTS.EllipticEst.TT.EllWeakPos α k (Work.Elliptic.orthSource g)
        (ellShift α g Φg) →
      Work.Spaces.HkMem α (k + 2) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2
        (ellShift α g Φg) z θ) →
      Work.Spaces.HkMem α (k + 2) (Work.Elliptic.orthSource g) →
      Work.FTS.VocabO.HQo α k (Work.Construction.Rop α (Work.Construction.PhiTil α g Φg)) ∧
      Work.Spaces.HkNorm α k (Work.Construction.Rop α (Work.Construction.PhiTil α g Φg))
        ≤ C * (α ^ 2 * Work.Spaces.HkNorm α k
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (ellShift α g Φg) z θ)
            + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (ellShift α g Φg))
            + Work.Spaces.HkNorm α k g) := by
  obtain ⟨CU, hCUpos, hU⟩ := PkgK6.uopTransferKSharp k hk hk6
  obtain ⟨CV, hCVpos, hV⟩ := PkgK6.vopTransferKSharp k hk
  obtain ⟨Ca, hCapos, ha⟩ := Work.Blocks.HkMul_ang_le k
  have hCU0 : (0 : ℝ) ≤ CU := le_of_lt hCUpos
  have hCV0 : (0 : ℝ) ≤ CV := le_of_lt hCVpos
  have hCa0 : (0 : ℝ) ≤ Ca := le_of_lt hCapos
  have hsCa0 : (0 : ℝ) ≤ Real.sqrt Ca := Real.sqrt_nonneg Ca
  refine ⟨Real.sqrt 2 * (2 * Real.sqrt Ca + 1) * (CU + CV), by positivity, ?_⟩
  intro α g Φg hα hα4 hC hsol hsmo hW hA hF
  have hα1 : α ≤ 1 := by linarith
  -- the source honesty `HkMem α k g` consumed by the two sharp siblings
  have hmg : Work.Spaces.HkMem α k g :=
    Work.FTS.OpenPkg.HkMem_mono_open (α := α) (k := 7) (f := g) hC.reg k (by omega) hC.mem
  set Ξ : ℝ → ℝ → ℝ := Work.Construction.PhiTil α g Φg with hΞdef
  set X : ℝ := α ^ 2 * Work.Spaces.HkNorm α k
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (ellShift α g Φg) z θ)
      + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (ellShift α g Φg))
      + Work.Spaces.HkNorm α k g with hXdef
  have hX0 : 0 ≤ X := by
    rw [hXdef]
    have h1 : (0 : ℝ) ≤ α ^ 2 * Work.Spaces.HkNorm α k
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (ellShift α g Φg) z θ) :=
      mul_nonneg (sq_nonneg α) (Work.Spaces.HkNorm_nonneg α k _)
    have h2 := Work.Spaces.HkNorm_nonneg α k (Work.Spaces.pthIter 2 (ellShift α g Φg))
    have h3 := Work.Spaces.HkNorm_nonneg α k g
    linarith
  -- the two sibling slots
  obtain ⟨hQHQo, hQb⟩ := hU α g Φg hα hα4 hC hmg hsol hsmo hW hA hF
  obtain ⟨hVHQo, hVb⟩ := hV α g Φg hα hα4 hC hmg hsol hsmo hW hA hF
  set Q : ℝ → ℝ → ℝ := fun z θ =>
    Work.Construction.Uop α Ξ z θ / Work.Construction.s2 θ with hQdef
  set Vf : ℝ → ℝ → ℝ := Work.Construction.Vop Ξ with hVdef
  set S : ℝ → ℝ → ℝ := fun z θ => Real.sin θ ^ 2 * Q z θ with hSdef
  set P : ℝ → ℝ → ℝ := fun z θ => (-2 : ℝ) * S z θ with hPdef
  have hQsmo : Work.FTS.EllipticEst.SmoothOpen Q := hQHQo.1
  have hQmem : Work.Spaces.HkMem α k Q := hQHQo.2
  have hVsmo : Work.FTS.EllipticEst.SmoothOpen Vf := hVHQo.1
  have hVmem : Work.Spaces.HkMem α k Vf := hVHQo.2
  -- the `sin²θ`-multiplier comparison and the two honesty transfers
  have hSsmem : Work.Spaces.HkMem α k S :=
    ((ha α Q hα hα1 hQsmo).2.2 hQmem).2.2.1
  have hSsq : Work.Spaces.HkSq α k S ≤ Ca * Work.Spaces.HkSq α k Q :=
    ((ha α Q hα hα1 hQsmo).2.2 hQmem).2.2.2
  have hSsmo : Work.FTS.EllipticEst.SmoothOpen S :=
    SmoothOpen_mul_sin_sq_local hQsmo
  have hPsmo : Work.FTS.EllipticEst.SmoothOpen P := hSsmo.const_mul' (-2)
  have hPmem : Work.Spaces.HkMem α k P := by
    rw [hPdef]
    exact Work.FTS.LocData.HkMem_const_mul α k (-2) hSsmem
  have hsum_smo : Work.FTS.EllipticEst.SmoothOpen (fun z θ => P z θ + Vf z θ) :=
    SmoothOpen_add_local hPsmo hVsmo
  have hsum_mem : Work.Spaces.HkMem α k (fun z θ => P z θ + Vf z θ) :=
    Work.FTS.EllipticEst.HkMem_add_open hPsmo hVsmo hPmem hVmem
  -- the a.e. identity
  have hAgree : Work.FTS.EllipticEst.AgreeOnQ (fun z θ => P z θ + Vf z θ)
      (Work.Construction.Rop α Ξ) := by
    intro z θ hz hθ0 hθ1
    rw [Work.FTS.EllSol.PkgK5.rop_eq_uop_vop_point hθ0 hθ1]
    simp only [hPdef, hSdef, hQdef, hVdef]
    ring
  have hRopsmo : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Rop α Ξ) :=
    Work.FTS.EllipticEst.SmoothOpen.congr hsum_smo hAgree
  have hRopmem : Work.Spaces.HkMem α k (Work.Construction.Rop α Ξ) :=
    Work.FTS.EllipticEst.HkMem_agreeOnQ hRopsmo hAgree hsum_mem
  -- the norm
  have hSnorm : Work.Spaces.HkNorm α k S ≤ Real.sqrt Ca * Work.Spaces.HkNorm α k Q := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, ← Real.sqrt_mul hCa0]
    exact Real.sqrt_le_sqrt hSsq
  have hPnorm : Work.Spaces.HkNorm α k P ≤ 2 * Work.Spaces.HkNorm α k S := by
    rw [hPdef, Work.FTS.EllipticEst.HkNorm_const_mul α k (-2) hSsmo.forall]
    norm_num
  have hQnorm : Work.Spaces.HkNorm α k Q ≤ CU * X := by
    rw [hXdef]
    exact hQb
  have hVnorm : Work.Spaces.HkNorm α k Vf ≤ CV * X := by
    rw [hXdef]
    exact hVb
  have htri : Work.Spaces.HkNorm α k (fun z θ => P z θ + Vf z θ)
      ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k P + Work.Spaces.HkNorm α k Vf) :=
    Work.FTS.EllipticEst.HkNorm_add_le α k hPsmo.forall hVsmo.forall hPmem hVmem
  have hsqeq : Work.Spaces.HkSq α k (Work.Construction.Rop α Ξ)
      = Work.Spaces.HkSq α k (fun z θ => P z θ + Vf z θ) :=
    (Work.FTS.EllipticEst.HkSq_congr_open α k hAgree).symm
  have hnormRop : Work.Spaces.HkNorm α k (Work.Construction.Rop α Ξ)
      = Work.Spaces.HkNorm α k (fun z θ => P z θ + Vf z θ) := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, hsqeq]
  -- the final arithmetic
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
  calc Work.Spaces.HkNorm α k (fun z θ => P z θ + Vf z θ)
      ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k P + Work.Spaces.HkNorm α k Vf) := htri
    _ ≤ Real.sqrt 2 * (2 * (Real.sqrt Ca * (CU * X)) + CV * X) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg 2)
        have h1 : Work.Spaces.HkNorm α k P ≤ 2 * (Real.sqrt Ca * (CU * X)) := by
          calc Work.Spaces.HkNorm α k P ≤ 2 * Work.Spaces.HkNorm α k S := hPnorm
            _ ≤ 2 * (Real.sqrt Ca * Work.Spaces.HkNorm α k Q) :=
                mul_le_mul_of_nonneg_left hSnorm (by norm_num)
            _ ≤ 2 * (Real.sqrt Ca * (CU * X)) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hQnorm hsCa0) (by norm_num)
        have h2 : Work.Spaces.HkNorm α k Vf ≤ CV * X := hVnorm
        linarith
    _ ≤ Real.sqrt 2 * (2 * Real.sqrt Ca + 1) * (CU + CV) * X := hfinal

/-! ## The target -/

theorem ellPkgK6_of_classC (hEst6 : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllEstUnif 6 C) :
    ∃ Ce α₀ : ℝ, 0 < Ce ∧ 0 < α₀ ∧
    ∀ (α : ℝ) (g Ψ : Work.FTS.Galerkin.Fn), 0 < α → α ≤ α₀ →
      Work.FTS.EllSol.ClassC α g →
      Work.FTS.EllExist.EllClassOk 8 α g Ψ →
      Work.FTS.EllSol.EllPkgK α 6 Ce g Ψ := by
  obtain ⟨Cest, hCest0, hEst⟩ := hEst6
  obtain ⟨Csrc, hCsrc0, hSrc⟩ :=
    EllPkgAux.orthSourceHkNormClassC 6 (by norm_num)
  obtain ⟨CR, hCR0, hR⟩ := ropTransferSharp 6 (by norm_num) (by norm_num)
  obtain ⟨CU, hCU0, hU⟩ := PkgK6.uopTransferKSharp 6 (by norm_num) (by norm_num)
  obtain ⟨CV, hCV0, hV⟩ := PkgK6.vopTransferKSharp 6 (by norm_num)
  refine ⟨(CR + CU + CV) * (Cest * Csrc + 1), 1 / 4, ?_, by norm_num, ?_⟩
  · have h1 : (0 : ℝ) < CR + CU + CV := by linarith
    have h2 : (0 : ℝ) < Cest * Csrc + 1 := by
      have := mul_pos hCest0 hCsrc0
      linarith
    exact mul_pos h1 h2
  intro α g Ψ hα hα4 hC hOK
  have hα1 : α ≤ 1 := by linarith
  -- `ellShift` is (definitionally) the `shiftSing` of the existence node
  have hshift : ellShift α g Ψ = Work.FTS.EllExist.shiftSing α g Ψ := rfl
  -- the weak class at level `6`, and the two `ℋ⁸`-pins
  have hW : Work.FTS.EllipticEst.TT.EllWeakPos α 6 (Work.Elliptic.orthSource g)
      (ellShift α g Ψ) := by
    have h8 := PkgK5.EllWeakPos_descend (l := 6) (K := 8) (by norm_num) hOK.2.2
    rw [← hshift] at h8
    exact h8
  have hA : Work.Spaces.HkMem α 8 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2
      (ellShift α g Ψ) z θ) := by
    have h8 := hOK.2.2.memA
    rw [← hshift] at h8
    exact h8
  have hF : Work.Spaces.HkMem α 8 (Work.Elliptic.orthSource g) := hOK.2.2.memF
  have hmg : Work.Spaces.HkMem α 6 g :=
    Work.FTS.OpenPkg.HkMem_mono_open (α := α) (k := 7) (f := g) hC.reg 6 (by norm_num) hC.mem
  have hsol : Work.FTS.StrongGlobal.IsBslSolPos α g Ψ :=
    Work.FTS.StrongGlobal.IsBslSol.toPos hOK.1
  have hsmo : Work.FTS.EllipticEst.SmoothOpen Ψ := hOK.2.1
  -- the abbreviations of the three norms
  set N1 : ℝ := Work.Spaces.HkNorm α 6 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2
        (ellShift α g Ψ) z θ) with hN1
  set N2 : ℝ := Work.Spaces.HkNorm α 6 (Work.Spaces.pthIter 2 (ellShift α g Ψ)) with hN2
  set Ng : ℝ := Work.Spaces.HkNorm α 6 g with hNg
  have hNg0 : 0 ≤ Ng := by rw [hNg]; exact Work.Spaces.HkNorm_nonneg α 6 g
  have hZ : (0 : ℝ) ≤ Cest * Csrc + 1 := by
    have := mul_pos hCest0 hCsrc0
    linarith
  -- the elliptic bound at level `6`
  have hell : α ^ 2 * N1 + N2 ≤ Cest * Csrc * Ng := by
    have h1 : α ^ 2 * Work.Spaces.HkNorm α 6 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2
          (ellShift α g Ψ) z θ)
        + Work.Spaces.HkNorm α 6 (Work.Spaces.pthIter 2 (ellShift α g Ψ))
        ≤ Cest * Work.Spaces.HkNorm α 6 (Work.Elliptic.orthSource g) :=
      hEst α (Work.Elliptic.orthSource g) (ellShift α g Ψ) hα hα4 hW
    have h2 : Work.Spaces.HkNorm α 6 (Work.Elliptic.orthSource g)
        ≤ Csrc * Ng := by
      rw [hNg]
      exact hSrc α g hα hα1 hC
    have h3 : Cest * Work.Spaces.HkNorm α 6 (Work.Elliptic.orthSource g)
        ≤ Cest * Csrc * Ng :=
      calc Cest * Work.Spaces.HkNorm α 6 (Work.Elliptic.orthSource g)
          ≤ Cest * (Csrc * Ng) := mul_le_mul_of_nonneg_left h2 hCest0.le
        _ = Cest * Csrc * Ng := by ring
    rw [hN1, hN2]
    exact le_trans h1 h3
  have hkey : α ^ 2 * N1 + N2 + Ng ≤ (Cest * Csrc + 1) * Ng := by
    have h : Cest * Csrc * Ng + Ng = (Cest * Csrc + 1) * Ng := by ring
    linarith [hell, h]
  -- the three slots
  obtain ⟨hRm, hRb⟩ := hR α g Ψ hα hα4 hC hsol hsmo hW hA hF
  obtain ⟨hUm, hUb⟩ := hU α g Ψ hα hα4 hC hmg hsol hsmo hW hA hF
  obtain ⟨hVm, hVb⟩ := hV α g Ψ hα hα4 hC hmg hsol hsmo hW hA hF
  have hRb' : Work.Spaces.HkNorm α 6 (Work.Construction.Rop α (Work.Construction.PhiTil α g Ψ))
      ≤ CR * (α ^ 2 * N1 + N2 + Ng) := by
    rw [hN1, hN2, hNg]
    exact hRb
  have hUb' : Work.Spaces.HkNorm α 6 (fun z θ =>
      Work.Construction.Uop α (Work.Construction.PhiTil α g Ψ) z θ / Work.Construction.s2 θ)
      ≤ CU * (α ^ 2 * N1 + N2 + Ng) := by
    rw [hN1, hN2, hNg]
    exact hUb
  have hVb' : Work.Spaces.HkNorm α 6 (Work.Construction.Vop (Work.Construction.PhiTil α g Ψ))
      ≤ CV * (α ^ 2 * N1 + N2 + Ng) := by
    rw [hN1, hN2, hNg]
    exact hVb
  have hsumR : CR * (Cest * Csrc + 1) ≤ (CR + CU + CV) * (Cest * Csrc + 1) :=
    mul_le_mul_of_nonneg_right (by linarith) hZ
  have hsumU : CU * (Cest * Csrc + 1) ≤ (CR + CU + CV) * (Cest * Csrc + 1) :=
    mul_le_mul_of_nonneg_right (by linarith) hZ
  have hsumV : CV * (Cest * Csrc + 1) ≤ (CR + CU + CV) * (Cest * Csrc + 1) :=
    mul_le_mul_of_nonneg_right (by linarith) hZ
  refine ⟨hsol, hsmo, ⟨hRm, ?_⟩, ⟨hUm, ?_⟩, ⟨hVm, ?_⟩⟩
  · calc Work.Spaces.HkNorm α 6 (Work.Construction.Rop α (Work.Construction.PhiTil α g Ψ))
        ≤ CR * (α ^ 2 * N1 + N2 + Ng) := hRb'
      _ ≤ CR * ((Cest * Csrc + 1) * Ng) := mul_le_mul_of_nonneg_left hkey hCR0.le
      _ = CR * (Cest * Csrc + 1) * Ng := by ring
      _ ≤ (CR + CU + CV) * (Cest * Csrc + 1) * Ng :=
          mul_le_mul_of_nonneg_right hsumR hNg0
      _ = (CR + CU + CV) * (Cest * Csrc + 1) * Work.Spaces.HkNorm α 6 g := by rw [hNg]
  · calc Work.Spaces.HkNorm α 6 (fun z θ =>
          Work.Construction.Uop α (Work.Construction.PhiTil α g Ψ) z θ / Work.Construction.s2 θ)
        ≤ CU * (α ^ 2 * N1 + N2 + Ng) := hUb'
      _ ≤ CU * ((Cest * Csrc + 1) * Ng) := mul_le_mul_of_nonneg_left hkey hCU0.le
      _ = CU * (Cest * Csrc + 1) * Ng := by ring
      _ ≤ (CR + CU + CV) * (Cest * Csrc + 1) * Ng :=
          mul_le_mul_of_nonneg_right hsumU hNg0
      _ = (CR + CU + CV) * (Cest * Csrc + 1) * Work.Spaces.HkNorm α 6 g := by rw [hNg]
  · calc Work.Spaces.HkNorm α 6 (Work.Construction.Vop (Work.Construction.PhiTil α g Ψ))
        ≤ CV * (α ^ 2 * N1 + N2 + Ng) := hVb'
      _ ≤ CV * ((Cest * Csrc + 1) * Ng) := mul_le_mul_of_nonneg_left hkey hCV0.le
      _ = CV * (Cest * Csrc + 1) * Ng := by ring
      _ ≤ (CR + CU + CV) * (Cest * Csrc + 1) * Ng :=
          mul_le_mul_of_nonneg_right hsumV hNg0
      _ = (CR + CU + CV) * (Cest * Csrc + 1) * Work.Spaces.HkNorm α 6 g := by rw [hNg]

end Work.FTS.EllSol
