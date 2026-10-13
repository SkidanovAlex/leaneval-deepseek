import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.JfamPDefectAlg
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.JfamPDefectTransfer
import Submission.Work.FTS.StrongEps.epsWP_hkMem4_KW_unif
import Submission.Work.FTS.StrongEps.L12_Jeps_sub_le4
import Submission.Work.FTS.StrongEps.EpsZeroMode
import Submission.Work.FTS.StrongEps.JfamP_norm
import Submission.Work.FTS.StrongEps.EpsApprox.HkNorm_Jeps_sub_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongEps Work.Spaces Work.FTS.EllipticEst Work.Construction
open Work.FTS.VocabO Work.FTS.VocabO2 Work.FTS.ClassC Work.FTS.StrongGlobal
open Work.FTS.Nonlin Work.FTS.NonlinRows Work.FTS.OpenPkg Work.FTS.GalFields
open RHS Work.FTS.GalBasis cc
open Work.FTS.CoercivityFix Transfer Work.FTS.StrongPersist Work.FTS.IPGen

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

local notation "IP4" => Assembly.IP4

/-- `Kc·ε`-defect of the projected `ε`-scheme's right-hand side (`jfamP_defect_bound`). -/
theorem jfamP_defect_bound_aux {ρ : ℝ × ℝ → ℝ} (c₁ c₂ c₃ c₄ c₅ c₆ : ℝ)
    (hρ : IsSmoothKernel ρ)
    {α₂ cc clo Cup Ccs CcN : ℝ}
    (hU : EpsE4Thr.UnifIPO
      (Assembly.IP4 c₁ c₂ c₃ c₄ c₅ c₆) α₂ cc clo Cup Ccs)
    {Ce Cs : ℝ}
    (hN4 : ∀ α ∈ Set.Ioc 0 α₂, ∀ {g Φs Φg : Fn},
      ClassC α g → EpsE4Thr.CoerAdmO α g →
      StarPkgo2 α Cs Φs → EllPkgGo α Ce g Φg →
      Xn α g ≤ α ^ (7 / 4 : ℝ) →
      |Work.FTS.Apriori.rhsPair (Assembly.IP4 c₁ c₂ c₃ c₄ c₅ c₆)
        α g (fun z θ => Φs z θ + Φg z θ)|
        ≤ CcN * Pbd α (Xn α g))
    {α C₀ M : ℝ} (hα : α ∈ Set.Ioc 0 α₂) (hα1 : α ≤ 1) (hC₀ : 0 < C₀) (hM : 0 ≤ M)
    (hsmall : C₀ * α ^ (1 / 4 : ℝ) ≤ 1) :
    ∃ Kc : ℝ, 0 ≤ Kc ∧
      ∀ {T τ ε : ℝ} {Φs : Fn}
        {E : Fn → Fn} {g₀ : Fn}
        {g : Fam},
        0 < T → τ ∈ Set.Ioo 0 T → ε ∈ Set.Ioc 0 1 →
        IsEpsSolP α ρ ε T Φs E g₀ g →
        EpsRegP α ρ ε T g →
        (∀ u : Fn, ClassC α u →
          EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u)) →
        StarPkgo2 α Cs Φs → MuLamOK α C₀ Φs E →
        (∀ s ∈ Set.Icc 0 T, Work.FTS.StrongGlobal.Xn6 α (slice g s) ≤ M) →
        (∀ t ∈ Set.Icc 0 τ, Xn α
          (slice (JfamP ρ ε g) t) ≤ C₀ * α ^ 2) →
        |Assembly.IP4 c₁ c₂ c₃ c₄ c₅ c₆ α
            (Pz (Jeps ρ ε
              (epsRHSP α ρ ε Φs E g τ)))
            (slice (JfamP ρ ε g) τ)
          - Assembly.IP4 c₁ c₂ c₃ c₄ c₅ c₆ α
              (Work.FTS.Galerkin.dynLin α (JfamP ρ ε g) τ
                + Work.FTS.Galerkin.dynRHS α
                    (PsiCan Φs E (JfamP ρ ε g))
                    (JfamP ρ ε g) τ)
              (slice (JfamP ρ ε g) τ)|
          ≤ Kc * ε := by
  have hα0 : 0 < α := hα.1
  have hαI : α ∈ Set.Ioc (0 : ℝ) 1 := ⟨hα0, hα1⟩
  obtain ⟨A6, hA6nn, hJfamP⟩ := HkNorm_JfamP_le (ρ := ρ) hρ
  obtain ⟨KW, hKWpos, hKW⟩ := epsWP_hkMem4_KW_unif (α := α) (C₀ := C₀)
    (B := A6 * M) (Ce := Ce) (Cs := Cs) (ρ := ρ) hαI
  obtain ⟨CT, hCTnn, hTR⟩ := IP4_transfer_deriv_local ρ hρ c₁ c₂ c₃ c₄ c₅ c₆
  obtain ⟨CJ, hCJpos, hJsub⟩ := EpsApprox.HkNorm_Jeps_sub_le ρ hρ.moll
  obtain ⟨CL, hCLpos, hL12sub⟩ := L12_Jeps_sub_le4 ρ hρ
  obtain ⟨CB, hCBpos, hBump⟩ := PZeroAux.exists_HkNorm_bump_le
  obtain ⟨CG, hCGpos, hJle⟩ := HkSq_Jeps_le ρ hρ.moll
  obtain ⟨CC, hCCnn, hCS⟩ := IP4_cs_local c₁ c₂ c₃ c₄ c₅ c₆
  have hpzpos : 0 < pzNorm := PZeroAux.pzNorm_pos
  have hpzne : pzNorm ≠ 0 := ne_of_gt hpzpos
  set Kx : ℝ := A6 * M with hKxdef
  set KR : ℝ := 2 * (Real.exp (CG / 2) * KW + CL * KW / pzNorm * CB + 1)
    with hKRdef
  have hKxnn : 0 ≤ Kx := by rw [hKxdef]; exact mul_nonneg hA6nn hM
  have hKRnn : 0 ≤ KR := by
    rw [hKRdef]
    have h1 : 0 ≤ CL * KW / pzNorm * CB :=
      mul_nonneg (div_nonneg (mul_nonneg hCLpos.le hKWpos.le) hpzpos.le) hCBpos.le
    positivity
  refine ⟨CT * KR * (2 * Kx) + CC * CJ * Kx * KR + CT * KW * (2 * Kx) + CC * CJ * Kx * KW
      + CC * CL * (KR + KW) * CB * Kx / pzNorm + 1, ?_, ?_⟩
  · have h1 : 0 ≤ CT * KR * (2 * Kx) := by
      have h2 : (0 : ℝ) ≤ 2 * Kx := by linarith
      positivity
    have h2 : 0 ≤ CC * CJ * Kx * KR := by positivity
    have h3 : 0 ≤ CT * KW * (2 * Kx) := by positivity
    have h4 : 0 ≤ CC * CJ * Kx * KW := by positivity
    have h5 : 0 ≤ CC * CL * (KR + KW) * CB * Kx / pzNorm := by positivity
    linarith
  · intro T τ ε Φs E g₀ g hT hτ hε hsol hreg hEll hstar hml h6M hXn
    have hτIcc : τ ∈ Set.Icc 0 T := ⟨hτ.1.le, hτ.2.le⟩
    have hτle : τ ≤ T := hτ.2.le
    have hDat := hreg.2 τ hτIcc
    have hSmo0 : SmoothOpen (slice g τ) := hDat.1
    have hMem60 : HkMem α 6 (slice g τ) := hDat.2.1
    have hCxP : ClassC α
        (Pz (Jeps ρ ε (slice g τ))) := hDat.2.2
    have hXnx : Xn α (slice (JfamP ρ ε g) τ) ≤ C₀ * α ^ 2 :=
      hXn τ ⟨hτ.1.le, le_refl _⟩
    have hX6x : HkNorm α 6 (slice (JfamP ρ ε g) τ) ≤ Kx := by
      rw [hKxdef]
      have h := (hJfamP (g := g) (s := τ) hαI ⟨hε.1, hε.2⟩ (fun n => hSmo0.forall n) hMem60).2
      exact le_trans h (mul_le_mul_of_nonneg_left (h6M τ hτIcc) hA6nn)
    have hC_τ : ∀ s ∈ Set.Icc 0 τ, ClassC α
        (slice (JfamP ρ ε g) s) :=
      fun s hs => (hreg.2 s ⟨hs.1, le_trans hs.2 hτle⟩).2.2
    have hb6_τ : ∀ s ∈ Set.Icc 0 τ, Work.FTS.StrongGlobal.Xn6 α
        (slice (JfamP ρ ε g) s) ≤ A6 * M := by
      intro s hs
      have hsT : s ∈ Set.Icc 0 T := ⟨hs.1, le_trans hs.2 hτle⟩
      have hDats := hreg.2 s hsT
      have h := (hJfamP (g := g) (s := s) hαI ⟨hε.1, hε.2⟩
        (fun n => hDats.1.forall n) hDats.2.1).2
      exact le_trans h (mul_le_mul_of_nonneg_left (h6M s hsT) hA6nn)
    obtain ⟨hSmoW, hMemW4, hXnW⟩ := hKW τ Φs E g ε hEll hstar hml hC_τ hXn hb6_τ τ
      ⟨hτ.1.le, le_refl _⟩
    -- the goal's second `IP4`-argument is definitionally `epsWP`
    have hWrfl : (Work.FTS.Galerkin.dynLin α (JfamP ρ ε g) τ
        + Work.FTS.Galerkin.dynRHS α (PsiCan Φs E
            (JfamP ρ ε g)) (JfamP ρ ε g) τ)
        = epsWP α ρ ε Φs E g τ := rfl
    rw [hWrfl]
    set x : Fn := slice (JfamP ρ ε g) τ with hxdef
    set W : Fn := epsWP α ρ ε Φs E g τ with hWdef
    set R : Fn := epsRHSP α ρ ε Φs E g τ with hRdef
    set A : Fn := Pz (Jeps ρ ε R) with hAdef
    set cR : ℝ := L12 (Jeps ρ ε R) 0
      / pzNorm with hcRdef
    set cW : ℝ := L12 (Jeps ρ ε W) 0
      / pzNorm with hcWdef
    have hSmoX : SmoothOpen x := by rw [hxdef]; exact hCxP.reg
    have hMem7x : HkMem α 7 x := by rw [hxdef]; exact hCxP.mem
    have hMem6x : HkMem α 6 x :=
      HkMem_mono_open hSmoX 6 (by norm_num) hMem7x
    have hMem5x : HkMem α 5 x :=
      HkMem_mono_open hSmoX 5 (by norm_num) hMem7x
    have hMem4x : HkMem α 4 x :=
      HkMem_mono_open hSmoX 4 (by norm_num) hMem7x
    have hX5x : HkNorm α 5 x ≤ Kx :=
      le_trans (Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 6) (k' := 5) (by norm_num)
        hMem6x) hX6x
    have hX4x : HkNorm α 4 x ≤ Kx :=
      le_trans (Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 5) (k' := 4) (by norm_num)
        hMem5x) hX5x
    have hQx : HQo α 4 x := ⟨hSmoX, hMem4x⟩
    have hXnx' : Xn α x ≤ C₀ * α ^ 2 := by rw [hxdef]; exact hXnx
    have hSmoB : SmoothOpen bump :=
      Work.FTS.EllipticEst.smoothOpen_of_smoothQuad
        PZeroAux.classC_Pz_smoothQuad_bump
    have hMemB4 : HkMem α 4 bump :=
      PZeroAux.classC_Pz_hkMem_bump α 4
    have hXnB : HkNorm α 4 bump ≤ CB :=
      hBump α hαI 4 (by norm_num)
    have hSmoJx : SmoothOpen (Jeps ρ ε x) :=
      smoothOpen_Jeps ρ hρ hε.1
        ((smoothOpen_iff_forall x).mp hSmoX)
    have hMemJx4 : HkMem α 4 (Jeps ρ ε x) :=
      HkMem_Jeps hρ.moll hαI hε.1
        ((smoothOpen_iff_forall x).mp hSmoX) hMem4x
    have hSmoJxSub : SmoothOpen
        (Jeps ρ ε x - x) :=
      Work.FTS.EllipticEst.smoothOpen_sub hSmoJx hSmoX
    have hMemJxSub4 : HkMem α 4 (Jeps ρ ε x - x) := by
      refine HkMem_add_open hSmoJx
        (smoothOpen_neg_epsWP hSmoX) hMemJx4 ?_
      exact hkMem_neg_epsWP hMem4x
    have hQJxSub : HQo α 4 (Jeps ρ ε x - x) :=
      ⟨hSmoJxSub, hMemJxSub4⟩
    have hJxN : HkNorm α 4 (Jeps ρ ε x - x) ≤ CJ * ε * Kx := by
      have h := hJsub α hαI 4 ε ⟨hε.1, hε.2⟩ x
        ((smoothOpen_iff_forall x).mp hSmoX) hMem5x hMemJx4
      refine h.trans ?_
      exact mul_le_mul_of_nonneg_left hX5x (mul_nonneg hCJpos.le hε.1.le)
    have hSmoJW : SmoothOpen (Jeps ρ ε W) :=
      smoothOpen_Jeps ρ hρ hε.1
        ((smoothOpen_iff_forall W).mp hSmoW)
    have hMemJW4 : HkMem α 4 (Jeps ρ ε W) :=
      HkMem_Jeps hρ.moll hαI hε.1
        ((smoothOpen_iff_forall W).mp hSmoW) hMemW4
    have hQW : HQo α 4 W := ⟨hSmoW, hMemW4⟩
    have hL12W : L12 W 0 = 0 := by
      rw [hWdef]
      exact EpsZeroMode hαI hρ hε.1 hCxP hXnx hEll hstar hml
    have hRval : R = Pz (Jeps ρ ε W) := hRdef
    have hSmoR : SmoothOpen R := by
      have hfun : R = fun z θ => Jeps ρ ε W z θ
          - (L12 (Jeps ρ ε W) 0
              / pzNorm) * bump z θ := by
        rw [hRval]
        funext z θ
        rw [Pz_apply]
      rw [hfun]
      exact Work.FTS.EllipticEst.smoothOpen_sub hSmoJW
        (smoothOpen_const_mul _ hSmoB)
    have hMemR4 : HkMem α 4 R := by
      rw [hRval]
      exact PZeroAux.PzJepsHkMem 4 hρ hαI hε.1
        ((smoothOpen_iff_forall W).mp hSmoW) hMemW4
    have hQR : HQo α 4 R := ⟨hSmoR, hMemR4⟩
    have hL12R : L12 R 0 = 0 := by
      rw [hRval]
      have hfun : Pz (Jeps ρ ε W)
          = fun z θ => Jeps ρ ε W z θ
              + (-(L12 (Jeps ρ ε W) 0
                  / pzNorm)) * bump z θ := by
        funext z θ
        rw [Pz_apply]
        ring
      rw [hfun, PZeroAux.L12_add_mul_ae]
      · rw [show L12 bump 0
            = pzNorm from rfl]
        field_simp
        ring
      · exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
          (Filter.Eventually.of_forall (fun s hs =>
            integrableOn_slice_of_SmoothOpen_HkMem hSmoJW hMemJW4 hs))
      · exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
          (Filter.Eventually.of_forall (fun s hs =>
            PZeroAux.integrableOn_slice_bump hs))
      · exact integrableOn_L12dens_of_SmoothOpen_HkMem hSmoJW hMemJW4
      · exact PZeroAux.integrableOn_L12dens_bump
    have hJepsWnorm : HkNorm α 4 (Jeps ρ ε W)
        ≤ Real.exp (CG / 2) * KW := by
      have hsq := hJle α hαI 4 ε hε.1 hε.2 W
        ((smoothOpen_iff_forall W).mp hSmoW) hMemW4 hMemJW4
      rw [show HkNorm α 4 (Jeps ρ ε W)
          = Real.sqrt (HkSq α 4 (Jeps ρ ε W)) from rfl]
      calc Real.sqrt (HkSq α 4 (Jeps ρ ε W))
          ≤ Real.sqrt (Real.exp (CG * ε) * HkSq α 4 W) := Real.sqrt_le_sqrt hsq
        _ = Real.sqrt (Real.exp (CG * ε)) * Real.sqrt (HkSq α 4 W) :=
            Real.sqrt_mul (Real.exp_pos _).le _
        _ = Real.exp (CG * ε / 2) * HkNorm α 4 W := by
            rw [← Real.exp_half,
              show HkNorm α 4 W = Real.sqrt (HkSq α 4 W) from rfl]
        _ ≤ Real.exp (CG / 2) * KW := by
            refine mul_le_mul ?_ hXnW (HkNorm_nonneg α 4 W) (Real.exp_pos _).le
            exact Real.exp_le_exp.mpr (by nlinarith [hε.2, hCGpos.le])
    have hcWbd : |cW| ≤ CL * ε * KW / pzNorm := by
      rw [hcWdef, abs_div, abs_of_pos hpzpos]
      refine div_le_div_of_nonneg_right ?_ hpzpos.le
      have h1 : |L12 (Jeps ρ ε W) 0|
          ≤ CL * ε * HkNorm α 4 W := by
        have h := hL12sub α hαI W hSmoW hMemW4 ε ⟨hε.1, hε.2⟩
        rwa [hL12W, sub_zero] at h
      refine h1.trans ?_
      exact mul_le_mul_of_nonneg_left hXnW (mul_nonneg hCLpos.le hε.1.le)
    have hRn : HkNorm α 4 R ≤ KR := by
      have hfun : R = fun z θ => Jeps ρ ε W z θ
          + (-(L12 (Jeps ρ ε W) 0
              / pzNorm)) * bump z θ := by
        rw [hRval]
        funext z θ
        rw [Pz_apply]
        ring
      rw [hfun, hKRdef]
      have hcbsmo : SmoothOpen
          (fun z θ => (-(L12 (Jeps ρ ε W) 0
              / pzNorm)) * bump z θ) :=
        smoothOpen_const_mul _ hSmoB
      have hmemb : HkMem α 4
          (fun z θ => (-(L12 (Jeps ρ ε W) 0
              / pzNorm)) * bump z θ) :=
        PZeroAux.HkMem_const_mul_gen _ hMemB4
      have hsum := HkNorm_add_le_open α 4 hα0 hSmoJW hcbsmo
        hMemJW4 hmemb
      have hcb : HkNorm α 4
          (fun z θ => (-(L12 (Jeps ρ ε W) 0
              / pzNorm)) * bump z θ)
          = |L12 (Jeps ρ ε W) 0
              / pzNorm| * HkNorm α 4 bump := by
        rw [HkNorm_const_mul α 4 _ hSmoB.forall, abs_neg]
      rw [hcb] at hsum
      have hcWbd0 : |cW| ≤ CL * KW / pzNorm := by
        refine hcWbd.trans ?_
        have h0 : CL * ε ≤ CL := by
          simpa using mul_le_mul_of_nonneg_left hε.2 hCLpos.le
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h0 hKWpos.le) hpzpos.le
      have h2 : |L12 (Jeps ρ ε W) 0
            / pzNorm| * HkNorm α 4 bump
          ≤ CL * KW / pzNorm * CB :=
        mul_le_mul hcWbd0 hXnB (HkNorm_nonneg α 4 _)
          (div_nonneg (mul_nonneg hCLpos.le hKWpos.le) hpzpos.le)
      have h3 : HkNorm α 4 (Jeps ρ ε W)
          + |L12 (Jeps ρ ε W) 0
              / pzNorm| * HkNorm α 4 bump
          ≤ Real.exp (CG / 2) * KW + CL * KW / pzNorm * CB :=
        add_le_add hJepsWnorm h2
      linarith [hsum, h3]
    have hSmoJR : SmoothOpen (Jeps ρ ε R) :=
      smoothOpen_Jeps ρ hρ hε.1
        ((smoothOpen_iff_forall R).mp hSmoR)
    have hMemJR4 : HkMem α 4 (Jeps ρ ε R) :=
      HkMem_Jeps hρ.moll hαI hε.1
        ((smoothOpen_iff_forall R).mp hSmoR) hMemR4
    have hSmoA : SmoothOpen A := by
      have hfun : A = fun z θ => Jeps ρ ε R z θ
          - (L12 (Jeps ρ ε R) 0
              / pzNorm) * bump z θ := by
        rw [hAdef]
        funext z θ
        rw [Pz_apply]
      rw [hfun]
      exact Work.FTS.EllipticEst.smoothOpen_sub hSmoJR
        (smoothOpen_const_mul _ hSmoB)
    have hMemA4 : HkMem α 4 A := by
      rw [hAdef]
      exact PZeroAux.PzJepsHkMem 4 hρ hαI hε.1
        ((smoothOpen_iff_forall R).mp hSmoR) hMemR4
    have hQA : HQo α 4 A := ⟨hSmoA, hMemA4⟩
    have hSmoAW : SmoothOpen (A - W) :=
      Work.FTS.EllipticEst.smoothOpen_sub hSmoA hSmoW
    have hMemAW4 : HkMem α 4 (A - W) := by
      refine HkMem_add_open hSmoA
        (smoothOpen_neg_epsWP hSmoW) hMemA4 ?_
      exact hkMem_neg_epsWP hMemW4
    have hcRbd : |cR| ≤ CL * ε * KR / pzNorm := by
      rw [hcRdef, abs_div, abs_of_pos hpzpos]
      refine div_le_div_of_nonneg_right ?_ hpzpos.le
      have h1 : |L12 (Jeps ρ ε R) 0|
          ≤ CL * ε * HkNorm α 4 R := by
        have h := hL12sub α hαI R hSmoR hMemR4 ε ⟨hε.1, hε.2⟩
        rwa [hL12R, sub_zero] at h
      refine h1.trans ?_
      exact mul_le_mul_of_nonneg_left hRn (mul_nonneg hCLpos.le hε.1.le)
    have hAW : ∀ z θ, A z θ - W z θ
        = (Jeps ρ ε R z θ - R z θ)
          + (Jeps ρ ε W z θ - W z θ)
          - (cR + cW) * bump z θ := by
      intro z θ
      have hA'' : A z θ = Jeps ρ ε R z θ
          - L12 (Jeps ρ ε R) 0
              / pzNorm * bump z θ := by
        rw [hAdef]
        exact Pz_apply (Jeps ρ ε R) z θ
      have hR'' : R z θ = Jeps ρ ε W z θ
          - L12 (Jeps ρ ε W) 0
              / pzNorm * bump z θ := by
        rw [hRval]
        exact Pz_apply (Jeps ρ ε W) z θ
      rw [hA'', hR'', hcRdef, hcWdef]
      ring
    have hSmoP : SmoothOpen
        (Jeps ρ ε R - R) :=
      Work.FTS.EllipticEst.smoothOpen_sub hSmoJR hSmoR
    have hMemP4 : HkMem α 4 (Jeps ρ ε R - R) := by
      refine HkMem_add_open hSmoJR
        (smoothOpen_neg_epsWP hSmoR) hMemJR4 ?_
      exact hkMem_neg_epsWP hMemR4
    have hSmoQ : SmoothOpen
        (Jeps ρ ε W - W) :=
      Work.FTS.EllipticEst.smoothOpen_sub hSmoJW hSmoW
    have hMemQ4 : HkMem α 4 (Jeps ρ ε W - W) := by
      refine HkMem_add_open hSmoJW
        (smoothOpen_neg_epsWP hSmoW) hMemJW4 ?_
      exact hkMem_neg_epsWP hMemW4
    have hSmoE : SmoothOpen
        (fun z θ => -((cR + cW) * bump z θ)) :=
      smoothOpen_neg_epsWP
        (smoothOpen_const_mul _ hSmoB)
    have hMemE4 : HkMem α 4
        (fun z θ => -((cR + cW) * bump z θ)) :=
      hkMem_neg_epsWP
        (PZeroAux.HkMem_const_mul_gen _ hMemB4)
    have hSmoQE : SmoothOpen
        ((Jeps ρ ε W - W)
          + (fun z θ => -((cR + cW) * bump z θ))) :=
      Work.FTS.EllipticEst.smoothOpen_add hSmoQ hSmoE
    have hMemQE4 : HkMem α 4
        ((Jeps ρ ε W - W)
          + (fun z θ => -((cR + cW) * bump z θ))) :=
      HkMem_add_open hSmoQ hSmoE hMemQ4 hMemE4
    have htrR : |IP4 c₁ c₂ c₃ c₄ c₅ c₆ α (Jeps ρ ε R) x
        - IP4 c₁ c₂ c₃ c₄ c₅ c₆ α R (Jeps ρ ε x)|
        ≤ CT * ε * KR * (2 * Kx) := by
      have h := hTR α hαI ε hε R x hSmoR hSmoX hMemR4 hMem5x
      refine h.trans ?_
      have hsum : HkNorm α 4 x + HkNorm α 5 x ≤ 2 * Kx := by linarith
      have hCTe : (0 : ℝ) ≤ CT * ε := mul_nonneg hCTnn hε.1.le
      exact mul_le_mul (mul_le_mul_of_nonneg_left hRn hCTe) hsum
        (add_nonneg (HkNorm_nonneg α 4 x) (HkNorm_nonneg α 5 x))
        (mul_nonneg hCTe hKRnn)
    have htrW : |IP4 c₁ c₂ c₃ c₄ c₅ c₆ α (Jeps ρ ε W) x
        - IP4 c₁ c₂ c₃ c₄ c₅ c₆ α W (Jeps ρ ε x)|
        ≤ CT * ε * KW * (2 * Kx) := by
      have h := hTR α hαI ε hε W x hSmoW hSmoX hMemW4 hMem5x
      refine h.trans ?_
      have hsum : HkNorm α 4 x + HkNorm α 5 x ≤ 2 * Kx := by linarith
      have hCTe : (0 : ℝ) ≤ CT * ε := mul_nonneg hCTnn hε.1.le
      exact mul_le_mul (mul_le_mul_of_nonneg_left hXnW hCTe) hsum
        (add_nonneg (HkNorm_nonneg α 4 x) (HkNorm_nonneg α 5 x))
        (mul_nonneg hCTe hKWpos.le)
    have hs2R : |IP4 c₁ c₂ c₃ c₄ c₅ c₆ α R (Jeps ρ ε x)
        - IP4 c₁ c₂ c₃ c₄ c₅ c₆ α R x| ≤ CC * CJ * Kx * KR * ε := by
      have hsym1 : IP4 c₁ c₂ c₃ c₄ c₅ c₆ α R (Jeps ρ ε x)
          = IP4 c₁ c₂ c₃ c₄ c₅ c₆ α (Jeps ρ ε x) R :=
        IP4_symm_local c₁ c₂ c₃ c₄ c₅ c₆ α R (Jeps ρ ε x)
      have hsym2 : IP4 c₁ c₂ c₃ c₄ c₅ c₆ α x R
          = IP4 c₁ c₂ c₃ c₄ c₅ c₆ α R x :=
        IP4_symm_local c₁ c₂ c₃ c₄ c₅ c₆ α x R
      have hsub : IP4 c₁ c₂ c₃ c₄ c₅ c₆ α (Jeps ρ ε x) R
          - IP4 c₁ c₂ c₃ c₄ c₅ c₆ α x R
          = IP4 c₁ c₂ c₃ c₄ c₅ c₆ α (Jeps ρ ε x - x) R :=
        (IP4_sub_local c₁ c₂ c₃ c₄ c₅ c₆ α hα0 hSmoJx hSmoX hSmoR hMemJx4 hMem4x hMemR4).symm
      rw [hsym1, ← hsym2, hsub]
      have hcs := hCS α hαI (Jeps ρ ε x - x) R hQJxSub hQR
      refine hcs.trans ?_
      have h1 : CC * HkNorm α 4 (Jeps ρ ε x - x)
            * HkNorm α 4 R ≤ CC * (CJ * ε * Kx) * KR :=
        mul_le_mul (mul_le_mul_of_nonneg_left hJxN hCCnn) hRn
          (HkNorm_nonneg α 4 R)
          (mul_nonneg hCCnn (mul_nonneg (mul_nonneg hCJpos.le hε.1.le) hKxnn))
      refine h1.trans (le_of_eq ?_)
      ring
    have hs2W : |IP4 c₁ c₂ c₃ c₄ c₅ c₆ α W (Jeps ρ ε x)
        - IP4 c₁ c₂ c₃ c₄ c₅ c₆ α W x| ≤ CC * CJ * Kx * KW * ε := by
      have hsym1 : IP4 c₁ c₂ c₃ c₄ c₅ c₆ α W (Jeps ρ ε x)
          = IP4 c₁ c₂ c₃ c₄ c₅ c₆ α (Jeps ρ ε x) W :=
        IP4_symm_local c₁ c₂ c₃ c₄ c₅ c₆ α W (Jeps ρ ε x)
      have hsym2 : IP4 c₁ c₂ c₃ c₄ c₅ c₆ α x W
          = IP4 c₁ c₂ c₃ c₄ c₅ c₆ α W x :=
        IP4_symm_local c₁ c₂ c₃ c₄ c₅ c₆ α x W
      have hsub : IP4 c₁ c₂ c₃ c₄ c₅ c₆ α (Jeps ρ ε x) W
          - IP4 c₁ c₂ c₃ c₄ c₅ c₆ α x W
          = IP4 c₁ c₂ c₃ c₄ c₅ c₆ α (Jeps ρ ε x - x) W :=
        (IP4_sub_local c₁ c₂ c₃ c₄ c₅ c₆ α hα0 hSmoJx hSmoX hSmoW hMemJx4 hMem4x hMemW4).symm
      rw [hsym1, ← hsym2, hsub]
      have hcs := hCS α hαI (Jeps ρ ε x - x) W hQJxSub hQW
      refine hcs.trans ?_
      have h1 : CC * HkNorm α 4 (Jeps ρ ε x - x)
            * HkNorm α 4 W ≤ CC * (CJ * ε * Kx) * KW :=
        mul_le_mul (mul_le_mul_of_nonneg_left hJxN hCCnn) hXnW
          (HkNorm_nonneg α 4 W)
          (mul_nonneg hCCnn (mul_nonneg (mul_nonneg hCJpos.le hε.1.le) hKxnn))
      refine h1.trans (le_of_eq ?_)
      ring
    have hEbd : |IP4 c₁ c₂ c₃ c₄ c₅ c₆ α
          (fun z θ => -((cR + cW) * bump z θ)) x|
        ≤ CC * CL * (KR + KW) * CB * Kx / pzNorm * ε := by
      have hcs := hCS α hαI (fun z θ => -((cR + cW) * bump z θ)) x
        ⟨hSmoE, hMemE4⟩ hQx
      refine hcs.trans ?_
      have hnorm : HkNorm α 4
            (fun z θ => -((cR + cW) * bump z θ))
          = |cR + cW| * HkNorm α 4 bump := by
        have hfe : (fun z θ => -((cR + cW) * bump z θ))
            = -(fun z θ => (cR + cW) * bump z θ) := by
          funext z θ
          simp only [Pi.neg_apply]
        rw [hfe, HkNorm_neg,
          HkNorm_const_mul α 4 (cR + cW) hSmoB.forall]
      rw [hnorm]
      have hcRW : |cR + cW| ≤ CL * ε * KR / pzNorm
          + CL * ε * KW / pzNorm := by
        refine (abs_add_le _ _).trans ?_
        linarith [hcRbd, hcWbd]
      have h1 : |cR + cW| * HkNorm α 4 bump
          ≤ (CL * ε * KR / pzNorm
              + CL * ε * KW / pzNorm) * CB :=
        mul_le_mul hcRW hXnB (HkNorm_nonneg α 4 _)
          (add_nonneg (div_nonneg (mul_nonneg (mul_nonneg hCLpos.le hε.1.le) hKRnn) hpzpos.le)
            (div_nonneg (mul_nonneg (mul_nonneg hCLpos.le hε.1.le) hKWpos.le) hpzpos.le))
      have h2 : CC * (|cR + cW| * HkNorm α 4 bump)
            * HkNorm α 4 x
          ≤ CC * ((CL * ε * KR / pzNorm
              + CL * ε * KW / pzNorm) * CB) * Kx :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 hCCnn) hX4x
          (HkNorm_nonneg α 4 x)
          (mul_nonneg hCCnn (mul_nonneg
            (add_nonneg (div_nonneg (mul_nonneg (mul_nonneg hCLpos.le hε.1.le) hKRnn) hpzpos.le)
              (div_nonneg (mul_nonneg (mul_nonneg hCLpos.le hε.1.le) hKWpos.le) hpzpos.le))
            hCBpos.le))
      refine h2.trans (le_of_eq ?_)
      field_simp
    have hdefect : |IP4 c₁ c₂ c₃ c₄ c₅ c₆ α A x
        - IP4 c₁ c₂ c₃ c₄ c₅ c₆ α W x|
        ≤ (CT * KR * (2 * Kx) + CC * CJ * Kx * KR + CT * KW * (2 * Kx) + CC * CJ * Kx * KW
            + CC * CL * (KR + KW) * CB * Kx / pzNorm) * ε := by
      have hsum1 : A - W + W = A := by
        funext z θ
        simp only [Pi.add_apply, Pi.sub_apply]
        ring
      have hadd := IP4_add_local c₁ c₂ c₃ c₄ c₅ c₆ α hα0 hSmoAW hSmoW hSmoX
        hMemAW4 hMemW4 hMem4x
      rw [hsum1] at hadd
      have h1 : IP4 c₁ c₂ c₃ c₄ c₅ c₆ α A x
          - IP4 c₁ c₂ c₃ c₄ c₅ c₆ α W x
          = IP4 c₁ c₂ c₃ c₄ c₅ c₆ α (A - W) x := by linarith [hadd]
      rw [h1]
      have h2 : IP4 c₁ c₂ c₃ c₄ c₅ c₆ α (A - W) x
          = IP4 c₁ c₂ c₃ c₄ c₅ c₆ α
              ((Jeps ρ ε R - R)
                + ((Jeps ρ ε W - W)
                  + (fun z θ => -((cR + cW) * bump z θ)))) x := by
        refine IP4_congr_local c₁ c₂ c₃ c₄ c₅ c₆ α hα0 ?_
        intro z θ _
        have hh := hAW z θ
        simp only [Pi.add_apply, Pi.sub_apply] at hh ⊢
        linarith [hh]
      rw [h2]
      have hA1 := IP4_add_local c₁ c₂ c₃ c₄ c₅ c₆ α hα0 hSmoP hSmoQE hSmoX
        hMemP4 hMemQE4 hMem4x
      have hA2 := IP4_add_local c₁ c₂ c₃ c₄ c₅ c₆ α hα0 hSmoQ hSmoE hSmoX
        hMemQ4 hMemE4 hMem4x
      rw [hA1, hA2,
        IP4_sub_local c₁ c₂ c₃ c₄ c₅ c₆ α hα0 hSmoJR hSmoR hSmoX hMemJR4 hMemR4 hMem4x,
        IP4_sub_local c₁ c₂ c₃ c₄ c₅ c₆ α hα0 hSmoJW hSmoW hSmoX hMemJW4 hMemW4 hMem4x]
      have hassoc : (IP4 c₁ c₂ c₃ c₄ c₅ c₆ α (Jeps ρ ε R) x
              - IP4 c₁ c₂ c₃ c₄ c₅ c₆ α R x)
            + ((IP4 c₁ c₂ c₃ c₄ c₅ c₆ α (Jeps ρ ε W) x
              - IP4 c₁ c₂ c₃ c₄ c₅ c₆ α W x)
            + IP4 c₁ c₂ c₃ c₄ c₅ c₆ α
                (fun z θ => -((cR + cW) * bump z θ)) x)
          = ((IP4 c₁ c₂ c₃ c₄ c₅ c₆ α (Jeps ρ ε R) x
              - IP4 c₁ c₂ c₃ c₄ c₅ c₆ α R x)
            + (IP4 c₁ c₂ c₃ c₄ c₅ c₆ α (Jeps ρ ε W) x
              - IP4 c₁ c₂ c₃ c₄ c₅ c₆ α W x))
            + IP4 c₁ c₂ c₃ c₄ c₅ c₆ α
                (fun z θ => -((cR + cW) * bump z θ)) x := by ring
      rw [hassoc]
      have ht1 : |(IP4 c₁ c₂ c₃ c₄ c₅ c₆ α (Jeps ρ ε R) x
              - IP4 c₁ c₂ c₃ c₄ c₅ c₆ α R x)
            + (IP4 c₁ c₂ c₃ c₄ c₅ c₆ α (Jeps ρ ε W) x
              - IP4 c₁ c₂ c₃ c₄ c₅ c₆ α W x)
            + IP4 c₁ c₂ c₃ c₄ c₅ c₆ α
                (fun z θ => -((cR + cW) * bump z θ)) x|
          ≤ |IP4 c₁ c₂ c₃ c₄ c₅ c₆ α (Jeps ρ ε R) x
              - IP4 c₁ c₂ c₃ c₄ c₅ c₆ α R x|
            + |IP4 c₁ c₂ c₃ c₄ c₅ c₆ α (Jeps ρ ε W) x
              - IP4 c₁ c₂ c₃ c₄ c₅ c₆ α W x|
            + |IP4 c₁ c₂ c₃ c₄ c₅ c₆ α
                (fun z θ => -((cR + cW) * bump z θ)) x| := by
        have hA := abs_add_le (IP4 c₁ c₂ c₃ c₄ c₅ c₆ α (Jeps ρ ε R) x
              - IP4 c₁ c₂ c₃ c₄ c₅ c₆ α R x
              + (IP4 c₁ c₂ c₃ c₄ c₅ c₆ α (Jeps ρ ε W) x
                - IP4 c₁ c₂ c₃ c₄ c₅ c₆ α W x))
          (IP4 c₁ c₂ c₃ c₄ c₅ c₆ α
            (fun z θ => -((cR + cW) * bump z θ)) x)
        have hB := abs_add_le (IP4 c₁ c₂ c₃ c₄ c₅ c₆ α (Jeps ρ ε R) x
              - IP4 c₁ c₂ c₃ c₄ c₅ c₆ α R x)
          (IP4 c₁ c₂ c₃ c₄ c₅ c₆ α (Jeps ρ ε W) x
            - IP4 c₁ c₂ c₃ c₄ c₅ c₆ α W x)
        linarith
      refine ht1.trans ?_
      have hPbd : |IP4 c₁ c₂ c₃ c₄ c₅ c₆ α (Jeps ρ ε R) x
            - IP4 c₁ c₂ c₃ c₄ c₅ c₆ α R x|
          ≤ (CT * KR * (2 * Kx) + CC * CJ * Kx * KR) * ε := by
        have hsplit : IP4 c₁ c₂ c₃ c₄ c₅ c₆ α (Jeps ρ ε R) x
              - IP4 c₁ c₂ c₃ c₄ c₅ c₆ α R x
            = (IP4 c₁ c₂ c₃ c₄ c₅ c₆ α (Jeps ρ ε R) x
                - IP4 c₁ c₂ c₃ c₄ c₅ c₆ α R (Jeps ρ ε x))
              + (IP4 c₁ c₂ c₃ c₄ c₅ c₆ α R (Jeps ρ ε x)
                - IP4 c₁ c₂ c₃ c₄ c₅ c₆ α R x) := by ring
        rw [hsplit]
        refine (abs_add_le _ _).trans ?_
        have e : CT * ε * KR * (2 * Kx) + CC * CJ * Kx * KR * ε
            = (CT * KR * (2 * Kx) + CC * CJ * Kx * KR) * ε := by ring
        linarith [htrR, hs2R]
      have hQbd : |IP4 c₁ c₂ c₃ c₄ c₅ c₆ α (Jeps ρ ε W) x
            - IP4 c₁ c₂ c₃ c₄ c₅ c₆ α W x|
          ≤ (CT * KW * (2 * Kx) + CC * CJ * Kx * KW) * ε := by
        have hsplit : IP4 c₁ c₂ c₃ c₄ c₅ c₆ α (Jeps ρ ε W) x
              - IP4 c₁ c₂ c₃ c₄ c₅ c₆ α W x
            = (IP4 c₁ c₂ c₃ c₄ c₅ c₆ α (Jeps ρ ε W) x
                - IP4 c₁ c₂ c₃ c₄ c₅ c₆ α W (Jeps ρ ε x))
              + (IP4 c₁ c₂ c₃ c₄ c₅ c₆ α W (Jeps ρ ε x)
                - IP4 c₁ c₂ c₃ c₄ c₅ c₆ α W x) := by ring
        rw [hsplit]
        refine (abs_add_le _ _).trans ?_
        have e : CT * ε * KW * (2 * Kx) + CC * CJ * Kx * KW * ε
            = (CT * KW * (2 * Kx) + CC * CJ * Kx * KW) * ε := by ring
        linarith [htrW, hs2W]
      have e : (CT * KR * (2 * Kx) + CC * CJ * Kx * KR) * ε
            + (CT * KW * (2 * Kx) + CC * CJ * Kx * KW) * ε
            + CC * CL * (KR + KW) * CB * Kx / pzNorm * ε
          = (CT * KR * (2 * Kx) + CC * CJ * Kx * KR + CT * KW * (2 * Kx) + CC * CJ * Kx * KW
              + CC * CL * (KR + KW) * CB * Kx / pzNorm) * ε := by ring
      linarith [hPbd, hQbd, hEbd]
    refine hdefect.trans ?_
    nlinarith [hε.1.le]

end E4R3.Apriori4Proofs.TransferDeriv
