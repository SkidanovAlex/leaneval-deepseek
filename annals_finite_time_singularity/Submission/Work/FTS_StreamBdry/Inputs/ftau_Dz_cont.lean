import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.GalFields.RHS.SharpAux.HonTerms.Base
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EpsLimitDefs
import Submission.Work.FTS.StrongEps.EpsMem
import Submission.Work.FTS.StrongEps.LocUnif.D5.rounds
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.StrongEps.epsWP_abs_le_on_compact
import Submission.Work.FTS.StrongPersist.SP6.WlInf6OfFlatW
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.PkgJets.cosWeightTail_le
import Submission.Work.FTS_EllLimOK.PkgJets.pinHardy
import Submission.Work.FTS_EllLimOK.PkgRepair
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.th2EgBasic
import Submission.Work.FTS_EllLimOK.ThetaJets.ClassC_le
import Submission.Work.FTS_MuLamOK.Defs
import Submission.Work.FTS_MuLipC.RowN.FaSlice
import Submission.Work.FTS_RegExport.C4.Dth_mixed_eq_C4
import Submission.Work.FTS_RegExport.RXB.l12_zero_lim_proved
import Submission.Work.FTS_RegExport.RXR1.HJ.AKBounds
import Submission.Work.FTS_RegExport.RXR5.Fstar_C1Jet
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.Sys.slice_contDiffOn_four
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_majorant
import Submission.Work.FTS_StreamBdry.SB4.l12_zero_plainE
import Submission.Work.FTS_StreamBdry.SB4.lim_mixed_plainE
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.R1G.vecResid_eq_scalar_smul
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux2.N0_N_Transport_dens_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux2

theorem N0_N_Transport_dens_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 →
      ∀ {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
        {ε τ C₀ B : ℝ} {g : Work.FTS.Galerkin.Fam} {Maj : ℝ → ℝ},
      Work.FTS.StrongEps.EpsDecay α ρ Φs E ε τ g Maj →
      Work.FTS.ClassC.ClassC α (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) →
      Work.FTS.Nonlin.Xn α (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)
        ≤ C₀ * α ^ 2 →
      Work.FTS.StrongGlobal.Xn6 α (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)
        ≤ B →
      ∀ s ∈ Set.Ioi (0 : ℝ),
        ‖Work.FM.L12dens Work.Spaces.K (fun z θ => Work.Construction.N0 α
            (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) τ)
            (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) z θ) s‖
          ≤ C * (1 + C₀) * (1 + B) * (Maj s / s + 1 / (1 + s) ^ 2) ∧
        ‖Work.FM.L12dens Work.Spaces.K (fun z θ => Work.Construction.N α
            (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) τ)
            (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g)) τ)
            z θ) s‖
          ≤ C * (1 + C₀) * (1 + B) * (Maj s / s + 1 / (1 + s) ^ 2) ∧
        ‖Work.FM.L12dens Work.Spaces.K (Work.Coercivity.Transport
            (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)) s‖
          ≤ C * (1 + C₀) * (1 + B) * (Maj s / s + 1 / (1 + s) ^ 2) := by
  obtain ⟨C0, hC0pos, hC0⟩ := DensN0Pointwise
  obtain ⟨C1, hC1pos, hC1⟩ := DensNPointwise
  obtain ⟨C2, hC2pos, hC2⟩ := DensTransportBound
  refine ⟨C0 + C1 + C2, by linarith, ?_⟩
  intro α hαIoc ρ Φs E ε τ C₀ B g Maj hDec hClass hXn hXn6 s hs
  have hα0 : 0 < α := hαIoc.1
  have hC₀0 : 0 ≤ C₀ := by
    have hX : 0 ≤ Work.FTS.Nonlin.Xn α
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) :=
      Work.Spaces.HkNorm_nonneg α 4 _
    nlinarith only [hX, hXn, pow_pos hα0 2]
  have hB0 : 0 ≤ B := by
    have hX : 0 ≤ Work.FTS.StrongGlobal.Xn6 α
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) :=
      Work.Spaces.HkNorm_nonneg α 6 _
    linarith only [hX, hXn6]
  have hs0 : (0 : ℝ) < s := hs
  have h1C : 0 ≤ 1 + C₀ := by linarith
  have h1B : 0 ≤ 1 + B := by linarith
  have hX0 : 0 ≤ Maj s / s + 1 / (1 + s) ^ 2 := by
    have h1 : 0 ≤ Maj s / s := div_nonneg (hDec.1 s) hs0.le
    have h2 : 0 ≤ 1 / (1 + s) ^ 2 := by positivity
    linarith only [h1, h2]
  have hpos : 0 ≤ (1 + C₀) * (1 + B) * (Maj s / s + 1 / (1 + s) ^ 2) :=
    mul_nonneg (mul_nonneg h1C h1B) hX0
  have hQ0 : 0 ≤ Maj s + s / (1 + s) ^ 2 := by
    have h1 : 0 ≤ s / (1 + s) ^ 2 := div_nonneg hs0.le (sq_nonneg _)
    linarith only [hDec.1 s, h1]
  have hQs : (Maj s + s / (1 + s) ^ 2) / s = Maj s / s + 1 / (1 + s) ^ 2 := by
    field_simp
  have hcoe0 : C0 * (1 + C₀) * (1 + B) ≤ (C0 + C1 + C2) * (1 + C₀) * (1 + B) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) h1C) h1B
  have hcoe1 : C1 * (1 + C₀) * (1 + B) ≤ (C0 + C1 + C2) * (1 + C₀) * (1 + B) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) h1C) h1B
  have hcoe2 : C2 * (1 + C₀) * (1 + B) ≤ (C0 + C1 + C2) * (1 + C₀) * (1 + B) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) h1C) h1B
  refine ⟨?_, ?_, ?_⟩
  · refine le_trans ?_ (mul_le_mul_of_nonneg_right hcoe0 hX0)
    have h := AbsL12densLe (Y := fun z θ => Work.Construction.N0 α
        (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) τ)
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) z θ) (s := s)
      (A := C0 * (1 + C₀) * (1 + B) * (Maj s + s / (1 + s) ^ 2)) hs
      (mul_nonneg (mul_nonneg (mul_nonneg hC0pos.le h1C) h1B) hQ0)
      (fun θ hθ => hC0 (α := α) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) (τ := τ) (C₀ := C₀) (B := B) (g := g) (Maj := Maj) hαIoc hDec hClass hXn hXn6 s hs θ hθ)
    have h2 : C0 * (1 + C₀) * (1 + B) * (Maj s + s / (1 + s) ^ 2) / s
        = C0 * (1 + C₀) * (1 + B) * (Maj s / s + 1 / (1 + s) ^ 2) := by
      rw [show C0 * (1 + C₀) * (1 + B) * (Maj s + s / (1 + s) ^ 2) / s
          = C0 * (1 + C₀) * (1 + B) * ((Maj s + s / (1 + s) ^ 2) / s) from by ring, hQs]
    simpa only [Real.norm_eq_abs, h2] using h
  · refine le_trans ?_ (mul_le_mul_of_nonneg_right hcoe1 hX0)
    have h := AbsL12densLe (Y := fun z θ => Work.Construction.N α
        (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) τ)
        (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
          (Work.FTS.StrongEps.JfamP ρ ε g)) τ) z θ) (s := s)
      (A := C1 * (1 + C₀) * (1 + B) * (Maj s + s / (1 + s) ^ 2)) hs
      (mul_nonneg (mul_nonneg (mul_nonneg hC1pos.le h1C) h1B) hQ0)
      (fun θ hθ => hC1 (α := α) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) (τ := τ) (C₀ := C₀) (B := B) (g := g) (Maj := Maj) hαIoc hDec hClass hXn hXn6 s hs θ hθ)
    have h2 : C1 * (1 + C₀) * (1 + B) * (Maj s + s / (1 + s) ^ 2) / s
        = C1 * (1 + C₀) * (1 + B) * (Maj s / s + 1 / (1 + s) ^ 2) := by
      rw [show C1 * (1 + C₀) * (1 + B) * (Maj s + s / (1 + s) ^ 2) / s
          = C1 * (1 + C₀) * (1 + B) * ((Maj s + s / (1 + s) ^ 2) / s) from by ring, hQs]
    simpa only [Real.norm_eq_abs, h2] using h
  · refine le_trans ?_ (mul_le_mul_of_nonneg_right hcoe2 hX0)
    have h := AbsL12densLe (Y := Work.Coercivity.Transport
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)) (s := s)
      (A := C2 * (1 + C₀) * (1 + B) * (Maj s + s / (1 + s) ^ 2)) hs
      (mul_nonneg (mul_nonneg (mul_nonneg hC2pos.le h1C) h1B) hQ0)
      (fun θ hθ => hC2 (α := α) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) (τ := τ) (C₀ := C₀) (B := B) (g := g) (Maj := Maj) hαIoc hDec hXn hXn6 s hs θ hθ)
    have h2 : C2 * (1 + C₀) * (1 + B) * (Maj s + s / (1 + s) ^ 2) / s
        = C2 * (1 + C₀) * (1 + B) * (Maj s / s + 1 / (1 + s) ^ 2) := by
      rw [show C2 * (1 + C₀) * (1 + B) * (Maj s + s / (1 + s) ^ 2) / s
          = C2 * (1 + C₀) * (1 + B) * ((Maj s + s / (1 + s) ^ 2) / s) from by ring, hQs]
    simpa only [Real.norm_eq_abs, h2] using h

end Work.FTS.StrongEps.E5Aux2
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux2.PTblocks =====
section

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux2

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **The `N₀`-block.** -/
theorem pt_N0_le {α C₀ B CL : ℝ} (hαι : α ∈ Set.Ioc 0 1) (hC₀ : 0 ≤ C₀) (hB : 0 ≤ B)
    (hCL : 0 < CL) {W F : ℝ → ℝ → ℝ}
    (hWS : Work.FTS.EllipticEst.SmoothOpen W)
    (hFeq : F = fun z θ => Work.Construction.Fstar α z θ + W z θ)
    (hWval : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ : ℝ, |W z θ| ≤ 1)
    (hWDz : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ : ℝ, |Work.Spaces.Dz W z θ| ≤ 1)
    (hWDth : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ : ℝ, |Work.Spaces.Dth W z θ| ≤ 1)
    (hL12W : ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Construction.L12 W z| ≤ CL * (C₀ * α ^ 2)) :
    ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Construction.N0 α F W z θ|
        ≤ (1000 * (CL + 1)) * (1 + C₀) * (1 + B) / Real.sin (2 * θ) := by
  have hα0 : 0 < α := hαι.1
  have hα1 : α ≤ 1 := hαι.2
  intro z hz θ hθ
  have hs2pos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hs2le1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  obtain ⟨hFval, hs2pthF, hDzF⟩ := pt_F_slots hα0 hα1 hWS hFeq hWval hWDz hWDth z hz θ hθ
  obtain ⟨-, hDzFstar, hDthFstar, hL12Fstar, -⟩ := pt_Fstar_pt_data hα0 hα1 hz hθ
  have hFstarsharp : |Work.Construction.L12 (Work.Construction.Fstar α) z| ≤ 2 * α :=
    hL12Fstar
  have hWv : |W z θ| ≤ 1 := hWval z hz θ
  have hWz : |Work.Spaces.Dz W z θ| ≤ 1 := hWDz z hz θ
  have hc2m : |Work.Construction.c2m θ| ≤ 2 := pt_abs_c2m_le_two θ
  have hL12Wz : |Work.Construction.L12 W z| ≤ CL * (C₀ * α ^ 2) := hL12W z hz
  have hL12Wnn : 0 ≤ CL * (C₀ * α ^ 2) :=
    mul_nonneg hCL.le (mul_nonneg hC₀ (sq_nonneg α))
  -- the six summands of `N₀`
  have hkey1 : |Work.Construction.s2 θ * Work.Spaces.pth (Work.Construction.Fstar α) z θ|
      ≤ 100 * α := by
    have h := hDthFstar
    rw [Work.Spaces.Dth, abs_mul] at h
    first
    | (rw [abs_mul]; exact h)
    | (simpa [Work.Construction.s2, abs_mul] using h)
    | (rw [abs_mul]; unfold Work.Construction.s2; exact h)
  have hCC : 0 ≤ CL * C₀ := mul_nonneg hCL.le hC₀
  have hα2 : α ^ 2 ≤ 1 := by nlinarith [hα0, hα1]
  have ht1 : |(3 / (2 * α)) * Work.Construction.s2 θ
      * Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.pth (Work.Construction.Fstar α) z θ| ≤ 300 := by
    have hre : (3 / (2 * α)) * Work.Construction.s2 θ
        * Work.Construction.L12 (Work.Construction.Fstar α) z
        * Work.Spaces.pth (Work.Construction.Fstar α) z θ
        = (3 / (2 * α)) * Work.Construction.L12 (Work.Construction.Fstar α) z
          * (Work.Construction.s2 θ * Work.Spaces.pth (Work.Construction.Fstar α) z θ) := by
      ring
    rw [hre, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 3 / (2 * α))]
    have h1 : 3 / (2 * α) * |Work.Construction.L12 (Work.Construction.Fstar α) z| ≤ 3 := by
      calc 3 / (2 * α) * |Work.Construction.L12 (Work.Construction.Fstar α) z|
          ≤ 3 / (2 * α) * (2 * α) :=
            mul_le_mul_of_nonneg_left hFstarsharp (by positivity)
        _ = 3 := by rw [div_mul_cancel₀ 3 (by positivity : (2 : ℝ) * α ≠ 0)]
    calc 3 / (2 * α) * |Work.Construction.L12 (Work.Construction.Fstar α) z|
          * |Work.Construction.s2 θ * Work.Spaces.pth (Work.Construction.Fstar α) z θ|
        ≤ 3 * (100 * α) := mul_le_mul h1 hkey1 (abs_nonneg _) (by norm_num)
      _ ≤ 300 := by nlinarith [hα0]
  have ht2 : |Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.Dz (Work.Construction.Fstar α) z θ| ≤ 400 := by
    rw [abs_mul, abs_mul]
    have h1 : |Work.Construction.c2m θ| * |Work.Construction.L12 (Work.Construction.Fstar α) z|
        ≤ 2 * (2 * α) := mul_le_mul hc2m hFstarsharp (abs_nonneg _) (by norm_num)
    calc |Work.Construction.c2m θ| * |Work.Construction.L12 (Work.Construction.Fstar α) z|
          * |Work.Spaces.Dz (Work.Construction.Fstar α) z θ|
        ≤ (2 * (2 * α)) * (100 * α) := mul_le_mul h1 hDzFstar (abs_nonneg _) (by positivity)
      _ ≤ 400 := by nlinarith [hα0, hα2]
  have ht3 : |(1 / α) * Work.Construction.L12 W z * W z θ| ≤ CL * C₀ := by
    rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / α)]
    have h1 : 1 / α * |Work.Construction.L12 W z| ≤ CL * C₀ * α := by
      calc 1 / α * |Work.Construction.L12 W z| ≤ 1 / α * (CL * (C₀ * α ^ 2)) :=
            mul_le_mul_of_nonneg_left hL12Wz (by positivity)
        _ = CL * C₀ * α := by field_simp
    calc 1 / α * |Work.Construction.L12 W z| * |W z θ| ≤ (CL * C₀ * α) * 1 :=
          mul_le_mul h1 hWv (abs_nonneg _) (by positivity)
      _ ≤ CL * C₀ := by nlinarith [hCC, hα0, hα1]
  have ht4 : |(3 / (2 * α)) * Work.Construction.s2 θ * Work.Construction.L12 W z
      * Work.Spaces.pth F z θ| ≤ 152 * CL * C₀ := by
    have hre : (3 / (2 * α)) * Work.Construction.s2 θ * Work.Construction.L12 W z
        * Work.Spaces.pth F z θ
        = (3 / (2 * α)) * Work.Construction.L12 W z
          * (Work.Construction.s2 θ * Work.Spaces.pth F z θ) := by ring
    rw [hre, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 3 / (2 * α))]
    have h1 : 3 / (2 * α) * |Work.Construction.L12 W z| ≤ 3 / 2 * CL * C₀ * α := by
      calc 3 / (2 * α) * |Work.Construction.L12 W z| ≤ 3 / (2 * α) * (CL * (C₀ * α ^ 2)) :=
            mul_le_mul_of_nonneg_left hL12Wz (by positivity)
        _ = 3 / 2 * CL * C₀ * α := by field_simp
    calc 3 / (2 * α) * |Work.Construction.L12 W z|
          * |Work.Construction.s2 θ * Work.Spaces.pth F z θ|
        ≤ (3 / 2 * CL * C₀ * α) * 101 :=
          mul_le_mul h1 hs2pthF (abs_nonneg _) (by positivity)
      _ ≤ 152 * CL * C₀ := by nlinarith [hCC, hα0, hα1]
  have ht5 : |Work.Construction.c2m θ * Work.Construction.L12 W z
      * Work.Spaces.Dz F z θ| ≤ 202 * CL * C₀ := by
    rw [abs_mul, abs_mul]
    have h1 : |Work.Construction.c2m θ| * |Work.Construction.L12 W z|
        ≤ 2 * (CL * (C₀ * α ^ 2)) := mul_le_mul hc2m hL12Wz (abs_nonneg _) (by positivity)
    calc |Work.Construction.c2m θ| * |Work.Construction.L12 W z| * |Work.Spaces.Dz F z θ|
        ≤ (2 * (CL * (C₀ * α ^ 2))) * 101 :=
          mul_le_mul h1 hDzF (abs_nonneg _) (by positivity)
      _ ≤ 202 * CL * C₀ := by
          calc (2 * (CL * (C₀ * α ^ 2))) * 101 = 202 * (CL * C₀) * α ^ 2 := by ring
            _ ≤ 202 * (CL * C₀) * 1 := mul_le_mul_of_nonneg_left hα2 (by positivity)
            _ = 202 * CL * C₀ := by ring
  have ht6 : |Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.Dz W z θ| ≤ 4 := by
    rw [abs_mul, abs_mul]
    have h1 : |Work.Construction.c2m θ| * |Work.Construction.L12 (Work.Construction.Fstar α) z|
        ≤ 2 * (2 * α) := mul_le_mul hc2m hFstarsharp (abs_nonneg _) (by norm_num)
    calc |Work.Construction.c2m θ| * |Work.Construction.L12 (Work.Construction.Fstar α) z|
          * |Work.Spaces.Dz W z θ|
        ≤ (2 * (2 * α)) * 1 := mul_le_mul h1 hWz (abs_nonneg _) (by positivity)
      _ ≤ 4 := by nlinarith [hα0, hα1]
  have htri : |Work.Construction.N0 α F W z θ|
      ≤ |(3 / (2 * α)) * Work.Construction.s2 θ
            * Work.Construction.L12 (Work.Construction.Fstar α) z
            * Work.Spaces.pth (Work.Construction.Fstar α) z θ|
          + |Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
            * Work.Spaces.Dz (Work.Construction.Fstar α) z θ|
          + |(1 / α) * Work.Construction.L12 W z * W z θ|
          + |(3 / (2 * α)) * Work.Construction.s2 θ * Work.Construction.L12 W z
            * Work.Spaces.pth F z θ|
          + |Work.Construction.c2m θ * Work.Construction.L12 W z * Work.Spaces.Dz F z θ|
          + |Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
            * Work.Spaces.Dz W z θ| := by
    rw [Work.Construction.N0]
    exact pt_abs_six_le _ _ _ _ _ _
  have hN0 : |Work.Construction.N0 α F W z θ| ≤ (1000 * (CL + 1)) * (1 + C₀) * (1 + B) := by
    have hB1 : (1 : ℝ) ≤ 1 + B := by linarith
    have hsum : |Work.Construction.N0 α F W z θ| ≤ 704 + 355 * (CL * C₀) := by
      linarith [htri, ht1, ht2, ht3, ht4, ht5, ht6, hCC]
    have h2 : 704 + 355 * (CL * C₀) ≤ (1000 * (CL + 1)) * (1 + C₀) := by
      nlinarith [hCL.le, hC₀, hCC]
    have h3 : (1000 * (CL + 1)) * (1 + C₀) ≤ (1000 * (CL + 1)) * (1 + C₀) * (1 + B) := by
      have h := mul_le_mul_of_nonneg_left hB1 (by positivity : (0 : ℝ) ≤ 1000 * (CL + 1) * (1 + C₀))
      calc (1000 * (CL + 1)) * (1 + C₀) = (1000 * (CL + 1)) * (1 + C₀) * 1 := by ring
        _ ≤ (1000 * (CL + 1)) * (1 + C₀) * (1 + B) := h
    linarith [hsum, h2, h3]
  refine le_trans hN0 ?_
  rw [le_div_iff₀ hs2pos]
  exact mul_le_of_le_one_right (by positivity) hs2le1

/-- **The `N`-block.** -/
theorem pt_N_le {α C₀ B C7 : ℝ} (hαι : α ∈ Set.Ioc 0 1) (hC₀ : 0 ≤ C₀) (hB : 0 ≤ B)
    (hC7nn : 0 ≤ C7) {W F Φg : ℝ → ℝ → ℝ}
    (hWS : Work.FTS.EllipticEst.SmoothOpen W)
    (hWC4 : Work.Spaces.HkMem α 4 W)
    (hFeq : F = fun z θ => Work.Construction.Fstar α z θ + W z θ)
    (hWval : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ : ℝ, |W z θ| ≤ 1)
    (hWDz : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ : ℝ, |Work.Spaces.Dz W z θ| ≤ 1)
    (hWDth : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ : ℝ, |Work.Spaces.Dth W z θ| ≤ 1)
    (hFKW : ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Construction.FK W z| ≤ C7 * B)
    (hΞ : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Construction.Rop α (Work.Construction.PhiTil α
          (fun z θ => Work.Construction.Fstar α z θ + W z θ) Φg) z θ| ≤ 13 ∧
        |Work.Construction.Uop α (Work.Construction.PhiTil α
          (fun z θ => Work.Construction.Fstar α z θ + W z θ) Φg) z θ
          / Work.Construction.s2 θ| ≤ 13 ∧
        |Work.Construction.Vop (Work.Construction.PhiTil α
          (fun z θ => Work.Construction.Fstar α z θ + W z θ) Φg) z θ| ≤ 13) :
    ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Construction.N α F Φg z θ|
        ≤ (30000 + 200 * C7) * (1 + C₀) * (1 + B) / Real.sin (2 * θ) := by
  have hα0 : 0 < α := hαι.1
  have hα1 : α ≤ 1 := hαι.2
  have hFKF := pt_FK_le hα0 hα1 hWS hWC4 hFeq hC7nn hB hFKW
  intro z hz θ hθ
  have hs2pos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hs2le1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hs2ne : Work.Construction.s2 θ ≠ 0 := by
    simp only [Work.Construction.s2]
    exact ne_of_gt hs2pos
  obtain ⟨hFval, hs2pthF, hDzF⟩ := pt_F_slots hα0 hα1 hWS hFeq hWval hWDz hWDth z hz θ hθ
  obtain ⟨hΞR', hΞU', hΞV'⟩ := hΞ z hz θ hθ
  -- pass from the slots of `PhiTil α (F_* + W) Φg` to those of `PhiTil α F Φg`
  have hpt : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < π / 2 →
      Work.Construction.PhiTil α F Φg z' θ'
        = Work.Construction.PhiTil α
            (fun z θ => Work.Construction.Fstar α z θ + W z θ) Φg z' θ' := by
    intro z' θ' _ _ _
    rw [hFeq]
  have hΞR : |Work.Construction.Rop α (Work.Construction.PhiTil α F Φg) z θ| ≤ 13 := by
    rw [Work.FTS.GalFields.RHS.Sharp.Rop_congr_Q0 hpt z θ hz hθ.1 hθ.2]
    exact hΞR'
  have hΞU : |Work.Construction.Uop α (Work.Construction.PhiTil α F Φg) z θ
      / Work.Construction.s2 θ| ≤ 13 := by
    rw [Work.FTS.GalFields.RHS.Sharp.Uop_congr_Q0 hpt z θ hz hθ.1 hθ.2]
    exact hΞU'
  have hΞV : |Work.Construction.Vop (Work.Construction.PhiTil α F Φg) z θ| ≤ 13 := by
    rw [Work.FTS.GalFields.RHS.Sharp.Vop_congr_Q0 hpt z θ hz hθ.1 hθ.2]
    exact hΞV'
  have hFKFz : |Work.Construction.FK F z| ≤ (100 + C7) * (1 + B) := hFKF z hz
  have hKB : 0 ≤ (100 + C7) * (1 + B) := by
    have : 0 ≤ 100 + C7 := by linarith
    positivity
  -- the five summands of `N`
  have hA : |2 * Work.Construction.Rop α (Work.Construction.PhiTil α F Φg) z θ * F z θ|
      ≤ 2626 := by
    rw [abs_mul, abs_mul, show |(2 : ℝ)| = 2 from by norm_num]
    calc 2 * |Work.Construction.Rop α (Work.Construction.PhiTil α F Φg) z θ| * |F z θ|
        ≤ 2 * 13 * 101 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hΞR (by norm_num)) hFval (abs_nonneg _)
            (by norm_num)
      _ = 2626 := by norm_num
  have hB' : |2 * Work.Construction.Uop α (Work.Construction.PhiTil α F Φg) z θ
      * Work.Spaces.pth F z θ| ≤ 2626 := by
    have hre : 2 * Work.Construction.Uop α (Work.Construction.PhiTil α F Φg) z θ
        * Work.Spaces.pth F z θ
        = 2 * (Work.Construction.Uop α (Work.Construction.PhiTil α F Φg) z θ
            / Work.Construction.s2 θ)
          * (Work.Construction.s2 θ * Work.Spaces.pth F z θ) := by
      field_simp
    rw [hre, abs_mul, abs_mul, show |(2 : ℝ)| = 2 from by norm_num]
    calc 2 * |Work.Construction.Uop α (Work.Construction.PhiTil α F Φg) z θ
            / Work.Construction.s2 θ| * |Work.Construction.s2 θ * Work.Spaces.pth F z θ|
        ≤ 2 * 13 * 101 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hΞU (by norm_num)) hs2pthF (abs_nonneg _)
            (by norm_num)
      _ = 2626 := by norm_num
  have hC' : |2 * α * Work.Construction.Vop (Work.Construction.PhiTil α F Φg) z θ
      * Work.Spaces.Dz F z θ| ≤ 2626 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hα0.le,
      show |(2 : ℝ)| = 2 from by norm_num]
    calc 2 * α * |Work.Construction.Vop (Work.Construction.PhiTil α F Φg) z θ|
          * |Work.Spaces.Dz F z θ|
        ≤ 2 * α * 13 * 101 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hΞV (by positivity)) hDzF (abs_nonneg _)
            (by positivity)
      _ ≤ 2626 := by nlinarith [hα0, hα1]
  have hD' : |(1 / 2) * Work.Construction.s2 θ * Work.Construction.FK F z
      * Work.Spaces.pth F z θ| ≤ 51 * ((100 + C7) * (1 + B)) := by
    have hre : (1 / 2) * Work.Construction.s2 θ * Work.Construction.FK F z
        * Work.Spaces.pth F z θ
        = (1 / 2) * Work.Construction.FK F z
          * (Work.Construction.s2 θ * Work.Spaces.pth F z θ) := by ring
    rw [hre, abs_mul, abs_mul, show |(1 : ℝ) / 2| = 1 / 2 from by norm_num]
    calc 1 / 2 * |Work.Construction.FK F z| * |Work.Construction.s2 θ * Work.Spaces.pth F z θ|
        ≤ 1 / 2 * ((100 + C7) * (1 + B)) * 101 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hFKFz (by norm_num)) hs2pthF (abs_nonneg _)
            (by positivity)
      _ ≤ 51 * ((100 + C7) * (1 + B)) := by nlinarith [hKB]
  have hE' : |Real.sin θ ^ 2 * Work.Construction.FK F z * F z θ|
      ≤ 101 * ((100 + C7) * (1 + B)) := by
    rw [abs_mul, abs_mul]
    have hsin : |Real.sin θ ^ 2| ≤ 1 := by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact Real.sin_sq_le_one θ
    calc |Real.sin θ ^ 2| * |Work.Construction.FK F z| * |F z θ|
        ≤ 1 * ((100 + C7) * (1 + B)) * 101 :=
          mul_le_mul (mul_le_mul hsin hFKFz (abs_nonneg _) (by positivity)) hFval
            (abs_nonneg _) (by positivity)
      _ = 101 * ((100 + C7) * (1 + B)) := by ring
  have htri : |Work.Construction.N α F Φg z θ|
      ≤ |2 * Work.Construction.Rop α (Work.Construction.PhiTil α F Φg) z θ * F z θ|
        + |2 * Work.Construction.Uop α (Work.Construction.PhiTil α F Φg) z θ
            * Work.Spaces.pth F z θ|
        + |2 * α * Work.Construction.Vop (Work.Construction.PhiTil α F Φg) z θ
            * Work.Spaces.Dz F z θ|
        + |(1 / 2) * Work.Construction.s2 θ * Work.Construction.FK F z
            * Work.Spaces.pth F z θ|
        + |Real.sin θ ^ 2 * Work.Construction.FK F z * F z θ| := by
    rw [Work.Construction.N]
    exact pt_abs_five_le _ _ _ _ _
  have hN : |Work.Construction.N α F Φg z θ|
      ≤ (30000 + 200 * C7) * (1 + C₀) * (1 + B) := by
    have hKBp : 0 ≤ (100 + C7) * (1 + B) := hKB
    have hsum : |Work.Construction.N α F Φg z θ| ≤ 7878 + 152 * ((100 + C7) * (1 + B)) := by
      linarith [htri, hA, hB', hC', hD', hE']
    have h2 : 7878 + 152 * ((100 + C7) * (1 + B)) ≤ (30000 + 200 * C7) * (1 + B) := by
      have h1 : (1 : ℝ) ≤ 1 + B := by linarith
      have h3 : 0 ≤ C7 * (1 + B) := mul_nonneg hC7nn (by linarith)
      have h4 : 0 ≤ 1 + B := by linarith
      nlinarith [h1, h3, h4, hC7nn]
    have h3 : (30000 + 200 * C7) * (1 + B) ≤ (30000 + 200 * C7) * (1 + C₀) * (1 + B) := by
      have h4 : 0 ≤ 30000 + 200 * C7 := by linarith
      have h5 : (1 : ℝ) ≤ 1 + C₀ := by linarith
      have h6 : 0 ≤ 1 + B := by linarith
      calc (30000 + 200 * C7) * (1 + B) = (30000 + 200 * C7) * 1 * (1 + B) := by ring
        _ ≤ (30000 + 200 * C7) * (1 + C₀) * (1 + B) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h5 h4) h6
    linarith [hsum, h2, h3]
  refine le_trans hN ?_
  rw [le_div_iff₀ hs2pos]
  exact mul_le_of_le_one_right (by positivity) hs2le1

/-- **The `Transport`-block.** -/
theorem pt_Transport_le {C₀ B : ℝ} (hC₀ : 0 ≤ C₀) (hB : 0 ≤ B) {W : ℝ → ℝ → ℝ}
    (hWDth : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ : ℝ, |Work.Spaces.Dth W z θ| ≤ 1) :
    ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Coercivity.Transport W z θ| ≤ 3 * (1 + C₀) * (1 + B) / Real.sin (2 * θ) := by
  intro z hz θ hθ
  have hz' : (0 : ℝ) < z := hz
  have hs2pos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hs2le1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h1 : (0 : ℝ) < 1 + z := by linarith
  have hDth : |Work.Spaces.Dth W z θ| ≤ 1 := hWDth z hz θ
  have h3 : |Work.Coercivity.Transport W z θ| ≤ 3 := by
    have h2 : Work.Coercivity.Transport W z θ = 3 * Work.Spaces.Dth W z θ / (1 + z) := rfl
    rw [h2, abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3), abs_of_pos h1,
      div_le_iff₀ h1]
    nlinarith [hDth, h1]
  have h4 : (3 : ℝ) ≤ 3 * (1 + C₀) * (1 + B) := by nlinarith [hC₀, hB]
  refine le_trans h3 (le_trans h4 ?_)
  rw [le_div_iff₀ hs2pos]
  exact mul_le_of_le_one_right (by positivity) hs2le1

end Work.FTS.StrongEps.E5Aux2
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.epsWP_blocks_bnd_fam =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.StrongEps

set_option maxHeartbeats 2000000

theorem epsWP_blocks_bnd_unif {α C₀ Cs Ce T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    (hα : α ∈ Set.Ioc 0 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKQ : K ⊆ Work.FTS.EllipticEst.Q0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (g : Work.FTS.Galerkin.Fam) (ε : ℝ),
      (∀ s ∈ Set.Icc 0 T,
        Work.FTS.ClassC.ClassC α (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s)) →
      (∀ s ∈ Set.Icc 0 T, Work.FTS.Nonlin.Xn α
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s) ≤ C₀ * α ^ 2) →
      (∀ s ∈ Set.Icc 0 T, Work.FTS.StrongGlobal.Xn6 α
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s) ≤ Ce) →
      ∀ s ∈ Set.Icc 0 T, ∀ z θ : ℝ, (z, θ) ∈ K →
      |Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) s z θ|
        + |Work.Spaces.pth (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) s) z θ|
        + |Work.Spaces.Dz (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) s) z θ|
        + |Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s z θ|
        + |Work.Spaces.Dz (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s) z θ|
        + |Work.Spaces.pth (Work.Construction.Fstar α) z θ|
        + |Work.Spaces.Dz (Work.Construction.Fstar α) z θ|
        + |Work.Construction.Rop α (Work.Construction.PhiTil α
            (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) s)
            (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
              (Work.FTS.StrongEps.JfamP ρ ε g)) s)) z θ|
        + |Work.Construction.Uop α (Work.Construction.PhiTil α
            (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) s)
            (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
              (Work.FTS.StrongEps.JfamP ρ ε g)) s)) z θ|
        + |Work.Construction.Vop (Work.Construction.PhiTil α
            (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) s)
            (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
              (Work.FTS.StrongEps.JfamP ρ ε g)) s)) z θ|
        + |Work.Construction.AK α z θ| ≤ B := by
  classical
  rcases Set.eq_empty_or_nonempty K with hKe | hne
  · subst hKe
    exact ⟨0, le_refl 0, fun g ε hC hb4 hb6 s hs z θ hp => absurd hp (by simp)⟩
  obtain ⟨zlo, zhi, tlo, thi, hzlo, hzlole, htlo, htlole, hthilt, hKbox⟩ :=
    Work.FTS_EllLimOK.box_of_compact_inside_Q0 hK hKQ hne
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  obtain ⟨Cx, hCxpos, hCx⟩ := Work.FTS.StrongEps.classC_mixed_sup_le_four
  obtain ⟨Cq, hCqpos, hCq⟩ := blocks.HQo_mixed_abs_le_on_compact_uniform (K := K) hK hKQ
  obtain ⟨CF, hCFpos, hCF⟩ := blocks.Fstar_AK_bnd hα0 hα1 htlo htlole hthilt
  obtain ⟨CS, hCSpos, hCS⟩ := blocks.star_blocks_bnd (α := α) (Cs := Cs) (c := tlo) hstar htlo
  refine ⟨(CF + Cx / Real.sqrt (Work.Spaces.gam α - 1) * max Ce 0)
      + (CF + (Cx / Real.sqrt (Work.Spaces.gam α - 1) * max Ce 0)
          / (4 / Real.pi * min tlo (Real.pi / 2 - thi)))
      + (CF + Cx / Real.sqrt (Work.Spaces.gam α - 1) * max Ce 0)
      + (Cx / Real.sqrt (Work.Spaces.gam α - 1) * max Ce 0)
      + (Cx / Real.sqrt (Work.Spaces.gam α - 1) * max Ce 0)
      + CF + CF
      + (CS + Cq * (max Ce 0 * max Ce 0))
      + (CS + Cq * (max Ce 0 * max Ce 0))
      + (CS + Cq * (max Ce 0 * max Ce 0))
      + CF, ?_, ?_⟩
  · -- nonnegativity
    have hγ1 : 0 < Work.Spaces.gam α - 1 := by
      rw [Work.Spaces.gam]; linarith
    have hK1 : 0 ≤ Cx / Real.sqrt (Work.Spaces.gam α - 1) :=
      (div_pos hCxpos (Real.sqrt_pos.mpr hγ1)).le
    have hCe : 0 ≤ max Ce 0 := le_max_right _ _
    have hmm : 0 < min tlo (Real.pi / 2 - thi) := lt_min htlo (by linarith)
    have hsLB : 0 < 4 / Real.pi * min tlo (Real.pi / 2 - thi) := by positivity
    have h1 : 0 ≤ CF + Cx / Real.sqrt (Work.Spaces.gam α - 1) * max Ce 0 := by
      have := mul_nonneg hK1 hCe; linarith
    have h2 : 0 ≤ CF + (Cx / Real.sqrt (Work.Spaces.gam α - 1) * max Ce 0)
        / (4 / Real.pi * min tlo (Real.pi / 2 - thi)) := by
      have h0 : 0 ≤ Cx / Real.sqrt (Work.Spaces.gam α - 1) * max Ce 0 := mul_nonneg hK1 hCe
      have := div_nonneg h0 hsLB.le; linarith
    have h3 : 0 ≤ Cx / Real.sqrt (Work.Spaces.gam α - 1) * max Ce 0 := mul_nonneg hK1 hCe
    have h4 : 0 ≤ CS + Cq * (max Ce 0 * max Ce 0) := by
      have := mul_nonneg hCqpos.le (mul_nonneg hCe hCe); linarith
    linarith [hCFpos, hCSpos, h1, h2, h3, h4]
  · intro g ε hC hb4 hb6 s hs z θ hzθ
    obtain ⟨hzQ, hθQ1, hθQ2⟩ := Work.FTS.EllipticEst.mem_Q0.mp (hKQ hzθ)
    obtain ⟨hzb, hθb⟩ := hKbox hzθ
    have htloθ : tlo ≤ θ := hθb.1
    have hθthi : θ ≤ thi := hθb.2
    -- the angular lower bound
    have hsinLB : 4 / Real.pi * min tlo (Real.pi / 2 - thi) ≤ Real.sin (2 * θ) := by
      have h1 : min tlo (Real.pi / 2 - thi) ≤ min θ (Real.pi / 2 - θ) :=
        le_min (le_trans (min_le_left _ _) htloθ)
          (le_trans (min_le_right _ _) (by linarith))
      have h2 := Work.FTS.H2.sin_two_ge_min θ ⟨le_of_lt hθQ1, le_of_lt hθQ2⟩
      exact le_trans (mul_le_mul_of_nonneg_left h1 (by positivity)) h2
    -- abbreviations
    let Gs : Fn := slice (Work.FTS.StrongEps.JfamP ρ ε g) s
    have hgsC : Work.FTS.ClassC.ClassC α Gs := hC s hs
    have hgsS : Work.FTS.EllipticEst.SmoothOpen Gs := hgsC.reg
    have hgs4 : Work.Spaces.HkMem α 4 Gs :=
      Work.FTS.OpenPkg.HkMem_mono_open hgsS 4 (by norm_num) hgsC.mem
    have hn6 : Work.Spaces.HkNorm α 6 Gs ≤ max Ce 0 :=
      le_trans (hb6 s hs) (le_max_left _ _)
    have hgo : Work.FTS.VocabO.EllPkgGo α Ce Gs (E Gs) := (hEll Gs hgsC).1
    have hk6 : Work.FTS.ClassC.EllPkgK α 6 Ce Gs (E Gs) := (hEll Gs hgsC).2
    have hFstarS : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
      Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
    have hPsiS : Work.FTS.EllipticEst.SmoothOpen
        (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) :=
      Work.FTS.GalFields.RHS.Sharp.smoothOpen_PhiTil_star hα0 hα1 hstar
    have hXiS : Work.FTS.EllipticEst.SmoothOpen
        (Work.Construction.PhiTil α Gs (E Gs)) :=
      Work.FTS.GalFields.RHS.Sharp.smoothOpen_PhiTil hα0 hgo
    -- constants
    have hγ1 : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam]; linarith
    have hK1nn : 0 ≤ Cx / Real.sqrt (Work.Spaces.gam α - 1) :=
      (div_pos hCxpos (Real.sqrt_pos.mpr hγ1)).le
    have hCenn : 0 ≤ max Ce 0 := le_max_right _ _
    have hsLBpos : 0 < 4 / Real.pi * min tlo (Real.pi / 2 - thi) := by positivity
    -- ### the eleven blocks
    -- (6),(7),(11): the star profile
    have eF : |Work.Construction.Fstar α z θ| ≤ CF := by
      have h := hCF z θ hzQ htloθ hθthi
      have h2 := abs_nonneg (Work.Spaces.pth (Work.Construction.Fstar α) z θ)
      have h3 := abs_nonneg (Work.Spaces.Dz (Work.Construction.Fstar α) z θ)
      have h4 := abs_nonneg (Work.Construction.AK α z θ)
      linarith
    have eFp : |Work.Spaces.pth (Work.Construction.Fstar α) z θ| ≤ CF := by
      have h := hCF z θ hzQ htloθ hθthi
      have h2 := abs_nonneg (Work.Construction.Fstar α z θ)
      have h3 := abs_nonneg (Work.Spaces.Dz (Work.Construction.Fstar α) z θ)
      have h4 := abs_nonneg (Work.Construction.AK α z θ)
      linarith
    have eFz : |Work.Spaces.Dz (Work.Construction.Fstar α) z θ| ≤ CF := by
      have h := hCF z θ hzQ htloθ hθthi
      have h2 := abs_nonneg (Work.Construction.Fstar α z θ)
      have h3 := abs_nonneg (Work.Spaces.pth (Work.Construction.Fstar α) z θ)
      have h4 := abs_nonneg (Work.Construction.AK α z θ)
      linarith
    have eAK : |Work.Construction.AK α z θ| ≤ CF := by
      have h := hCF z θ hzQ htloθ hθthi
      have h2 := abs_nonneg (Work.Construction.Fstar α z θ)
      have h3 := abs_nonneg (Work.Spaces.pth (Work.Construction.Fstar α) z θ)
      have h4 := abs_nonneg (Work.Spaces.Dz (Work.Construction.Fstar α) z θ)
      linarith
    -- (4),(5): the slots of `Gs`
    have hslot : ∀ (b a : ℕ), a + b ≤ 4 →
        |Work.Spaces.mixed b a Gs z θ| ≤ Cx / Real.sqrt (Work.Spaces.gam α - 1) * max Ce 0 := by
      intro b a hab
      have h := hCx α hα hgsC b a hab ⟨hzQ, hθQ1, hθQ2⟩
      exact le_trans h (mul_le_mul_of_nonneg_left hn6 hK1nn)
    have eG : |slice (Work.FTS.StrongEps.JfamP ρ ε g) s z θ|
        ≤ Cx / Real.sqrt (Work.Spaces.gam α - 1) * max Ce 0 := by
      have h := hslot 0 0 (by norm_num)
      simpa only [Gs, Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using h
    have eGz : |Work.Spaces.Dz (slice (Work.FTS.StrongEps.JfamP ρ ε g) s) z θ|
        ≤ Cx / Real.sqrt (Work.Spaces.gam α - 1) * max Ce 0 := by
      have h := hslot 1 0 (by norm_num)
      simpa only [Gs, Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_succ,
        Work.Spaces.DzIter_zero] using h
    -- (1): `Ftau = F* + Gs`
    have e1 : |Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) s z θ|
        ≤ CF + Cx / Real.sqrt (Work.Spaces.gam α - 1) * max Ce 0 := by
      rw [show Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) s z θ
          = Work.Construction.Fstar α z θ + Gs z θ from rfl]
      exact le_trans (abs_add_le _ _) (add_le_add eF eG)
    -- (2): `pth Ftau = pth F* + pth Gs`
    have eGp : |Work.Spaces.pth Gs z θ|
        ≤ (Cx / Real.sqrt (Work.Spaces.gam α - 1) * max Ce 0)
          / (4 / Real.pi * min tlo (Real.pi / 2 - thi)) := by
      have hsinpos : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
      have hmix : |Work.Spaces.Dth Gs z θ| ≤ Cx / Real.sqrt (Work.Spaces.gam α - 1) * max Ce 0 := by
        have h := hslot 0 1 (by norm_num)
        simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ,
          Work.Spaces.DthIter_zero, Work.Spaces.Dth] using h
      have hmul : Real.sin (2 * θ) * |Work.Spaces.pth Gs z θ|
          ≤ Cx / Real.sqrt (Work.Spaces.gam α - 1) * max Ce 0 := by
        rw [Work.Spaces.Dth, abs_mul, abs_of_pos hsinpos] at hmix
        exact hmix
      have h1 : |Work.Spaces.pth Gs z θ|
          ≤ Cx / Real.sqrt (Work.Spaces.gam α - 1) * max Ce 0 / Real.sin (2 * θ) := by
        rw [le_div_iff₀ hsinpos, mul_comm]
        exact hmul
      refine le_trans h1 (div_le_div_of_nonneg_left (mul_nonneg hK1nn hCenn) hsLBpos hsinLB)
    have e2 : |Work.Spaces.pth (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) s) z θ|
        ≤ CF + (Cx / Real.sqrt (Work.Spaces.gam α - 1) * max Ce 0)
          / (4 / Real.pi * min tlo (Real.pi / 2 - thi)) := by
      rw [show Work.Spaces.pth (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) s) z θ
          = Work.Spaces.pth (Work.Construction.Fstar α) z θ + Work.Spaces.pth Gs z θ from ?_]
      · exact le_trans (abs_add_le _ _) (add_le_add eFp eGp)
      · exact Work.FTS.GalFields.RHS.Sharp.pth_add_Q0 hFstarS hgsS z θ hzQ hθQ1 hθQ2
    -- (3): `Dz Ftau = Dz F* + Dz Gs`
    have e3 : |Work.Spaces.Dz (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) s) z θ|
        ≤ CF + Cx / Real.sqrt (Work.Spaces.gam α - 1) * max Ce 0 := by
      have hpz := Work.FTS.GalFields.RHS.Sharp.pz_add_Q0 hFstarS hgsS z θ hzQ hθQ1 hθQ2
      rw [show Work.Spaces.Dz (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) s) z θ
          = Work.Spaces.Dz (fun z θ => Work.Construction.Fstar α z θ + Gs z θ) z θ from rfl]
      rw [show Work.Spaces.Dz (fun z θ => Work.Construction.Fstar α z θ + Gs z θ) z θ
          = Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz Gs z θ from ?_]
      · exact le_trans (abs_add_le _ _) (add_le_add eFz (by
          have h := hslot 1 0 (by norm_num)
          simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_succ,
            Work.Spaces.DzIter_zero] using h))
      · simp only [Work.Spaces.Dz, hpz]; ring
    -- (8),(9),(10): the `PhiTil` split
    have hpot : ∀ z' θ' : ℝ, 0 < z' →
        Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + Gs z θ)
            (fun z θ => Φs z θ + E Gs z θ) z' θ'
          = Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z' θ'
            + Work.Construction.PhiTil α Gs (E Gs) z' θ' := by
      intro z' θ' hz'
      have hL := blocks.L12_Fstar_add_open hα0 hα1 hgsS hgs4 (z := z') (le_of_lt hz')
      simp only [Work.Construction.PhiTil, Work.Construction.Theta]
      rw [hL]
      ring
    have hXinorm : Work.Spaces.HkNorm α 6 (Work.Construction.Rop α (Work.Construction.PhiTil α Gs (E Gs)))
        ≤ max Ce 0 * max Ce 0 := by
      refine le_trans hk6.R.2 ?_
      by_cases hCe : 0 ≤ Ce
      · have hCe' : max Ce 0 = Ce := max_eq_left hCe
        have hn6' : Work.Spaces.HkNorm α 6 Gs ≤ Ce := by rw [← hCe']; exact hn6
        rw [hCe']
        exact mul_le_mul_of_nonneg_left hn6' hCe
      · have hCe' : max Ce 0 = 0 := max_eq_right (not_le.mp hCe).le
        have h1 : Work.Spaces.HkNorm α 6 Gs ≤ 0 := le_trans hn6 (le_of_eq hCe')
        have h2 : 0 ≤ Work.Spaces.HkNorm α 6 Gs := Work.Spaces.HkNorm_nonneg α 6 Gs
        rw [hCe']
        nlinarith [h1, h2, hCe]
    have hXiUnorm : Work.Spaces.HkNorm α 6 (fun z θ =>
          Work.Construction.Uop α (Work.Construction.PhiTil α Gs (E Gs)) z θ
            / Work.Construction.s2 θ) ≤ max Ce 0 * max Ce 0 := by
      refine le_trans hk6.U.2 ?_
      by_cases hCe : 0 ≤ Ce
      · have hCe' : max Ce 0 = Ce := max_eq_left hCe
        have hn6' : Work.Spaces.HkNorm α 6 Gs ≤ Ce := by rw [← hCe']; exact hn6
        rw [hCe']
        exact mul_le_mul_of_nonneg_left hn6' hCe
      · have hCe' : max Ce 0 = 0 := max_eq_right (not_le.mp hCe).le
        have h1 : Work.Spaces.HkNorm α 6 Gs ≤ 0 := le_trans hn6 (le_of_eq hCe')
        have h2 : 0 ≤ Work.Spaces.HkNorm α 6 Gs := Work.Spaces.HkNorm_nonneg α 6 Gs
        rw [hCe']
        nlinarith [h1, h2, hCe]
    have hXiVnorm : Work.Spaces.HkNorm α 6 (Work.Construction.Vop (Work.Construction.PhiTil α Gs (E Gs)))
        ≤ max Ce 0 * max Ce 0 := by
      refine le_trans hk6.V.2 ?_
      by_cases hCe : 0 ≤ Ce
      · have hCe' : max Ce 0 = Ce := max_eq_left hCe
        have hn6' : Work.Spaces.HkNorm α 6 Gs ≤ Ce := by rw [← hCe']; exact hn6
        rw [hCe']
        exact mul_le_mul_of_nonneg_left hn6' hCe
      · have hCe' : max Ce 0 = 0 := max_eq_right (not_le.mp hCe).le
        have h1 : Work.Spaces.HkNorm α 6 Gs ≤ 0 := le_trans hn6 (le_of_eq hCe')
        have h2 : 0 ≤ Work.Spaces.HkNorm α 6 Gs := Work.Spaces.HkNorm_nonneg α 6 Gs
        rw [hCe']
        nlinarith [h1, h2, hCe]
    -- the star part
    have eS : |Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ|
        + |Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ|
        + |Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ|
        ≤ CS := hCS z θ hzQ htloθ hθQ2
    have eSR : |Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ| ≤ CS := by
      have h2 := abs_nonneg (Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ)
      have h3 := abs_nonneg (Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ)
      linarith
    have eSU : |Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ| ≤ CS := by
      have h2 := abs_nonneg (Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ)
      have h3 := abs_nonneg (Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ)
      linarith
    have eSV : |Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ| ≤ CS := by
      have h2 := abs_nonneg (Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ)
      have h3 := abs_nonneg (Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ)
      linarith
    -- the `EllPkgK` part
    have eXR : |Work.Construction.Rop α (Work.Construction.PhiTil α Gs (E Gs)) z θ|
        ≤ Cq * (max Ce 0 * max Ce 0) := by
      have h := hCq α hα0 hα1 (Work.Construction.Rop α (Work.Construction.PhiTil α Gs (E Gs)))
        hk6.R.1 0 0 (by norm_num) z θ hzθ
      have h' : |Work.Construction.Rop α (Work.Construction.PhiTil α Gs (E Gs)) z θ|
          ≤ Cq * Work.Spaces.HkNorm α 6 (Work.Construction.Rop α (Work.Construction.PhiTil α Gs (E Gs))) := by
        simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using h
      exact le_trans h' (mul_le_mul_of_nonneg_left hXinorm hCqpos.le)
    have eXU : |Work.Construction.Uop α (Work.Construction.PhiTil α Gs (E Gs)) z θ|
        ≤ Cq * (max Ce 0 * max Ce 0) := by
      have h := hCq α hα0 hα1 (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α Gs (E Gs)) z θ
          / Work.Construction.s2 θ) hk6.U.1 0 0 (by norm_num) z θ hzθ
      have h' : |Work.Construction.Uop α (Work.Construction.PhiTil α Gs (E Gs)) z θ
          / Work.Construction.s2 θ| ≤ Cq * (max Ce 0 * max Ce 0) := by
        have h'' : |(fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α Gs (E Gs)) z θ
            / Work.Construction.s2 θ) z θ| ≤ Cq *
            Work.Spaces.HkNorm α 6 (fun z θ => Work.Construction.Uop α
              (Work.Construction.PhiTil α Gs (E Gs)) z θ / Work.Construction.s2 θ) := by
          simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using h
        exact le_trans h'' (mul_le_mul_of_nonneg_left hXiUnorm hCqpos.le)
      have hs2pos : 0 < Work.Construction.s2 θ :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
      have hs2le : Work.Construction.s2 θ ≤ 1 := by
        simp only [Work.Construction.s2]; exact Real.sin_le_one _
      have hs2nn : 0 ≤ Work.Construction.s2 θ := le_of_lt hs2pos
      rw [show Work.Construction.Uop α (Work.Construction.PhiTil α Gs (E Gs)) z θ
          = (Work.Construction.Uop α (Work.Construction.PhiTil α Gs (E Gs)) z θ
              / Work.Construction.s2 θ) * Work.Construction.s2 θ from by
        field_simp]
      calc |(Work.Construction.Uop α (Work.Construction.PhiTil α Gs (E Gs)) z θ
            / Work.Construction.s2 θ) * Work.Construction.s2 θ|
          = |Work.Construction.Uop α (Work.Construction.PhiTil α Gs (E Gs)) z θ
              / Work.Construction.s2 θ| * |Work.Construction.s2 θ| := abs_mul _ _
        _ ≤ (Cq * (max Ce 0 * max Ce 0)) * 1 :=
            mul_le_mul h' (by rw [abs_of_nonneg hs2nn]; exact hs2le) (abs_nonneg _)
              (mul_nonneg hCqpos.le (mul_nonneg hCenn hCenn))
        _ = Cq * (max Ce 0 * max Ce 0) := by ring
    have eXV : |Work.Construction.Vop (Work.Construction.PhiTil α Gs (E Gs)) z θ|
        ≤ Cq * (max Ce 0 * max Ce 0) := by
      have h := hCq α hα0 hα1 (Work.Construction.Vop (Work.Construction.PhiTil α Gs (E Gs)))
        hk6.V.1 0 0 (by norm_num) z θ hzθ
      have h' : |Work.Construction.Vop (Work.Construction.PhiTil α Gs (E Gs)) z θ|
          ≤ Cq * Work.Spaces.HkNorm α 6 (Work.Construction.Vop (Work.Construction.PhiTil α Gs (E Gs))) := by
        simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using h
      exact le_trans h' (mul_le_mul_of_nonneg_left hXiVnorm hCqpos.le)
    -- the three operator blocks
    have e8 : |Work.Construction.Rop α (Work.Construction.PhiTil α
          (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) s)
          (slice (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g)) s)) z θ|
        ≤ CS + Cq * (max Ce 0 * max Ce 0) := by
      have hcongr := Work.FTS.GalFields.RHS.Sharp.Rop_congr_Q0
        (α := α)
        (f := Work.Construction.PhiTil α (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) s)
          (slice (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g)) s))
        (g := fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
          + Work.Construction.PhiTil α Gs (E Gs) z θ)
        (fun z' θ' hz' _ _ => hpot z' θ' hz') z θ hzQ hθQ1 hθQ2
      rw [hcongr, Work.FTS.GalFields.RHS.Sharp.Rop_add_Q0 hPsiS hXiS z θ hzQ hθQ1 hθQ2]
      exact le_trans (abs_add_le _ _) (add_le_add eSR eXR)
    have e9 : |Work.Construction.Uop α (Work.Construction.PhiTil α
          (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) s)
          (slice (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g)) s)) z θ|
        ≤ CS + Cq * (max Ce 0 * max Ce 0) := by
      have hcongr := Work.FTS.GalFields.RHS.Sharp.Uop_congr_Q0
        (α := α)
        (f := Work.Construction.PhiTil α (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) s)
          (slice (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g)) s))
        (g := fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
          + Work.Construction.PhiTil α Gs (E Gs) z θ)
        (fun z' θ' hz' _ _ => hpot z' θ' hz') z θ hzQ hθQ1 hθQ2
      rw [hcongr, Work.FTS.GalFields.RHS.Sharp.Uop_add_Q0 hPsiS hXiS z θ hzQ hθQ1 hθQ2]
      exact le_trans (abs_add_le _ _) (add_le_add eSU eXU)
    have e10 : |Work.Construction.Vop (Work.Construction.PhiTil α
          (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) s)
          (slice (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g)) s)) z θ|
        ≤ CS + Cq * (max Ce 0 * max Ce 0) := by
      have hcongr := Work.FTS.GalFields.RHS.Sharp.Vop_congr_Q0
        (f := Work.Construction.PhiTil α (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) s)
          (slice (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g)) s))
        (g := fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
          + Work.Construction.PhiTil α Gs (E Gs) z θ)
        (fun z' θ' hz' _ _ => hpot z' θ' hz') z θ hzQ hθQ1 hθQ2
      rw [hcongr, Work.FTS.GalFields.RHS.Sharp.Vop_add_Q0 hPsiS hXiS z θ hzQ hθQ1 hθQ2]
      exact le_trans (abs_add_le _ _) (add_le_add eSV eXV)
    -- ### assembly
    exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
      (add_le_add (add_le_add (add_le_add (add_le_add e1 e2) e3) eG) eGz) eFp) eFz)
      e8) e9) e10) eAK

theorem epsWP_blocks_bnd_fam {α C₀ Cs Ce T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {G : ℕ → Work.FTS.Galerkin.Fam}
    {ε : ℕ → ℝ}
    (hα : α ∈ Set.Ioc 0 1) (hε : ∀ n : ℕ, ε n ∈ Set.Ioc 0 1) (hT : 0 ≤ T)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hC : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, Work.FTS.ClassC.ClassC α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s))
    (hb4 : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, Work.FTS.Nonlin.Xn α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) ≤ C₀ * α ^ 2)
    (hb6 : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, Work.FTS.StrongGlobal.Xn6 α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) ≤ Ce)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKQ : K ⊆ Work.FTS.EllipticEst.Q0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, ∀ z θ : ℝ, (z, θ) ∈ K →
      |Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s z θ|
        + |Work.Spaces.pth (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ|
        + |Work.Spaces.Dz (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ|
        + |Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s z θ|
        + |Work.Spaces.Dz (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ|
        + |Work.Spaces.pth (Work.Construction.Fstar α) z θ|
        + |Work.Spaces.Dz (Work.Construction.Fstar α) z θ|
        + |Work.Construction.Rop α (Work.Construction.PhiTil α
            (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
            (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
              (Work.FTS.StrongEps.JfamP ρ (ε n) (G n))) s)) z θ|
        + |Work.Construction.Uop α (Work.Construction.PhiTil α
            (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
            (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
              (Work.FTS.StrongEps.JfamP ρ (ε n) (G n))) s)) z θ|
        + |Work.Construction.Vop (Work.Construction.PhiTil α
            (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
            (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
              (Work.FTS.StrongEps.JfamP ρ (ε n) (G n))) s)) z θ|
        + |Work.Construction.AK α z θ| ≤ B := by
  obtain ⟨B, hBnn, hkey⟩ :=
    epsWP_blocks_bnd_unif (α := α) (C₀ := C₀) (Cs := Cs) (Ce := Ce) (T := T) (ρ := ρ)
      (Φs := Φs) (E := E) hα hEll hstar (K := K) hK hKQ
  exact ⟨B, hBnn, fun n s hs z θ hzθ =>
    hkey (G n) (ε n) (fun s hs => hC n s hs) (fun s hs => hb4 n s hs)
      (fun s hs => hb6 n s hs) s hs z θ hzθ⟩

end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.epsWP_sup_le_of_classC =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps


end Work.FTS.StrongEps
end
-- ===== merged: Submission.Work.FTS_EllLimOK.Pinning.hpin_of_pkgCos =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.Pinning

set_option autoImplicit false

theorem hpin_of_pkgCos {α Ce : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (h : Work.FTS_EllLimOK.HasPkg α Ce E) (hcos : Work.FTS_EllLimOK.PkgCos α E) :
    ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g → ∀ z ∈ Set.Ioi (0 : ℝ),
      Filter.Tendsto (fun s => Real.cos s
        * Work.Construction.PhiTil α g (E g) z s)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  intro g hg z hz
  obtain ⟨hGo, _hK6⟩ := h g hg
  set Ψ : ℝ → ℝ → ℝ := Work.Construction.PhiTil α g (E g) with hΨ
  have hsm : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.GalFields.RHS.Sharp.smoothOpen_PhiTil hα hGo
  have hVsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Vop Ψ) := hGo.V.1.1
  have hV4 : Work.Spaces.HkMem α 4 (Work.Construction.Vop Ψ) := hGo.V.1.2
  have hV0 : Work.Spaces.HkMem α 0 (Work.Construction.Vop Ψ) :=
    Work.FTS.OpenPkg.HkMem_mono_open hVsm 0 (by norm_num) hV4
  have hmemCos : Work.Spaces.HkMem α 0 (fun z θ => Ψ z θ / Real.cos θ) := hcos g hg
  have hVint : MeasureTheory.IntegrableOn
      (fun θ => (Work.Construction.Vop Ψ z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
    integrableOn_sq_rpow_of_HkMem hVsm hV0 z hz
  have hcint : MeasureTheory.IntegrableOn
      (fun θ => (Ψ z θ / Real.cos θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
    integrableOn_sq_rpow_of_HkMem (smoothOpen_div_cos hsm) hmemCos z hz
  have h1 : MeasureTheory.IntegrableOn
      (fun θ => (Real.cos θ * Ψ z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta + 4)))
      (Set.Ioo (Real.pi / 6) (Real.pi / 2)) :=
    integrableOn_cos_sq_rpow_tail hsm hz hcint
  have h2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun s => Real.cos s * Ψ z s) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) (Set.Ioo 0 (Real.pi / 2)) :=
    integrableOn_deriv_cos_mul_sq_rpow hsm hz hVint
  have ht : (Real.pi / 6) ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hmain := Work.FTS_EllLimOK.SliceTrace.tendsto_zero_of_deriv_sq_integrable
    (η := Work.Spaces.eta) (γ := Work.Spaces.eta + 4)
    (by norm_num [Work.Spaces.eta]) (by norm_num [Work.Spaces.eta]) ht
    (contDiffOn_one_cos_mul_slice hsm hz) h1 h2
  exact hmain

end Work.FTS_EllLimOK.Pinning
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.PkgJets.pinningBoundClean =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.PkgJets

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## §0  The level-`0` `ℋ`-integrand (copies of `PkgJets.hkZero`, under fresh names)

Two elementary facts about `Work.Spaces.HkIntegrand` at level `0`, used to transfer the
per-slice weighted Hardy inequality of `PkgJets.pinHardy` to the `ℋ⁰`-norm of the slot
`Φ̃/cos θ`.  They are the facts of `PkgJets/hkZero.lean`, copied verbatim under the names
`HkIntegrand_zero_eq_pin` / `HkIntegrand_zero_le_pin` so that this module does not need to
import `hkZero` (whose `HkIntegrand_zero_le` clashes with `PkgJets/thetaBound.lean`). -/



/-! ## §1  The angular weighted Hardy inequality -/


/-! ## §2  The pinning bound -/


end Work.FTS_EllLimOK.PkgJets
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR5L.DthFtau_C1Jet =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXR5L

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## §1  Differentiability of the two `θ`-slices on the open quadrant -/

/-- `Γ(θ') = (sin θ' · cos²θ')^{β/3}` is differentiable at every interior point of the angular
interval (no constraint on the exponent `β`: only the strict positivity of the base is used). -/
theorem differentiableAt_Gam {β θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < π / 2) :
    DifferentiableAt ℝ (fun θ' => Work.Spaces.Gam β θ') θ := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [hθ2, Real.pi_pos])
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hθ2⟩
  have hpos : Real.sin θ * Real.cos θ ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hφ : HasDerivAt (fun θ' : ℝ => Real.sin θ' * Real.cos θ' ^ 2)
      (Real.cos θ * Real.cos θ ^ 2
        + Real.sin θ * (2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ))) θ :=
    (Real.hasDerivAt_sin θ).mul ((Real.hasDerivAt_cos θ).pow 2)
  simpa only [Work.Spaces.Gam] using
    (hφ.rpow_const (p := β / 3) (Or.inl hpos)).differentiableAt

/-- The `θ`-slice of the static profile `F_*` is differentiable on the open angular interval. -/
theorem differentiableAt_Fstar_slice {β z θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < π / 2) :
    DifferentiableAt ℝ (fun θ' => Work.Construction.Fstar β z θ') θ := by
  have hG : DifferentiableAt ℝ
      (fun θ' : ℝ => β * (Work.Spaces.Gam β θ' / Work.Spaces.c β) * Work.FM.Fstar z) θ :=
    (((differentiableAt_Gam (β := β) hθ0 hθ2).div_const (Work.Spaces.c β)).const_mul β).mul_const
      (Work.FM.Fstar z)
  simpa only [Work.Construction.Fstar] using hG

/-- The `θ`-slice of `SG α g (·,·,τ)` is differentiable at every point of the open quadrant, as
soon as the `τ`-slice `slice g τ` is `C⁴` there.  Near `θ` the sanitised family `SG α g` agrees
with `tauExt g`, which for `τ ≥ 0` agrees with `g`, i.e. with the slice. -/
theorem differentiableAt_SG_slice {α τ z θ : ℝ} {g : Work.FTS.Galerkin.Fam}
    (hc4 : ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice g τ))
      Work.FTS.EllipticEst.Q0)
    (hτ : 0 ≤ τ) (hz : 0 < z) (hθ0 : 0 < θ) (hθ2 : θ < π / 2) :
    DifferentiableAt ℝ (fun θ' => Work.FTS_RegExport.RXR5.SG α g z θ' τ) θ := by
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := by
    rw [Work.FTS.EllipticEst.mem_Q0]; exact ⟨hz, hθ0, hθ2⟩
  have hdiff : DifferentiableAt ℝ (Function.uncurry (Work.FTS.Galerkin.slice g τ)) (z, θ) :=
    (hc4.differentiableOn (by norm_num)).differentiableAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)
  have hslice : DifferentiableAt ℝ (fun θ' => Work.FTS.Galerkin.slice g τ z θ') θ :=
    Work.Spaces.differentiableAt_curry_right hdiff
  refine hslice.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds ⟨hθ0, hθ2⟩] with θ' hθ'
  simp only [Work.FTS.Galerkin.slice]
  rw [Work.FTS_RegExport.RXR5.SG_apply_of_pos hz hθ'.1.le hθ'.2.le,
    Work.FTS.FinalV2.tauExt_of_nonneg g hτ]


/-! ## §2  The pointwise split `D_θ(F_* + g̃) = D_θF_* + D_θg̃` on the strip -/

/-- **The `D_θ`-split on the strip.**  For `z ≥ 0`, `θ ∈ [0,π/2]`, `τ ∈ [0,S]`,

`D_θ F_* z θ + D_θ(g̃(τ)) z θ = D_θ(F_* + g̃(τ)) z θ`,

where `g̃ = SG α g`.  Off the open quadrant (`z = 0`, or `sin(2θ) = 0`) all three `D_θ`'s vanish;
on the open quadrant this is `deriv_add` for the two `θ`-slices. -/
theorem Dth_Ftau_eq_strip {α S : ℝ} {g : Work.FTS.Galerkin.Fam}
    (hc4 : ∀ τ, 0 ≤ τ → ContDiffOn ℝ 4
      (Function.uncurry (Work.FTS.Galerkin.slice g τ)) Work.FTS.EllipticEst.Q0)
    {z θ τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Dth (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
      + Work.Spaces.Dth (fun z θ => Work.FTS_RegExport.RXR5.SG α g z θ τ) z θ
    = Work.Spaces.Dth (fun z θ => Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS_RegExport.RXR5.SG α g) τ z θ) z θ := by
  simp only [Work.Spaces.Dth, Work.Spaces.pth, Work.Construction.Ftau]
  rcases eq_or_lt_of_le hz with hz0 | hzp
  · -- `z = 0`: both slices vanish identically, hence all three `D_θ`'s vanish
    subst hz0
    have hF : ∀ θ' : ℝ, Work.Construction.Fstar (Work.FTS.Regularity.pExp α) 0 θ' = 0 :=
      fun θ' => by simp [Work.Construction.Fstar, Work.FM.Fstar]
    have hH : ∀ θ' : ℝ, Work.FTS_RegExport.RXR5.SG α g 0 θ' τ = 0 :=
      fun θ' => Work.FTS_RegExport.RXR5.SG_apply_of_nonpos le_rfl
    rw [show (fun θ' : ℝ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) 0 θ')
          = fun _ => (0 : ℝ) from funext hF,
      show (fun θ' : ℝ => Work.FTS_RegExport.RXR5.SG α g 0 θ' τ) = fun _ => (0 : ℝ)
          from funext hH,
      show (fun θ' : ℝ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) 0 θ'
            + Work.FTS_RegExport.RXR5.SG α g 0 θ' τ) = fun _ => (0 : ℝ) from
        funext (fun θ' => by rw [hF θ', hH θ', zero_add])]
    simp
  · by_cases hs : Real.sin (2 * θ) = 0
    · -- `sin(2θ) = 0`: all three `D_θ`'s vanish
      rw [hs]
      ring
    · -- the open quadrant: `deriv_add` on the two slices
      have hθ0 : 0 < θ := by
        rcases eq_or_lt_of_le hθ.1 with h | h
        · exact absurd (by rw [← h]; simp) hs
        · exact h
      have hθ2 : θ < π / 2 := by
        rcases lt_or_eq_of_le hθ.2 with h | h
        · exact h
        · exact absurd (by
            rw [h]
            have h2 : 2 * (π / 2) = π := by ring
            rw [h2, Real.sin_pi]) hs
      have hdF : DifferentiableAt ℝ
          (fun θ' => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ') θ :=
        differentiableAt_Fstar_slice hθ0 hθ2
      have hdH : DifferentiableAt ℝ
          (fun θ' => Work.FTS_RegExport.RXR5.SG α g z θ' τ) θ :=
        differentiableAt_SG_slice (hc4 τ hτ.1) hτ.1 hzp hθ0 hθ2
      rw [show (fun θ' : ℝ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ'
            + Work.FTS_RegExport.RXR5.SG α g z θ' τ)
          = (fun θ' : ℝ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ')
            + (fun θ' : ℝ => Work.FTS_RegExport.RXR5.SG α g z θ' τ) from rfl,
        deriv_add hdF hdH]
      ring

/-! ## §3  The target -/

theorem DthFtau_C1Jet {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S)
    (hSt1 : Work.FTS.RegPkgGal.St1Class α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)))
    (hO1 : ∃ N₂ N₃ : ℝ, 0 ≤ N₂ ∧ 0 ≤ N₃ ∧
      Work.FTS.RegPkgGal.C1Jet α S N₂
        (fun z θ τ => Work.Spaces.Dz (fun z θ => Work.FTS_RegExport.RXR5.SG α g z θ τ) z θ) ∧
      Work.FTS.RegPkgGal.C1Jet α S N₃
        (fun z θ τ => Work.Spaces.Dth (fun z θ => Work.FTS_RegExport.RXR5.SG α g z θ τ) z θ)) :
    ∃ N₅ : ℝ, 0 ≤ N₅ ∧
      Work.FTS.RegPkgGal.C1Jet α S N₅
        (fun z θ τ => Work.Spaces.Dth (fun z θ => Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α)
          (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ z θ) z θ) := by
  obtain ⟨N₂, N₃, hN₂0, hN₃0, _hDzSG, hDthSG⟩ := hO1
  obtain ⟨Nf, hNf0, hDthFstar⟩ :=
    Work.FTS_RegExport.RXR5.C1Jet_Dth_Fstar (α := α) (S := S) hα hα13
  refine ⟨Nf + N₃, add_nonneg hNf0 hN₃0, ?_⟩
  refine Work.FTS.RegPkgGal.C1Jet.congr
    (Work.FTS.RegPkgGal.C1Jet.add hDthFstar hDthSG) ?_
  intro z θ τ hz hθ hτ
  exact Dth_Ftau_eq_strip (α := α) (S := S) (g := g)
    (fun τ hτ => hOK.1.1.c4 τ hτ) hτ hz hθ

end Work.FTS_RegExport.RXR5L
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR5L.DzFtau_C1Jet =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXR5L

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 Linearity of `D_z` at the level of `C1Jet`s -/

/-- **`D_z` of a sum of two families is a `C1Jet`.**  If the `D_z`-slots of `a` and `b` are
`C1Jet`s and both families have differentiable `z`-slices at every `z > 0` (uniformly in
`(θ,τ) ∈ Iθ × [0,S]`), then so is the `D_z`-slot of the pointwise sum `a + b`.

The only pointwise input is `deriv (f + g) = deriv f + deriv g` on `z > 0`; at `z = 0` both
sides of `D_z` vanish (`D_z f 0 θ = 0 · ∂_z f`), so the identity holds on the whole closed half
line `z ≥ 0` on which the `Jet` clause of `C1Jet` is stated. -/
theorem C1Jet_dz_add {α S N₁ N₂ : ℝ} {a b : ℝ → ℝ → ℝ → ℝ}
    (Ha : Work.FTS.RegPkgGal.C1Jet α S N₁
      (fun z θ τ => Work.Spaces.Dz (fun z θ => a z θ τ) z θ))
    (Hb : Work.FTS.RegPkgGal.C1Jet α S N₂
      (fun z θ τ => Work.Spaces.Dz (fun z θ => b z θ τ) z θ))
    (had : ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (fun z' => a z' θ τ) z)
    (hbd : ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (fun z' => b z' θ τ) z) :
    Work.FTS.RegPkgGal.C1Jet α S (N₁ + N₂)
      (fun z θ τ => Work.Spaces.Dz (fun z θ => a z θ τ + b z θ τ) z θ) := by
  refine (Work.FTS.RegPkgGal.C1Jet.add Ha Hb).congr ?_
  intro z θ τ hz hθ hτ
  rcases eq_or_lt_of_le hz with h | h
  · -- `z = 0`: every `D_z` vanishes
    rw [← h]
    simp only [Work.Spaces.Dz]
    ring
  · -- `z > 0`: the pointwise product rule
    simp only [Work.Spaces.Dz, Work.Spaces.pz]
    rw [show (fun z' : ℝ => a z' θ τ + b z' θ τ)
        = (fun z' : ℝ => a z' θ τ) + (fun z' => b z' θ τ) from rfl,
      deriv_add (had τ hτ θ hθ z h) (hbd τ hτ θ hθ z h), mul_add]

/-! ## §2 The `D_z`-slot of the fake-time profile -/

theorem DzFtau_C1Jet {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S)
    (hSt1 : Work.FTS.RegPkgGal.St1Class α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)))
    (hO1 : ∃ N₂ N₃ : ℝ, 0 ≤ N₂ ∧ 0 ≤ N₃ ∧
      Work.FTS.RegPkgGal.C1Jet α S N₂
        (fun z θ τ => Work.Spaces.Dz (fun z θ => Work.FTS_RegExport.RXR5.SG α g z θ τ) z θ) ∧
      Work.FTS.RegPkgGal.C1Jet α S N₃
        (fun z θ τ => Work.Spaces.Dth (fun z θ => Work.FTS_RegExport.RXR5.SG α g z θ τ) z θ)) :
    ∃ N₆ : ℝ, 0 ≤ N₆ ∧
      Work.FTS.RegPkgGal.C1Jet α S N₆
        (fun z θ τ => Work.Spaces.Dz (fun z θ => Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α)
          (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ z θ) z θ) := by
  -- the `D_z`-slot of the (sanitised) family, from the hypothesis `hO1`
  obtain ⟨N₂, _, hN₂0, _, hDzSG, _⟩ := hO1
  -- the `D_z`-slot of the static profile `F_*`
  obtain ⟨N₁₁, hN₁₁0, hDzFs⟩ :=
    Work.FTS_RegExport.RXR5.C1Jet_Dz_Fstar (α := α) (S := S) hα hα13
  -- the `z`-derivative of the slices of the sanitised family, from `SG_C1Jet`
  obtain ⟨_, _, hC1G⟩ := SG_C1Jet hα hα13 hOK hS hSt1
  refine ⟨N₁₁ + N₂, by linarith, ?_⟩
  -- `F_τ = F_* + g(τ)`, and `D_z` is additive
  refine (C1Jet_dz_add
    (a := fun z θ _ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ)
    (b := fun z θ τ => Work.FTS_RegExport.RXR5.SG α g z θ τ)
    hDzFs hDzSG ?_ ?_).congr ?_
  · intro τ _hτ θ _hθ z hz
    exact Work.Stability.differentiableAt_Fstar_slice (Work.FTS.Regularity.pExp α) θ z
      (by linarith [Set.mem_Ioi.mp hz])
  · intro τ hτ θ hθ z hz
    obtain ⟨d, hd, _⟩ := hC1G.2 τ hτ θ hθ z hz
    exact hd.differentiableAt
  · -- `Ftau α g τ = Fstar α + g τ` by definition
    intro z θ τ _hz _hθ _hτ
    simp only [Work.Construction.Ftau]

end Work.FTS_RegExport.RXR5L
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR5L.FK_C1Jet =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXR5L

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 Elementary facts about the angular weight `K` and the interval `Iθ` -/

/-- The angular weight `K(θ) = 3 sinθ cos²θ` is continuous. -/
theorem continuous_K : Continuous Work.Spaces.K := by
  rw [show Work.Spaces.K = fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2 from rfl]
  fun_prop

/-- `|K| ≤ 3` on `Iθ` (from `Der.L12fBasic`). -/
theorem abs_K_le_three' {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : |Work.Spaces.K θ| ≤ 3 :=
  Work.FTS.RegPkgGal.Der.abs_K_le_three hθ

/-! ## §2 The angular moment of a `C1Jet` family -/

/-- **The Lipschitz bound in `z` of a `C1Jet`, slice by slice.**  A pointwise `z`-derivative
bounded by `N` upgrades to a Lipschitz bound by the mean value theorem (applied on `Ioi 0`, a
convex set on which the slice is differentiable with `|deriv| ≤ N`). -/
theorem c1jet_z_lipschitz {α S N : ℝ} {h : ℝ → ℝ → ℝ → ℝ}
    (H : Work.FTS.RegPkgGal.C1Jet α S N h) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S)
    {σ : ℝ} (hσ : σ ∈ Work.Spaces.Iθ) {z z' : ℝ} (hz : 0 < z) (hz' : 0 < z') :
    |h z' σ τ - h z σ τ| ≤ N * |z' - z| := by
  have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ (fun y => h y σ τ) x := fun x hx =>
    (H.2 τ hτ σ hσ x hx).choose_spec.1.differentiableAt
  have hbd : ∀ x ∈ Set.Ioi (0 : ℝ), ‖deriv (fun y => h y σ τ) x‖ ≤ N := by
    intro x hx
    obtain ⟨d, hd, hdb⟩ := H.2 τ hτ σ hσ x hx
    rw [hd.deriv, Real.norm_eq_abs]
    exact hdb
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun y => h y σ τ)
    hderiv hbd (convex_Ioi (0 : ℝ)) hz hz'
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  exact h

/-- **Integrability of the moment integrand.**  A bounded, angularly continuous slice is
integrable against `K` on the finite interval `Iθ`. -/
theorem c1jet_integrable_Kmul {α S N : ℝ} (hα : 0 < α) {h : ℝ → ℝ → ℝ → ℝ}
    (H : Work.FTS.RegPkgGal.C1Jet α S N h) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S)
    {z : ℝ} (hz : 0 ≤ z) :
    MeasureTheory.Integrable (fun σ => h z σ τ * Work.Spaces.K σ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hN : 0 ≤ N := H.1.1
  have hcont : ContinuousOn (fun σ => h z σ τ) Work.Spaces.Iθ :=
    Work.FTS.RegPkgGal.Der.continuousOn_of_holder hN hα
      (fun σ hσ σ' hσ' => H.1.thmod hz hσ hσ' hτ)
  have hmeas : AEStronglyMeasurable (fun σ => h z σ τ * Work.Spaces.K σ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (hcont.mul continuous_K.continuousOn).aestronglyMeasurable_of_isCompact
      isCompact_Icc measurableSet_Icc
  refine MeasureTheory.Integrable.mono' (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (g := fun _ : ℝ => 3 * N) ?_ hmeas ?_
  · exact MeasureTheory.integrableOn_const (μ := MeasureTheory.volume)
      (s := Work.Spaces.Iθ) (C := 3 * N) (ne_of_lt Work.Spaces.volume_Iθ_lt_top)
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with σ hσ
    rw [Real.norm_eq_abs, abs_mul]
    calc |h z σ τ| * |Work.Spaces.K σ| ≤ N * 3 :=
          mul_le_mul (H.1.abs_le hz hσ hτ) (abs_K_le_three' hσ) (abs_nonneg _) hN
      _ = 3 * N := by ring

/-- **The crude sup bound of the angular moment.** -/
theorem Kavg_abs_le {N z τ : ℝ} {h : ℝ → ℝ → ℝ → ℝ} (hN : 0 ≤ N)
    (hb : ∀ σ ∈ Work.Spaces.Iθ, |h z σ τ| ≤ N) :
    |∫ σ in Work.Spaces.Iθ, h z σ τ * Work.Spaces.K σ| ≤ 3 * N * (π / 2) := by
  have hmn := Work.FTS.RegPkgGal.Der.setIntegral_abs_le_of_bound (c := 3 * N)
    (f := fun σ => h z σ τ * Work.Spaces.K σ) (fun σ hσ => by
      rw [abs_mul]
      calc |h z σ τ| * |Work.Spaces.K σ| ≤ N * 3 :=
            mul_le_mul (hb σ hσ) (abs_K_le_three' hσ) (abs_nonneg _) hN
        _ = 3 * N := by ring)
  have hnorm := MeasureTheory.norm_integral_le_integral_norm
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (fun σ => h z σ τ * Work.Spaces.K σ)
  rw [Real.norm_eq_abs] at hnorm
  exact le_trans hnorm hmn

/-- **The moment of the difference is the difference of the moments.** -/
theorem Kavg_sub {α S N : ℝ} (hα : 0 < α) {h : ℝ → ℝ → ℝ → ℝ}
    (H : Work.FTS.RegPkgGal.C1Jet α S N h) {τ τ' : ℝ} (hτ : τ ∈ Set.Icc 0 S)
    (hτ' : τ' ∈ Set.Icc 0 S) {z z' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z') :
    (∫ σ in Work.Spaces.Iθ, h z σ τ * Work.Spaces.K σ)
        - (∫ σ in Work.Spaces.Iθ, h z' σ τ' * Work.Spaces.K σ)
      = ∫ σ in Work.Spaces.Iθ, (h z σ τ - h z' σ τ') * Work.Spaces.K σ := by
  rw [← MeasureTheory.integral_sub (c1jet_integrable_Kmul hα H hτ hz) (c1jet_integrable_Kmul hα H hτ' hz')]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun σ _ => by ring)

/-- **The joint `(z,τ)`-modulus of the angular moment.** -/
theorem Kavg_modulus {α S N : ℝ} (hα : 0 < α) {h : ℝ → ℝ → ℝ → ℝ}
    (H : Work.FTS.RegPkgGal.C1Jet α S N h) {z z' τ τ' : ℝ}
    (hz : 0 ≤ z) (hz' : 0 ≤ z') (hτ : τ ∈ Set.Icc 0 S) (hτ' : τ' ∈ Set.Icc 0 S) :
    |(∫ σ in Work.Spaces.Iθ, h z σ τ * Work.Spaces.K σ)
        - (∫ σ in Work.Spaces.Iθ, h z' σ τ' * Work.Spaces.K σ)|
      ≤ 3 * N * (π / 2) * (|z - z'| + |τ - τ'|) ^ α := by
  have hN : 0 ≤ N := H.1.1
  rw [Kavg_sub hα H hτ hτ' hz hz']
  have hnorm := MeasureTheory.norm_integral_le_integral_norm
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (fun σ => (h z σ τ - h z' σ τ') * Work.Spaces.K σ)
  rw [Real.norm_eq_abs] at hnorm
  have hmn := Work.FTS.RegPkgGal.Der.setIntegral_abs_le_of_bound
    (f := fun σ => (h z σ τ - h z' σ τ') * Work.Spaces.K σ)
    (c := 3 * N * (|z - z'| + |τ - τ'|) ^ α) (fun σ hσ => by
      rw [abs_mul]
      have h1 := H.1.2.2 z z' σ σ τ τ' hz hz' hσ hσ hτ hτ'
      simp only [sub_self, abs_zero, add_zero] at h1
      calc |h z σ τ - h z' σ τ'| * |Work.Spaces.K σ|
          ≤ (N * (|z - z'| + |τ - τ'|) ^ α) * 3 :=
            mul_le_mul h1 (abs_K_le_three' hσ) (abs_nonneg _)
              (mul_nonneg hN (Real.rpow_nonneg (by positivity) α))
        _ = 3 * N * (|z - z'| + |τ - τ'|) ^ α := by ring)
  calc |∫ σ in Work.Spaces.Iθ, (h z σ τ - h z' σ τ') * Work.Spaces.K σ|
      ≤ ∫ σ in Work.Spaces.Iθ, ‖(h z σ τ - h z' σ τ') * Work.Spaces.K σ‖ := hnorm
    _ ≤ 3 * N * (|z - z'| + |τ - τ'|) ^ α * (π / 2) := hmn
    _ = 3 * N * (π / 2) * (|z - z'| + |τ - τ'|) ^ α := by ring

/-- **The `z`-derivative of the angular moment of a `C1Jet` family.**  Dominated convergence
along the punctured filter `𝓝[≠] z`, with the *uniform* (in the parameter) bound `3N` on the
difference quotients supplied by `c1jet_z_lipschitz`. -/
theorem Kavg_hasDerivAt {α S N : ℝ} (hα : 0 < α) {h : ℝ → ℝ → ℝ → ℝ}
    (H : Work.FTS.RegPkgGal.C1Jet α S N h) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) {z : ℝ}
    (hz : 0 < z) :
    ∃ d : ℝ, HasDerivAt (fun z' => ∫ σ in Work.Spaces.Iθ, h z' σ τ * Work.Spaces.K σ) d z ∧
      |d| ≤ 3 * N * (π / 2) := by
  have hN : 0 ≤ N := H.1.1
  -- the candidate derivative
  set D : ℝ := ∫ σ in Work.Spaces.Iθ, deriv (fun y => h y σ τ) z * Work.Spaces.K σ with hD
  -- the uniform bound on the difference quotients
  have hquot : ∀ z' σ : ℝ, 0 < z' → z' ≠ z → σ ∈ Work.Spaces.Iθ →
      |(z' - z)⁻¹ * (h z' σ τ * Work.Spaces.K σ - h z σ τ * Work.Spaces.K σ)| ≤ 3 * N := by
    intro z' σ hz' hzne hσ
    have hlip := c1jet_z_lipschitz H hτ hσ hz hz'
    have hkey : h z' σ τ * Work.Spaces.K σ - h z σ τ * Work.Spaces.K σ
        = (h z' σ τ - h z σ τ) * Work.Spaces.K σ := by ring
    rw [hkey, abs_mul, abs_mul, abs_inv]
    calc |z' - z|⁻¹ * (|h z' σ τ - h z σ τ| * |Work.Spaces.K σ|)
        ≤ |z' - z|⁻¹ * ((N * |z' - z|) * 3) := by
          refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (abs_nonneg _))
          exact mul_le_mul hlip (abs_K_le_three' hσ) (abs_nonneg _) (by positivity)
      _ = 3 * N := by
          rw [show |z' - z|⁻¹ * ((N * |z' - z|) * 3) = (|z' - z|⁻¹ * |z' - z|) * (3 * N)
            from by ring, inv_mul_cancel₀ (abs_ne_zero.mpr (sub_ne_zero.mpr hzne)), one_mul]
  -- the dominated convergence step
  have hDCT : Tendsto (fun z' => ∫ σ in Work.Spaces.Iθ,
      (z' - z)⁻¹ * (h z' σ τ * Work.Spaces.K σ - h z σ τ * Work.Spaces.K σ))
      (𝓝[≠] z) (𝓝 D) := by
    have hmain := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ) (l := 𝓝[≠] z)
      (F := fun z' σ => (z' - z)⁻¹ * (h z' σ τ * Work.Spaces.K σ - h z σ τ * Work.Spaces.K σ))
      (f := fun σ => deriv (fun y => h y σ τ) z * Work.Spaces.K σ)
      (bound := fun _ : ℝ => 3 * N) ?_ ?_ ?_ ?_
    · rw [hD]
      exact hmain
    · -- a.e. strong measurability of the difference quotients
      filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds
        (by linarith : z / 2 < z) (by linarith : z < 2 * z))] with z' hz'
      have hz'0 : (0 : ℝ) < z' := lt_trans (by linarith : (0 : ℝ) < z / 2) hz'.1
      have hcont1 : ContinuousOn (fun σ => h z' σ τ) Work.Spaces.Iθ :=
        Work.FTS.RegPkgGal.Der.continuousOn_of_holder hN hα
          (fun σ hσ σ' hσ' => H.1.thmod hz'0.le hσ hσ' hτ)
      have hcont2 : ContinuousOn (fun σ => h z σ τ) Work.Spaces.Iθ :=
        Work.FTS.RegPkgGal.Der.continuousOn_of_holder hN hα
          (fun σ hσ σ' hσ' => H.1.thmod hz.le hσ hσ' hτ)
      have hcont : ContinuousOn (fun σ => h z' σ τ * Work.Spaces.K σ
          - h z σ τ * Work.Spaces.K σ) Work.Spaces.Iθ :=
        (hcont1.mul continuous_K.continuousOn).sub (hcont2.mul continuous_K.continuousOn)
      exact (hcont.const_mul ((z' - z)⁻¹)).aestronglyMeasurable_of_isCompact
        isCompact_Icc measurableSet_Icc
    · -- the uniform bound on the quotients
      filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds
        (by linarith : z / 2 < z) (by linarith : z < 2 * z)), self_mem_nhdsWithin] with z' hz' hzne
      have hz'0 : (0 : ℝ) < z' := lt_trans (by linarith : (0 : ℝ) < z / 2) hz'.1
      have hzne' : z' ≠ z := by simpa using hzne
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with σ hσ
      rw [Real.norm_eq_abs]
      exact hquot z' σ hz'0 hzne' hσ
    · -- the dominating function is integrable
      exact MeasureTheory.integrableOn_const (μ := MeasureTheory.volume)
        (s := Work.Spaces.Iθ) (C := 3 * N) (ne_of_lt Work.Spaces.volume_Iθ_lt_top)
    · -- pointwise convergence of the quotients to the pointwise derivative
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with σ hσ
      obtain ⟨d, hd, _hdb⟩ := H.2 τ hτ σ hσ z hz
      have h1 : Tendsto (slope (fun y => h y σ τ) z) (𝓝[≠] z) (𝓝 d) := hd.tendsto_slope
      have h2 : Tendsto (fun z' => slope (fun y => h y σ τ) z z' * Work.Spaces.K σ)
          (𝓝[≠] z) (𝓝 (d * Work.Spaces.K σ)) := h1.mul_const _
      have h3 : Tendsto (fun z' => (z' - z)⁻¹ * (h z' σ τ - h z σ τ) * Work.Spaces.K σ)
          (𝓝[≠] z) (𝓝 (d * Work.Spaces.K σ)) :=
        Filter.Tendsto.congr' (Filter.Eventually.of_forall
          (fun z' => by simp only [slope, vsub_eq_sub, smul_eq_mul])) h2
      have h4 : Tendsto (fun z' => (z' - z)⁻¹
          * (h z' σ τ * Work.Spaces.K σ - h z σ τ * Work.Spaces.K σ))
          (𝓝[≠] z) (𝓝 (d * Work.Spaces.K σ)) :=
        Filter.Tendsto.congr' (Filter.Eventually.of_forall (fun z' => by ring)) h3
      rw [hd.deriv]
      exact h4
  -- identify the two expressions of the difference quotients
  have hcongr : (fun z' => (z' - z)⁻¹ * ((∫ σ in Work.Spaces.Iθ, h z' σ τ * Work.Spaces.K σ)
        - (∫ σ in Work.Spaces.Iθ, h z σ τ * Work.Spaces.K σ)))
      =ᶠ[𝓝[≠] z] (fun z' => ∫ σ in Work.Spaces.Iθ,
        (z' - z)⁻¹ * (h z' σ τ * Work.Spaces.K σ - h z σ τ * Work.Spaces.K σ)) := by
    filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds
      (by linarith : z / 2 < z) (by linarith : z < 2 * z))] with z' hz'
    have hz'0 : (0 : ℝ) < z' := lt_trans (by linarith : (0 : ℝ) < z / 2) hz'.1
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_sub (c1jet_integrable_Kmul hα H hτ hz'0.le)
        (c1jet_integrable_Kmul hα H hτ hz.le)]
  have hslope : Tendsto (slope (fun z' => ∫ σ in Work.Spaces.Iθ, h z' σ τ * Work.Spaces.K σ) z)
      (𝓝[≠] z) (𝓝 D) :=
    Filter.Tendsto.congr' (hcongr.symm.trans (Filter.Eventually.of_forall
      (fun z' => by simp only [slope, vsub_eq_sub, smul_eq_mul]))) hDCT
  refine ⟨D, hasDerivAt_iff_tendsto_slope.mpr hslope, ?_⟩
  -- bound on the derivative
  rw [hD]
  have hnorm := MeasureTheory.norm_integral_le_integral_norm
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (fun σ => deriv (fun y => h y σ τ) z * Work.Spaces.K σ)
  rw [Real.norm_eq_abs] at hnorm
  refine le_trans hnorm (Work.FTS.RegPkgGal.Der.setIntegral_abs_le_of_bound
    (f := fun σ => deriv (fun y => h y σ τ) z * Work.Spaces.K σ) (c := 3 * N)
    (fun σ hσ => by
      rw [abs_mul]
      obtain ⟨d, hd, hdb⟩ := H.2 τ hτ σ hσ z hz
      rw [hd.deriv]
      calc |d| * |Work.Spaces.K σ| ≤ N * 3 :=
            mul_le_mul hdb (abs_K_le_three' hσ) (abs_nonneg _) hN
        _ = 3 * N := by ring))

/-- **The angular moment of a `C1Jet` family is a `C1Jet`.** -/
theorem c1jet_Kavg {α S N : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {h : ℝ → ℝ → ℝ → ℝ} (H : Work.FTS.RegPkgGal.C1Jet α S N h) :
    ∃ N' : ℝ, 0 ≤ N' ∧ Work.FTS.RegPkgGal.C1Jet α S N'
      (fun z θ τ => ∫ σ in Work.Spaces.Iθ, h z σ τ * Work.Spaces.K σ) := by
  have hN : 0 ≤ N := H.1.1
  have hpi1 : (0 : ℝ) < π / 2 := by linarith [Real.pi_pos]
  refine ⟨6 * N, by linarith, ⟨by linarith, ?_, ?_⟩, ?_⟩
  · -- the sup bound
    intro z θ τ hz hθ hτ
    refine le_trans (Kavg_abs_le hN (fun σ hσ => H.1.abs_le hz hσ hτ)) ?_
    nlinarith [Real.pi_lt_four, hN]
  · -- the joint modulus
    intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    refine le_trans (Kavg_modulus hα H hz hz' hτ hτ') ?_
    have hbase : 0 ≤ |z - z'| + |τ - τ'| := by positivity
    have hle : |z - z'| + |τ - τ'| ≤ |z - z'| + |θ - θ'| + |τ - τ'| := by
      have := abs_nonneg (θ - θ')
      linarith
    have h2 : (|z - z'| + |τ - τ'|) ^ α ≤ (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α :=
      Real.rpow_le_rpow hbase hle hα.le
    have h3 : 0 ≤ (|z - z'| + |τ - τ'|) ^ α := Real.rpow_nonneg hbase α
    have hNL : N * (|z - z'| + |τ - τ'|) ^ α ≤ N * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α :=
      mul_le_mul_of_nonneg_left h2 hN
    have hpi : 3 * (π / 2) ≤ 6 := by linarith [Real.pi_lt_four]
    calc 3 * N * (π / 2) * (|z - z'| + |τ - τ'|) ^ α
        = 3 * (π / 2) * (N * (|z - z'| + |τ - τ'|) ^ α) := by ring
      _ ≤ 6 * (N * (|z - z'| + |τ - τ'|) ^ α) :=
          mul_le_mul_of_nonneg_right hpi (mul_nonneg hN h3)
      _ ≤ 6 * (N * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α) :=
          mul_le_mul_of_nonneg_left hNL (by norm_num)
      _ = 6 * N * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α := by ring
  · -- the `z`-derivative
    intro τ hτ θ hθ z hz
    obtain ⟨d, hd, hdb⟩ := Kavg_hasDerivAt hα H hτ hz
    refine ⟨d, hd, ?_⟩
    have hpi2 : (π : ℝ) / 2 ≤ 2 := by linarith [Real.pi_lt_four]
    nlinarith [hN, hpi1, hpi2, hdb]

/-! ## §3 The `C1Jet`-slot of the full profile -/

/-- **`F_τ = F_* + g̃(τ)` is a `C1Jet`** from the class data of the sanitised family (the
`hO1`-free version of `RXR5L.Ftau_C1Jet`). -/
theorem Ftau_C1Jet' {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S)
    (hSt1 : Work.FTS.RegPkgGal.St1Class α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))) :
    ∃ N₄ : ℝ, 0 ≤ N₄ ∧
      Work.FTS.RegPkgGal.C1Jet α S N₄
        (fun z θ τ => Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ z θ) := by
  obtain ⟨N₁, hN₁0, hN₁⟩ := SG_C1Jet (S := S) hα hα13 hOK hS hSt1
  have hF : Work.FTS.RegPkgGal.C1Jet α S (100 + 20 * Work.FTS.Regularity.pExp α)
      (fun z θ (_ : ℝ) => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) :=
    Work.FTS.RegPkgGal.Der.C1JetFstar (S := S) hα hα13
  have hsum : Work.FTS.RegPkgGal.C1Jet α S
      ((100 + 20 * Work.FTS.Regularity.pExp α) + N₁)
      (fun z θ τ =>
        Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
          + Work.FTS_RegExport.RXR5.SG α g z θ τ) :=
    Work.FTS.RegPkgGal.C1Jet.add hF hN₁
  exact ⟨(100 + 20 * Work.FTS.Regularity.pExp α) + N₁,
    by have hp := Work.FTS.Regularity.pExp_pos hα; linarith, hsum⟩

/-! ## §4 The target -/

theorem FK_C1Jet {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S)
    (hSt1 : Work.FTS.RegPkgGal.St1Class α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))) :
    ∃ N₁₄ : ℝ, 0 ≤ N₁₄ ∧
      Work.FTS.RegPkgGal.C1Jet α S N₁₄
        (fun z θ τ => Work.Construction.FK (Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α) (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ) z) := by
  have hα1 : α ≤ 1 := by linarith
  obtain ⟨N₄, hN₄0, hC1⟩ := Ftau_C1Jet' hα hα13 hOK hS hSt1
  obtain ⟨N', hN'0, hKavg⟩ := c1jet_Kavg (S := S) hα hα1 hC1
  refine ⟨N', hN'0, Work.FTS.RegPkgGal.C1Jet.congr hKavg (fun z θ τ _ _ _ => ?_)⟩
  simp only [Work.Construction.FK, Work.Construction.Ftau]

end Work.FTS_RegExport.RXR5L
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR5L.L12fAux.SG_tau_mod_weighted =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXR5L.L12fAux.SG_tau_mod_weighted` — the *`z`-weighted* `τ`-modulus of `SG`

The sibling `Work.FTS_RegExport.RXR5L.SG_tau_mod` proves the unweighted `α`-Hölder modulus in the
fake time `τ` of the sanitised family `SG α g = gS α (tauExt g)` on the horizon `[0,S]`:

`|SG α g z θ τ - SG α g z θ τ'| ≤ Lt · |τ - τ'|^α`.

Here we prove the genuinely stronger, *weighted* statement

`|SG α g z θ τ - SG α g z θ τ'| ≤ Nt · z · |τ - τ'|^α`   (`0 ≤ z`),

i.e. the modulus is priced by a factor `z` vanishing at the axis `z = 0`.  This is exactly the
weight needed when the modulus is consumed inside a `z`-integral at the origin (the slots of
`L12`/`FK` carry the radial weight `w(z) = (1+z)²/z²`, so an unweighted modulus loses an integrable
factor).

The proof is the same three-step reduction as in `SG_tau_mod`:

* the weighted interior trade-off `RXR5.Pieces.mixed_slice_tau_modulus` at slot `(b,a) = (0,0)`
  turns the `ℋ⁴`-Lipschitz clause of `LimApprox` into
  `|g z θ τ - g z θ τ'| ≤ L · (z^{3/2}/(1+z)²) · |τ - τ'|` on the open quadrant;
* **the new ingredient** is `sliceW_le_z`: the interior weight is dominated by `z` itself, so the
  bound becomes `≤ L · z · |τ - τ'|` — this is what upgrades the *weight* from `z^{3/2}/(1+z)²`
  (`≤ 1`, the `SG_tau_mod` version) to `z`;
* on the horizon `[0,S]` the distance is dominated by `(S+1)·|τ - τ'|^α` (`tauDist_le_rpow`), which
  upgrades the Lipschitz bound to the weighted `α`-Hölder bound with constant `L·(S+1)`;
* on the two angular edges `θ = 0`, `θ = π/2` both values vanish identically by the
  `RegPkgMin.vanish` clause of `DynOK'`, and on the closed half-plane `z = 0` (the only place with
  `¬ 0 < z` and `0 ≤ z`) the sanitised family vanishes by `SG_apply_of_nonpos`, so both sides are
  `0` there — this is precisely why the weighted claim is *not* false for `z = 0`.
-/

namespace Work.FTS_RegExport.RXR5L.L12fAux

open scoped Real Topology
open Set Filter

/-- The radial weight `z^{3/2}/(1+z)²` of the weighted interior trade-off is dominated by `z`
itself: `z^{3/2}/(1+z)² ≤ z` for `z > 0`.  (For `0 < z ≤ 1` it is `z^{3/2} ≤ z`; for `z ≥ 1` it is
`z^{3/2} ≤ z² ≤ z(1+z)²`.) -/
lemma sliceW_le_z {z : ℝ} (hz : 0 < z) : z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2 ≤ z := by
  have h2 : 0 < (1 + z) ^ 2 := by positivity
  rw [div_le_iff₀ h2]
  have hsq : (1 : ℝ) ≤ (1 + z) ^ 2 := by nlinarith [sq_nonneg z, hz.le]
  rcases le_or_gt z 1 with hz1 | hz1
  · have hb : z ^ ((3 : ℝ) / 2) ≤ z := by
      have h := Real.rpow_le_rpow_of_exponent_ge hz hz1 (by norm_num : (1 : ℝ) ≤ (3 : ℝ) / 2)
      simpa using h
    nlinarith [hb, hsq, hz.le]
  · have hb : z ^ ((3 : ℝ) / 2) ≤ z ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hz1.le (by norm_num : (3 : ℝ) / 2 ≤ (2 : ℝ))
    rw [Real.rpow_two] at hb
    nlinarith [hb, hsq, hz.le]

/-- On `[0,S]` the distance of two points is dominated by `(S+1)·(distance)^α` for `0 < α ≤ 1`:
for small distances `t ≤ t^α`, for large ones `t^α ≥ 1` while `t ≤ S`. -/
lemma tauDist_le_rpow {α S t : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hS : 0 < S) (ht0 : 0 ≤ t)
    (htS : t ≤ S) : t ≤ (S + 1) * t ^ α := by
  rcases lt_or_ge t 1 with h1 | h1
  · have hle : t ≤ t ^ α := by
      rcases eq_or_lt_of_le ht0 with h0 | h0
      · rw [← h0]; simp [Real.zero_rpow (ne_of_gt hα)]
      · have h2 := Real.rpow_le_rpow_of_exponent_ge h0 h1.le hα1
        rwa [Real.rpow_one] at h2
    have hr : 0 ≤ t ^ α := Real.rpow_nonneg ht0 _
    nlinarith [hle, hr, hS]
  · have hle : (1 : ℝ) ≤ t ^ α := Real.one_le_rpow h1 (le_of_lt hα)
    nlinarith [hle, htS, hS]

theorem SG_tau_mod_weighted {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S) :
    ∃ Nt : ℝ, 0 ≤ Nt ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
      ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 ≤ z →
        |Work.FTS_RegExport.RXR5.SG α g z θ τ - Work.FTS_RegExport.RXR5.SG α g z θ τ'|
          ≤ Nt * z * |τ - τ'| ^ α := by
  have hDyn : Work.FTS.Final.DynOK (Work.FTS.Regularity.pExp α) C₀ g := hOK.1
  have hLim : Work.FTS.FinalV2.LimApprox (Work.FTS.Regularity.pExp α) C₀ Φs E g := hOK.2
  obtain ⟨L, hL0, hL⟩ :=
    Work.FTS_RegExport.RXR5.Pieces.mixed_slice_tau_modulus hLim
      (Work.FTS.Regularity.pExp_pos hα) (Work.FTS.Regularity.pExp_le_one hα13) S hS
  refine ⟨L * (S + 1), mul_nonneg hL0 (by linarith), ?_⟩
  intro τ hτ τ' hτ' θ hθ z hz
  have hτ0 : 0 ≤ τ := hτ.1
  have hτ'0 : 0 ≤ τ' := hτ'.1
  have hnn : 0 ≤ L * (S + 1) * z * |τ - τ'| ^ α :=
    mul_nonneg (mul_nonneg (mul_nonneg hL0 (by linarith)) hz)
      (Real.rpow_nonneg (abs_nonneg _) _)
  rcases lt_or_ge 0 z with hzpos | hznp
  · have hSGτ : Work.FTS_RegExport.RXR5.SG α g z θ τ = g z θ τ := by
      rw [Work.FTS_RegExport.RXR5.SG_apply_of_pos hzpos hθ.1 hθ.2,
        Work.FTS.FinalV2.tauExt_of_nonneg g hτ0]
    have hSGτ' : Work.FTS_RegExport.RXR5.SG α g z θ τ' = g z θ τ' := by
      rw [Work.FTS_RegExport.RXR5.SG_apply_of_pos hzpos hθ.1 hθ.2,
        Work.FTS.FinalV2.tauExt_of_nonneg g hτ'0]
    rw [hSGτ, hSGτ']
    rcases eq_or_lt_of_le hθ.1 with hθ0 | hθpos
    · obtain ⟨hv, -⟩ := hDyn.1.vanish τ hτ0 z hz
      obtain ⟨hv', -⟩ := hDyn.1.vanish τ' hτ'0 z hz
      rw [← hθ0, hv, hv', sub_self, abs_zero]
      exact hnn
    · rcases eq_or_lt_of_le hθ.2 with hθ2 | hθlt
      · obtain ⟨-, hv⟩ := hDyn.1.vanish τ hτ0 z hz
        obtain ⟨-, hv'⟩ := hDyn.1.vanish τ' hτ'0 z hz
        rw [hθ2, hv, hv', sub_self, abs_zero]
        exact hnn
      · -- open quadrant: the weighted Lipschitz bound, then `weight ≤ z`, then `τ`-length
        have hb := hL τ hτ τ' hτ' 0 0 (by norm_num) z θ hzpos hθpos hθlt
        have htz : |τ - τ'| ≤ S :=
          abs_sub_le_iff.mpr ⟨by linarith [hτ.1, hτ.2, hτ'.1, hτ'.2],
            by linarith [hτ.1, hτ.2, hτ'.1, hτ'.2]⟩
        have hself : |τ - τ'| ≤ (S + 1) * |τ - τ'| ^ α :=
          tauDist_le_rpow (t := |τ - τ'|) (S := S) hα (by linarith) hS (abs_nonneg _) htz
        calc |g z θ τ - g z θ τ'|
            = |Work.Spaces.mixed 0 0 (Work.FTS.Galerkin.slice g τ) z θ
                - Work.Spaces.mixed 0 0 (Work.FTS.Galerkin.slice g τ') z θ| := rfl
          _ ≤ L * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) * |τ - τ'| := hb
          _ ≤ L * z * |τ - τ'| := by
              refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
              exact mul_le_mul_of_nonneg_left (sliceW_le_z hzpos) hL0
          _ ≤ L * z * ((S + 1) * |τ - τ'| ^ α) :=
              mul_le_mul_of_nonneg_left hself (mul_nonneg hL0 hzpos.le)
          _ = L * (S + 1) * z * |τ - τ'| ^ α := by ring
  · -- `z = 0` (the only point with `0 ≤ z` and `¬ 0 < z`): both values vanish
    have hz0 : z = 0 := le_antisymm hznp hz
    rw [hz0,
      Work.FTS_RegExport.RXR5.SG_apply_of_nonpos (α := α) (θ := θ) (τ := τ) (z := 0) le_rfl,
      Work.FTS_RegExport.RXR5.SG_apply_of_nonpos (α := α) (θ := θ) (τ := τ') (z := 0) le_rfl,
      sub_self, abs_zero]
    simp

end Work.FTS_RegExport.RXR5L.L12fAux
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR5L.NsData_C1Jet =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXR5L

set_option autoImplicit false

theorem NsData_C1Jet {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S)
    (hSt1 : Work.FTS.RegPkgGal.St1Class α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)))
    (hO1 : ∃ N₂ N₃ : ℝ, 0 ≤ N₂ ∧ 0 ≤ N₃ ∧
      Work.FTS.RegPkgGal.C1Jet α S N₂
        (fun z θ τ => Work.Spaces.Dz (fun z θ => Work.FTS_RegExport.RXR5.SG α g z θ τ) z θ) ∧
      Work.FTS.RegPkgGal.C1Jet α S N₃
        (fun z θ τ => Work.Spaces.Dth (fun z θ => Work.FTS_RegExport.RXR5.SG α g z θ τ) z θ))
    (hMuB : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc (0:ℝ) S,
      |Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SΨ α Φs E g)
          (Work.FTS_RegExport.RXR5.SG α g) τ| ≤ M ∧
      |Work.FTS.Galerkin.lamDyn (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SΨ α Φs E g)
          (Work.FTS_RegExport.RXR5.SG α g) τ| ≤ M)
    (hMuH : ∃ L : ℝ, 0 ≤ L ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
      |Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SΨ α Φs E g)
          (Work.FTS_RegExport.RXR5.SG α g) τ
        - Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SΨ α Φs E g)
          (Work.FTS_RegExport.RXR5.SG α g) τ'| ≤ L * |τ - τ'| ^ α ∧
      |Work.FTS.Galerkin.lamDyn (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SΨ α Φs E g)
          (Work.FTS_RegExport.RXR5.SG α g) τ
        - Work.FTS.Galerkin.lamDyn (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SΨ α Φs E g)
          (Work.FTS_RegExport.RXR5.SG α g) τ'| ≤ L * |τ - τ'| ^ α) :
    ∃ N₁ : ℝ, 0 ≤ N₁ ∧
      Work.FTS.Regularity.Jet α S N₁ (fun z θ τ => Work.Construction.Nstar
        (Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SΨ α Φs E g)
          (Work.FTS_RegExport.RXR5.SG α g) τ)
        (Work.FTS.Galerkin.lamDyn (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SΨ α Φs E g)
          (Work.FTS_RegExport.RXR5.SG α g) τ)
        (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SG α g) τ) z θ) ∧
      ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0:ℝ),
        ∃ d : ℝ, HasDerivAt (fun z' => Work.Construction.Nstar
          (Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
            (Work.FTS_RegExport.RXR5.SΨ α Φs E g) (Work.FTS_RegExport.RXR5.SG α g) τ)
          (Work.FTS.Galerkin.lamDyn (Work.FTS.Regularity.pExp α)
            (Work.FTS_RegExport.RXR5.SΨ α Φs E g) (Work.FTS_RegExport.RXR5.SG α g) τ)
          (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SG α g) τ) z' θ) d z ∧
          |d| ≤ N₁ := by
  obtain ⟨N₂, N₃, hN₂0, hN₃0, hC1₂, hC1₃⟩ := hO1
  obtain ⟨NG, hNG0, hC1G⟩ := SG_C1Jet hα hα13 hOK hS hSt1
  obtain ⟨M, hM0, hMB⟩ := hMuB
  obtain ⟨L, hL0, hLH⟩ := hMuH
  -- the two `Jet`-slots on a common constant `max NG N₂`
  have hJGN : Work.FTS.Regularity.Jet α S (max NG N₂) (Work.FTS_RegExport.RXR5.SG α g) :=
    Jet_mono hC1G.1 (le_max_left NG N₂)
  have hJZN : Work.FTS.Regularity.Jet α S (max NG N₂)
      (fun z θ τ => Work.Spaces.Dz (fun z θ => Work.FTS_RegExport.RXR5.SG α g z θ τ) z θ) :=
    Jet_mono hC1₂.1 (le_max_right NG N₂)
  -- the two `z`-derivative slots on the same constant
  have hDG : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0:ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => Work.FTS_RegExport.RXR5.SG α g z' θ τ) d z ∧
        |d| ≤ max NG N₂ := by
    intro τ hτ θ hθ z hz
    obtain ⟨d, hd, hb⟩ := hC1G.2 τ hτ θ hθ z hz
    exact ⟨d, hd, le_trans hb (le_max_left NG N₂)⟩
  have hDZ : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0:ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => Work.Spaces.Dz
          (fun z θ => Work.FTS_RegExport.RXR5.SG α g z θ τ) z' θ) d z ∧
        |d| ≤ max NG N₂ := by
    intro τ hτ θ hθ z hz
    obtain ⟨d, hd, hb⟩ := hC1₂.2 τ hτ θ hθ z hz
    exact ⟨d, hd, le_trans hb (le_max_right NG N₂)⟩
  -- the clock bounds on the common constant `max M L`
  have hmuB : ∀ τ ∈ Set.Icc (0:ℝ) S,
      |Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SΨ α Φs E g)
        (Work.FTS_RegExport.RXR5.SG α g) τ| ≤ max M L :=
    fun τ hτ => le_trans (hMB τ hτ).1 (le_max_left M L)
  have hlamB : ∀ τ ∈ Set.Icc (0:ℝ) S,
      |Work.FTS.Galerkin.lamDyn (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SΨ α Φs E g)
        (Work.FTS_RegExport.RXR5.SG α g) τ| ≤ max M L :=
    fun τ hτ => le_trans (hMB τ hτ).2 (le_max_left M L)
  have hMuhH : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
      |Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SΨ α Φs E g)
          (Work.FTS_RegExport.RXR5.SG α g) τ
        - Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
            (Work.FTS_RegExport.RXR5.SΨ α Φs E g) (Work.FTS_RegExport.RXR5.SG α g) τ'|
        ≤ max M L * |τ - τ'| ^ α :=
    fun τ hτ τ' hτ' => le_trans (hLH τ hτ τ' hτ').1
      (mul_le_mul_of_nonneg_right (le_max_right M L) (Real.rpow_nonneg (abs_nonneg _) α))
  have hLamhH : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
      |Work.FTS.Galerkin.lamDyn (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SΨ α Φs E g)
          (Work.FTS_RegExport.RXR5.SG α g) τ
        - Work.FTS.Galerkin.lamDyn (Work.FTS.Regularity.pExp α)
            (Work.FTS_RegExport.RXR5.SΨ α Φs E g) (Work.FTS_RegExport.RXR5.SG α g) τ'|
        ≤ max M L * |τ - τ'| ^ α :=
    fun τ hτ τ' hτ' => le_trans (hLH τ hτ τ' hτ').2
      (mul_le_mul_of_nonneg_right (le_max_right M L) (Real.rpow_nonneg (abs_nonneg _) α))
  -- the clock data in the shape `jet_Nstar` / `zderiv_Nstar` consume
  have hmuPair : 0 ≤ max M L ∧ ∀ τ ∈ Set.Icc (0:ℝ) S,
      |Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SΨ α Φs E g)
          (Work.FTS_RegExport.RXR5.SG α g) τ| ≤ max M L ∧
      ∀ τ' ∈ Set.Icc (0:ℝ) S,
        |Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
            (Work.FTS_RegExport.RXR5.SΨ α Φs E g) (Work.FTS_RegExport.RXR5.SG α g) τ
          - Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
            (Work.FTS_RegExport.RXR5.SΨ α Φs E g) (Work.FTS_RegExport.RXR5.SG α g) τ'|
          ≤ max M L * |τ - τ'| ^ α :=
    ⟨le_trans hM0 (le_max_left M L), fun τ hτ => ⟨hmuB τ hτ, hMuhH τ hτ⟩⟩
  have hlamPair : ∀ τ ∈ Set.Icc (0:ℝ) S,
      |Work.FTS.Galerkin.lamDyn (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SΨ α Φs E g)
          (Work.FTS_RegExport.RXR5.SG α g) τ| ≤ max M L ∧
      ∀ τ' ∈ Set.Icc (0:ℝ) S,
        |Work.FTS.Galerkin.lamDyn (Work.FTS.Regularity.pExp α)
            (Work.FTS_RegExport.RXR5.SΨ α Φs E g) (Work.FTS_RegExport.RXR5.SG α g) τ
          - Work.FTS.Galerkin.lamDyn (Work.FTS.Regularity.pExp α)
            (Work.FTS_RegExport.RXR5.SΨ α Φs E g) (Work.FTS_RegExport.RXR5.SG α g) τ'|
          ≤ max M L * |τ - τ'| ^ α :=
    fun τ hτ => ⟨hlamB τ hτ, hLamhH τ hτ⟩
  -- the two library lemmas at the sanitised family and the dynamic clocks
  obtain ⟨Nj, hJet⟩ := Work.FTS.RegPkgGal.Der.jet_Nstar (α := α) (S := S)
    (g := Work.FTS_RegExport.RXR5.SG α g)
    (mu := fun τ => Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
      (Work.FTS_RegExport.RXR5.SΨ α Φs E g) (Work.FTS_RegExport.RXR5.SG α g) τ)
    (lam := fun τ => Work.FTS.Galerkin.lamDyn (Work.FTS.Regularity.pExp α)
      (Work.FTS_RegExport.RXR5.SΨ α Φs E g) (Work.FTS_RegExport.RXR5.SG α g) τ)
    (N := max NG N₂) (Nmu := max M L) hα hS hJGN hJZN hmuPair hlamPair
  obtain ⟨Nz, hNz0, hZderiv⟩ := Work.FTS.RegPkgGal.Der.zderiv_Nstar (α := α) (S := S)
    (g := Work.FTS_RegExport.RXR5.SG α g)
    (mu := fun τ => Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
      (Work.FTS_RegExport.RXR5.SΨ α Φs E g) (Work.FTS_RegExport.RXR5.SG α g) τ)
    (lam := fun τ => Work.FTS.Galerkin.lamDyn (Work.FTS.Regularity.pExp α)
      (Work.FTS_RegExport.RXR5.SΨ α Φs E g) (Work.FTS_RegExport.RXR5.SG α g) τ)
    (N := max NG N₂) (Nmu := max M L) hα hS hDG hDZ
    ⟨le_trans hM0 (le_max_left M L), hmuB⟩ hlamB
  refine ⟨max Nj Nz, le_trans hJet.1 (le_max_left Nj Nz), ?_, ?_⟩
  · refine Work.FTS.Regularity.Jet.congr (Jet_mono hJet (le_max_left Nj Nz)) ?_
    intro z θ τ _ _ _
    rfl
  · intro τ hτ θ hθ z hz
    obtain ⟨d, hd, hb⟩ := hZderiv τ hτ θ hθ z hz
    exact ⟨d, hd, le_trans hb (le_max_right Nj Nz)⟩

end Work.FTS_RegExport.RXR5L
end
-- ===== merged: Submission.Work.FTS_RegExport.Vz7Wire =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.Vz7Wire` — `vz0` for the wire family from TWO quantitative clauses

`Vz7Split.lean` reduces the frozen field `VelPkg.vz0` to the sharp identity

    Vz7 = (1 − μτ) + 2·αG·V(Φ̃_*) + (2·αG/(1+z))·c2m(θ) + 2·αG·V(u),    u = E (slice (tauExt g) τ),

together with the criterion `4αG + 2·Cs·αG² + 2·CE·αG² ≤ 1/2` for the two slot bounds
`|V(Φ̃_*)| ≤ Cs·αG`, `|V(u)| ≤ CE·αG`.  This file proves the missing *step structure* for the
concrete family `Φ = psiR α Φs E (tauExt g)`, `G = gS α (tauExt g)`:

* `vz7_eq_of_phiTil` — the *closed form of `Vz7`* (`Vz7 = (1−μτ) + 2·αG·V(slice Φ τ)`) proved
  **directly from the defining formula**, with **no** integrability/continuity hypotheses on
  `L₁₂dens` (unlike `RXDiag.closedFormOpen`, whose `hint`/`hcont` are only needed for the `cs7`
  half): the `Θ`-part is absorbed by the exact identity `2αG·V(Θ αG F) = L₁₂(F)·c2m`;
* `vop_slice_eq_star_add_E_q` — the sharp split in its **quadrant-restricted** form (the form in
  which it applies to `psiR`, which agrees with `PsiCan` only on the open quadrant), via the
  proved congruence `Work.FTS.GalFields.RHS.Sharp.Vop_congr_Q0`;
* `vz7_nonneg_wire` — **`vz0` for the wire family**, i.e. the pointwise sign condition
  `0 ≤ Vz7 αG μ G Φ z θ τ` for every `τ ≥ 0` and every point of the open quadrant, from exactly:
  the star slot (`hVstar`; *derivable* from the frozen `hStar.VW` by
  `Vz7Split.starVop_pointwise_le`), the `E`-slot (`hVeu`) and the tie (`htie`), plus the
  differentiability data of the three `θ`-slices;
* `vz7_nonneg_wire_of_star` — the same with the star slot **discharged from `StarPkgo2.VW`**.

So the whole remaining content of `vz0` is the two quantitative clauses

    hVeu : ∀ τ z θ, 0 ≤ τ → quadrant → |V(E (slice (tauExt g) τ)) z θ| ≤ CE·αG      (E-slot)
    htie : 4·αG + 2·Cs·αG² + 2·CE·αG² ≤ 1/2                                        (the tie)

— both *satisfiable* by the construction (the E-slot is the elliptic `V`-slot of `EllPkgK` with
its `αG`-factor kept; the tie holds whenever `αG ≲ 1/8` and the two constants are not
astronomically large, which is exactly what the wire's `Inputs'`-style normalisations give), and
neither equivalent to `vz0`.  See `NOTES_FINAL.md` §18–§20.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## 1. The closed form of `Vz7`, from the definition only -/

/-- **`Vz7 = (1 − μτ) + 2·αG·V(slice Φ τ)`**, proved directly from the defining formula of `Vz7`
(`(1−μ) + L₁₂(F_τ)·c2m + 2αG·V(Φ̃_τ)`) by absorbing the `Θ`-part with the identity
`2αG·V(Θ αG F) = L₁₂(F)·c2m`.  No integrability or continuity hypothesis on `L₁₂dens` is used —
only the differentiability of the `θ`-slice of `slice Φ τ`. -/
theorem vz7_eq_of_phiTil {αG : ℝ} (hαG : 0 < αG) {μ : ℝ → ℝ} {G Φ : Fam} {τ z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2)
    (hdΦ : DifferentiableAt ℝ (fun θ' => slice Φ τ z θ') θ) :
    Work.FTS.RegExportIface.Vz7 αG μ G Φ z θ τ
      = (1 - μ τ) + 2 * αG * Work.Construction.Vop (slice Φ τ) z θ := by
  -- `phiTil = slice Φ τ − Θ(F_τ)` has a differentiable `θ`-slice
  have hdΘ : DifferentiableAt ℝ
      (fun θ' => Work.Construction.Theta αG (Work.Construction.Ftau αG G τ) z θ') θ :=
    differentiableAt_thetaslice_Theta z θ
  have hdTil : DifferentiableAt ℝ
      (fun θ' => Work.FTS.RegExportIface.phiTil αG G Φ τ z θ') θ := by
    show DifferentiableAt ℝ (fun θ' => Work.Construction.PhiTil αG
      (Work.Construction.Ftau αG G τ) (slice Φ τ) z θ') θ
    simp only [Work.Construction.PhiTil]
    exact hdΦ.sub hdΘ
  -- the additive split `V(Φ) = V(Φ̃) + V(Θ)`
  have hadd := Vop_add_point (A := Work.FTS.RegExportIface.phiTil αG G Φ τ)
    (B := Work.Construction.Theta αG (Work.Construction.Ftau αG G τ)) hdTil hdΘ
  -- the `Θ`-identity
  have hVΘ := two_mul_Vop_Theta (αG := αG) hαG (F := Work.Construction.Ftau αG G τ)
    (z := z) (θ := θ) hθ hθ2
  -- `V(slice Φ τ) = V(Φ̃) + V(Θ)` by the quadrant congruence
  have hcongr : Work.Construction.Vop (slice Φ τ) z θ
      = Work.Construction.Vop (fun z θ => Work.FTS.RegExportIface.phiTil αG G Φ τ z θ
          + Work.Construction.Theta αG (Work.Construction.Ftau αG G τ) z θ) z θ := by
    refine Work.FTS.GalFields.RHS.Sharp.Vop_congr_Q0 ?_ z θ hz hθ hθ2
    intro z θ hz hθ hθ2
    simp only [Work.FTS.RegExportIface.phiTil, Work.Construction.PhiTil]
    ring
  -- assemble
  have hkey : 2 * αG * Work.Construction.Vop (slice Φ τ) z θ
      = 2 * αG * Work.Construction.Vop (Work.FTS.RegExportIface.phiTil αG G Φ τ) z θ
        + Work.Construction.L12 (Work.Construction.Ftau αG G τ) z * Work.Construction.c2m θ := by
    rw [hcongr, hadd]
    linear_combination hVΘ
  show (1 - μ τ) + Work.Construction.L12 (Work.Construction.Ftau αG G τ) z
      * Work.Construction.c2m θ
      + 2 * αG * Work.Construction.Vop (Work.FTS.RegExportIface.phiTil αG G Φ τ) z θ
    = (1 - μ τ) + 2 * αG * Work.Construction.Vop (slice Φ τ) z θ
  linarith [hkey]

/-! ## 2. The sharp split, quadrant-restricted -/

/-- **The sharp split on the open quadrant.**  If `Φ = Φs + E u` pointwise on the quadrant and the
two `θ`-slices are differentiable there, then

    V(Φ) = V(Φ̃_*) + c2m(θ)/(1+z) + V(E u),      Φ̃_* = Φs − Θ(F_*).

This is the form that applies to `Φ = slice (psiR α Φs E G) τ`, for which the pointwise identity
holds only on the open quadrant (`psiR_of_mem`). -/
theorem vop_slice_eq_star_add_E_q {αG : ℝ} (hαG : 0 < αG) (hαG1 : αG ≤ 1)
    {Φs : Fn} {E : Fn → Fn} {u Φ : Fn} {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ)
    (hθ2 : θ < Real.pi / 2)
    (hslice : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → Φ z θ = Φs z θ + E u z θ)
    (hdΦs : DifferentiableAt ℝ (fun θ' => Φs z θ') θ)
    (hdE : DifferentiableAt ℝ (fun θ' => E u z θ') θ) :
    Work.Construction.Vop Φ z θ
      = Work.Construction.Vop
          (Work.Construction.PhiTil αG (Work.Construction.Fstar αG) Φs) z θ
        + Work.Construction.c2m θ / (1 + z)
        + Work.Construction.Vop (E u) z θ := by
  -- `Φ` agrees on the quadrant with `(Φ̃_* + Θ(F_*)) + E u`
  have hcongr : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Φ z θ = (Work.Construction.PhiTil αG (Work.Construction.Fstar αG) Φs z θ
        + Work.Construction.Theta αG (Work.Construction.Fstar αG) z θ) + E u z θ := by
    intro z θ hz hθ hθ2
    rw [hslice z θ hz hθ hθ2]
    simp only [Work.Construction.PhiTil]
    ring
  rw [Work.FTS.GalFields.RHS.Sharp.Vop_congr_Q0 hcongr z θ hz hθ hθ2]
  -- differentiability of the three `θ`-slices
  have hdΘs : DifferentiableAt ℝ
      (fun θ' => Work.Construction.Theta αG (Work.Construction.Fstar αG) z θ') θ :=
    differentiableAt_thetaslice_Theta z θ
  have hdTil : DifferentiableAt ℝ
      (fun θ' => Work.Construction.PhiTil αG (Work.Construction.Fstar αG) Φs z θ') θ := by
    simp only [Work.Construction.PhiTil]
    exact hdΦs.sub hdΘs
  have hdSum : DifferentiableAt ℝ
      (fun θ' => (Work.Construction.PhiTil αG (Work.Construction.Fstar αG) Φs z θ'
        + Work.Construction.Theta αG (Work.Construction.Fstar αG) z θ')) θ :=
    hdTil.add hdΘs
  have hV1 := Vop_add_point (A := fun z θ => Work.Construction.PhiTil αG
      (Work.Construction.Fstar αG) Φs z θ
      + Work.Construction.Theta αG (Work.Construction.Fstar αG) z θ) (B := E u) hdSum hdE
  have hV2 := Vop_add_point (A := Work.Construction.PhiTil αG (Work.Construction.Fstar αG) Φs)
    (B := Work.Construction.Theta αG (Work.Construction.Fstar αG)) hdTil hdΘs
  -- the `Θ`-identity, divided by `2 αG`
  have hVΘ := two_mul_Vop_Theta (αG := αG) hαG (F := Work.Construction.Fstar αG)
    (z := z) (θ := θ) hθ hθ2
  rw [Work.Construction.L12_Fstar_eq (α := αG) hαG hαG1 hz.le] at hVΘ
  have hVΘ' : Work.Construction.Vop
        (Work.Construction.Theta αG (Work.Construction.Fstar αG)) z θ
      = Work.Construction.c2m θ / (1 + z) := by
    have h3 : 2 * αG * Work.Construction.Vop
          (Work.Construction.Theta αG (Work.Construction.Fstar αG)) z θ
        = 2 * αG * (Work.Construction.c2m θ / (1 + z)) := by
      rw [hVΘ]
      field_simp
    exact mul_left_cancel₀ (by positivity : (2 : ℝ) * αG ≠ 0) h3
  rw [hV1, hV2, hVΘ']

/-! ## 3. `vz0` for the wire family from the two quantitative clauses -/

/-- **`vz0` for the wire family.**  For `Φ = psiR α Φs E (tauExt g)` (so that
`slice Φ τ = Φs + E (slice (tauExt g) τ)` on the open quadrant) and any clock `μ` with
`|μ τ| ≤ 1/2`, the sign condition `0 ≤ Vz7 αG μ G Φ z θ τ` holds for **every** `τ ≥ 0` and every
point of the open quadrant, from the two quantitative clauses

* `hVstar : |V(Φ̃_*)| ≤ Cs·αG` (the star slot — provable from the frozen `hStar.VW`, see
  `vz7_nonneg_wire_of_star`),
* `hVeu : |V(u τ)| ≤ CE·αG` (the elliptic slot, with its `αG` factor kept),

together with the tie `4·αG + 2·Cs·αG² + 2·CE·αG² ≤ 1/2`. -/
theorem vz7_nonneg_wire {αG Cs CE : ℝ} (hαG : 0 < αG) (hαG1 : αG ≤ 1)
    {μ : ℝ → ℝ} {G Φ : Fam} {Φs : Fn} {u : ℝ → Fn}
    (hmu : ∀ τ : ℝ, 0 ≤ τ → |μ τ| ≤ 1 / 2)
    (hslice : ∀ τ z θ : ℝ, 0 ≤ τ → 0 < z → 0 < θ → θ < Real.pi / 2 →
      slice Φ τ z θ = Φs z θ + u τ z θ)
    (hdΦ : ∀ τ z θ : ℝ, 0 ≤ τ → 0 < z → 0 < θ → θ < Real.pi / 2 →
      DifferentiableAt ℝ (fun θ' => slice Φ τ z θ') θ)
    (hdΦs : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      DifferentiableAt ℝ (fun θ' => Φs z θ') θ)
    (hdu : ∀ τ z θ : ℝ, 0 ≤ τ → 0 < z → 0 < θ → θ < Real.pi / 2 →
      DifferentiableAt ℝ (fun θ' => u τ z θ') θ)
    (hVstar : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Construction.Vop
        (Work.Construction.PhiTil αG (Work.Construction.Fstar αG) Φs) z θ| ≤ Cs * αG)
    (hVeu : ∀ τ z θ : ℝ, 0 ≤ τ → 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Construction.Vop (u τ) z θ| ≤ CE * αG)
    (htie : 4 * αG + 2 * Cs * αG ^ 2 + 2 * CE * αG ^ 2 ≤ 1 / 2) :
    ∀ τ z θ : ℝ, 0 ≤ τ → 0 < z → 0 < θ → θ < Real.pi / 2 →
      0 ≤ Work.FTS.RegExportIface.Vz7 αG μ G Φ z θ τ := by
  intro τ z θ hτ hz hθ hθ2
  -- the closed form at `(z,θ,τ)`
  have hclosed := vz7_eq_of_phiTil (αG := αG) hαG (μ := μ) (G := G) (Φ := Φ) (τ := τ)
    hz hθ hθ2 (hdΦ τ z θ hτ hz hθ hθ2)
  -- the sharp split at `(z,θ,τ)`
  have hsplit := vop_slice_eq_star_add_E_q (αG := αG) hαG hαG1 (Φs := Φs)
    (E := fun _ : Fn => u τ) (u := 0) (Φ := slice Φ τ) (z := z) (θ := θ) hz hθ hθ2
    (fun a b ha hb hb2 => by
      rw [hslice τ a b hτ ha hb hb2])
    (hdΦs z θ hz hθ hθ2) (hdu τ z θ hτ hz hθ hθ2)
  exact vz7_nonneg_of_sharp (αG := αG) hαG hz (hmu τ hτ) hsplit
    (hVstar z θ hz hθ hθ2) (hVeu τ z θ hτ hz hθ hθ2) hclosed htie

/-- **The same, with the star slot discharged from the frozen `StarPkgo2.VW`.**  The hypotheses are
those of `velPkg` for the star part, the `E`-slot clause, the tie, and the differentiability data. -/
theorem vz7_nonneg_wire_of_star {αG Cs CE : ℝ} (hαG : 0 < αG) (hαG1 : αG ≤ 1)
    {μ : ℝ → ℝ} {G Φ : Fam} {Φs : Fn} {u : ℝ → Fn}
    (hVWmem : Work.Spaces.WlInfMem αG 4 (Work.Construction.Vop
      (Work.Construction.PhiTil αG (Work.Construction.Fstar αG) Φs)))
    (hVWbnd : Work.Spaces.WlInf αG 4 (Work.Construction.Vop
      (Work.Construction.PhiTil αG (Work.Construction.Fstar αG) Φs)) ≤ Cs * αG)
    (hmu : ∀ τ : ℝ, 0 ≤ τ → |μ τ| ≤ 1 / 2)
    (hslice : ∀ τ z θ : ℝ, 0 ≤ τ → 0 < z → 0 < θ → θ < Real.pi / 2 →
      slice Φ τ z θ = Φs z θ + u τ z θ)
    (hdΦ : ∀ τ z θ : ℝ, 0 ≤ τ → 0 < z → 0 < θ → θ < Real.pi / 2 →
      DifferentiableAt ℝ (fun θ' => slice Φ τ z θ') θ)
    (hdΦs : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      DifferentiableAt ℝ (fun θ' => Φs z θ') θ)
    (hdu : ∀ τ z θ : ℝ, 0 ≤ τ → 0 < z → 0 < θ → θ < Real.pi / 2 →
      DifferentiableAt ℝ (fun θ' => u τ z θ') θ)
    (hVeu : ∀ τ z θ : ℝ, 0 ≤ τ → 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Construction.Vop (u τ) z θ| ≤ CE * αG)
    (htie : 4 * αG + 2 * Cs * αG ^ 2 + 2 * CE * αG ^ 2 ≤ 1 / 2) :
    ∀ τ z θ : ℝ, 0 ≤ τ → 0 < z → 0 < θ → θ < Real.pi / 2 →
      0 ≤ Work.FTS.RegExportIface.Vz7 αG μ G Φ z θ τ :=
  vz7_nonneg_wire (αG := αG) (Cs := Cs) (CE := CE) hαG hαG1 hmu hslice hdΦ hdΦs hdu
    (starVop_pointwise_le hVWmem hVWbnd) hVeu htie

end Work.FTS_RegExport
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.Inputs.ftau_Dz_cont =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_StreamBdry.Inputs

set_option autoImplicit false

/-! ## §0 A Hölder function of `(z,θ)` (for the metric `|Δz| + |Δθ|`) is continuous -/

/-- **Continuity from a joint `a`-Hölder bound of the sum metric.**  If `|f z θ - f z' θ'|` is
dominated by `N·(|z-z'| + |θ-θ'|)^a` — exactly the shape of the `(z,θ)`-half of
`Work.FTS.Regularity.Jet` — then `f` is continuous on the closed angular strip. -/
theorem contOn_of_holder2 {N a : ℝ} (hN : 0 ≤ N) (ha : 0 < a) {f : ℝ → ℝ → ℝ}
    (h : ∀ z z' θ θ', 0 ≤ z → 0 ≤ z' → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
      |f z θ - f z' θ'| ≤ N * (|z - z'| + |θ - θ'|) ^ a) :
    ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := by
  refine Metric.continuousOn_iff.2 fun b hb ε hε => ?_
  obtain ⟨hbz, hbθ⟩ := hb
  have hN1 : (0 : ℝ) < N + 1 := by linarith
  have hpos : (0 : ℝ) < ε / (2 ^ a * (N + 1)) := by positivity
  set δ : ℝ := (ε / (2 ^ a * (N + 1))) ^ (1 / a) with hδ
  have hδpos : 0 < δ := Real.rpow_pos_of_pos hpos _
  refine ⟨δ, hδpos, fun q hq hdist => ?_⟩
  obtain ⟨hqz, hqθ⟩ := hq
  have hmain := h q.1 b.1 q.2 b.2 (le_of_lt hqz) (le_of_lt hbz) hqθ hbθ
  have hdist' : dist q b < δ := hdist
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq] at hdist'
  have h1 : |q.1 - b.1| < δ := lt_of_le_of_lt (le_max_left _ _) hdist'
  have h2 : |q.2 - b.2| < δ := lt_of_le_of_lt (le_max_right _ _) hdist'
  have hsum_lt : |q.1 - b.1| + |q.2 - b.2| < 2 * δ := by linarith
  have hsum_nonneg : 0 ≤ |q.1 - b.1| + |q.2 - b.2| := by positivity
  have hrpow : (|q.1 - b.1| + |q.2 - b.2|) ^ a ≤ (2 * δ) ^ a :=
    Real.rpow_le_rpow hsum_nonneg (le_of_lt hsum_lt) ha.le
  have hmul : (2 * δ) ^ a = 2 ^ a * δ ^ a := Real.mul_rpow (by norm_num) hδpos.le
  have hδa : δ ^ a = ε / (2 ^ a * (N + 1)) := by
    rw [hδ, ← Real.rpow_mul hpos.le]
    have hone : 1 / a * a = 1 := by
      rw [one_div, inv_mul_cancel₀ (ne_of_gt ha)]
    rw [hone, Real.rpow_one]
  have hstep : N * (|q.1 - b.1| + |q.2 - b.2|) ^ a ≤ N * (2 ^ a * δ ^ a) := by
    rw [hmul] at hrpow
    exact mul_le_mul_of_nonneg_left hrpow hN
  have hkey : N * (2 ^ a * (ε / (2 ^ a * (N + 1)))) = ε * N / (N + 1) := by
    field_simp
  have hfinal : N * (|q.1 - b.1| + |q.2 - b.2|) ^ a < ε := by
    have h2' : N * (|q.1 - b.1| + |q.2 - b.2|) ^ a ≤ ε * N / (N + 1) := by
      rw [hδa, hkey] at hstep
      exact hstep
    have h3 : ε * N / (N + 1) < ε := by
      rw [div_lt_iff₀ hN1]
      nlinarith
    exact lt_of_le_of_lt h2' h3
  rw [Real.dist_eq]
  exact lt_of_le_of_lt hmain hfinal

/-! ## §1 The target -/


end Work.FTS_StreamBdry.Inputs
end
end
