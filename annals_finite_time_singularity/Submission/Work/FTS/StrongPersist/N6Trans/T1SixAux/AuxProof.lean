import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.GalBasis.cut.LN_slot_tendsto
import Submission.Work.FTS.GalBasis.hk_sq_api
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.JepsHkMem.continuousOn_Jeps
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Gmaj6
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Majorant6
import Submission.Work.FTS.StrongPersist.L3Rhs.L3MulDzBackupM
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.ProdRadSup
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.Asm
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.leibnizRem6
import Submission.Work.FTS.StrongPersist.SupOpenH2
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T2Sup.GenSlot
import Submission.Work.FTS.TransportS.T3SlotAux.Flux
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.Pinning.integrableOn_sq_rpow_of_HkMem
import Submission.Work.FTS_MuLipC.RowN.PvAesmOpen
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_RegExport.RXT.starVop
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.EllipticEst.AeI1Fts.tendsto_terms_cut =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AeI1Fts


end Work.FTS.EllipticEst.AeI1Fts
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc.HkSq_sub_psiCut_tendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000


end Work.FTS.GalBasis.cc
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.HkMem_Jeps =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1000000

/-! ## The main theorem -/

theorem HkMem_Jeps {ρ : ℝ × ℝ → ℝ} (hρ : IsMollKernel ρ) {α : ℝ}
    (hα : α ∈ Set.Ioc 0 1) {k : ℕ} {ε : ℝ} (hε : 0 < ε) {f : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad)
    (hmem : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α k (Jeps ρ ε f) := by
  -- the two weight-shift constants
  obtain ⟨cη, hcηpos, hWη0⟩ := HkSqAux.wdiv_shift_le
  obtain ⟨cγ, hcγpos, hWγ0⟩ := HkSqAux.Wt_shift_le
  set c : ℝ := max cη cγ with hcdef
  have hc0 : 0 ≤ c := le_of_lt (lt_of_lt_of_le hcηpos (le_max_left _ _))
  have hWη : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ p : ℝ × ℝ,
      Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        ≤ Real.exp (c * (|p.1| + |p.2|))
          * (Work.Spaces.w (zShift z p.1)
              / (Real.sin (2 * thShift θ p.2)) ^ (Work.Spaces.eta / 2)) := by
    intro z θ hz hθ p
    refine (hWη0 z θ p.1 p.2 hz hθ).trans (mul_le_mul_of_nonneg_right ?_ ?_)
    · exact Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    · exact div_nonneg (Work.FTS.StrongEps.w_nonneg _)
        (Real.rpow_nonneg (le_of_lt (sin_two_pos (thShift_mem hθ))) _)
  have hWγ : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ p : ℝ × ℝ,
      Work.Spaces.Wt α z θ
        ≤ Real.exp (c * (|p.1| + |p.2|))
          * Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2) := by
    intro z θ hz hθ p
    exact (hWγ0 α hα z θ p.1 p.2 hz hθ).trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
      (mul_nonneg (Work.FTS.StrongEps.w_nonneg _)
        (Real.rpow_nonneg (le_of_lt (sin_two_pos (thShift_mem hθ))) _)))
  -- continuity of the integrand of `f` on the open quadrant
  have hcontf : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α k f q.1 q.2) Quad :=
    HkSqAux.continuousOn_HkIntegrand_Quad α k hsm
  -- the pointwise bound in `ℝ≥0∞`
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α k (Jeps ρ ε f) z θ)
        ≤ ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p)
            * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
            * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift z p.1) (thShift θ p.2)) :=
    fun z hz θ hθ => HkSqAux.ofReal_GJ_le ρ hρ hε hα hsm hWη hWγ hz hθ k
  -- the finiteness of each angular slice
  have hslice_fin : ∀ z ∈ Work.Spaces.Iz,
      (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k (Jeps ρ ε f) z θ)) < ⊤ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · rw [← hz0]
      have hzero : (fun θ : ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k (Jeps ρ ε f) 0 θ))
          = fun _ => 0 := by
        funext θ
        simp only [Work.Spaces.HkIntegrand, Work.Spaces.w, Work.Spaces.Wt]
        simp
      rw [hzero]
      simp
    · -- measurability of the pair `(θ, p) ↦ kernel · shifted integrand`
      have hpair : AEMeasurable (fun q : ℝ × (ℝ × ℝ) =>
          ENNReal.ofReal (Jker ρ ε q.2)
            * ENNReal.ofReal (Real.exp (2 * c * (|q.2.1| + |q.2.2|)))
            * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift z q.2.1)
                (thShift q.1 q.2.2)))
          ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod MeasureTheory.volume) :=
        JepsHkMem.aemeasurable_pair_slice hcontf hρ.cont hzpos
      set G : ℝ → ENNReal := fun z' => ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z' θ) with hGdef
      have hGmeas : AEMeasurable (fun p₁ : ℝ => G (z * Real.exp (-p₁))) MeasureTheory.volume :=
        (JepsHkMem.aemeasurable_shift_z_pair hcontf hzpos).lintegral_prod_right'
      have hGfin : (∫⁻ z' in Set.Ioi 0, G z') < ⊤ := by
        have hHk : ENNReal.ofReal (Work.Spaces.HkSq α k f)
            = ∫⁻ z' in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z' θ) := by
          rw [Work.Spaces.HkSq]
          rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hmem.2
            (Eventually.of_forall fun z' => integral_nonneg fun θ =>
              Work.Spaces.HkIntegrand_nonneg α k f z' θ)]
          exact MeasureTheory.setLIntegral_congr_fun measurableSet_Ici (fun z' hz' =>
            MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hmem.1 z' hz')
              (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k f z' θ))
        have hIoi : (∫⁻ z' in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z' θ))
            = ∫⁻ z' in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z' θ) :=
          MeasureTheory.setLIntegral_congr (f := fun z' : ℝ => ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z' θ))
            (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0))
        rw [hIoi, ← hHk]
        exact ENNReal.ofReal_lt_top
      -- the constant dominating the kernel factor
      set D : ℝ := Real.exp (4 * c * ε) * Real.exp (3 * ε) with hDdef
      have hD0 : 0 ≤ D := by rw [hDdef]; positivity
      have hkern : ∀ p : ℝ × ℝ,
          ENNReal.ofReal (Jker ρ ε p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
              * ENNReal.ofReal (Real.exp (3 * |p.2|))
            ≤ ENNReal.ofReal D * ENNReal.ofReal (Jker ρ ε p) := by
        intro p
        rcases eq_or_ne (Jker ρ ε p) 0 with hp | hp
        · simp [hp]
        · have hb : |p.2| ≤ ε := by
            have h := Jker_ne_zero_support hρ hε hp
            have h2 : p.2 ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg p.1]
            rw [sq_le_sq] at h2
            rwa [abs_of_nonneg hε.le] at h2
          have h1 : Real.exp (2 * c * (|p.1| + |p.2|)) ≤ Real.exp (4 * c * ε) := by
            rw [Real.exp_le_exp]
            have hsupp := HkSqAux.Jker_support_abs hρ hε hp
            nlinarith [hc0, abs_nonneg p.1, abs_nonneg p.2]
          have h2 : Real.exp (3 * |p.2|) ≤ Real.exp (3 * ε) := by
            rw [Real.exp_le_exp]
            linarith [mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 3)]
          have hprod : Real.exp (2 * c * (|p.1| + |p.2|)) * Real.exp (3 * |p.2|) ≤ D := by
            rw [hDdef]
            exact mul_le_mul h1 h2 (Real.exp_pos _).le (Real.exp_pos _).le
          have hjk : 0 ≤ Jker ρ ε p := HkSqAux.Jker_nonneg ρ hρ ε p
          have hmul : Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|)) * Real.exp (3 * |p.2|)
              ≤ D * Jker ρ ε p := by
            rw [mul_assoc, mul_comm D (Jker ρ ε p)]
            exact mul_le_mul_of_nonneg_left hprod hjk
          calc ENNReal.ofReal (Jker ρ ε p)
                * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
                * ENNReal.ofReal (Real.exp (3 * |p.2|))
              = ENNReal.ofReal (Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
                  * Real.exp (3 * |p.2|)) := by
                rw [ENNReal.ofReal_mul (mul_nonneg hjk (Real.exp_pos _).le),
                  ENNReal.ofReal_mul hjk]
            _ ≤ ENNReal.ofReal (D * Jker ρ ε p) := ENNReal.ofReal_le_ofReal hmul
            _ = ENNReal.ofReal D * ENNReal.ofReal (Jker ρ ε p) :=
                ENNReal.ofReal_mul (p := D) hD0
      -- the chain of inequalities
      have hchain : (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α k (Jeps ρ ε f) z θ))
          ≤ ENNReal.ofReal D * (∫⁻ p : ℝ × ℝ,
              ENNReal.ofReal (Jker ρ ε p) * G (zShift z p.1)) := by
        calc (∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (Work.Spaces.HkIntegrand α k (Jeps ρ ε f) z θ))
            ≤ (∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p)
                * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
                * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift z p.1)
                    (thShift θ p.2))) :=
              MeasureTheory.setLIntegral_mono' measurableSet_Icc
                (fun θ hθ => hpt z hzpos.le θ hθ)
          _ = (∫⁻ p : ℝ × ℝ, (ENNReal.ofReal (Jker ρ ε p)
                * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|))))
                * (∫⁻ θ in Work.Spaces.Iθ,
                    ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift z p.1)
                      (thShift θ p.2)))) := by
              rw [MeasureTheory.lintegral_lintegral_swap
                (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
                (ν := MeasureTheory.volume) hpair]
              refine lintegral_congr fun p => ?_
              exact MeasureTheory.lintegral_const_mul' _
                (fun θ : ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift z p.1)
                  (thShift θ p.2)))
                (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
          _ ≤ (∫⁻ p : ℝ × ℝ, (ENNReal.ofReal (Jker ρ ε p)
                * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|))))
                * (ENNReal.ofReal (Real.exp (3 * |p.2|))
                    * (∫⁻ θ in Work.Spaces.Iθ,
                        ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift z p.1) θ)))) := by
              refine lintegral_mono fun p => ?_
              exact mul_le_mul_right
                (JepsHkMem.lintegral_thShift_le
                  (fun θ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift z p.1) θ))
                  p.2) _
          _ = (∫⁻ p : ℝ × ℝ, (ENNReal.ofReal (Jker ρ ε p)
                * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
                * ENNReal.ofReal (Real.exp (3 * |p.2|))) * G (zShift z p.1)) := by
              refine lintegral_congr fun p => ?_
              have hAz : (∫⁻ θ in Work.Spaces.Iθ,
                    ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift z p.1) θ))
                  = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
                      Work.Spaces.HkIntegrand α k f (zShift z p.1) θ) :=
                (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
                  (hmem.1 _ (zShift_pos hzpos).le)
                  (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k f _ θ)).symm
              simp only [hGdef]
              simp only [mul_assoc]
          _ ≤ ENNReal.ofReal D * (∫⁻ p : ℝ × ℝ,
                ENNReal.ofReal (Jker ρ ε p) * G (zShift z p.1)) := by
              rw [← MeasureTheory.lintegral_const_mul' (ENNReal.ofReal D)
                (fun p : ℝ × ℝ => ENNReal.ofReal (Jker ρ ε p) * G (zShift z p.1))
                ENNReal.ofReal_ne_top]
              refine lintegral_mono fun p => ?_
              calc (ENNReal.ofReal (Jker ρ ε p)
                    * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
                    * ENNReal.ofReal (Real.exp (3 * |p.2|))) * G (zShift z p.1)
                  ≤ (ENNReal.ofReal D * ENNReal.ofReal (Jker ρ ε p)) * G (zShift z p.1) :=
                    mul_le_mul_left (hkern p) _
                _ = ENNReal.ofReal D * (ENNReal.ofReal (Jker ρ ε p) * G (zShift z p.1)) := by
                    rw [mul_assoc]
      refine lt_of_le_of_lt hchain (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
      exact JepsHkMem.Jker_comp_zShift_lt_top hρ hε hzpos hGmeas hGfin
  -- membership in each slice
  have hSliceInt : ∀ z ∈ Work.Spaces.Iz,
      IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k (Jeps ρ ε f) z θ)
        Work.Spaces.Iθ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · rw [← hz0]
      have hzero : (fun θ : ℝ => Work.Spaces.HkIntegrand α k (Jeps ρ ε f) 0 θ) = fun _ => 0 := by
        funext θ
        simp only [Work.Spaces.HkIntegrand, Work.Spaces.w, Work.Spaces.Wt]
        simp
      rw [hzero]
      exact integrableOn_zero
    · refine ⟨JepsHkMem.aestronglyMeasurable_HkIntegrand_Jeps_slice hρ hε hsm hzpos, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      refine lt_of_le_of_lt (lintegral_mono fun θ => ?_) (hslice_fin z hzpos.le)
      rw [Real.enorm_eq_ofReal (Work.Spaces.HkIntegrand_nonneg α k (Jeps ρ ε f) z θ)]
  exact ⟨hSliceInt,
    JepsHkMem.integrableOn_sliceIntegral_of_lintegral_lt_top
      (fun z θ => Work.Spaces.HkIntegrand_nonneg α k (Jeps ρ ε f) z θ) hSliceInt
      (JepsHkMem.aestronglyMeasurable_HkIntegrand_Jeps hρ hε hsm)
      (JepsHkMem.lintegral_HkIntegrand_Jeps_lt_top hρ hα hε hsm hmem)⟩

end Work.FTS.StrongEps
end
-- ===== merged: Submission.Work.FTS.StrongEps.JepsSubAux.HkMem_of_majorant_ae =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.JepsSubAux

set_option autoImplicit false

/-- `ℋ^k`-membership by an a.e. domination, with the measurability of the integrand supplied by
continuity on the open quadrant `Quad = (0,∞) × (0,π/2)` (which is conull for the product of the
two restricted measures).  This is `Work.FTS.LocData.HkMem_of_majorant` with the *everywhere*
pointwise domination weakened to an a.e. one; the continuity hypothesis is what supplies both the
slicewise and the joint a.e. strong measurability of the integrand.

Declare it in namespace `Work.FTS.StrongEps.JepsSubAux` (full name
`Work.FTS.StrongEps.JepsSubAux.HkMem_of_majorant_ae`).

Route: (i) at `z = 0` the integrand vanishes identically (`Work.Spaces.w 0 = 0`, resp. the mixed
slots carry `Work.Spaces.Wt α 0 θ = 0`), so the slice is integrable outright (there is a ready-made
`Work.FTS.LocData.HkIntegrand_zero_fst`);
(ii) for `z > 0` the slice `θ ↦ HkIntegrand α k h z θ` is continuous on `Ioo 0 (π/2)` (compose
`hcont` with `θ ↦ (z,θ)`), hence a.e. strongly measurable for `volume.restrict Iθ` — use
`Work.FTS.StrongEps.JepsHkMem.restrict_Iθ_eq` to replace the closed interval by the open one —
and `Integrable.mono'` against the slice of `M` closes it;
(iii) the joint function is a.e. strongly measurable for
`(volume.restrict Iz).prod (volume.restrict Iθ)` by `hcont` and the conull-ness of `Quad`
(`Work.FTS.StrongEps.JepsHkMem.ae_mem_Quad_prod`), so Fubini's measurability
(`AEStronglyMeasurable.integral_prod_right'`) gives the a.e. strong measurability of the
slice-integral, and `Integrable.mono'` against `z ↦ ∫_θ M z θ` (using `integral_mono_of_nonneg`
slicewise) closes the second conjunct. -/
theorem HkMem_of_majorant_ae (α : ℝ) (k : ℕ) {h M : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α k h q.1 q.2)
      Work.FTS.StrongEps.Quad)
    (hMslice : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ => M z θ) Work.Spaces.Iθ)
    (hMz : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, M z θ) Work.Spaces.Iz)
    (hle : ∀ z ∈ Work.Spaces.Iz,
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        Work.Spaces.HkIntegrand α k h z θ ≤ M z θ) :
    Work.Spaces.HkMem α k h := by
  have hIoo : Set.Ioo 0 (π / 2) =ᵐ[volume] Set.Icc 0 (π / 2) :=
    MeasureTheory.Ioo_ae_eq_Icc
  constructor
  · -- Step 1: the `θ`-slices of the integrand are integrable on `Iθ`.
    intro z hz
    show IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k h z θ) (Set.Icc 0 (π / 2))
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · -- `z = 0`: the integrand vanishes identically
      subst h0
      refine IntegrableOn.congr_fun integrableOn_zero (fun θ _ => ?_) measurableSet_Icc
      exact (Work.FTS.LocData.HkIntegrand_zero_fst α k h θ).symm
    · -- `z > 0`: continuity of the slice on the open interval, then `mono'` against `M`
      have haesm : AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.HkIntegrand α k h z θ)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
        rw [Work.FTS.StrongEps.JepsHkMem.restrict_Iθ_eq]
        exact (Work.FTS.LocData.continuousOn_slice_theta
          (G := Work.Spaces.HkIntegrand α k h) hcont hz0
            ).aestronglyMeasurable measurableSet_Ioo
      refine MeasureTheory.Integrable.mono' (hMslice z hz) haesm ?_
      filter_upwards [hle z hz] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α k h z θ)]
      exact hθ
  · -- Step 2: the `z`-integral of the slices is integrable on `Iz`.
    have hprod : AEStronglyMeasurable
        (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k h p.1 p.2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      rw [Work.FTS.StrongEps.JepsHkMem.restrict_Iz_eq,
        Work.FTS.StrongEps.JepsHkMem.restrict_Iθ_eq,
        MeasureTheory.Measure.prod_restrict,
        ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
      exact hcont.aestronglyMeasurable
        (Work.FTS.StrongEps.isOpen_Quad.measurableSet)
    have h1 : AEStronglyMeasurable
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := hprod.integral_prod_right'
    refine MeasureTheory.Integrable.mono' hMz h1 ?_
    filter_upwards [ae_restrict_mem (s := Work.Spaces.Iz) measurableSet_Ici] with z hz
    have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h z θ :=
      integral_nonneg_of_ae (ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α k h z θ))
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact integral_mono_of_nonneg
      (ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α k h z θ))
      (hMslice z hz) (hle z hz)

end Work.FTS.StrongEps.JepsSubAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.JepsSubAux.continuousOn_HkIntDiff =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.JepsSubAux

open scoped Real Topology
open MeasureTheory Set Filter


end Work.FTS.StrongEps.JepsSubAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.IP6AddFin =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist

open Work.FTS.CoercivityFix.Transfer (CommSm CommSm_L1 CommSm_succ AddOKSm)
open Work.FTS.CoercivityFix.Assembly (IP2 IP3 IP4)
open Work.Coercivity (H1IP HkIPStep)

theorem IP6AddFin {α : ℝ} {u v w : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hu : ContDiffOn ℝ 6 (Function.uncurry u) Work.FTS.EllipticEst.Q0)
    (hv : ContDiffOn ℝ 6 (Function.uncurry v) Work.FTS.EllipticEst.Q0)
    (hw : ContDiffOn ℝ 6 (Function.uncurry w) Work.FTS.EllipticEst.Q0)
    (hmu : Work.Spaces.HkMem α 6 u) (hmv : Work.Spaces.HkMem α 6 v)
    (hmw : Work.Spaces.HkMem α 6 w) :
    Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α (fun z θ => u z θ + v z θ) w
      = Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α u w
        + Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α v w := by
  -- The finite-order algebraic package `CommSm` climbs the paper's recursion
  -- `IP^{k+1} = IP^k + c₁ IP^k(D_θ·,D_θ·) + c₂ IP^k(D_z·,D_z·)` five times, from the
  -- level-`1` base `H1IP` up to the level-`6` pairing `IP6`.  Its `add` clause takes exactly
  -- the hypotheses at hand: `C⁶` on the open quadrant (the finite order that the level-`6`
  -- pairing consumes) and `ℋ⁶`-membership.
  have h1 : CommSm α 1 (H1IP α) := CommSm_L1 α hα
  have h2 : CommSm α 2 (IP2 1 1 α) := CommSm_succ α hα 1 h1
  have h3 : CommSm α 3 (IP3 1 1 1 1 α) := CommSm_succ α hα 2 h2
  have h4 : CommSm α 4 (IP4 1 1 1 1 1 1 α) := CommSm_succ α hα 3 h3
  have h5 : CommSm α 5 (HkIPStep 1 1 (IP4 1 1 1 1 1 1 α)) := CommSm_succ α hα 4 h4
  have h6 : CommSm α 6 (HkIPStep 1 1 (HkIPStep 1 1 (IP4 1 1 1 1 1 1 α))) :=
    CommSm_succ α hα 5 h5
  exact h6.add u v w ⟨hu, hv, hw, hmu, hmv, hmw⟩

end Work.FTS.StrongPersist
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

open Work.FTS.Galerkin (Fn)
open Work.Spaces (HkMem HkSq HkNorm Dz Dth mixed pth pzIter DthIter DzIter)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The three pieces -/

/-- The angular half `Γ(θ)/c(α)` of the two `(z,θ)`-separated coefficients. -/
def gamCoef (α : ℝ) (θ : ℝ) : ℝ := Work.Spaces.Gam α θ / Work.Spaces.c α

/-- The radial half `2z/(1+z)²` of the nonlocal coefficient. -/
def acoef (z : ℝ) : ℝ := 2 * z / (1 + z) ^ 2

/-- The radial half `2z²/(1+z)³` of the projector coefficient. -/
def bcoef (z : ℝ) : ℝ := 2 * z ^ 2 / (1 + z) ^ 3

/-- The coefficient `2zΓ(θ)/(c(α)(1+z)²)` of the nonlocal term of `𝓛_Γ`, verbatim as it
appears in `Work.Coercivity.LGamma`. -/
def Acoef (α : ℝ) (z θ : ℝ) : ℝ :=
  2 * z * Work.Spaces.Gam α θ / (Work.Spaces.c α * (1 + z) ^ 2)

/-- The coefficient `(Γ(θ)/c(α))·2z²/(1+z)³` of the projector `𝕡`, verbatim as it appears in
`Work.Coercivity.Proj`. -/
def Bcoef (α : ℝ) (z θ : ℝ) : ℝ :=
  (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)

/-- The radial function `L₁₂(f)`, extended constantly in `θ`. -/
def Mf (f : Fn) : Fn := fun z _ => Work.Coercivity.L12f f z

/-- The projector constant `L₁₂(Transport f)(0)`. -/
def K0f (f : Fn) : ℝ := Work.Coercivity.L12f (Work.Coercivity.Transport f) 0

/-- The local part `-(𝓛 f) + Transport f` of `linPart`. -/
def locOp (f : Fn) : Fn :=
  fun z θ => -(Work.Coercivity.L f z θ) + Work.Coercivity.Transport f z θ

/-! ## Identifications -/




/-- **The nonlocal coefficient is `(z,θ)`-separated** (for every `z`, not only `z ≥ 0`). -/
theorem Acoef_eq_mul (α : ℝ) (z θ : ℝ) : Acoef α z θ = acoef z * gamCoef α θ := by
  rw [Acoef, gamCoef, acoef]
  rcases eq_or_ne (1 + z) 0 with h | h
  · simp [h]
  · field_simp

/-- **The projector coefficient is `(z,θ)`-separated.** -/
theorem Bcoef_eq_mul (α : ℝ) (z θ : ℝ) : Bcoef α z θ = gamCoef α θ * bcoef z := rfl

/-! ## The decomposition -/

/-- **The decomposition of `linPart` into its three pieces.**  This is a purely algebraic
identity (no hypothesis on `f`): `linPart α f = locOp f + Acoef α · Mf f - Bcoef α · K0f f`. -/
theorem linPart_eq (α : ℝ) (f : Fn) :
    linPart α f
      = fun z θ => locOp f z θ + Acoef α z θ * Mf f z θ - Bcoef α z θ * K0f f := by
  funext z θ
  simp only [linPart, Work.Coercivity.LGammaT, Work.Coercivity.LGamma, Work.Coercivity.Proj,
    Work.Coercivity.Transport, locOp, Mf, K0f, Acoef, Bcoef]
  ring

end Work.FTS.StrongPersist
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.Pricing =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

open Work.FTS.Galerkin (Fn)
open Work.Spaces (HkMem HkSq HkNorm)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The factor `R = (1+|Ce|+|Cs|)⁴ α^{-Cpow} (1+M)⁴ (1+|f|_{ℋ⁶})²` in which every block
estimate is expressed. -/
def pricedR (α Cpow M X Ce Cs : ℝ) : ℝ :=
  (1 + |Ce| + |Cs|) ^ 4 * α ^ (-Cpow) * (1 + M) ^ 4 * (1 + X) ^ 2


/-- `α^{-Cpow} ≥ 1` for `0 < α ≤ 1` and `Cpow ≥ 0`. -/
theorem one_le_rpow_neg {α Cpow : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCpow : 0 ≤ Cpow) :
    (1 : ℝ) ≤ α ^ (-Cpow) := by
  have h1α : (1 : ℝ) ≤ α⁻¹ := (one_le_inv₀ hα).mpr hα1
  calc (1 : ℝ) = (α⁻¹) ^ (0 : ℝ) := (Real.rpow_zero _).symm
    _ ≤ (α⁻¹) ^ Cpow := Real.rpow_le_rpow_of_exponent_le h1α hCpow
    _ = α ^ (-Cpow) := by rw [Real.inv_rpow hα.le Cpow, Real.rpow_neg hα.le Cpow]

/-- `α^{-Cp} ≤ α^{-Cpow}` for `0 < α ≤ 1` and `Cp ≤ Cpow`. -/
theorem rpow_neg_le_neg {α Cp Cpow : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hle : Cp ≤ Cpow) :
    α ^ (-Cp) ≤ α ^ (-Cpow) := by
  have h1α : (1 : ℝ) ≤ α⁻¹ := (one_le_inv₀ hα).mpr hα1
  calc α ^ (-Cp) = (α⁻¹) ^ Cp := by rw [Real.inv_rpow hα.le Cp, Real.rpow_neg hα.le Cp]
    _ ≤ (α⁻¹) ^ Cpow := Real.rpow_le_rpow_of_exponent_le h1α hle
    _ = α ^ (-Cpow) := by rw [Real.inv_rpow hα.le Cpow, Real.rpow_neg hα.le Cpow]

theorem one_le_pricedR {α Cpow M X Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCpow : 0 ≤ Cpow)
    (hM : 0 ≤ M) (hX : 0 ≤ X) : 1 ≤ pricedR α Cpow M X Ce Cs := by
  have h1 : (1 : ℝ) ≤ (1 + |Ce| + |Cs|) ^ 4 :=
    one_le_pow₀ (by have := abs_nonneg Ce; have := abs_nonneg Cs; linarith)
  have h2 : (1 : ℝ) ≤ α ^ (-Cpow) := one_le_rpow_neg hα hα1 hCpow
  have h3 : (1 : ℝ) ≤ (1 + M) ^ 4 := one_le_pow₀ (by linarith)
  have h4 : (1 : ℝ) ≤ (1 + X) ^ 2 := one_le_pow₀ (by linarith)
  have h12 : (1 : ℝ) ≤ (1 + |Ce| + |Cs|) ^ 4 * α ^ (-Cpow) :=
    le_trans h1 (le_mul_of_one_le_right (by positivity) h2)
  have h123 : (1 : ℝ) ≤ (1 + |Ce| + |Cs|) ^ 4 * α ^ (-Cpow) * (1 + M) ^ 4 :=
    le_trans h12 (le_mul_of_one_le_right (by positivity) h3)
  have h1234 : (1 : ℝ) ≤ (1 + |Ce| + |Cs|) ^ 4 * α ^ (-Cpow) * (1 + M) ^ 4 * (1 + X) ^ 2 :=
    le_trans h123 (le_mul_of_one_le_right (by positivity) h4)
  simpa only [pricedR] using h1234

/-- **Factor-wise domination of any partial product by the pricing factor.** -/
theorem pricedR_of_factors {α Cpow M X Ce Cs A B C D : ℝ} (hα : 0 < α)
    (hA : A ≤ (1 + |Ce| + |Cs|) ^ 4) (hB : B ≤ α ^ (-Cpow))
    (hC : C ≤ (1 + M) ^ 4) (hD : D ≤ (1 + X) ^ 2)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hC0 : 0 ≤ C) (hD0 : 0 ≤ D) :
    A * B * C * D ≤ pricedR α Cpow M X Ce Cs := by
  rw [pricedR]
  have ha4 : (0 : ℝ) ≤ (1 + |Ce| + |Cs|) ^ 4 := by positivity
  have hrp : (0 : ℝ) ≤ α ^ (-Cpow) := Real.rpow_nonneg hα.le _
  have hm4 : (0 : ℝ) ≤ (1 + M) ^ 4 := by positivity
  have hAB : A * B ≤ (1 + |Ce| + |Cs|) ^ 4 * α ^ (-Cpow) := mul_le_mul hA hB hB0 ha4
  have hABC : A * B * C ≤ (1 + |Ce| + |Cs|) ^ 4 * α ^ (-Cpow) * (1 + M) ^ 4 :=
    mul_le_mul hAB hC hC0 (mul_nonneg ha4 hrp)
  exact mul_le_mul hABC hD hD0 (mul_nonneg (mul_nonneg ha4 hrp) hm4)

/-! ## The block shapes -/

theorem shape_alpha2 {α Cpow M X Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCpow : 0 ≤ Cpow)
    (hM : 0 ≤ M) (hX : 0 ≤ X) : α ^ 2 ≤ pricedR α Cpow M X Ce Cs := by
  have h1 : (1 : ℝ) ≤ (1 + |Ce| + |Cs|) ^ 4 :=
    one_le_pow₀ (by have := abs_nonneg Ce; have := abs_nonneg Cs; linarith)
  have h2 : (1 : ℝ) ≤ α ^ (-Cpow) := one_le_rpow_neg hα hα1 hCpow
  have h3 : (1 : ℝ) ≤ (1 + M) ^ 4 := one_le_pow₀ (by linarith)
  have h4 : (1 : ℝ) ≤ (1 + X) ^ 2 := one_le_pow₀ (by linarith)
  have hα2 : α ^ 2 ≤ 1 := by nlinarith [hα.le, hα1]
  have := pricedR_of_factors hα (A := 1) (B := α ^ 2) (C := 1) (D := 1)
    h1 (le_trans hα2 h2) h3 h4 (by norm_num) (by positivity) (by norm_num) (by norm_num)
  simpa using this

theorem shape_M {α Cpow M X Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCpow : 0 ≤ Cpow)
    (hM : 0 ≤ M) (hX : 0 ≤ X) : 1 + M ≤ pricedR α Cpow M X Ce Cs := by
  have h1 : (1 : ℝ) ≤ (1 + |Ce| + |Cs|) ^ 4 :=
    one_le_pow₀ (by have := abs_nonneg Ce; have := abs_nonneg Cs; linarith)
  have h2 : (1 : ℝ) ≤ α ^ (-Cpow) := one_le_rpow_neg hα hα1 hCpow
  have h4 : (1 : ℝ) ≤ (1 + X) ^ 2 := one_le_pow₀ (by linarith)
  have hM4 : 1 + M ≤ (1 + M) ^ 4 := by
    have hy1 : (1 : ℝ) ≤ 1 + M := by linarith
    simpa using pow_le_pow_right₀ hy1 (by norm_num : (1 : ℕ) ≤ 4)
  have := pricedR_of_factors hα (A := 1) (B := 1) (C := 1 + M) (D := 1)
    h1 h2 hM4 h4 (by norm_num) (by norm_num) (by linarith) (by norm_num)
  simpa using this

theorem shape_MX {α Cp Cpow M X Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCp : 0 ≤ Cp)
    (hCple : Cp ≤ Cpow) (hCpow : 0 ≤ Cpow) (hM : 0 ≤ M) (hX : 0 ≤ X) :
    α ^ (-Cp) * (1 + M) ^ 4 * (1 + X) ^ 2 ≤ pricedR α Cpow M X Ce Cs := by
  have h1 : (1 : ℝ) ≤ (1 + |Ce| + |Cs|) ^ 4 :=
    one_le_pow₀ (by have := abs_nonneg Ce; have := abs_nonneg Cs; linarith)
  have h2 : α ^ (-Cp) ≤ α ^ (-Cpow) := rpow_neg_le_neg hα hα1 hCple
  have h3 : (0 : ℝ) ≤ α ^ (-Cp) := Real.rpow_nonneg hα.le _
  have := pricedR_of_factors hα (A := 1) (B := α ^ (-Cp))
    (C := (1 + M) ^ 4) (D := (1 + X) ^ 2)
    h1 h2 le_rfl le_rfl (by norm_num) h3 (by positivity) (by positivity)
  simpa using this

theorem shape_s {α Cp Cpow M X Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCp : 0 ≤ Cp)
    (hCple : Cp ≤ Cpow) (hCpow : 0 ≤ Cpow) (hM : 0 ≤ M) (hX : 0 ≤ X) :
    (1 + |Cs|) ^ 4 * α ^ (-Cp) ≤ pricedR α Cpow M X Ce Cs := by
  have h1 : (1 + |Cs|) ^ 4 ≤ (1 + |Ce| + |Cs|) ^ 4 :=
    pow_le_pow_left₀ (by positivity) (by have := abs_nonneg Ce; linarith) 4
  have h2 : α ^ (-Cp) ≤ α ^ (-Cpow) := rpow_neg_le_neg hα hα1 hCple
  have h3 : (0 : ℝ) ≤ α ^ (-Cp) := Real.rpow_nonneg hα.le _
  have h4 : (1 : ℝ) ≤ (1 + M) ^ 4 := one_le_pow₀ (by linarith)
  have h5 : (1 : ℝ) ≤ (1 + X) ^ 2 := one_le_pow₀ (by linarith)
  have := pricedR_of_factors hα (A := (1 + |Cs|) ^ 4) (B := α ^ (-Cp)) (C := 1) (D := 1)
    h1 h2 h4 h5 (by positivity) h3 (by norm_num) (by norm_num)
  simpa using this

theorem shape_sM {α Cp Cpow M X Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCp : 0 ≤ Cp)
    (hCple : Cp ≤ Cpow) (hCpow : 0 ≤ Cpow) (hM : 0 ≤ M) (hX : 0 ≤ X) :
    (1 + |Cs|) ^ 4 * α ^ (-Cp) * (1 + M) ^ 4 ≤ pricedR α Cpow M X Ce Cs := by
  have h1 : (1 + |Cs|) ^ 4 ≤ (1 + |Ce| + |Cs|) ^ 4 :=
    pow_le_pow_left₀ (by positivity) (by have := abs_nonneg Ce; linarith) 4
  have h2 : α ^ (-Cp) ≤ α ^ (-Cpow) := rpow_neg_le_neg hα hα1 hCple
  have h3 : (0 : ℝ) ≤ α ^ (-Cp) := Real.rpow_nonneg hα.le _
  have h5 : (1 : ℝ) ≤ (1 + X) ^ 2 := one_le_pow₀ (by linarith)
  have := pricedR_of_factors hα (A := (1 + |Cs|) ^ 4) (B := α ^ (-Cp))
    (C := (1 + M) ^ 4) (D := 1)
    h1 h2 le_rfl h5 (by positivity) h3 (by positivity) (by norm_num)
  simpa using this

theorem shape_e {α Cp Cpow M X Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCp : 0 ≤ Cp)
    (hCple : Cp ≤ Cpow) (hCpow : 0 ≤ Cpow) (hM : 0 ≤ M) (hX : 0 ≤ X) :
    (1 + |Ce|) ^ 4 * α ^ (-Cp) * (1 + M) ^ 4 * (1 + X) ^ 2 ≤ pricedR α Cpow M X Ce Cs := by
  have h1 : (1 + |Ce|) ^ 4 ≤ (1 + |Ce| + |Cs|) ^ 4 :=
    pow_le_pow_left₀ (by positivity) (by have := abs_nonneg Cs; linarith) 4
  have h2 : α ^ (-Cp) ≤ α ^ (-Cpow) := rpow_neg_le_neg hα hα1 hCple
  have h3 : (0 : ℝ) ≤ α ^ (-Cp) := Real.rpow_nonneg hα.le _
  have := pricedR_of_factors hα (A := (1 + |Ce|) ^ 4) (B := α ^ (-Cp))
    (C := (1 + M) ^ 4) (D := (1 + X) ^ 2)
    h1 h2 le_rfl le_rfl (by positivity) h3 (by positivity) (by positivity)
  simpa using this

/-! ## The shapes with a constant factor -/

theorem mul_shape_alpha2 {α Cpow M X Ce Cs C : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hCpow : 0 ≤ Cpow) (hM : 0 ≤ M) (hX : 0 ≤ X) (hC : 0 ≤ C) :
    C * α ^ 2 ≤ C * pricedR α Cpow M X Ce Cs :=
  mul_le_mul_of_nonneg_left (shape_alpha2 hα hα1 hCpow hM hX) hC

theorem mul_shape_M {α Cpow M X Ce Cs C : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hCpow : 0 ≤ Cpow) (hM : 0 ≤ M) (hX : 0 ≤ X) (hC : 0 ≤ C) :
    C * (1 + M) ≤ C * pricedR α Cpow M X Ce Cs :=
  mul_le_mul_of_nonneg_left (shape_M hα hα1 hCpow hM hX) hC

theorem mul_shape_MX {α Cp Cpow M X Ce Cs C : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCp : 0 ≤ Cp)
    (hCple : Cp ≤ Cpow) (hCpow : 0 ≤ Cpow) (hM : 0 ≤ M) (hX : 0 ≤ X) (hC : 0 ≤ C) :
    C * α ^ (-Cp) * (1 + M) ^ 4 * (1 + X) ^ 2 ≤ C * pricedR α Cpow M X Ce Cs := by
  rw [show C * α ^ (-Cp) * (1 + M) ^ 4 * (1 + X) ^ 2
      = C * (α ^ (-Cp) * (1 + M) ^ 4 * (1 + X) ^ 2) by ring]
  exact mul_le_mul_of_nonneg_left (shape_MX hα hα1 hCp hCple hCpow hM hX) hC

theorem mul_shape_s {α Cp Cpow M X Ce Cs C : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCp : 0 ≤ Cp)
    (hCple : Cp ≤ Cpow) (hCpow : 0 ≤ Cpow) (hM : 0 ≤ M) (hX : 0 ≤ X) (hC : 0 ≤ C) :
    C * (1 + |Cs|) ^ 4 * α ^ (-Cp) ≤ C * pricedR α Cpow M X Ce Cs := by
  rw [show C * (1 + |Cs|) ^ 4 * α ^ (-Cp) = C * ((1 + |Cs|) ^ 4 * α ^ (-Cp)) by ring]
  exact mul_le_mul_of_nonneg_left (shape_s hα hα1 hCp hCple hCpow hM hX) hC

theorem mul_shape_sM {α Cp Cpow M X Ce Cs C : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCp : 0 ≤ Cp)
    (hCple : Cp ≤ Cpow) (hCpow : 0 ≤ Cpow) (hM : 0 ≤ M) (hX : 0 ≤ X) (hC : 0 ≤ C) :
    C * (1 + |Cs|) ^ 4 * α ^ (-Cp) * (1 + M) ^ 4 ≤ C * pricedR α Cpow M X Ce Cs := by
  rw [show C * (1 + |Cs|) ^ 4 * α ^ (-Cp) * (1 + M) ^ 4
      = C * ((1 + |Cs|) ^ 4 * α ^ (-Cp) * (1 + M) ^ 4) by ring]
  exact mul_le_mul_of_nonneg_left (shape_sM hα hα1 hCp hCple hCpow hM hX) hC

theorem mul_shape_e {α Cp Cpow M X Ce Cs C : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCp : 0 ≤ Cp)
    (hCple : Cp ≤ Cpow) (hCpow : 0 ≤ Cpow) (hM : 0 ≤ M) (hX : 0 ≤ X) (hC : 0 ≤ C) :
    C * (1 + |Ce|) ^ 4 * α ^ (-Cp) * (1 + M) ^ 4 * (1 + X) ^ 2
      ≤ C * pricedR α Cpow M X Ce Cs := by
  rw [show C * (1 + |Ce|) ^ 4 * α ^ (-Cp) * (1 + M) ^ 4 * (1 + X) ^ 2
      = C * ((1 + |Ce|) ^ 4 * α ^ (-Cp) * (1 + M) ^ 4 * (1 + X) ^ 2) by ring]
  exact mul_le_mul_of_nonneg_left (shape_e hα hα1 hCp hCple hCpow hM hX) hC

/-! ## Binary additivity of `HkNorm` -/

private theorem sqrt_add_le' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    rw [add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]
    nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  calc Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt a + Real.sqrt b := Real.sqrt_sq (by positivity)

theorem HkNorm_add_le2 (α : ℝ) {u v : Fn} {Bu Bv : ℝ}
    (hu : HkMem α 3 u) (hv : HkMem α 3 v)
    (hc : ContDiffOn ℝ 3 (Function.uncurry u) Work.FTS.EllipticEst.Q0)
    (hd : ContDiffOn ℝ 3 (Function.uncurry v) Work.FTS.EllipticEst.Q0)
    (bu : HkNorm α 3 u ≤ Bu) (bv : HkNorm α 3 v ≤ Bv)
    (hBu : 0 ≤ Bu) (hBv : 0 ≤ Bv) :
    HkMem α 3 (fun z θ => u z θ + v z θ) ∧
      HkNorm α 3 (fun z θ => u z θ + v z θ) ≤ 2 * (Bu + Bv) := by
  obtain ⟨hm, hsq⟩ := HkMem_HkSq_add2 α hc hd hu hv
  refine ⟨hm, ?_⟩
  have hsqrt : HkNorm α 3 (fun z θ => u z θ + v z θ)
      ≤ Real.sqrt 2 * (HkNorm α 3 u + HkNorm α 3 v) := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    calc Real.sqrt (HkSq α 3 (fun z θ => u z θ + v z θ))
        ≤ Real.sqrt (2 * HkSq α 3 u + 2 * HkSq α 3 v) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt 2 * Real.sqrt (HkSq α 3 u + HkSq α 3 v) := by
          rw [show (2 : ℝ) * HkSq α 3 u + 2 * HkSq α 3 v
              = 2 * (HkSq α 3 u + HkSq α 3 v) by ring, Real.sqrt_mul (by norm_num)]
      _ ≤ Real.sqrt 2 * (Real.sqrt (HkSq α 3 u) + Real.sqrt (HkSq α 3 v)) :=
          mul_le_mul_of_nonneg_left
            (sqrt_add_le' (Work.Spaces.HkSq_nonneg α 3 u) (Work.Spaces.HkSq_nonneg α 3 v))
            (Real.sqrt_nonneg 2)
  have h1 : Real.sqrt 2 * (HkNorm α 3 u + HkNorm α 3 v) ≤ 2 * (Bu + Bv) := by
    have h2 : Real.sqrt 2 ≤ 2 := by
      have := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      nlinarith [Real.sqrt_nonneg 2, this]
    have h3 : (0 : ℝ) ≤ HkNorm α 3 u := Real.sqrt_nonneg _
    have h4 : (0 : ℝ) ≤ HkNorm α 3 v := Real.sqrt_nonneg _
    nlinarith [bu, bv]
  exact le_trans hsqrt h1

end Work.FTS.StrongPersist.L3Rhs
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.AuxProof =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_zero_z)
open Work.Spaces

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false


end Work.FTS.StrongPersist.N6Trans
end
end
