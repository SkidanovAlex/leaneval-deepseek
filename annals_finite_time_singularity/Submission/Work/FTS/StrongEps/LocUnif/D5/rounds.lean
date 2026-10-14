import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.TT.ESW.Tk_B_le_chain_uniform
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.L12.LocUnifTendsto
import Submission.Work.FTS.StrongEps.LocUnif.D5.deriv_slot_lintegral_bounds
import Submission.Work.FTS.StrongEps.LocUnif.mixed_rect_L2_bounds
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T45AslotLe
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.c2mGam_Wt_bound
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.KsAux
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_EllLimOK.wt_bddAbove_of_compact
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.H2W.PsiSlices.shiftedSourcePoleBound
import Submission.Work.H2W.asliceMomentEq
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.ClassC.HkMem_seven_slots_of_vanishing_family =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false
set_option maxHeartbeats 1000000



end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.PerzTools.Main =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EpsEngine.PerzTools

set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem intervalIntegral_perz_aux (hcar : CarathTheta) (hexch : ExchMixed)
    {α B : ℝ} {k : ℕ} {T a b : ℝ} {H : ℝ → ℝ → ℝ → ℝ}
    (hab : a ≤ b) (hT : 0 ≤ T) (haT : a ∈ Set.Icc 0 T) (hbT : b ∈ Set.Icc 0 T)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hmem : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.Spaces.HkMem α k (H s))
    (hbd : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.Spaces.HkNorm α k (H s) ≤ B)
    (hmeas : ∀ (j i : ℕ), j + i ≤ k → ∀ z θ : ℝ,
      (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (H s) z θ)
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)))
    (hjoint : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => Work.Spaces.HkIntegrand α k (H p.1) p.2.1 p.2.2)
      ((MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)).prod
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))))
    (hsup : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ q ∈ K, ∀ (j i : ℕ), j + i ≤ k →
        |Work.Spaces.mixed j i (H s) q.1 q.2| ≤ C)
    (hperz : ∀ z ∈ Work.Spaces.Iz, ∃ Cz : ℝ,
      ∀ s ∈ Set.Icc (0 : ℝ) T,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (H s) z θ) ≤ Cz) :
    Work.Spaces.HkMem α k (fun z θ => ∫ s in a..b, H s z θ) ∧
      Work.Spaces.HkNorm α k (fun z θ => ∫ s in a..b, H s z θ) ≤ B * (b - a) := by
  classical
  set G : ℝ → ℝ → ℝ := fun z θ => ∫ s in a..b, H s z θ with hG
  have hab0 : (0 : ℝ) ≤ b - a := by linarith
  -- ## (1) elementary consequences of the hypotheses
  have hB : 0 ≤ B := le_trans (Work.Spaces.HkNorm_nonneg α k (H a)) (hbd a haT)
  have hSq_le : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.Spaces.HkSq α k (H s) ≤ B ^ 2 := by
    intro s hs
    have hnn : 0 ≤ Work.Spaces.HkSq α k (H s) :=
      integral_nonneg fun z =>
        integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k (H s) z θ
    calc Work.Spaces.HkSq α k (H s) = (Work.Spaces.HkNorm α k (H s)) ^ 2 := by
          rw [Work.Spaces.HkNorm, Real.sq_sqrt hnn]
      _ ≤ B ^ 2 := pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α k (H s)) (hbd s hs) 2
  have hsub : Set.uIoc a b ⊆ Set.Icc (0 : ℝ) T := by
    intro t ht
    rw [Set.uIoc_of_le hab] at ht
    exact ⟨le_trans haT.1 ht.1.le, le_trans ht.2 hbT.2⟩
  -- ## (2) measurability of the primitive's integrand
  have hsliceAESM : ∀ z ∈ Work.Spaces.Iz,
      AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.HkIntegrand α k G z θ)
        (volume.restrict Work.Spaces.Iθ) :=
    fun z hz => aesm_slice_HkIntegrand_primitive hcar hexch haT hbT hab hsm hmeas hsup hz
  have hjointG : AEStronglyMeasurable
      (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α k G q.1 q.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    aesm_HkIntegrand_primitive hexch haT hbT hab hsm hmeas hsup
  have houterAESM : AEStronglyMeasurable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k G z θ)
      (volume.restrict Work.Spaces.Iz) :=
    hjointG.integral_prod_right'
  -- ## (3) the per-`z` energy bound of the primitive's integrand
  have hzFin : ∀ z ∈ Work.Spaces.Iz,
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k G z θ)) < ⊤ := by
    intro z hz
    obtain ⟨Cz, hCz⟩ := hperz z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · rw [← hz0]
      have hzero : (fun θ : ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k G 0 θ))
          = fun _ : ℝ => (0 : ENNReal) := by
        funext θ
        rw [HkIntegrand_fst_zero α k G θ]
        simp
      rw [hzero]
      simp
    · have hIθ : volume.restrict (Set.Ioo 0 (Real.pi / 2)) = volume.restrict Work.Spaces.Iθ :=
        MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc
      have key : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k G z θ)
            ≤ ENNReal.ofReal (b - a) * (∫⁻ s in Set.uIoc a b,
                ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) z θ)) := by
        rw [← hIθ]
        refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
        have hq : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
          Work.FTS.EllipticEst.mem_Q0.mpr ⟨hzpos, hθ⟩
        have hcv := cv_bound (α := α) hexch haT hbT hab hsm hmeas hsup hq
        have hconv : ∫ s in a..b, Work.Spaces.HkIntegrand α k (H s) z θ
            = ∫ s in Set.uIoc a b, Work.Spaces.HkIntegrand α k (H s) z θ := by
          rw [intervalIntegral.integral_of_le hab, Set.uIoc_of_le hab]
        calc ENNReal.ofReal (Work.Spaces.HkIntegrand α k G z θ)
            ≤ ENNReal.ofReal ((b - a) * ∫ s in a..b, Work.Spaces.HkIntegrand α k (H s) z θ) :=
              ENNReal.ofReal_le_ofReal hcv
          _ = ENNReal.ofReal (b - a)
                * ENNReal.ofReal (∫ s in a..b, Work.Spaces.HkIntegrand α k (H s) z θ) :=
              ENNReal.ofReal_mul hab0
          _ ≤ ENNReal.ofReal (b - a)
                * (∫⁻ s in Set.uIoc a b,
                    ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) z θ)) := by
              refine mul_le_mul_right ?_ _
              rw [hconv]
              exact ofReal_integral_le_lintegral_ofReal
                (fun s => Work.Spaces.HkIntegrand_nonneg α k (H s) z θ)
      have step2 : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (b - a)
            * (∫⁻ s in Set.uIoc a b, ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) z θ)))
          = ENNReal.ofReal (b - a) * ∫⁻ s in Set.uIoc a b,
              ∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) z θ) := by
        rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        symm
        refine MeasureTheory.lintegral_lintegral_swap
          (μ := volume.restrict (Set.uIoc a b)) (ν := volume.restrict Work.Spaces.Iθ)
          (f := fun s θ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) z θ)) ?_
        have h3 := perz_aesm_HkIntegrand hcar hsm hmeas hzpos (α := α) (k := k)
        exact ((h3.mono_measure
          (Measure.prod_mono (Measure.restrict_mono hsub le_rfl) le_rfl)).aemeasurable).ennreal_ofReal
      have step3 : (∫⁻ s in Set.uIoc a b,
            ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) z θ))
          ≤ ∫⁻ s in Set.uIoc a b, ENNReal.ofReal Cz := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
        have hsT : s ∈ Set.Icc (0 : ℝ) T := hsub hs
        rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal ((hmem s hsT).1 z hz)
          (Filter.Eventually.of_forall
            (fun θ => Work.Spaces.HkIntegrand_nonneg α k (H s) z θ))]
        exact ENNReal.ofReal_le_ofReal (hCz s hsT)
      have step4 : (∫⁻ s in Set.uIoc a b, ENNReal.ofReal Cz)
          = ENNReal.ofReal Cz * ENNReal.ofReal (b - a) := by
        rw [MeasureTheory.lintegral_const, MeasureTheory.Measure.restrict_apply_univ,
          Real.volume_uIoc, abs_of_nonneg hab0]
      refine lt_of_le_of_lt ?_ (ENNReal.mul_lt_top (ENNReal.ofReal_lt_top (r := b - a))
        (ENNReal.mul_lt_top (ENNReal.ofReal_lt_top (r := Cz))
          (ENNReal.ofReal_lt_top (r := b - a))))
      calc (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k G z θ))
          ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (b - a)
              * (∫⁻ s in Set.uIoc a b,
                  ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) z θ)) :=
            lintegral_mono_ae key
        _ = ENNReal.ofReal (b - a) * ∫⁻ s in Set.uIoc a b,
              ∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) z θ) := step2
        _ ≤ ENNReal.ofReal (b - a) * ∫⁻ s in Set.uIoc a b, ENNReal.ofReal Cz :=
            mul_le_mul_right step3 _
        _ = ENNReal.ofReal (b - a) * (ENNReal.ofReal Cz * ENNReal.ofReal (b - a)) := by
            rw [step4]
  -- ## (4) the energy bound of the primitive on the whole quadrant
  have hqFin : (∫⁻ q, ENNReal.ofReal (Work.Spaces.HkIntegrand α k G q.1 q.2)
        ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
      ≤ ENNReal.ofReal ((b - a) ^ 2 * B ^ 2) := by
    have key : ∀ᵐ q ∂((volume.restrict Work.Spaces.Iz).prod
        (volume.restrict Work.Spaces.Iθ)),
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k G q.1 q.2)
          ≤ ENNReal.ofReal (b - a) * (∫⁻ s in Set.uIoc a b,
              ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) q.1 q.2)) := by
      filter_upwards [ae_mem_Q0] with q hq
      have hcv := cv_bound (α := α) hexch haT hbT hab hsm hmeas hsup hq
      have hconv : ∫ s in a..b, Work.Spaces.HkIntegrand α k (H s) q.1 q.2
          = ∫ s in Set.uIoc a b, Work.Spaces.HkIntegrand α k (H s) q.1 q.2 := by
        rw [intervalIntegral.integral_of_le hab, Set.uIoc_of_le hab]
      calc ENNReal.ofReal (Work.Spaces.HkIntegrand α k G q.1 q.2)
          ≤ ENNReal.ofReal ((b - a) * ∫ s in a..b,
              Work.Spaces.HkIntegrand α k (H s) q.1 q.2) := ENNReal.ofReal_le_ofReal hcv
        _ = ENNReal.ofReal (b - a)
              * ENNReal.ofReal (∫ s in a..b, Work.Spaces.HkIntegrand α k (H s) q.1 q.2) :=
            ENNReal.ofReal_mul hab0
        _ ≤ ENNReal.ofReal (b - a)
              * (∫⁻ s in Set.uIoc a b,
                  ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) q.1 q.2)) := by
            refine mul_le_mul_right ?_ _
            rw [hconv]
            exact ofReal_integral_le_lintegral_ofReal
              (fun s => Work.Spaces.HkIntegrand_nonneg α k (H s) q.1 q.2)
    have step2 : (∫⁻ x, ENNReal.ofReal (b - a)
          * (∫⁻ s in Set.uIoc a b,
              ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) x.1 x.2))
          ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
        = ENNReal.ofReal (b - a) * ∫⁻ s in Set.uIoc a b,
            ∫⁻ x, ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) x.1 x.2)
              ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
      rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      congr 1
      symm
      refine MeasureTheory.lintegral_lintegral_swap
        (μ := volume.restrict (Set.uIoc a b))
        (ν := (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))
        (f := fun s x => ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) x.1 x.2)) ?_
      exact ((hjoint.mono_measure
        (Measure.prod_mono (Measure.restrict_mono hsub le_rfl) le_rfl)).aemeasurable).ennreal_ofReal
    have hsliceEq : ∀ s ∈ Set.Icc (0 : ℝ) T,
        (∫⁻ x, ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) x.1 x.2)
          ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
          = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
              (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (H s) z θ) := by
      intro s hsT
      have hprod : AEMeasurable
          (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) p.1 p.2))
          ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
        (Work.Spaces.aesm_of_continuousOn_Qd _
          ((hsm s hsT).continuousOn_HkIntegrand α k)).aemeasurable.ennreal_ofReal
      rw [MeasureTheory.lintegral_prod _ hprod]
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
      exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal ((hmem s hsT).1 z hz)
        (Filter.Eventually.of_forall
          (fun θ => Work.Spaces.HkIntegrand_nonneg α k (H s) z θ))).symm
    have step3 : (∫⁻ s in Set.uIoc a b, ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (H s) z θ))
        ≤ ∫⁻ s in Set.uIoc a b, ENNReal.ofReal (B ^ 2) := by
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
      have hsT : s ∈ Set.Icc (0 : ℝ) T := hsub hs
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hmem s hsT).2
        (Filter.Eventually.of_forall (fun z =>
          integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k (H s) z θ))]
      exact ENNReal.ofReal_le_ofReal (hSq_le s hsT)
    have step4 : (∫⁻ s in Set.uIoc a b, ENNReal.ofReal (B ^ 2))
        = ENNReal.ofReal (B ^ 2) * ENNReal.ofReal (b - a) := by
      rw [MeasureTheory.lintegral_const, MeasureTheory.Measure.restrict_apply_univ,
        Real.volume_uIoc, abs_of_nonneg hab0]
    have hB2 : (0 : ℝ) ≤ B ^ 2 := sq_nonneg B
    calc (∫⁻ q, ENNReal.ofReal (Work.Spaces.HkIntegrand α k G q.1 q.2)
          ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
        ≤ ∫⁻ q, ENNReal.ofReal (b - a) * (∫⁻ s in Set.uIoc a b,
              ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) q.1 q.2))
            ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
          lintegral_mono_ae key
      _ = ENNReal.ofReal (b - a) * ∫⁻ s in Set.uIoc a b,
            ∫⁻ q, ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) q.1 q.2)
              ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := step2
      _ = ENNReal.ofReal (b - a) * ∫⁻ s in Set.uIoc a b,
            ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
              (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (H s) z θ) := by
          congr 1
          refine lintegral_congr_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
          exact hsliceEq s (hsub hs)
      _ ≤ ENNReal.ofReal (b - a) * ∫⁻ s in Set.uIoc a b, ENNReal.ofReal (B ^ 2) :=
          mul_le_mul_right step3 _
      _ = ENNReal.ofReal ((b - a) ^ 2 * B ^ 2) := by
          rw [step4, ← ENNReal.ofReal_mul hB2, ← ENNReal.ofReal_mul hab0]
          ring_nf
  -- ## (5) the `z`-integral of the primitive's angular energy
  have houterBound : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k G z θ))
      ≤ ENNReal.ofReal ((b - a) ^ 2 * B ^ 2) := by
    have hconv1 : (∫⁻ q, ENNReal.ofReal (Work.Spaces.HkIntegrand α k G q.1 q.2)
          ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
        = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α k G z θ) :=
      MeasureTheory.lintegral_prod _ (hjointG.aemeasurable.ennreal_ofReal)
    have hstep : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k G z θ))
        = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α k G z θ) := by
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
      exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        ((MeasureTheory.lintegral_ofReal_ne_top_iff_integrable (hsliceAESM z hz)
            (Filter.Eventually.of_forall
              (fun θ => Work.Spaces.HkIntegrand_nonneg α k G z θ))).mp
          (ne_of_lt (hzFin z hz)))
        (Filter.Eventually.of_forall (fun θ => Work.Spaces.HkIntegrand_nonneg α k G z θ))
    calc (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k G z θ))
        = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α k G z θ) := hstep
      _ = ∫⁻ q, ENNReal.ofReal (Work.Spaces.HkIntegrand α k G q.1 q.2)
            ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
          hconv1.symm
      _ ≤ ENNReal.ofReal ((b - a) ^ 2 * B ^ 2) := hqFin
  -- ## (6) assembly
  have hsliceInt : ∀ z ∈ Work.Spaces.Iz,
      IntegrableOn (fun θ : ℝ => Work.Spaces.HkIntegrand α k G z θ) Work.Spaces.Iθ := by
    intro z hz
    exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable (hsliceAESM z hz)
      (Filter.Eventually.of_forall
        (fun θ => Work.Spaces.HkIntegrand_nonneg α k G z θ))).mp (ne_of_lt (hzFin z hz))
  have houterInt : IntegrableOn
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k G z θ)
      Work.Spaces.Iz := by
    refine ⟨houterAESM, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall (fun z =>
        integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k G z θ))]
    exact lt_of_le_of_lt houterBound ENNReal.ofReal_lt_top
  have hSqG : Work.Spaces.HkSq α k G ≤ (b - a) ^ 2 * B ^ 2 := by
    have h1 : ENNReal.ofReal (Work.Spaces.HkSq α k G)
        = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
            (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k G z θ) :=
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal houterInt
        (Filter.Eventually.of_forall (fun z =>
          integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k G z θ))
    rw [← h1] at houterBound
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg _) (sq_nonneg B))).mp houterBound
  refine ⟨⟨hsliceInt, houterInt⟩, ?_⟩
  rw [Work.Spaces.HkNorm]
  have h2 : (b - a) ^ 2 * B ^ 2 = ((b - a) * B) ^ 2 := by ring
  calc Real.sqrt (Work.Spaces.HkSq α k G)
      ≤ Real.sqrt (((b - a) * B) ^ 2) := Real.sqrt_le_sqrt (by rw [← h2]; exact hSqG)
    _ = |(b - a) * B| := Real.sqrt_sq_eq_abs _
    _ = (b - a) * B := abs_of_nonneg (mul_nonneg hab0 hB)
    _ = B * (b - a) := by ring

end Work.FTS.EpsEngine.PerzTools
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptApp.lam_Dz_sq_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `lam_Dz_sq_le`

The angular moment of the truncated source is `lam n F z = ∫_θ zetaR n θ · F z θ · sinθcos²θ`.
Because `F_*(F) = 0`, the radial derivative `D_z^s(lam n F)` differs from the *truncated*
moment integral only through the factor `zetaR n θ - 1`, which is supported where
`sin(2θ) ≤ 2·(2/n)`: this produces the smallness `(2/n)^(2+η)`.

`D_z^m (chiR n · lam n F)` is then expanded by the Leibniz rule; the multipliers `D_z^b(chiR n)`
are uniformly bounded in `n`, which gives the stated estimate.

The proof is split into elementary inputs (proved elsewhere) and the present assembly:
* `LamEst.lamContDiffOn` — `lam n F` is `C^m` on `(0,∞)`;
* `LamEst.chiR_dzIter_bound` — a uniform bound for `D_z^b (chiR n)`;
* `LamEst.lam_correction_sq_le` — the pointwise (a.e.) Cauchy–Schwarz bound on the correction
  `D_z^s(lam n F)`;
* `LamEst.integrableOn_slice_L2` — the `z`-integrability of the weighted `L²`-slice of `D_z^i F`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptApp

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The radial cutoff `chiR n` is `C^m` on `(0,∞)` (indeed smooth on all of `ℝ`). -/
private theorem chiR_contDiffOn (n m : ℕ) : ContDiffOn ℝ m (chiR n) (Set.Ioi (0 : ℝ)) := by
  have hcut : ContDiff ℝ ((m : ℕ) : WithTop ℕ∞) cut01 :=
    Real.smoothTransition.contDiff (n := (m : ℕ∞))
  have h1 : ContDiff ℝ ((m : ℕ) : WithTop ℕ∞) (fun z : ℝ => cut01 ((n : ℝ) * z - 1)) :=
    hcut.comp (by fun_prop)
  have h2 : ContDiff ℝ ((m : ℕ) : WithTop ℕ∞) (fun z : ℝ => cut01 (2 - z / (n : ℝ))) :=
    hcut.comp (by fun_prop)
  have h3 : ContDiff ℝ ((m : ℕ) : WithTop ℕ∞)
      (fun z : ℝ => cut01 ((n : ℝ) * z - 1) * cut01 (2 - z / (n : ℝ))) := h1.mul h2
  change ContDiffOn ℝ ((m : ℕ) : WithTop ℕ∞)
    (fun z : ℝ => cut01 ((n : ℝ) * z - 1) * cut01 (2 - z / (n : ℝ))) (Set.Ioi (0 : ℝ))
  exact h3.contDiffOn

/-- The assembly of the estimate `lam_Dz_sq_le` from its four elementary inputs. -/
private theorem lam_Dz_sq_le_of_estimates {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF : Work.Spaces.HkMem α k F)
    {K : ℕ → ℝ} (hK0 : ∀ b, 0 ≤ K b)
    (hK : ∀ (n b : ℕ) (z θ : ℝ),
        |Work.Spaces.DzIter b (fun z _ : ℝ => chiR n z) z θ| ≤ K b)
    (hLam : ∀ (n : ℕ), 1 ≤ n → ∀ m : ℕ,
        ContDiffOn ℝ m (fun z : ℝ => lam n F z) (Set.Ioi (0 : ℝ)))
    {Cmom : ℝ} (hCmom0 : 0 ≤ Cmom)
    (hcorr : ∀ (n : ℕ), 2 ≤ n → ∀ (s : ℕ), s ≤ k →
        ∀ᵐ z ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi (0 : ℝ))),
          (Work.Spaces.DzIter s (fun z _ => lam n F z) z 0) ^ 2 * (Work.Spaces.w z) ^ 2
            ≤ Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)
              * (∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.DzIter s F z θ
                    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2))
    (hint : ∀ (i : ℕ), i ≤ k →
        MeasureTheory.IntegrableOn
          (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.DzIter i F z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          Work.Spaces.Iz) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ), 2 ≤ n → ∀ (m : ℕ), m ≤ k → ∀ θ₀ : ℝ,
      MeasureTheory.integral
        (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi (0 : ℝ)))
        (fun z => (Work.Spaces.DzIter m
            (fun z _ => chiR n z * lam n F z) z θ₀) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ C * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F := by
  set Ssum : ℝ := ∑ b ∈ Finset.range (k + 1), ((k.choose b : ℝ)) ^ 2 * (K b) ^ 2 with hSsum
  have hSsum0 : 0 ≤ Ssum := by
    rw [hSsum]
    exact Finset.sum_nonneg fun b _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hk1 : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  have hC0 : 0 ≤ 1 + ((k : ℝ) + 1) * Ssum * Cmom * ((k : ℝ) + 1) := by
    have : 0 ≤ ((k : ℝ) + 1) * Ssum * Cmom * ((k : ℝ) + 1) :=
      mul_nonneg (mul_nonneg (mul_nonneg hk1 hSsum0) hCmom0) hk1
    linarith
  refine ⟨1 + ((k : ℝ) + 1) * Ssum * Cmom * ((k : ℝ) + 1), hC0, ?_⟩
  intro n hn m hm θ₀
  -- the a.e. statement of the correction bound, for all `b ≤ k`
  have hae : ∀ᵐ z ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi (0 : ℝ))),
      ∀ b ∈ Finset.range (k + 1),
        (Work.Spaces.w z) ^ 2
            * (Work.Spaces.DzIter b (fun z _ => lam n F z) z 0) ^ 2
          ≤ Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)
            * (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.DzIter b F z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
    rw [Finset.eventually_all]
    intro b hb
    filter_upwards [hcorr n hn b (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb))] with z hz
    calc (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter b (fun z _ => lam n F z) z 0) ^ 2
        = (Work.Spaces.DzIter b (fun z _ => lam n F z) z 0) ^ 2 * (Work.Spaces.w z) ^ 2 := by
          ring
      _ ≤ _ := hz
  -- the Leibniz expansion
  have hchi : ContDiffOn ℝ m (chiR n) (Set.Ioi (0 : ℝ)) := chiR_contDiffOn n m
  have hlam : ContDiffOn ℝ m (fun z : ℝ => lam n F z) (Set.Ioi (0 : ℝ)) := hLam n (by omega) m
  have hZop_chi : ∀ (b : ℕ) (z : ℝ),
      Work.Spaces.Zop^[b] (chiR n) z = Work.Spaces.DzIter b (fun z _ : ℝ => chiR n z) z θ₀ := by
    intro b z
    have h1 := congrFun (Work.FTS.LocData.Zop_iterate_slice b (fun z _ : ℝ => chiR n z) θ₀) z
    have h2 : (fun z : ℝ => (fun z _ : ℝ => chiR n z) z θ₀) = chiR n := by funext z; rfl
    rw [h2] at h1
    exact h1.symm
  have hZop_lam : ∀ (b : ℕ) (z : ℝ),
      Work.Spaces.Zop^[b] (lam n F) z = Work.Spaces.DzIter b (fun z _ : ℝ => lam n F z) z 0 := by
    intro b z
    have h1 := congrFun (Work.FTS.LocData.Zop_iterate_slice b (fun z _ : ℝ => lam n F z) 0) z
    have h2 : (fun z : ℝ => (fun z _ : ℝ => lam n F z) z 0) = lam n F := by funext z; rfl
    rw [h2] at h1
    exact h1.symm
  have hZop_prod : ∀ z : ℝ,
      Work.Spaces.Zop^[m] (chiR n * lam n F) z
        = Work.Spaces.DzIter m (fun z _ : ℝ => chiR n z * lam n F z) z θ₀ := by
    intro z
    have h1 := congrFun (Work.FTS.LocData.Zop_iterate_slice m
      (fun z _ : ℝ => chiR n z * lam n F z) θ₀) z
    have h2 : (fun z : ℝ => (fun z _ : ℝ => chiR n z * lam n F z) z θ₀) = chiR n * lam n F := by
      funext z
      rfl
    rw [h2] at h1
    exact h1.symm
  have hLeib : ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Spaces.DzIter m (fun z _ : ℝ => chiR n z * lam n F z) z θ₀
        = ∑ b ∈ Finset.range (m + 1), (m.choose b : ℝ)
            * (Work.Spaces.DzIter b (fun z _ : ℝ => chiR n z) z θ₀
                * Work.Spaces.DzIter (m - b) (fun z _ : ℝ => lam n F z) z 0) := by
    intro z hz
    have hkey : Work.Spaces.Zop^[m] (chiR n * lam n F) z
        = ∑ b ∈ Finset.range (m + 1), (m.choose b : ℝ)
            * (Work.Spaces.Zop^[b] (chiR n) z * Work.Spaces.Zop^[m - b] (lam n F) z) :=
      Work.FTS.FinalClock.ZopIterLeibniz (N := m) (U := Set.Ioi (0 : ℝ)) isOpen_Ioi
        (u := chiR n) (v := lam n F) hchi hlam hz
    rw [← hZop_prod z, hkey]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hZop_chi b z, hZop_lam (m - b) z]
  -- the pointwise bound
  have hp2n0 : 0 ≤ (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) :=
    Real.rpow_nonneg (by positivity) _
  have hpoint :
      ∀ᵐ z ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi (0 : ℝ))),
      (Work.Spaces.w z) ^ 2
          * (Work.Spaces.DzIter m (fun z _ : ℝ => chiR n z * lam n F z) z θ₀) ^ 2
        ≤ ((k : ℝ) + 1) * Ssum * Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)
            * ∑ i ∈ Finset.range (k + 1),
                (∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.DzIter i F z θ
                    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
    filter_upwards [hae, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi]
      with z hz_ae hz
    set Ab : ℕ → ℝ := fun b => (m.choose b : ℝ)
      * (Work.Spaces.DzIter b (fun z _ : ℝ => chiR n z) z θ₀
          * Work.Spaces.DzIter (m - b) (fun z _ : ℝ => lam n F z) z 0) with hAb
    set hh : ℕ → ℝ := fun i => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.DzIter i F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 with hhh
    have hhh0 : ∀ i : ℕ, 0 ≤ hh i := by
      intro i
      rw [hhh]
      exact integral_nonneg fun θ => sq_nonneg _
    have hleib := hLeib z hz
    have hsq : (Work.Spaces.DzIter m (fun z _ : ℝ => chiR n z * lam n F z) z θ₀) ^ 2
        ≤ ((m : ℝ) + 1) * ∑ b ∈ Finset.range (m + 1), (Ab b) ^ 2 := by
      rw [hleib]
      have h := sq_sum_le_card_mul_sum_sq (s := Finset.range (m + 1)) (f := Ab)
      simpa only [Finset.card_range, Nat.cast_add, Nat.cast_one] using h
    have hterm : ∀ b ∈ Finset.range (m + 1),
        (Work.Spaces.w z) ^ 2 * (Ab b) ^ 2
          ≤ Ssum * (Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * hh (m - b)) := by
      intro b hb
      have hb1 : b ≤ k := by
        have := Finset.mem_range.mp hb
        omega
      have hmbk : m - b ∈ Finset.range (k + 1) := by
        have := Finset.mem_range.mp hb
        exact Finset.mem_range.mpr (by omega)
      have hcb : ((m.choose b : ℝ)) ^ 2 ≤ ((k.choose b : ℝ)) ^ 2 := by
        have h1 : m.choose b ≤ k.choose b := Nat.choose_le_choose b hm
        have h2 : ((m.choose b : ℕ) : ℝ) ≤ ((k.choose b : ℕ) : ℝ) := by exact_mod_cast h1
        nlinarith [h2]
      have hkb : |Work.Spaces.DzIter b (fun z _ : ℝ => chiR n z) z θ₀| ≤ K b := hK n b z θ₀
      have hsq2 : (Work.Spaces.DzIter b (fun z _ : ℝ => chiR n z) z θ₀) ^ 2 ≤ (K b) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hkb 2
      have hcor := hz_ae (m - b) hmbk
      have hcor' : (Work.Spaces.DzIter (m - b) (fun z _ : ℝ => lam n F z) z 0) ^ 2
            * (Work.Spaces.w z) ^ 2
          ≤ Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * hh (m - b) := by
        rw [hhh]
        calc (Work.Spaces.DzIter (m - b) (fun z _ : ℝ => lam n F z) z 0) ^ 2
              * (Work.Spaces.w z) ^ 2
            = (Work.Spaces.w z) ^ 2
              * (Work.Spaces.DzIter (m - b) (fun z _ : ℝ => lam n F z) z 0) ^ 2 := by ring
          _ ≤ _ := hcor
      have hcK : ((m.choose b : ℝ)) ^ 2
            * (Work.Spaces.DzIter b (fun z _ : ℝ => chiR n z) z θ₀) ^ 2
          ≤ ((k.choose b : ℝ)) ^ 2 * (K b) ^ 2 :=
        mul_le_mul hcb hsq2 (sq_nonneg _) (sq_nonneg _)
      have hmain := mul_le_mul hcK hcor'
        (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      have hSle : ((k.choose b : ℝ)) ^ 2 * (K b) ^ 2 ≤ Ssum := by
        rw [hSsum]
        exact Finset.single_le_sum (f := fun b => ((k.choose b : ℝ)) ^ 2 * (K b) ^ 2)
          (fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
          (Finset.mem_range.mpr (by omega))
      have hC0 : 0 ≤ Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * hh (m - b) :=
        mul_nonneg (mul_nonneg hCmom0 hp2n0) (hhh0 _)
      calc (Work.Spaces.w z) ^ 2 * (Ab b) ^ 2
          = ((m.choose b : ℝ)) ^ 2
              * (Work.Spaces.DzIter b (fun z _ : ℝ => chiR n z) z θ₀) ^ 2
              * ((Work.Spaces.DzIter (m - b) (fun z _ : ℝ => lam n F z) z 0) ^ 2
                * (Work.Spaces.w z) ^ 2) := by
            rw [hAb]
            ring
        _ ≤ ((k.choose b : ℝ)) ^ 2 * (K b) ^ 2
              * (Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * hh (m - b)) := hmain
        _ ≤ Ssum * (Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * hh (m - b)) :=
              mul_le_mul_of_nonneg_right hSle hC0
    have hsumprod : (∑ b ∈ Finset.range (m + 1),
          Ssum * (Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * hh (m - b)))
        = (Ssum * (Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)))
          * ∑ b ∈ Finset.range (m + 1), hh (m - b) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by ring
    calc (Work.Spaces.w z) ^ 2
          * (Work.Spaces.DzIter m (fun z _ : ℝ => chiR n z * lam n F z) z θ₀) ^ 2
        ≤ (Work.Spaces.w z) ^ 2 * (((m : ℝ) + 1) * ∑ b ∈ Finset.range (m + 1), (Ab b) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
      _ = ((m : ℝ) + 1) * ((Work.Spaces.w z) ^ 2
            * ∑ b ∈ Finset.range (m + 1), (Ab b) ^ 2) := by ring
      _ = ((m : ℝ) + 1) * ∑ b ∈ Finset.range (m + 1),
            (Work.Spaces.w z) ^ 2 * (Ab b) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ ((m : ℝ) + 1) * ∑ b ∈ Finset.range (m + 1),
            Ssum * (Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * hh (m - b)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by positivity)
      _ = ((m : ℝ) + 1) * ((Ssum * (Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)))
            * ∑ b ∈ Finset.range (m + 1), hh (m - b)) := by rw [hsumprod]
      _ = ((m : ℝ) + 1) * ((Ssum * (Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)))
            * ∑ i ∈ Finset.range (m + 1), hh i) := by
          rw [show (∑ b ∈ Finset.range (m + 1), hh (m - b))
              = ∑ b ∈ Finset.range (m + 1), hh (m + 1 - 1 - b) from rfl,
            Finset.sum_range_reflect hh (m + 1)]
      _ ≤ ((m : ℝ) + 1) * ((Ssum * (Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)))
            * ∑ i ∈ Finset.range (k + 1), hh i) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ ?_)
            (by positivity)
          · exact Finset.sum_le_sum_of_subset_of_nonneg
              (fun i hi => Finset.mem_range.mpr (by
                have := Finset.mem_range.mp hi; omega))
              (fun i _ _ => hhh0 i)
          · exact mul_nonneg hSsum0 (mul_nonneg hCmom0 hp2n0)
      _ ≤ ((k : ℝ) + 1) * ((Ssum * (Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)))
            * ∑ i ∈ Finset.range (k + 1), hh i) :=
          mul_le_mul_of_nonneg_right (by
            have : m + 1 ≤ k + 1 := by omega
            exact_mod_cast this)
            (mul_nonneg (mul_nonneg hSsum0 (mul_nonneg hCmom0 hp2n0))
              (Finset.sum_nonneg fun i _ => hhh0 i))
      _ = ((k : ℝ) + 1) * Ssum * Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)
            * ∑ i ∈ Finset.range (k + 1),
                (∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.DzIter i F z θ
                    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
          rw [hhh]
          ring
  -- integrability of the majorant
  have hmeas : MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi (0 : ℝ))
      = MeasureTheory.Measure.restrict MeasureTheory.volume Work.Spaces.Iz := by
    rw [Work.Spaces.Iz]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))
  have hmaj_int : MeasureTheory.Integrable
      (fun z => ((k : ℝ) + 1) * Ssum * Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)
        * ∑ i ∈ Finset.range (k + 1),
            (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.DzIter i F z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2))
      (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi (0 : ℝ))) := by
    rw [hmeas]
    exact (integrable_finsetSum (Finset.range (k + 1))
      (fun i hi => hint i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))).const_mul _
  have hmain := MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hmaj_int hpoint
  -- compute the integral of the majorant
  have hInt : MeasureTheory.integral
      (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi (0 : ℝ)))
      (fun z => ∑ i ∈ Finset.range (k + 1),
        (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter i F z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2))
      = ∑ i ∈ Finset.range (k + 1),
          Work.Spaces.L2Sq (fun z θ => Work.Spaces.DzIter i F z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) := by
    rw [hmeas]
    rw [integral_finsetSum]
    · exact Finset.sum_congr rfl fun i _ => rfl
    · intro i hi
      exact hint i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  have hL2 : ∀ i ∈ Finset.range (k + 1),
      Work.Spaces.L2Sq (fun z θ => Work.Spaces.DzIter i F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
        ≤ Work.Spaces.HkSq α k F := fun i hi =>
    Work.Spaces.L2Sq_DzIter_le_HkSq α k F hF i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  have hsum_le : (∑ i ∈ Finset.range (k + 1),
      Work.Spaces.L2Sq (fun z θ => Work.Spaces.DzIter i F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
      ≤ ((k : ℝ) + 1) * Work.Spaces.HkSq α k F := by
    calc (∑ i ∈ Finset.range (k + 1),
        Work.Spaces.L2Sq (fun z θ => Work.Spaces.DzIter i F z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
        ≤ ∑ _i ∈ Finset.range (k + 1), Work.Spaces.HkSq α k F := Finset.sum_le_sum hL2
      _ = ((k : ℝ) + 1) * Work.Spaces.HkSq α k F := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have hconst : 0 ≤ ((k : ℝ) + 1) * Ssum * Cmom :=
    mul_nonneg (mul_nonneg hk1 hSsum0) hCmom0
  have hmaj_val : MeasureTheory.integral
      (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi (0 : ℝ)))
      (fun z => ((k : ℝ) + 1) * Ssum * Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)
        * ∑ i ∈ Finset.range (k + 1),
            (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.DzIter i F z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2))
      = ((k : ℝ) + 1) * Ssum * Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)
        * (∑ i ∈ Finset.range (k + 1),
            Work.Spaces.L2Sq (fun z θ => Work.Spaces.DzIter i F z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) := by
    rw [MeasureTheory.integral_const_mul, hInt]
  have hfinal : ((k : ℝ) + 1) * Ssum * Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)
        * (∑ i ∈ Finset.range (k + 1),
            Work.Spaces.L2Sq (fun z θ => Work.Spaces.DzIter i F z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
      ≤ (1 + ((k : ℝ) + 1) * Ssum * Cmom * ((k : ℝ) + 1))
          * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F := by
    have hHk := Work.Spaces.HkSq_nonneg α k F
    have hstep : ((k : ℝ) + 1) * Ssum * Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)
          * (∑ i ∈ Finset.range (k + 1),
              Work.Spaces.L2Sq (fun z θ => Work.Spaces.DzIter i F z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
        ≤ ((k : ℝ) + 1) * Ssum * Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)
          * (((k : ℝ) + 1) * Work.Spaces.HkSq α k F) :=
      mul_le_mul_of_nonneg_left hsum_le
        (mul_nonneg (mul_nonneg (mul_nonneg hk1 hSsum0) hCmom0) hp2n0)
    have hstep2 : ((k : ℝ) + 1) * Ssum * Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)
          * (((k : ℝ) + 1) * Work.Spaces.HkSq α k F)
        ≤ (1 + ((k : ℝ) + 1) * Ssum * Cmom * ((k : ℝ) + 1))
          * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F := by
      nlinarith [hconst, hp2n0, hHk, hk1]
    linarith [hstep, hstep2]
  have hgoal_eq : MeasureTheory.integral
        (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi (0 : ℝ)))
        (fun z => (Work.Spaces.DzIter m
            (fun z _ => chiR n z * lam n F z) z θ₀) ^ 2 * (Work.Spaces.w z) ^ 2)
      = MeasureTheory.integral
        (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi (0 : ℝ)))
        (fun z => (Work.Spaces.w z) ^ 2
          * (Work.Spaces.DzIter m (fun z _ => chiR n z * lam n F z) z θ₀) ^ 2) :=
    integral_congr_ae (Eventually.of_forall fun z => by ring)
  rw [hgoal_eq]
  calc MeasureTheory.integral
        (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi (0 : ℝ)))
        (fun z => (Work.Spaces.w z) ^ 2
          * (Work.Spaces.DzIter m (fun z _ => chiR n z * lam n F z) z θ₀) ^ 2)
      ≤ MeasureTheory.integral
          (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi (0 : ℝ)))
          (fun z => ((k : ℝ) + 1) * Ssum * Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)
            * ∑ i ∈ Finset.range (k + 1),
                (∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.DzIter i F z θ
                    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)) :=
        hmain
    _ = ((k : ℝ) + 1) * Ssum * Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)
        * (∑ i ∈ Finset.range (k + 1),
            Work.Spaces.L2Sq (fun z θ => Work.Spaces.DzIter i F z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) := hmaj_val
    _ ≤ (1 + ((k : ℝ) + 1) * Ssum * Cmom * ((k : ℝ) + 1))
          * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F := hfinal

theorem lam_Dz_sq_le {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF : Work.Spaces.HkMem α k F)
    (hFs : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar F z = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ), 2 ≤ n → ∀ (m : ℕ), m ≤ k → ∀ θ₀ : ℝ,
      MeasureTheory.integral
        (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi 0))
        (fun z => (Work.Spaces.DzIter m
            (fun z _ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
              * Work.FTS.PhiStar.Honesty.CptApp.lam n F z) z θ₀)^2 * (Work.Spaces.w z)^2)
      ≤ C * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F := by
  obtain ⟨K, hK0, hK⟩ := Work.FTS.PhiStar.Honesty.CptApp.LamAux.chiR_dzIter_boundAux
  have hlam : ∀ (n : ℕ), 1 ≤ n → ∀ m : ℕ,
      ContDiffOn ℝ m (fun z : ℝ => lam n F z) (Set.Ioi (0 : ℝ)) :=
    fun n hn m => Work.FTS.PhiStar.Honesty.CptApp.LamEst.lamContDiffOn hsm hn m
  have hint : ∀ (i : ℕ), i ≤ k →
      MeasureTheory.IntegrableOn
        (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter i F z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        Work.Spaces.Iz :=
    fun i hi => Work.FTS.PhiStar.Honesty.CptApp.LamEst.integrableOn_slice_L2 hsm hF hi
  obtain ⟨Cmom, hCmom0, hcorr⟩ :=
    Work.FTS.PhiStar.Honesty.CptApp.LamEst.lam_correction_sq_le hsm hF hFs
  exact lam_Dz_sq_le_of_estimates hsm hF hK0 hK hlam hCmom0 hcorr hint

end Work.FTS.PhiStar.Honesty.CptApp
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.HkIntegrand_K_le_of_bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

theorem HkIntegrand_K_le_of_bounds {α : ℝ} (hα : 0 < α)
    (hγ : Work.Spaces.gam α ≤ 3 / 2) {K : ℕ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) {G : ℝ → ℝ → ℝ}
    (hGnn : ∀ z : ℝ, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ G z θ)
    (h0 : ∀ j : ℕ, j ≤ K → ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter j f) z θ ≤ 4 * G z θ)
    (h1 : ∀ j r : ℕ, 1 ≤ r → r + j ≤ K → ∀ z : ℝ, 0 < z →
      ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
        Work.FTS.ClassC.vig α f r j z θ ≤ 4 * G z θ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.HkIntegrand α K f z θ
      ≤ (4 * ((K : ℝ) + 1) + 4 * (K : ℝ) * Work.FTS.ClassC.vanSum α hα hγ f hsm K) * G z θ := by
  classical
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hGz : 0 ≤ G z θ := hGnn z θ hθ
  -- the pointwise slot reduction: pure radial level-`0` slots + `vanC`-weighted vanishing slots
  have hkey := Work.FTS.ClassC.HkIntegrand_le_pure_vanishing hα hγ hsm K z θ hzI hθI
  -- the pure part: `K + 1` slots, each `≤ 4G`
  have hpure : (∑ j ∈ Finset.range (K + 1),
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter j f) z θ)
      ≤ 4 * ((K : ℝ) + 1) * G z θ := by
    calc (∑ j ∈ Finset.range (K + 1),
            Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter j f) z θ)
        ≤ ∑ j ∈ Finset.range (K + 1), 4 * G z θ := by
          refine Finset.sum_le_sum fun j hj => ?_
          exact h0 j (by have := Finset.mem_range.mp hj; omega) z hz θ hθ
      _ = 4 * ((K : ℝ) + 1) * G z θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  -- the mixed part: each slot carries a factor `vanC ≥ 0` and an inner sum of at most `i ≤ K`
  -- vanishing-weight slots, each `≤ 4G`
  have hmix : (∑ j ∈ Finset.range (K + 1), ∑ i ∈ Finset.Icc 1 (K - j),
        (if h : 1 ≤ i then Work.FTS.ClassC.vanC α hα hγ f hsm i j h else 0)
          * ∑ r ∈ Finset.Icc 1 i, Work.FTS.ClassC.vig α f r j z θ)
      ≤ 4 * (K : ℝ) * Work.FTS.ClassC.vanSum α hα hγ f hsm K * G z θ := by
    have hinner : ∀ j ∈ Finset.range (K + 1), ∀ i ∈ Finset.Icc 1 (K - j),
        ∑ r ∈ Finset.Icc 1 i, Work.FTS.ClassC.vig α f r j z θ ≤ 4 * (K : ℝ) * G z θ := by
      intro j hj i hi
      have hile : i ≤ K - j := (Finset.mem_Icc.mp hi).2
      have hiK : i ≤ K := by omega
      calc ∑ r ∈ Finset.Icc 1 i, Work.FTS.ClassC.vig α f r j z θ
          ≤ ∑ r ∈ Finset.Icc 1 i, 4 * G z θ := by
            refine Finset.sum_le_sum fun r hr => ?_
            have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
            have hrl : r ≤ i := (Finset.mem_Icc.mp hr).2
            exact h1 j r hr1 (by omega) z hz θ hθ
        _ = ((Finset.Icc 1 i).card : ℝ) * (4 * G z θ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 4 * (K : ℝ) * G z θ := by
            have hcard : (Finset.Icc 1 i).card ≤ K := by
              have hsub : Finset.Icc 1 i ⊆ Finset.Icc 1 K := by
                intro x hx
                exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hx).1,
                  le_trans (Finset.mem_Icc.mp hx).2 hiK⟩
              calc (Finset.Icc 1 i).card ≤ (Finset.Icc 1 K).card := Finset.card_le_card hsub
                _ = K := by rw [Nat.card_Icc]; omega
            have hcardR : ((Finset.Icc 1 i).card : ℝ) ≤ (K : ℝ) := by exact_mod_cast hcard
            have h4 : 0 ≤ 4 * G z θ := by linarith
            calc ((Finset.Icc 1 i).card : ℝ) * (4 * G z θ)
                ≤ (K : ℝ) * (4 * G z θ) := mul_le_mul_of_nonneg_right hcardR h4
              _ = 4 * (K : ℝ) * G z θ := by ring
    have hmul : ∀ j ∈ Finset.range (K + 1), ∀ i ∈ Finset.Icc 1 (K - j),
        (if h : 1 ≤ i then Work.FTS.ClassC.vanC α hα hγ f hsm i j h else 0)
          * (∑ r ∈ Finset.Icc 1 i, Work.FTS.ClassC.vig α f r j z θ)
        ≤ (if h : 1 ≤ i then Work.FTS.ClassC.vanC α hα hγ f hsm i j h else 0)
          * (4 * (K : ℝ) * G z θ) := by
      intro j hj i hi
      have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
      have hpos : 0 ≤ (if h : 1 ≤ i then Work.FTS.ClassC.vanC α hα hγ f hsm i j h else 0) := by
        rw [dite_eq_left hi1]
        exact le_of_lt (Work.FTS.ClassC.vanC_pos α hα hγ f hsm i j hi1)
      exact mul_le_mul_of_nonneg_left (hinner j hj i hi) hpos
    calc (∑ j ∈ Finset.range (K + 1), ∑ i ∈ Finset.Icc 1 (K - j),
          (if h : 1 ≤ i then Work.FTS.ClassC.vanC α hα hγ f hsm i j h else 0)
            * ∑ r ∈ Finset.Icc 1 i, Work.FTS.ClassC.vig α f r j z θ)
        ≤ ∑ j ∈ Finset.range (K + 1), ∑ i ∈ Finset.Icc 1 (K - j),
            (if h : 1 ≤ i then Work.FTS.ClassC.vanC α hα hγ f hsm i j h else 0)
              * (4 * (K : ℝ) * G z θ) :=
          Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun i hi => hmul j hj i hi
      _ = (∑ j ∈ Finset.range (K + 1), ∑ i ∈ Finset.Icc 1 (K - j),
            (if h : 1 ≤ i then Work.FTS.ClassC.vanC α hα hγ f hsm i j h else 0))
              * (4 * (K : ℝ) * G z θ) := by
          simp only [← Finset.sum_mul]
      _ = 4 * (K : ℝ) * Work.FTS.ClassC.vanSum α hα hγ f hsm K * G z θ := by
          simp only [Work.FTS.ClassC.vanSum]
          ring
  have hfin : Work.Spaces.HkIntegrand α K f z θ
      ≤ 4 * ((K : ℝ) + 1) * G z θ
        + 4 * (K : ℝ) * Work.FTS.ClassC.vanSum α hα hγ f hsm K * G z θ := by
    linarith
  calc Work.Spaces.HkIntegrand α K f z θ
      ≤ 4 * ((K : ℝ) + 1) * G z θ
        + 4 * (K : ℝ) * Work.FTS.ClassC.vanSum α hα hγ f hsm K * G z θ := hfin
    _ = (4 * ((K : ℝ) + 1) + 4 * (K : ℝ) * Work.FTS.ClassC.vanSum α hα hγ f hsm K) * G z θ := by
        ring

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.HkIntegrand_zero_DzIter_zsqPz2_le_K =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Two elementary bookkeeping lemmas -/

/-- At level `0` the `ℋ⁰`-integrand is the single weighted square
`(f z θ · w z / sin(2θ)^{η/2})²`: the first sum of `HkIntegrand` has the single term `i = 0`
and the second (mixed) sum is empty, its index condition `1 ≤ i` being false. -/
theorem HkIntegrand_zero_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  rw [Work.Spaces.HkIntegrand, Finset.sum_range_one, Finset.sum_range_one, Finset.sum_range_one,
    Work.Spaces.DzIter_zero]
  norm_num

/-- **The operator identity.**  On the open quadrant, `D_z^j` commutes with `z²∂_z²`, and
`z²∂_z² = D_z² − D_z` there (both `z²∂_z²` and `D_z` are `z`-only operators, so the commutation
is Clairaut for the `z`-variable):
`D_z^j (z²∂_z²Ψ) = D_z^{j+2}Ψ − D_z^{j+1}Ψ`. -/
theorem DzIter_zsqPzIter2_eq {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) (j : ℕ) :
    ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.Spaces.DzIter j (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
        = Work.Spaces.DzIter (j + 2) Ψ z θ - Work.Spaces.DzIter (j + 1) Ψ z θ := by
  intro z θ hz hθ
  have hθ0 : 0 < θ := hθ.1
  have hπ : θ < Real.pi / 2 := hθ.2
  have hD : Work.Spaces.DzIter j (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
      = z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ :=
    Work.FTS.ClassC.NormPiecesAux.zsqPz2_DzIter_eqOn Ψ hΨ j z θ hz hθ0 hπ
  have hE : z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ
      = Work.Spaces.DzIter 2 (Work.Spaces.DzIter j Ψ) z θ
        - Work.Spaces.DzIter 1 (Work.Spaces.DzIter j Ψ) z θ :=
    Work.FTS.ClassC.seven_zsq_pzIter_two_eq (Work.Spaces.DzIter j Ψ) (hΨ.DzIter j)
      z θ hz hθ0 hπ
  have e2 : Work.Spaces.DzIter 2 (Work.Spaces.DzIter j Ψ)
      = Work.Spaces.DzIter (j + 2) Ψ := by
    rw [← Work.FTS.ClassC.seven_DzIter_add 2 j Ψ]
    exact congrArg (fun n => Work.Spaces.DzIter n Ψ) (by omega)
  have e1 : Work.Spaces.DzIter 1 (Work.Spaces.DzIter j Ψ)
      = Work.Spaces.DzIter (j + 1) Ψ := by
    rw [← Work.FTS.ClassC.seven_DzIter_add 1 j Ψ]
    exact congrArg (fun n => Work.Spaces.DzIter n Ψ) (by omega)
  rw [hD, hE, e2, e1]

/-! ## The target -/

theorem HkIntegrand_zero_DzIter_zsqPz2_le_K {α : ℝ} {K : ℕ}
    (hγ : Work.Spaces.gam α ≤ 3 / 2) {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    ∀ j : ℕ, j ≤ K → ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.Spaces.HkIntegrand α 0
          (Work.Spaces.DzIter j (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
        ≤ 4 * Work.FTS.PhiStar.Honesty.vanGridK α Ψ K z θ := by
  intro j hj z hz θ hθ
  -- the AM–GM kernel and the two dominating grid slots
  have hAM := Work.FTS.ClassC.seven_sq_sub_mul_sq_le
    (Work.Spaces.DzIter (j + 2) Ψ z θ) (Work.Spaces.DzIter (j + 1) Ψ z θ)
    (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
  have hA : Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter (j + 2) Ψ) z θ
      ≤ vanGridK α Ψ K z θ :=
    hkDze_zero_DzIter_le_vanGridK (α := α) (Ψ := Ψ) (K := K) (l := j + 2) (by omega) z θ hθ
  have hB : Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter (j + 1) Ψ) z θ
      ≤ vanGridK α Ψ K z θ :=
    hkDze_zero_DzIter_le_vanGridK (α := α) (Ψ := Ψ) (K := K) (l := j + 1) (by omega) z θ hθ
  rw [HkIntegrand_zero_eq α _ z θ, DzIter_zsqPzIter2_eq hΨ j z θ hz hθ]
  calc ((Work.Spaces.DzIter (j + 2) Ψ z θ - Work.Spaces.DzIter (j + 1) Ψ z θ)
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ 2 * (Work.Spaces.DzIter (j + 2) Ψ z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        + 2 * (Work.Spaces.DzIter (j + 1) Ψ z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := hAM
    _ ≤ 4 * vanGridK α Ψ K z θ := by
        rw [← HkIntegrand_zero_eq α (Work.Spaces.DzIter (j + 2) Ψ) z θ,
          ← HkIntegrand_zero_eq α (Work.Spaces.DzIter (j + 1) Ψ) z θ]
        linarith

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.vanGridK_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

theorem vanGridK_integrable {α : ℝ} {K : ℕ} {Ψ : ℝ → ℝ → ℝ}
    (hσ : ∀ l m : ℕ, l ≤ K + 2 → m ≤ 2 →
      Work.Spaces.HkMem α 0 (Work.Spaces.DzIter l (Work.Spaces.pthIter m Ψ)))
    (hV : ∀ t l : ℕ, 3 ≤ t → t ≤ K + 2 → l ≤ K + 2 →
      (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ =>
          (Work.Spaces.DzIter l (Work.Spaces.pthIter t Ψ) z θ * Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (t : ℝ) - 4 - Work.Spaces.gam α)) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter l (Work.Spaces.pthIter t Ψ) z θ * Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (t : ℝ) - 4 - Work.Spaces.gam α)) Work.Spaces.Iz) :
    (∀ z ∈ Work.Spaces.Iz,
        MeasureTheory.IntegrableOn (fun θ => Work.FTS.PhiStar.Honesty.vanGridK α Ψ K z θ)
          Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
          Work.FTS.PhiStar.Honesty.vanGridK α Ψ K z θ) Work.Spaces.Iz := by
  -- The grid majorant is the sum of two finite families of level-`0` honest integrands.
  have hA : Work.FTS.ClassC.Level0Integrable (fun z θ =>
      ∑ l ∈ Finset.range (K + 3), ∑ m ∈ Finset.range 3,
        Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l (Work.Spaces.pthIter m Ψ)) z θ) := by
    refine Work.FTS.ClassC.Level0Integrable_sum _ fun l hl =>
      Work.FTS.ClassC.Level0Integrable_sum _ fun m hm => ?_
    exact hσ l m (by have := Finset.mem_range.mp hl; omega)
      (by have := Finset.mem_range.mp hm; omega)
  have hB : Work.FTS.ClassC.Level0Integrable (fun z θ =>
      ∑ t ∈ Finset.Icc 3 (K + 2), ∑ l ∈ Finset.range (K + 3),
        Work.FTS.ClassC.hVint α Ψ t l z θ) := by
    refine Work.FTS.ClassC.Level0Integrable_sum _ fun t ht =>
      Work.FTS.ClassC.Level0Integrable_sum _ fun l hl => ?_
    have ht' := Finset.mem_Icc.mp ht
    have hl' : l ≤ K + 2 := by have := Finset.mem_range.mp hl; omega
    exact hV t l ht'.1 ht'.2 hl'
  -- `vanGridK` unfolds definitionally to the sum of the two families.
  exact Work.FTS.ClassC.Level0Integrable_add hA hB

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.vig_zsqPz2_le_K =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem vig_zsqPz2_le_K {α : ℝ} {K : ℕ} (hγ : Work.Spaces.gam α ≤ 3 / 2)
    {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    ∀ j r : ℕ, 1 ≤ r → r + j ≤ K → ∀ z : ℝ, 0 < z →
      ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.FTS.ClassC.vig α (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) r j z θ
        ≤ 4 * Work.FTS.PhiStar.Honesty.vanGridK α Ψ K z θ := by
  intro j r hr hrj z hz θ hθ
  have hrK : r ≤ K + 2 := by omega
  have hj2 : j + 2 ≤ K + 2 := by omega
  have hj1 : j + 1 ≤ K + 2 := by omega
  have hid := Work.FTS.ClassC.vig_DzIter_pthIter_eq hΨ r j z θ hz hθ
  have hsq := Work.FTS.ClassC.seven_sq_sub_mul_sq_le
    (Work.Spaces.DzIter (j + 2) (Work.Spaces.pthIter r Ψ) z θ)
    (Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter r Ψ) z θ) (Work.Spaces.w z)
  have hsnn : 0 ≤ (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - Work.Spaces.gam α) :=
    Real.rpow_nonneg (le_of_lt (Work.FTS.ClassC.sin_two_pos_of_mem_Ioo hθ)) _
  have hA := vig_slot_le_vanGridK hγ Ψ K r (j + 2) hr hrK hj2 z θ hθ
  have hB := vig_slot_le_vanGridK hγ Ψ K r (j + 1) hr hrK hj1 z θ hθ
  rw [Work.FTS.ClassC.vig, hid]
  calc ((Work.Spaces.DzIter (j + 2) (Work.Spaces.pthIter r Ψ) z θ
          - Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter r Ψ) z θ)
        * Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - Work.Spaces.gam α)
      ≤ (2 * (Work.Spaces.DzIter (j + 2) (Work.Spaces.pthIter r Ψ) z θ
              * Work.Spaces.w z) ^ 2
          + 2 * (Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter r Ψ) z θ
              * Work.Spaces.w z) ^ 2)
          * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - Work.Spaces.gam α) :=
        mul_le_mul_of_nonneg_right hsq hsnn
    _ = 2 * ((Work.Spaces.DzIter (j + 2) (Work.Spaces.pthIter r Ψ) z θ
              * Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - Work.Spaces.gam α))
          + 2 * ((Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter r Ψ) z θ
              * Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - Work.Spaces.gam α)) := by ring
    _ ≤ 4 * Work.FTS.PhiStar.Honesty.vanGridK α Ψ K z θ := by linarith

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.StrongEps.HQoAux.cut_slot_L2_bounds_uniform =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.HQoAux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The `α`-uniform version of `Work.FTS.StrongEps.HQoAux.cut_slot_L2_bounds`: the two
constants `C1`, `C2` are chosen *before* `α` and `F`, so they depend only on the cut-off `χ`
and the bound `M`.  Proof = the existing proof of `cut_slot_L2_bounds` with the constant
extraction (`∃ C` from `LocUnif.mixed_rect_L2_bounds`, then `C1 := C`,
`C2 := 3 * (16 + 17 * M ^ 2) * C`) moved *before* the introduction of `α`, `hα`, `F`, `hF`,
`hmem`; everything else is verbatim.-/
theorem cut_slot_L2_bounds_uniform
    {zlo' zhi' tlo' thi' : ℝ} (hzlo' : 0 < zlo') (hzi' : zlo' ≤ zhi') (htlo' : 0 < tlo')
    (hthi' : thi' < Real.pi / 2)
    {χ : ℝ × ℝ → ℝ} (hχsm : ContDiff ℝ 2 χ) (hχnn : ∀ x, 0 ≤ χ x) (hχle1 : ∀ x, χ x ≤ 1)
    (hχzero : ∀ x, x ∉ Set.Icc zlo' zhi' ×ˢ Set.Icc tlo' thi' → χ x = 0)
    {M : ℝ} (hM1 : ∀ x, ‖fderiv ℝ χ x‖ ≤ M) (hM2 : ∀ x, ‖fderiv ℝ (fderiv ℝ χ) x‖ ≤ M) :
    ∃ C1 C2 : ℝ, 0 < C1 ∧ 0 < C2 ∧ ∀ (α : ℝ), 0 < α → ∀ (F : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen F → Work.Spaces.HkMem α 6 F → ∀ (b a : ℕ), a + b ≤ 4 →
      ((∫ x : ℝ × ℝ, (χ x * Function.uncurry (Work.Spaces.mixed b a F) x) ^ 2)
          ≤ C1 * Work.Spaces.HkSq α 6 F) ∧
      ((∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ (fun y : ℝ × ℝ =>
            χ y * Function.uncurry (Work.Spaces.mixed b a F) y)) x‖ ^ 2)
          ≤ C2 * Work.Spaces.HkSq α 6 F) := by
  classical
  -- the rectangle carrying the support of `χ`
  set s : Set (ℝ × ℝ) := Set.Icc zlo' zhi' ×ˢ Set.Icc tlo' thi' with hsdef
  have hsc : IsClosed s := by rw [hsdef]; exact isClosed_Icc.prod isClosed_Icc
  have hsmeas : MeasurableSet s := hsc.measurableSet
  have hscpt : IsCompact s := by rw [hsdef]; exact isCompact_Icc.prod isCompact_Icc
  have hsQ0 : s ⊆ Work.FTS.EllipticEst.Q0 := by
    intro p hp
    rw [hsdef] at hp
    rw [Work.FTS.EllipticEst.mem_Q0]
    exact ⟨lt_of_lt_of_le hzlo' hp.1.1, lt_of_lt_of_le htlo' hp.2.1,
      lt_of_le_of_lt hp.2.2 hthi'⟩
  -- the constant of `mixed_rect_L2_bounds` (independent of `α`, `F`, `b`, `a`)
  obtain ⟨C, hCpos, hCbound⟩ :=
    Work.FTS.StrongEps.LocUnif.mixed_rect_L2_bounds (a := zlo') (b := zhi')
      (c := tlo') (d := thi') hzlo' hzi' htlo' hthi'
  refine ⟨C, 3 * (16 + 17 * M ^ 2) * C, hCpos, ?_, ?_⟩
  · have h16 : (0 : ℝ) < 16 + 17 * M ^ 2 := by nlinarith [sq_nonneg M]
    have h3 : (0 : ℝ) < 3 * (16 + 17 * M ^ 2) := by linarith
    exact mul_pos h3 hCpos
  · intro α hα F hF hmem b a hab
    have hab' : b + a ≤ 4 := by omega
    have hCb := hCbound α hα F hF hmem b a hab'
    have hGsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.mixed b a F) := hF.mixed b a
    have hG2 : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.mixed b a F))
        Work.FTS.EllipticEst.Q0 :=
      hGsm.of_le Work.FTS.StrongEps.LocUnif.two_le_smoothOrder
    have hcont : ContinuousOn (Function.uncurry (Work.Spaces.mixed b a F)) s :=
      hG2.continuousOn.mono hsQ0
    have hI0 : IntegrableOn
        (fun x : ℝ × ℝ => (Function.uncurry (Work.Spaces.mixed b a F) x) ^ 2) s :=
      ContinuousOn.integrableOn_compact hscpt (hcont.pow 2)
    -- ## the first conjunct
    have hb0 : ∫ x in s, (Function.uncurry (Work.Spaces.mixed b a F) x) ^ 2
        ≤ C * Work.Spaces.HkSq α 6 F := by
      rw [hsdef] at hI0 ⊢
      rw [Work.FTS.StrongLWP.Sobolev.eqc_setIntegral_rect_eq hI0]
      exact hCb.1
    -- ## the second conjunct
    have hfd1 : ContDiffOn ℝ 1 (fderiv ℝ (Function.uncurry (Work.Spaces.mixed b a F)))
        Work.FTS.EllipticEst.Q0 :=
      hG2.fderiv_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 (by norm_num)
    have hgd : ∀ y ∈ Work.FTS.EllipticEst.Q0,
        DifferentiableAt ℝ (Function.uncurry (Work.Spaces.mixed b a F)) y := fun y hy =>
      (hG2.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hy)).differentiableAt (by norm_num)
    have hgd2 : ∀ y ∈ Work.FTS.EllipticEst.Q0,
        DifferentiableAt ℝ (fderiv ℝ (Function.uncurry (Work.Spaces.mixed b a F))) y :=
      fun y hy =>
        (hfd1.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hy)).differentiableAt
          (by norm_num)
    have hI1 : IntegrableOn
        (fun x : ℝ × ℝ => ‖fderiv ℝ (Function.uncurry (Work.Spaces.mixed b a F)) x‖ ^ 2) s :=
      ContinuousOn.integrableOn_compact hscpt ((hfd1.continuousOn.mono hsQ0).norm.pow 2)
    -- the dominating function for the second derivative
    set E : ℝ × ℝ → ℝ := fun x =>
        |Work.Spaces.pzIter 2 (Work.Spaces.mixed b a F) x.1 x.2|
          + |Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.mixed b a F)) x.1 x.2|
          + |Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.mixed b a F)) x.1 x.2|
          + |Work.Spaces.pthIter 2 (Work.Spaces.mixed b a F) x.1 x.2| with hEdef
    have hE : ∀ x ∈ s, ‖fderiv ℝ (fderiv ℝ (Function.uncurry (Work.Spaces.mixed b a F))) x‖
        ≤ E x := by
      intro x hx
      exact Work.FTS.StrongEps.LocUnif.norm_fderiv_fderiv_le_basis
        Work.FTS.EllipticEst.isOpen_Q0 hG2 (hsQ0 hx)
    have hcontE : ContinuousOn E s := by
      have hp1 : ContinuousOn
          (fun x : ℝ × ℝ => Work.Spaces.pzIter 2 (Work.Spaces.mixed b a F) x.1 x.2) s :=
        (hGsm.pzIter 2).continuousOn.mono hsQ0
      have hp2 : ContinuousOn
          (fun x : ℝ × ℝ => Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.mixed b a F)) x.1 x.2)
          s := ((hGsm.pth).pz).continuousOn.mono hsQ0
      have hp3 : ContinuousOn
          (fun x : ℝ × ℝ => Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.mixed b a F)) x.1 x.2)
          s := ((hGsm.pz).pth).continuousOn.mono hsQ0
      have hp4 : ContinuousOn
          (fun x : ℝ × ℝ => Work.Spaces.pthIter 2 (Work.Spaces.mixed b a F) x.1 x.2) s :=
        ((hGsm.pth).pth).continuousOn.mono hsQ0
      exact ((hp1.abs.add hp2.abs).add hp3.abs).add hp4.abs
    have hI2 : IntegrableOn (fun x => E x ^ 2) s :=
      ContinuousOn.integrableOn_compact hscpt (hcontE.pow 2)
    -- the four individual `L²`-bounds of the second partials
    have hA1 : IntegrableOn
        (fun x : ℝ × ℝ => (Work.Spaces.pzIter 2 (Work.Spaces.mixed b a F) x.1 x.2) ^ 2) s :=
      ContinuousOn.integrableOn_compact hscpt (((hGsm.pzIter 2).continuousOn.mono hsQ0).pow 2)
    have hA2 : IntegrableOn
        (fun x : ℝ × ℝ => (Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.mixed b a F)) x.1 x.2) ^ 2)
        s :=
      ContinuousOn.integrableOn_compact hscpt
        ((((hGsm.pth).pz).continuousOn.mono hsQ0).pow 2)
    have hA3 : IntegrableOn
        (fun x : ℝ × ℝ => (Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.mixed b a F)) x.1 x.2) ^ 2)
        s :=
      ContinuousOn.integrableOn_compact hscpt
        ((((hGsm.pz).pth).continuousOn.mono hsQ0).pow 2)
    have hA4 : IntegrableOn
        (fun x : ℝ × ℝ => (Work.Spaces.pthIter 2 (Work.Spaces.mixed b a F) x.1 x.2) ^ 2) s :=
      ContinuousOn.integrableOn_compact hscpt
        ((((hGsm.pth).pth).continuousOn.mono hsQ0).pow 2)
    have hb2 : ∫ x in s, E x ^ 2 ≤ 16 * C * Work.Spaces.HkSq α 6 F :=
      Work.FTS.StrongEps.HQoAux.integral_sq_basis_second_le
        (G := Work.Spaces.mixed b a F) (a := zlo') (b := zhi') (c := tlo') (d := thi')
        (C := C) (K := Work.Spaces.HkSq α 6 F)
        hA1 hA2 hA3 hA4
        hCb.2.2.2.1 hCb.2.2.2.2.1 hCb.2.2.2.2.2.1 hCb.2.2.2.2.2.2
    -- the bound for the first derivative of the datum
    obtain ⟨hRD1, hRD2⟩ :=
      Work.FTS.StrongEps.LocUnif.rect_deriv_bounds (F := F) (α := α) (C := C)
        (a' := zlo') (b' := zhi') (c' := tlo') (d' := thi') b a hsQ0 hF
        hCb.2.1 hCb.2.2.1 hCb.2.2.2.1 hCb.2.2.2.2.1 hCb.2.2.2.2.2.1 hCb.2.2.2.2.2.2
    have hb1' : ∫ x in s, ‖fderiv ℝ (Function.uncurry (Work.Spaces.mixed b a F)) x‖ ^ 2
        ≤ 4 * C * Work.Spaces.HkSq α 6 F := hRD1
    have hM0 : ∀ x, ‖χ x‖ ≤ (1 : ℝ) := fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hχnn x)]; exact hχle1 x
    have hmain : ∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ (fun y : ℝ × ℝ =>
          χ y * Function.uncurry (Work.Spaces.mixed b a F) y)) x‖ ^ 2
        ≤ 3 * ((1 ^ 2 * ∫ x in s, E x ^ 2)
            + ((2 * M) ^ 2 * ∫ x in s,
                ‖fderiv ℝ (Function.uncurry (Work.Spaces.mixed b a F)) x‖ ^ 2)
            + M ^ 2 * ∫ x in s, (Function.uncurry (Work.Spaces.mixed b a F) x) ^ 2) :=
      Work.FTS.StrongLWP.Sobolev.eqc_integral_fderiv_fderiv_mul_sq_le
        (χ := χ) (g := Function.uncurry (Work.Spaces.mixed b a F)) (s := s)
        (U := Work.FTS.EllipticEst.Q0) (M0 := 1) (M1 := M) (M2 := M) (E := E)
        hχsm hsc hχzero hM0 hM1 hM2 Work.FTS.EllipticEst.isOpen_Q0 hsQ0 hgd hgd2 hE hI0 hI1 hI2
    constructor
    · calc ∫ x : ℝ × ℝ, (χ x * Function.uncurry (Work.Spaces.mixed b a F) x) ^ 2
          ≤ ∫ x in s, (Function.uncurry (Work.Spaces.mixed b a F) x) ^ 2 :=
            Work.FTS.StrongLWP.Sobolev.eqc_integral_mul_sq_le hχzero hχle1 hχnn hsmeas hI0
        _ ≤ C * Work.Spaces.HkSq α 6 F := hb0
    · have e1 : (1 : ℝ) ^ 2 * (∫ x in s, E x ^ 2)
          ≤ (1 : ℝ) ^ 2 * (16 * C * Work.Spaces.HkSq α 6 F) := by
        rw [one_pow, one_mul, one_mul]; exact hb2
      have e2 : (2 * M) ^ 2 * (∫ x in s,
            ‖fderiv ℝ (Function.uncurry (Work.Spaces.mixed b a F)) x‖ ^ 2)
          ≤ (2 * M) ^ 2 * (4 * C * Work.Spaces.HkSq α 6 F) :=
        mul_le_mul_of_nonneg_left hb1' (sq_nonneg (2 * M))
      have e3 : M ^ 2 * (∫ x in s, (Function.uncurry (Work.Spaces.mixed b a F) x) ^ 2)
          ≤ M ^ 2 * (C * Work.Spaces.HkSq α 6 F) :=
        mul_le_mul_of_nonneg_left hb0 (sq_nonneg M)
      have hsum : (1 : ℝ) ^ 2 * (∫ x in s, E x ^ 2)
            + (2 * M) ^ 2 * (∫ x in s,
                ‖fderiv ℝ (Function.uncurry (Work.Spaces.mixed b a F)) x‖ ^ 2)
            + M ^ 2 * (∫ x in s, (Function.uncurry (Work.Spaces.mixed b a F) x) ^ 2)
          ≤ (1 : ℝ) ^ 2 * (16 * C * Work.Spaces.HkSq α 6 F)
            + (2 * M) ^ 2 * (4 * C * Work.Spaces.HkSq α 6 F)
            + M ^ 2 * (C * Work.Spaces.HkSq α 6 F) := by
        linarith [e1, e2, e3]
      calc ∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ (fun y : ℝ × ℝ =>
            χ y * Function.uncurry (Work.Spaces.mixed b a F) y)) x‖ ^ 2
          ≤ 3 * ((1 ^ 2 * ∫ x in s, E x ^ 2)
              + ((2 * M) ^ 2 * ∫ x in s,
                  ‖fderiv ℝ (Function.uncurry (Work.Spaces.mixed b a F)) x‖ ^ 2)
              + M ^ 2 * ∫ x in s, (Function.uncurry (Work.Spaces.mixed b a F) x) ^ 2) := hmain
        _ ≤ 3 * ((1 : ℝ) ^ 2 * (16 * C * Work.Spaces.HkSq α 6 F)
              + (2 * M) ^ 2 * (4 * C * Work.Spaces.HkSq α 6 F)
              + M ^ 2 * (C * Work.Spaces.HkSq α 6 F)) :=
            mul_le_mul_of_nonneg_left hsum (by norm_num)
        _ = (3 * (16 + 17 * M ^ 2) * C) * Work.Spaces.HkSq α 6 F := by ring

end Work.FTS.StrongEps.HQoAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.HQo_mixed_abs_le_on_compact =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## A Morrey-type bound on compacts for the open class `HQo α 6`

`Work.FTS.VocabO.HQo α 6 f` carries only open-quadrant smoothness and the honest membership
`HkMem α 6 f`; in particular there is no angular vanishing and no decay at `z = ∞`, so the
route of `Work.FTS.StrongLWP.Sobolev.supAbs_mixed_le` (Hardy inequalities on the whole
quadrant) is not available.  On a *compact* `K ⊆ Q0 = (0,∞) × (0,π/2)` however the classical
2-dimensional Sobolev/Morrey mechanism applies:

* a compact subset of the open quadrant sits in a closed box whose two-fold enlargement still
  lies in `Q0` (`Work.FTS_EllLimOK.box_of_compact_inside_Q0` plus padding);
* cut off by a smooth `χ` which is `1` on the box and vanishes off its enlargement
  (`Work.FTS.StrongLWP.Sobolev.EqcAux.exists_cutoff_rect_C2`);
* the products `χ · D_z^bD_θ^a f` are `C²` with compact support
  (`Work.FTS.StrongEps.LocUnif.contDiff_two_mul_of_contDiffOn_two`,
  `Work.FTS.StrongLWP.Sobolev.eqc_hasCompactSupport_mul`), and their `L²`-norms of order `0`
  and `2` are dominated by `HkNorm α 6 f` (`cut_slot_L2_bounds`, whose proof reads the box
  integrals of the mixed slots off `mixed_rect_L2_bounds`);
* Morrey's inequality `W^{2,2}(ℝ²) ⊂ C^{0,1/2}`
  (`Work.FTS.StrongLWP.Sobolev.holder_half_of_W22_real`) then gives a Hölder-`1/2` modulus
  proportional to those two `L²`-norms, and the averaging lemma
  `Work.FTS.StrongLWP.Sobolev.HolderHalf.sup_le_of_holder` converts the modulus plus the
  `L²`-bound into a *pointwise* bound.

Everything is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`. -/


end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.L12.L12_tendsto_locUnif =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.L12

set_option autoImplicit false
set_option maxHeartbeats 2000000


end Work.FTS.StrongEps.L12
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.D5.rounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif.D5

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Elementary facts -/

/-- The exhaustion boxes are measurable. -/
theorem measurableSet_eBox (m : ℕ) : MeasurableSet (eBox m) :=
  measurableSet_Icc.prod measurableSet_Icc

/-- `1 ≤ smoothOrder`: `C^∞` on the open quadrant gives `C¹` on any subset. -/
theorem one_le_smoothOrder : (1 : WithTop ℕ∞) ≤ Work.Stability.smoothOrder := by
  rw [Work.Stability.smoothOrder]
  exact WithTop.coe_le_coe.mpr le_top

/-- `D_z^{j+1}D_θ^i = z ∂_z (D_z^j D_θ^i)`. -/
theorem mixed_succ_apply (j i : ℕ) (X : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed (j + 1) i X z θ = z * Work.Spaces.pz (Work.Spaces.mixed j i X) z θ := rfl

/-- `D_θ^5 = sin 2θ · ∂_θ (D_θ^4)`. -/
theorem mixed_zero_five_apply (X : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed 0 5 X z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.mixed 0 4 X) z θ := rfl

/-! ## Transport along `Prod.swap` -/

/-- Uniform convergence is preserved by exchanging the two coordinates. -/
theorem tendstoUniformlyOn_swap_box {F : ℕ → ℝ → ℝ → ℝ} {g : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (h : TendstoUniformlyOn (fun n (p : ℝ × ℝ) => F n p.1 p.2) (fun p => g p.1 p.2)
      Filter.atTop (Set.Icc a b ×ˢ Set.Icc c d)) :
    TendstoUniformlyOn (fun n (p : ℝ × ℝ) => F n p.2 p.1) (fun p => g p.2 p.1)
      Filter.atTop (Set.Icc c d ×ˢ Set.Icc a b) := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with n hn p hp
  exact hn (Prod.swap p) ⟨hp.2, hp.1⟩

/-- Joint continuity is preserved by exchanging the two coordinates. -/
theorem continuousOn_swap_box {F : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (h : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Set.Icc a b ×ˢ Set.Icc c d)) :
    ContinuousOn (fun p : ℝ × ℝ => F p.2 p.1) (Set.Icc c d ×ˢ Set.Icc a b) :=
  h.comp continuous_swap.continuousOn (fun q hq => ⟨hq.2, hq.1⟩)

/-- The `θ`-derivative of the `θ`-slice, on the open quadrant. -/
theorem hasDerivAt_slice_theta {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun θ' => F z θ') (Work.Spaces.pth F z θ) θ := by
  have hd : DifferentiableAt ℝ (fun θ' => F z θ') θ :=
    ((hF.curry_θ hz).differentiableOn (by rw [Work.Stability.smoothOrder]; simp)).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  exact hd.hasDerivAt

/-- The `θ`-direction `L¹`-Cauchy bound, obtained from the box-local `z`-direction engine
`l1_cauchy_pz_gen` by transposing the two coordinates.  All the hypotheses are box-local, so the
transposition is legitimate even when the box is not contained in the open quadrant. -/
theorem cauchy_theta_of_z_gen {a b c c₀ d d₀ M : ℝ} (ha : 0 < a) (hab : a < b)
    (hc₀ : 0 < c₀) (hc₀c : c₀ < c) (hcd : c < d) (hdd₀ : d < d₀) (hM : 0 ≤ M)
    {L : ℕ → ℝ → ℝ → ℝ} {Llim : ℝ → ℝ → ℝ}
    (hconv : TendstoUniformlyOn (fun n (p : ℝ × ℝ) => L n p.1 p.2) (fun p => Llim p.1 p.2)
      Filter.atTop (Set.Icc a b ×ˢ Set.Icc c₀ d₀))
    (hder : ∀ n : ℕ, ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c₀ d₀,
      HasDerivAt (fun θ' => L n z θ') (Work.Spaces.pth (L n) z θ) θ)
    (hder2 : ∀ n : ℕ, ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c₀ d₀,
      HasDerivAt (fun θ' => Work.Spaces.pth (L n) z θ')
        (Work.Spaces.pth (Work.Spaces.pth (L n)) z θ) θ)
    (hcont : ∀ n : ℕ, ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth (L n) p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc c₀ d₀))
    (hcont2 : ∀ n : ℕ, ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.pth (Work.Spaces.pth (L n)) p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc c₀ d₀))
    (h1 : ∀ n : ℕ, ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c₀ d₀,
        ENNReal.ofReal ((Work.Spaces.pth (L n) p.1 p.2) ^ 2) ≤ ENNReal.ofReal M)
    (h2 : ∀ n : ℕ, ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c₀ d₀,
        ENNReal.ofReal ((Work.Spaces.pth (Work.Spaces.pth (L n)) p.1 p.2) ^ 2)
          ≤ ENNReal.ofReal M) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
        ENNReal.ofReal |Work.Spaces.pth (L n) p.1 p.2 - Work.Spaces.pth (L m) p.1 p.2|
          ≤ ENNReal.ofReal ε := by
  intro ε hε
  have hconvS : TendstoUniformlyOn (fun n (p : ℝ × ℝ) => L n p.2 p.1) (fun p => Llim p.2 p.1)
      Filter.atTop (Set.Icc c₀ d₀ ×ˢ Set.Icc a b) := tendstoUniformlyOn_swap_box hconv
  have hcontS : ∀ n : ℕ, ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.pth (L n) p.2 p.1) (Set.Icc c₀ d₀ ×ˢ Set.Icc a b) :=
    fun n => continuousOn_swap_box (hcont n)
  have hcont2S : ∀ n : ℕ, ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.pth (Work.Spaces.pth (L n)) p.2 p.1)
      (Set.Icc c₀ d₀ ×ˢ Set.Icc a b) :=
    fun n => continuousOn_swap_box (hcont2 n)
  have h1S : ∀ n : ℕ, ∫⁻ p in Set.Icc c₀ d₀ ×ˢ Set.Icc a b,
      ENNReal.ofReal ((Work.Spaces.pth (L n) p.2 p.1) ^ 2) ≤ ENNReal.ofReal M := by
    intro n
    have hgoal : ∫⁻ p in Set.Icc c₀ d₀ ×ˢ Set.Icc a b,
        (fun q : ℝ × ℝ => ENNReal.ofReal ((Work.Spaces.pth (L n) q.1 q.2) ^ 2))
          (Prod.swap p) ≤ ENNReal.ofReal M := by
      rw [← lintegral_swap_box (a := a) (b := b) (c := c₀) (d := d₀)
        (f := fun q : ℝ × ℝ => ENNReal.ofReal ((Work.Spaces.pth (L n) q.1 q.2) ^ 2))]
      exact h1 n
    exact hgoal
  have h2S : ∀ n : ℕ, ∫⁻ p in Set.Icc c₀ d₀ ×ˢ Set.Icc a b,
      ENNReal.ofReal ((Work.Spaces.pth (Work.Spaces.pth (L n)) p.2 p.1) ^ 2)
        ≤ ENNReal.ofReal M := by
    intro n
    have hgoal : ∫⁻ p in Set.Icc c₀ d₀ ×ˢ Set.Icc a b,
        (fun q : ℝ × ℝ =>
          ENNReal.ofReal ((Work.Spaces.pth (Work.Spaces.pth (L n)) q.1 q.2) ^ 2))
          (Prod.swap p) ≤ ENNReal.ofReal M := by
      rw [← lintegral_swap_box (a := a) (b := b) (c := c₀) (d := d₀)
        (f := fun q : ℝ × ℝ =>
          ENNReal.ofReal ((Work.Spaces.pth (Work.Spaces.pth (L n)) q.1 q.2) ^ 2))]
      exact h2 n
    exact hgoal
  obtain ⟨N, hN⟩ := l1_cauchy_pz_gen (a := c) (b := d) (a₀ := c₀) (b₀ := d₀) (c := a) (d := b)
    (M := M) (L := fun n x y => L n y x) (Llim := fun x y => Llim y x)
    hc₀ hc₀c hcd hdd₀ hab hM hconvS hder hder2 hcontS hcont2S h1S h2S ε hε
  refine ⟨N, fun n m hn hm => ?_⟩
  have hgoal : ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
      (fun q : ℝ × ℝ => ENNReal.ofReal
        |Work.Spaces.pth (L n) q.1 q.2 - Work.Spaces.pth (L m) q.1 q.2|) p
      ≤ ENNReal.ofReal ε := by
    rw [lintegral_swap_box (a := a) (b := b) (c := c) (d := d)
      (f := fun q : ℝ × ℝ => ENNReal.ofReal
        |Work.Spaces.pth (L n) q.1 q.2 - Work.Spaces.pth (L m) q.1 q.2|)]
    exact hN n m hn hm
  exact hgoal

/-! ## The `z`-slot round -/

/-- The `z`-direction round: the slot `(j' + 1, i)` converges a.e. on `eBox m` along a
subsequence. -/
theorem round_z {α B : ℝ} (hα : 0 < α) {G : ℕ → ℝ → ℝ → ℝ} {φ : ℕ → ℕ} {f : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (G n))
    (hmem : ∀ n : ℕ, Work.Spaces.HkMem α 6 (G n))
    (hb : ∀ n : ℕ, Work.Spaces.HkNorm α 6 (G n) ≤ B)
    (hconv4 : ∀ (j i : ℕ), j + i ≤ 4 → ∀ K : Set (ℝ × ℝ), IsCompact K →
      K ⊆ Work.FTS.EllipticEst.Q0 →
      TendstoUniformlyOn (fun n (p : ℝ × ℝ) => Work.Spaces.mixed j i (G (φ n)) p.1 p.2)
        (fun p => Work.Spaces.mixed j i f p.1 p.2) Filter.atTop K)
    {j' i : ℕ} (hji : j' + i ≤ 4) {τ : ℕ → ℕ} (hτ : StrictMono τ) (m : ℕ) :
    ∃ ν : ℕ → ℕ, StrictMono ν ∧
      ∀ᵐ p ∂(volume.restrict (eBox m)),
        Filter.Tendsto (fun n => Work.Spaces.mixed (j' + 1) i (G (φ (τ (ν n)))) p.1 p.2)
          Filter.atTop (nhds (Work.Spaces.mixed (j' + 1) i f p.1 p.2)) := by
  classical
  obtain ⟨M, hM, hM1, hM2, -, -⟩ :=
    deriv_slot_lintegral_bounds (α := α) (B := B) hα (F := fun n => G (φ (τ n)))
      (fun n => hsm (φ (τ n))) (fun n => hmem (φ (τ n))) (fun n => hb (φ (τ n)))
      (ea₀_pos m) (((ea₀_lt_ea m).le.trans (ea_lt_eb m).le).trans (eb_lt_eb₀ m).le)
      (ec_pos m) (ed_lt_pi m) j' i hji
  have hsub : eBoxZ m ⊆ Work.FTS.EllipticEst.Q0 := eBoxZ_subset_Q0 m
  have hcompact : IsCompact (eBoxZ m) := by
    simpa only [eBoxZ] using
      (isCompact_Icc.prod isCompact_Icc :
        IsCompact (Set.Icc (ea₀ m) (eb₀ m) ×ˢ Set.Icc (ec m) (ed m)))
  have hconv : TendstoUniformlyOn
      (fun n (p : ℝ × ℝ) => Work.Spaces.mixed j' i (G (φ (τ n))) p.1 p.2)
      (fun p => Work.Spaces.mixed j' i f p.1 p.2) Filter.atTop (eBoxZ m) :=
    tendstoUniformlyOn_subseq hτ (hconv4 j' i hji (eBoxZ m) hcompact hsub)
  have hcont : ∀ n : ℕ, ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.mixed j' i (G (φ (τ n))) p.1 p.2) (eBoxZ m) :=
    fun n => ((hsm (φ (τ n))).mixed j' i).continuousOn.mono hsub
  have hcontdz : ∀ n : ℕ, ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.pz (Work.Spaces.mixed j' i (G (φ (τ n)))) p.1 p.2)
      (eBoxZ m) :=
    fun n => (((hsm (φ (τ n))).mixed j' i).pz).continuousOn.mono hsub
  have hslice : ∀ n : ℕ, ∀ θ ∈ Set.Icc (ec m) (ed m),
      ContDiffOn ℝ 1 (fun z => Work.Spaces.mixed j' i (G (φ (τ n))) z θ)
        (Set.Ioo (ea₀ m) (eb₀ m)) := by
    intro n θ hθ
    have hθ' : θ ∈ Set.Ioo (0 : ℝ) (π / 2) :=
      ⟨lt_of_lt_of_le (ec_pos m) hθ.1, lt_of_le_of_lt hθ.2 (ed_lt_pi m)⟩
    exact ((((hsm (φ (τ n))).mixed j' i).curry_z hθ').of_le one_le_smoothOrder).mono
      (fun z hz => lt_of_lt_of_le (ea₀_pos m) hz.1.le)
  obtain ⟨ν, hν, hνae⟩ :=
    ae_extract_z (M := M) (ha₀ := ea₀_pos m) (ha₀a := ea₀_lt_ea m) (hab := ea_lt_eb m)
      (hbb₀ := eb_lt_eb₀ m) (hc := ec_pos m) (hcd := ec_lt_ed m) (hM := hM)
      hcont hcontdz hslice hconv
      (l1_cauchy_pz (M := M) (ha₀ := ea₀_pos m) (ha₀a := ea₀_lt_ea m) (hab := ea_lt_eb m)
        (hbb₀ := eb_lt_eb₀ m) (hc := ec_pos m) (hcd := ec_lt_ed m) (hd := ed_lt_pi m)
        (hM := hM) (fun n => (hsm (φ (τ n))).mixed j' i) hconv hM1 hM2)
      hM1
  refine ⟨ν, hν, ?_⟩
  filter_upwards [hνae] with p hp
  simpa only [mixed_succ_apply] using hp.const_mul p.1

/-! ## The `θ`-slot round -/

/-- The `θ`-direction round: the slot `(0, 5)` converges a.e. on `eBox m` along a subsequence. -/
theorem round_theta {α B : ℝ} (hα : 0 < α) {G : ℕ → ℝ → ℝ → ℝ} {φ : ℕ → ℕ} {f : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (G n))
    (hmem : ∀ n : ℕ, Work.Spaces.HkMem α 6 (G n))
    (hb : ∀ n : ℕ, Work.Spaces.HkNorm α 6 (G n) ≤ B)
    (hconv4 : ∀ (j i : ℕ), j + i ≤ 4 → ∀ K : Set (ℝ × ℝ), IsCompact K →
      K ⊆ Work.FTS.EllipticEst.Q0 →
      TendstoUniformlyOn (fun n (p : ℝ × ℝ) => Work.Spaces.mixed j i (G (φ n)) p.1 p.2)
        (fun p => Work.Spaces.mixed j i f p.1 p.2) Filter.atTop K)
    {τ : ℕ → ℕ} (hτ : StrictMono τ) (m : ℕ) :
    ∃ ν : ℕ → ℕ, StrictMono ν ∧
      ∀ᵐ p ∂(volume.restrict (eBox m)),
        Filter.Tendsto (fun n => Work.Spaces.mixed 0 5 (G (φ (τ (ν n)))) p.1 p.2)
          Filter.atTop (nhds (Work.Spaces.mixed 0 5 f p.1 p.2)) := by
  classical
  obtain ⟨M, hM, -, -, hM3, hM4⟩ :=
    deriv_slot_lintegral_bounds (α := α) (B := B) hα (F := fun n => G (φ (τ n)))
      (fun n => hsm (φ (τ n))) (fun n => hmem (φ (τ n))) (fun n => hb (φ (τ n)))
      (ea_pos m) (ea_lt_eb m).le (ec₀_pos m) (ed₀_lt_pi m) 0 4 (by norm_num)
  have hsubT : eBoxT m ⊆ Work.FTS.EllipticEst.Q0 := eBoxT_subset_Q0 m
  have hcompactT : IsCompact (eBoxT m) := by
    simpa only [eBoxT] using
      (isCompact_Icc.prod isCompact_Icc :
        IsCompact (Set.Icc (ea m) (eb m) ×ˢ Set.Icc (ec₀ m) (ed₀ m)))
  have hconvT : TendstoUniformlyOn
      (fun n (p : ℝ × ℝ) => Work.Spaces.mixed 0 4 (G (φ (τ n))) p.1 p.2)
      (fun p => Work.Spaces.mixed 0 4 f p.1 p.2) Filter.atTop (eBoxT m) :=
    tendstoUniformlyOn_subseq hτ (hconv4 0 4 (by norm_num) (eBoxT m) hcompactT hsubT)
  have hcontT : ∀ n : ℕ, ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.mixed 0 4 (G (φ (τ n))) p.1 p.2) (eBoxT m) :=
    fun n => ((hsm (φ (τ n))).mixed 0 4).continuousOn.mono hsubT
  have hthcontT : ∀ n : ℕ, ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.pth (Work.Spaces.mixed 0 4 (G (φ (τ n)))) p.1 p.2)
      (eBoxT m) :=
    fun n => (((hsm (φ (τ n))).mixed 0 4).pth).continuousOn.mono hsubT
  have hth2contT : ∀ n : ℕ, ContinuousOn
      (fun p : ℝ × ℝ =>
        Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.mixed 0 4 (G (φ (τ n))))) p.1 p.2)
      (eBoxT m) :=
    fun n => ((((hsm (φ (τ n))).mixed 0 4).pth).pth).continuousOn.mono hsubT
  have hsliceT : ∀ n : ℕ, ∀ z ∈ Set.Icc (ea m) (eb m),
      ContDiffOn ℝ 1 (fun θ => Work.Spaces.mixed 0 4 (G (φ (τ n))) z θ)
        (Set.Ioo (ec₀ m) (ed₀ m)) := by
    intro n z hz
    have hz' : 0 < z := lt_of_lt_of_le (ea_pos m) hz.1
    exact ((((hsm (φ (τ n))).mixed 0 4).curry_θ hz').of_le one_le_smoothOrder).mono
      (Set.Ioo_subset_Ioo (ec₀_pos m).le (ed₀_lt_pi m).le)
  have hderT : ∀ n : ℕ, ∀ z ∈ Set.Icc (ea m) (eb m), ∀ θ ∈ Set.Icc (ec₀ m) (ed₀ m),
      HasDerivAt (fun θ' => Work.Spaces.mixed 0 4 (G (φ (τ n))) z θ')
        (Work.Spaces.pth (Work.Spaces.mixed 0 4 (G (φ (τ n)))) z θ) θ := by
    intro n z hz θ hθ
    have hz' : 0 < z := lt_of_lt_of_le (ea_pos m) hz.1
    have hθ' : θ ∈ Set.Ioo (0 : ℝ) (π / 2) :=
      ⟨lt_of_lt_of_le (ec₀_pos m) hθ.1, lt_of_le_of_lt hθ.2 (ed₀_lt_pi m)⟩
    exact hasDerivAt_slice_theta ((hsm (φ (τ n))).mixed 0 4) hz' hθ'
  have hder2T : ∀ n : ℕ, ∀ z ∈ Set.Icc (ea m) (eb m), ∀ θ ∈ Set.Icc (ec₀ m) (ed₀ m),
      HasDerivAt (fun θ' => Work.Spaces.pth (Work.Spaces.mixed 0 4 (G (φ (τ n)))) z θ')
        (Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.mixed 0 4 (G (φ (τ n))))) z θ) θ := by
    intro n z hz θ hθ
    have hz' : 0 < z := lt_of_lt_of_le (ea_pos m) hz.1
    have hθ' : θ ∈ Set.Ioo (0 : ℝ) (π / 2) :=
      ⟨lt_of_lt_of_le (ec₀_pos m) hθ.1, lt_of_le_of_lt hθ.2 (ed₀_lt_pi m)⟩
    exact hasDerivAt_slice_theta (((hsm (φ (τ n))).mixed 0 4).pth) hz' hθ'
  have hcauchy := cauchy_theta_of_z_gen (a := ea m) (b := eb m) (c := ec m) (c₀ := ec₀ m)
    (d := ed m) (d₀ := ed₀ m) (M := M) (ea_pos m) (ea_lt_eb m) (ec₀_pos m) (ec₀_lt_ec m)
    (ec_lt_ed m) (ed_lt_ed₀ m) hM hconvT hderT hder2T hthcontT hth2contT hM3 hM4
  obtain ⟨ν, hν, hνae⟩ :=
    ae_extract_theta (M := M) (a := ea m) (b := eb m) (c := ec m) (c₀ := ec₀ m) (d := ed m)
      (d₀ := ed₀ m) (ea_pos m) (ea_lt_eb m) (ec₀_pos m) (ec₀_lt_ec m) (ec_lt_ed m)
      (ed_lt_ed₀ m) hM hcontT hthcontT hsliceT hconvT hcauchy hM3
  refine ⟨ν, hν, ?_⟩
  filter_upwards [hνae] with p hp
  simpa only [mixed_zero_five_apply] using hp.const_mul (Real.sin (2 * p.2))

/-! ## The diagonal round for one slot -/

/-- One diagonal-extraction round: for the fixed slot `(j, i)` with `j + i = 5` and the current
base `φ ∘ τ`, there is a further strictly increasing `Φ` such that the slot converges a.e. on each
exhaustion box along `G (φ (τ (Φ n)))`. -/
theorem round_slot {α B : ℝ} (hα : 0 < α) {G : ℕ → ℝ → ℝ → ℝ} {φ : ℕ → ℕ} {f : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (G n))
    (hmem : ∀ n : ℕ, Work.Spaces.HkMem α 6 (G n))
    (hb : ∀ n : ℕ, Work.Spaces.HkNorm α 6 (G n) ≤ B)
    (hconv4 : ∀ (j i : ℕ), j + i ≤ 4 → ∀ K : Set (ℝ × ℝ), IsCompact K →
      K ⊆ Work.FTS.EllipticEst.Q0 →
      TendstoUniformlyOn (fun n (p : ℝ × ℝ) => Work.Spaces.mixed j i (G (φ n)) p.1 p.2)
        (fun p => Work.Spaces.mixed j i f p.1 p.2) Filter.atTop K)
    {j i : ℕ} (hji : j + i = 5) {τ : ℕ → ℕ} (hτ : StrictMono τ) :
    ∃ Φ : ℕ → ℕ, StrictMono Φ ∧
      ∀ m : ℕ, ∀ᵐ p ∂(volume.restrict Work.FTS.EllipticEst.Q0), p ∈ eBox m →
        Filter.Tendsto (fun n => Work.Spaces.mixed j i (G (φ (τ (Φ n)))) p.1 p.2)
          Filter.atTop (nhds (Work.Spaces.mixed j i f p.1 p.2)) := by
  classical
  have hrow : ∀ m : ℕ, ∀ σ : ℕ → ℕ, StrictMono σ →
      ∃ ν : ℕ → ℕ, StrictMono ν ∧
        ∀ᵐ p ∂(volume.restrict (eBox m)),
          Filter.Tendsto (fun n => Work.Spaces.mixed j i (G (φ (τ (σ (ν n))))) p.1 p.2)
            Filter.atTop (nhds (Work.Spaces.mixed j i f p.1 p.2)) := by
    intro m σ hσ
    rcases j with _ | j'
    · have hi : i = 5 := by omega
      subst hi
      exact round_theta (α := α) (B := B) hα hsm hmem hb hconv4 (τ := fun n => τ (σ n))
        (hτ.comp hσ) m
    · have hji' : j' + i ≤ 4 := by omega
      exact round_z (α := α) (B := B) hα hsm hmem hb hconv4 hji' (τ := fun n => τ (σ n))
        (hτ.comp hσ) m
  obtain ⟨Φ, hΦ, hdiag⟩ := exists_diag_extract
    (μ := volume.restrict Work.FTS.EllipticEst.Q0)
    (F := fun k n p => if p ∈ eBox k then Work.Spaces.mixed j i (G (φ (τ n))) p.1 p.2 else 0)
    (G := fun k p => if p ∈ eBox k then Work.Spaces.mixed j i f p.1 p.2 else 0)
    (fun k σ hσ => by
      obtain ⟨ν, hν, hνae⟩ := hrow k σ hσ
      refine ⟨ν, hν, ?_⟩
      have hmemk : ∀ᵐ p ∂(volume.restrict Work.FTS.EllipticEst.Q0), p ∈ eBox k →
          Filter.Tendsto
            (fun n => Work.Spaces.mixed j i (G (φ (τ (σ (ν n))))) p.1 p.2)
            Filter.atTop (nhds (Work.Spaces.mixed j i f p.1 p.2)) := by
        rw [MeasureTheory.ae_restrict_iff' (μ := volume) (s := eBox k) (measurableSet_eBox k)]
          at hνae
        rw [MeasureTheory.ae_restrict_iff' (μ := volume) (s := Work.FTS.EllipticEst.Q0)
          Work.FTS.EllipticEst.isOpen_Q0.measurableSet]
        filter_upwards [hνae] with p hp _
        exact hp
      filter_upwards [hmemk] with p hp
      by_cases h : p ∈ eBox k
      · simpa [h] using hp h
      · simp only [h, if_false]
        exact tendsto_const_nhds)
  refine ⟨Φ, hΦ, fun m => ?_⟩
  filter_upwards [hdiag m] with p hp hpm
  simpa only [hpm, if_true] using hp

end Work.FTS.StrongEps.LocUnif.D5
end
end
