import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Submission.Work.FTS.EllipticEst.Honest.HR2.HonToAe
import Submission.Work.FTS.EllipticEst.Honest.HR2.Prep
import Submission.Work.FTS.EllipticEst.Honest.HonSliceFinite
import Submission.Work.FTS.EllipticEst.Honest.Step1G.EnergyG
import Submission.Work.FTS.EllipticEst.Honest.honSliceIntFacts
import Submission.Work.FTS.EllipticEst.Honest.honYcBound
import Submission.Work.FTS.EllipticEst.remov.SourceBound.sliceMomentIdentity
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocDataExt.LocG5
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.H2W.momentChainAe
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.mixed_mul_le
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.Pieces.AeGradRho.aeEnergyOfCutEnergy =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores.Pieces.AeGradRho

open scoped Real Topology BigOperators ENNReal
open MeasureTheory Set Filter
open Work.FTS.EllipticEst.H2W.AeProof

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **Removing the cutoff from the truncated `w²`-energy inequality.**

Given the truncated inequality `AeCutEnergyProp` (Step 1 of `prop:H2` with a `C²` cutoff vanishing
near `z = 0`), the untruncated inequality of Step 1 follows in the class `AeData`: the cutoff
family `Work.FTS.EllipticEst.cut n` is monotone, tends to `1` pointwise off `z = 0`, the two
`∫⁻`-sides converge by monotone convergence, and the truncation error `AeCutErr` tends to `0`
because the `θ`-profile `P z = ∫_θ u z θ²` is `z`-integrable (`HkMem α 0 u`) and
`w²P`-integrable (`HkMem α 0 G`). -/
theorem aeEnergyOfCutEnergy
    (hcut : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.Cores.Pieces.AeGradRho.AeCutEnergyProp α u G) :
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
        ENNReal.ofReal (α ^ 2) * (∫⁻ z in Work.Spaces.Iz,
            ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
              * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((z * Work.Spaces.pz u z θ) ^ 2)))
          + (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
              * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2)))
        ≤ ENNReal.ofReal (13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α)))
            * (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
              * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2)))
          + ENNReal.ofReal (1 / 2) * ENNReal.ofReal (Work.Spaces.HkSq α 0 G) := by
  intro α u G h
  have hL0 : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ => u z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    Work.FTS.EllipticEst.H2W.AeLeftClean.sliceLeftTendstoClean α u G h
  have hLπ : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ => u z θ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
        (nhds 0) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hz
    exact Work.FTS.EllipticEst.H2W.Ae.AeSliceRightTendsto α u G h z hz
  set Kn : ℝ := 13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α)) with hKn
  have hKpos : 0 < Kn := by rw [hKn]; nlinarith [sq_nonneg α, h.1, h.2.1]
  set Mc : ℝ≥0∞ := ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
      * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2)) with hMc
  set Ac : ℝ≥0∞ := ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
      * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((z * Work.Spaces.pz u z θ) ^ 2)) with hAc
  set Bc : ℝ≥0∞ := ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
      * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2)) with hBc
  have hgoal : ENNReal.ofReal (α ^ 2) * Ac + Bc
      ≤ ENNReal.ofReal Kn * Mc
        + ENNReal.ofReal (1 / 2) * ENNReal.ofReal (Work.Spaces.HkSq α 0 G) := by
    by_cases hMtop : Mc = ⊤
    · have hR : ENNReal.ofReal Kn * Mc
          + ENNReal.ofReal (1 / 2) * ENNReal.ofReal (Work.Spaces.HkSq α 0 G) = ⊤ := by
        rw [hMtop, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hKpos), top_add]
      rw [hR]; exact le_top
    · have hMlt : Mc < ⊤ := lt_top_iff_ne_top.mpr hMtop
      -- the θ-profile `P`
      set P : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 with hPdef
      -- the sup identities
      have hptA : ∀ (n : ℕ) (z : ℝ), ENNReal.ofReal (Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2 * z ^ 2)
            * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pz u z θ) ^ 2))
          = ENNReal.ofReal (Work.FTS.EllipticEst.cut n z)
            * (ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
              * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((z * Work.Spaces.pz u z θ) ^ 2))) := by
        intro n z
        have h1 : ENNReal.ofReal (Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2 * z ^ 2)
            = ENNReal.ofReal (Work.FTS.EllipticEst.cut n z)
              * ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * ENNReal.ofReal (z ^ 2) := by
          rw [show Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2 * z ^ 2
              = Work.FTS.EllipticEst.cut n z * ((Work.Spaces.w z) ^ 2 * z ^ 2) from by ring]
          rw [ENNReal.ofReal_mul (Work.FTS.EllipticEst.cut_nonneg n z),
            ENNReal.ofReal_mul (sq_nonneg (Work.Spaces.w z))]
          ring
        have h2 : ENNReal.ofReal (z ^ 2) * (∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal ((Work.Spaces.pz u z θ) ^ 2))
            = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((z * Work.Spaces.pz u z θ) ^ 2) := by
          rw [← MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (z ^ 2))
            (fun θ => ENNReal.ofReal ((Work.Spaces.pz u z θ) ^ 2)) ENNReal.ofReal_ne_top]
          refine lintegral_congr fun θ => ?_
          rw [← ENNReal.ofReal_mul (sq_nonneg z)]
          congr 1
          ring
        rw [h1]
        rw [show ENNReal.ofReal (Work.FTS.EllipticEst.cut n z)
              * ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * ENNReal.ofReal (z ^ 2)
              * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pz u z θ) ^ 2))
            = ENNReal.ofReal (Work.FTS.EllipticEst.cut n z)
              * (ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
                * (ENNReal.ofReal (z ^ 2)
                  * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pz u z θ) ^ 2))))
            from by ring]
        rw [h2]
      have hAsup : (⨆ n : ℕ, ∫⁻ z in Work.Spaces.Iz,
            ENNReal.ofReal (Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2 * z ^ 2)
              * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pz u z θ) ^ 2))) = Ac := by
        have hcongr : (fun n : ℕ => ∫⁻ z in Work.Spaces.Iz,
              ENNReal.ofReal (Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2 * z ^ 2)
                * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pz u z θ) ^ 2)))
            = fun n : ℕ => ∫⁻ z in Work.Spaces.Iz,
                ENNReal.ofReal (Work.FTS.EllipticEst.cut n z)
                  * (ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
                    * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((z * Work.Spaces.pz u z θ) ^ 2))) := by
          funext n
          exact lintegral_congr fun z => hptA n z
        rw [hcongr, iSup_cut_mul (gA_aemeasurable h), hAc]
      have hptB : ∀ (n : ℕ) (z : ℝ), ENNReal.ofReal (Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2)
            * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2))
          = ENNReal.ofReal (Work.FTS.EllipticEst.cut n z)
            * (ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
              * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2))) := by
        intro n z
        rw [ENNReal.ofReal_mul (Work.FTS.EllipticEst.cut_nonneg n z)]
        ring
      have hBsup : (⨆ n : ℕ, ∫⁻ z in Work.Spaces.Iz,
            ENNReal.ofReal (Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2)
              * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2))) = Bc := by
        have hcongr : (fun n : ℕ => ∫⁻ z in Work.Spaces.Iz,
              ENNReal.ofReal (Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2)
                * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2)))
            = fun n : ℕ => ∫⁻ z in Work.Spaces.Iz,
                ENNReal.ofReal (Work.FTS.EllipticEst.cut n z)
                  * (ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
                    * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2))) := by
          funext n
          exact lintegral_congr fun z => hptB n z
        rw [hcongr, iSup_cut_mul (gB_aemeasurable h), hBc]
      -- the monotonicity
      have hcutmono : Monotone (fun n : ℕ => fun z : ℝ => ENNReal.ofReal (Work.FTS.EllipticEst.cut n z)) :=
        fun m n hmn z => ENNReal.ofReal_le_ofReal
          (Nat.le_induction le_rfl (fun k _ hk => le_trans hk (cut_mono k z)) n hmn)
      have hAmono : Monotone (fun n : ℕ => ∫⁻ z in Work.Spaces.Iz,
            ENNReal.ofReal (Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2 * z ^ 2)
              * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pz u z θ) ^ 2))) := by
        intro m n hmn
        refine lintegral_mono fun z => ?_
        rw [hptA n z, hptA m z]
        exact mul_le_mul_of_nonneg_right (hcutmono hmn z) (bot_le : (⊥ : ℝ≥0∞) ≤ _)
      have hBmono : Monotone (fun n : ℕ => ∫⁻ z in Work.Spaces.Iz,
            ENNReal.ofReal (Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2)
              * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2))) := by
        intro m n hmn
        refine lintegral_mono fun z => ?_
        rw [hptB n z, hptB m z]
        exact mul_le_mul_of_nonneg_right (hcutmono hmn z) (bot_le : (⊥ : ℝ≥0∞) ≤ _)
      -- the crux for each `n`
      have hcrux : ∀ n : ℕ,
          ENNReal.ofReal (α ^ 2) * (∫⁻ z in Work.Spaces.Iz,
              ENNReal.ofReal (Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2 * z ^ 2)
                * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pz u z θ) ^ 2)))
            + (∫⁻ z in Work.Spaces.Iz,
                ENNReal.ofReal (Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2)
                  * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2)))
          ≤ ENNReal.ofReal Kn * (∫⁻ z in Work.Spaces.Iz,
                ENNReal.ofReal (Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2)
                  * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2)))
            + ENNReal.ofReal (1 / 2) * (∫⁻ z in Work.Spaces.Iz,
                ENNReal.ofReal (Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2)
                  * (∫⁻ θ in Work.Spaces.Iθ,
                      ENNReal.ofReal ((G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))
            + ENNReal.ofReal ((α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
                  (2 * |deriv (Work.FTS.EllipticEst.cut n) z|
                      * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
                    + |deriv (deriv (Work.FTS.EllipticEst.cut n)) z|
                      * (z ^ 2 * (Work.Spaces.w z) ^ 2)) * P z)
                + (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz,
                    |deriv (Work.FTS.EllipticEst.cut n) z| * (z * (Work.Spaces.w z) ^ 2) * P z)) := by
        intro n
        have hMcut : (∫⁻ z in Work.Spaces.Iz,
              ENNReal.ofReal (Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2)
                * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2))) ≠ ⊤ := by
          refine ne_top_of_le_ne_top hMtop (lintegral_mono fun z => ?_)
          refine mul_le_mul_of_nonneg_right ?_ (bot_le : (⊥ : ℝ≥0∞) ≤ _)
          exact ENNReal.ofReal_le_ofReal (by
            have h1 := Work.FTS.EllipticEst.cut_le_one n z
            have h2 : (0:ℝ) ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
            nlinarith)
        have hcutδ : ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℝ, z ≤ δ → Work.FTS.EllipticEst.cut n z = 0 :=
          ⟨1 / ((n : ℝ) + 1), by
            have h : (0 : ℝ) < (n : ℝ) + 1 := by positivity
            exact div_pos one_pos h,
            fun z hz => Work.FTS.EllipticEst.cut_apply_zero_of_le n hz⟩
        have hres := hcut α u G h hL0 hLπ (Work.FTS.EllipticEst.cut n)
          (cut_contDiff_two n) (cut_hasCompactSupport n) (fun z hz => cut_zero_of_nonpos n hz)
          (Work.FTS.EllipticEst.cut_nonneg n) (Work.FTS.EllipticEst.cut_le_one n) hcutδ hMcut
        rw [hKn]
        exact hres
      -- ### the properties of `P`
      have hE0P : ∀ z : ℝ, 0 ≤ P z := by
        intro z; rw [hPdef]; exact MeasureTheory.integral_nonneg fun θ => sq_nonneg _
      have hslice_ae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
          MeasureTheory.AEStronglyMeasurable (fun θ => (u z θ) ^ 2)
            (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
        rw [restrict_Iz_eq_Ioi']
        refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
          (Filter.Eventually.of_forall fun z hz => ?_)
        have hSO : Work.FTS.EllipticEst.SmoothOpen u :=
          Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
        have h1 : ContinuousOn (fun θ => (u z θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) :=
          ((Work.FTS.EllipticEst.SmoothOpen.curry_θ hSO hz).continuousOn).pow 2
        have h2 : MeasureTheory.AEStronglyMeasurable (fun θ => (u z θ) ^ 2)
            (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
          h1.aestronglyMeasurable measurableSet_Ioo
        rw [Work.Spaces.Iθ, ← MeasureTheory.Measure.restrict_congr_set
          (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0) (b := Real.pi / 2))]
        exact h2
      have hcmp : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
          ENNReal.ofReal (P z) ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2) := by
        filter_upwards [hslice_ae] with z hz
        rw [hPdef]
        exact ofReal_integral_le_lintegral hz (fun θ => sq_nonneg _)
      have hw2P : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * P z)) ≠ ⊤ := by
        have h1 : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * P z))
            = ∫⁻ z in Work.Spaces.Iz,
                ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * ENNReal.ofReal (P z) := by
          refine lintegral_congr fun z => ?_
          rw [ENNReal.ofReal_mul (sq_nonneg _)]
        rw [h1]
        refine ne_top_of_le_ne_top hMtop ?_
        rw [hMc]
        refine lintegral_mono_ae ?_
        filter_upwards [hcmp] with z hz
        exact mul_le_mul_of_nonneg_left hz (bot_le : (⊥ : ℝ≥0∞) ≤ _)
      have hPmeas : MeasureTheory.AEStronglyMeasurable (fun z => (Work.Spaces.w z) ^ 2 * P z)
          (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
        (w_sq_measurable'.aestronglyMeasurable).mul (P_aesm h)
      have hE2 : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * P z)
          Work.Spaces.Iz :=
        (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hPmeas
          (Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (hE0P z))).mp hw2P
      have hE1 : MeasureTheory.IntegrableOn P Work.Spaces.Iz := by
        refine (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable (P_aesm h)
          (Filter.Eventually.of_forall hE0P)).mp ?_
        refine ne_top_of_le_ne_top hw2P (lintegral_mono_ae ?_)
        have h0 : ∀ᵐ z ∂(MeasureTheory.volume : Measure ℝ), z ≠ 0 := by
          rw [MeasureTheory.ae_iff]; simp
        rw [Work.Spaces.Iz, MeasureTheory.ae_restrict_iff' measurableSet_Ici]
        filter_upwards [h0] with z hz hzI
        have hz0 : (0:ℝ) < z := lt_of_le_of_ne hzI (Ne.symm hz)
        rw [ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg _) (hE0P z))]
        have hw : (1:ℝ) ≤ (Work.Spaces.w z) ^ 2 := by
          rw [Work.Spaces.w, div_pow, le_div_iff₀ (by positivity : (0:ℝ) < (z^2)^2)]
          have h1 : (0:ℝ) ≤ 1 + z := by linarith
          have h2 : z ^ 2 ≤ (1 + z) ^ 2 := by nlinarith [h1]
          calc (1:ℝ) * (z ^ 2) ^ 2 = (z ^ 2) ^ 2 := by ring
            _ ≤ ((1 + z) ^ 2) ^ 2 := pow_le_pow_left₀ (sq_nonneg z) h2 2
        nlinarith [hE0P z, hw]
      -- the nonnegativity of the two error integrals
      have hErrA0 : ∀ n : ℕ, 0 ≤ (∫ z in Work.Spaces.Iz,
            (2 * |deriv (Work.FTS.EllipticEst.cut n) z|
                * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
              + |deriv (deriv (Work.FTS.EllipticEst.cut n)) z|
                * (z ^ 2 * (Work.Spaces.w z) ^ 2)) * P z) := by
        intro n
        exact MeasureTheory.setIntegral_nonneg measurableSet_Ici fun z _ => by
          have hPz := hE0P z
          have h1 : (0:ℝ) ≤ 2 * |deriv (Work.FTS.EllipticEst.cut n) z|
              * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
              + |deriv (deriv (Work.FTS.EllipticEst.cut n)) z|
                * (z ^ 2 * (Work.Spaces.w z) ^ 2) := by positivity
          exact mul_nonneg h1 hPz
      have hErrB0 : ∀ n : ℕ, 0 ≤ (∫ z in Work.Spaces.Iz,
            |deriv (Work.FTS.EllipticEst.cut n) z| * (z * (Work.Spaces.w z) ^ 2) * P z) := by
        intro n
        exact MeasureTheory.setIntegral_nonneg measurableSet_Ici fun z hz => by
          have hPz := hE0P z
          exact mul_nonneg (mul_nonneg (abs_nonneg _)
            (mul_nonneg hz (sq_nonneg _))) hPz
      -- the error convergence
      have herr : Filter.Tendsto (fun n : ℕ => (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
              (2 * |deriv (Work.FTS.EllipticEst.cut n) z|
                  * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
                + |deriv (deriv (Work.FTS.EllipticEst.cut n)) z|
                  * (z ^ 2 * (Work.Spaces.w z) ^ 2)) * P z)
            + (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz,
                |deriv (Work.FTS.EllipticEst.cut n) z| * (z * (Work.Spaces.w z) ^ 2) * P z))
          Filter.atTop (nhds 0) := by
        have hsum := AeCutErr P hE0P (P_aesm h) hE1 hE2
        set Cst : ℝ := max (α ^ 2 / 2) (α * (5 + α) / 2) with hCst
        have hCst0 : 0 ≤ Cst := by rw [hCst]; exact le_max_of_le_left (by positivity)
        have hg : Filter.Tendsto (fun n : ℕ => Cst * ((∫ z in Work.Spaces.Iz,
              (2 * |deriv (Work.FTS.EllipticEst.cut n) z|
                  * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
                + |deriv (deriv (Work.FTS.EllipticEst.cut n)) z|
                  * (z ^ 2 * (Work.Spaces.w z) ^ 2)) * P z)
            + (∫ z in Work.Spaces.Iz,
                |deriv (Work.FTS.EllipticEst.cut n) z| * (z * (Work.Spaces.w z) ^ 2) * P z)))
            Filter.atTop (nhds 0) := by
          have := hsum.const_mul Cst
          simpa using this
        refine squeeze_zero (f := fun n : ℕ => (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
              (2 * |deriv (Work.FTS.EllipticEst.cut n) z|
                  * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
                + |deriv (deriv (Work.FTS.EllipticEst.cut n)) z|
                  * (z ^ 2 * (Work.Spaces.w z) ^ 2)) * P z)
            + (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz,
                |deriv (Work.FTS.EllipticEst.cut n) z| * (z * (Work.Spaces.w z) ^ 2) * P z))
          (g := fun n : ℕ => Cst * ((∫ z in Work.Spaces.Iz,
              (2 * |deriv (Work.FTS.EllipticEst.cut n) z|
                  * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
                + |deriv (deriv (Work.FTS.EllipticEst.cut n)) z|
                  * (z ^ 2 * (Work.Spaces.w z) ^ 2)) * P z)
            + (∫ z in Work.Spaces.Iz,
                |deriv (Work.FTS.EllipticEst.cut n) z| * (z * (Work.Spaces.w z) ^ 2) * P z)))
          (fun n => ?_)
          (fun n => ?_) hg
        · have h1 := hErrA0 n
          have h2 := hErrB0 n
          have h3 : (0:ℝ) ≤ α ^ 2 / 2 := by positivity
          have h4 : (0:ℝ) ≤ α * (5 + α) / 2 := by nlinarith [h.1, h.2.1]
          nlinarith [mul_nonneg h3 h1, mul_nonneg h4 h2]
        · have h1 := hErrA0 n
          have h2 := hErrB0 n
          have h3 : (0:ℝ) ≤ α ^ 2 / 2 := by positivity
          have h4 : (0:ℝ) ≤ α * (5 + α) / 2 := by nlinarith [h.1, h.2.1]
          have h5 : α ^ 2 / 2 ≤ Cst := by rw [hCst]; exact le_max_left _ _
          have h6 : α * (5 + α) / 2 ≤ Cst := by rw [hCst]; exact le_max_right _ _
          nlinarith [mul_le_mul_of_nonneg_right h5 h1, mul_le_mul_of_nonneg_right h6 h2,
            mul_nonneg hCst0 h1, mul_nonneg hCst0 h2]
      have he0 : ∀ n : ℕ, 0 ≤ (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
              (2 * |deriv (Work.FTS.EllipticEst.cut n) z|
                  * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
                + |deriv (deriv (Work.FTS.EllipticEst.cut n)) z|
                  * (z ^ 2 * (Work.Spaces.w z) ^ 2)) * P z)
            + (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz,
                |deriv (Work.FTS.EllipticEst.cut n) z| * (z * (Work.Spaces.w z) ^ 2) * P z) := by
        intro n
        have h1 := hErrA0 n
        have h2 := hErrB0 n
        have h3 : (0:ℝ) ≤ α ^ 2 / 2 := by positivity
        have h4 : (0:ℝ) ≤ α * (5 + α) / 2 := by nlinarith [h.1, h.2.1]
        nlinarith [mul_nonneg h3 h1, mul_nonneg h4 h2]
      -- the RHS bound
      have hRHS : ∀ n : ℕ,
          ENNReal.ofReal Kn * (∫⁻ z in Work.Spaces.Iz,
                ENNReal.ofReal (Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2)
                  * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2)))
            + ENNReal.ofReal (1 / 2) * (∫⁻ z in Work.Spaces.Iz,
                ENNReal.ofReal (Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2)
                  * (∫⁻ θ in Work.Spaces.Iθ,
                      ENNReal.ofReal ((G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))
            + ENNReal.ofReal ((α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
                  (2 * |deriv (Work.FTS.EllipticEst.cut n) z|
                      * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
                    + |deriv (deriv (Work.FTS.EllipticEst.cut n)) z|
                      * (z ^ 2 * (Work.Spaces.w z) ^ 2)) * P z)
                + (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz,
                    |deriv (Work.FTS.EllipticEst.cut n) z| * (z * (Work.Spaces.w z) ^ 2) * P z))
          ≤ ENNReal.ofReal Kn * Mc
            + ENNReal.ofReal (1 / 2) * ENNReal.ofReal (Work.Spaces.HkSq α 0 G)
            + ENNReal.ofReal ((α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
                  (2 * |deriv (Work.FTS.EllipticEst.cut n) z|
                      * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
                    + |deriv (deriv (Work.FTS.EllipticEst.cut n)) z|
                      * (z ^ 2 * (Work.Spaces.w z) ^ 2)) * P z)
                + (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz,
                    |deriv (Work.FTS.EllipticEst.cut n) z| * (z * (Work.Spaces.w z) ^ 2) * P z)) := by
        intro n
        refine add_le_add (add_le_add ?_ ?_) le_rfl
        · refine mul_le_mul_of_nonneg_left ?_ (bot_le : (⊥ : ℝ≥0∞) ≤ _)
          rw [hMc]
          refine lintegral_mono fun z => ?_
          refine mul_le_mul_of_nonneg_right ?_ (bot_le : (⊥ : ℝ≥0∞) ≤ _)
          exact ENNReal.ofReal_le_ofReal (by
            have h1 := Work.FTS.EllipticEst.cut_le_one n z
            have h2 : (0:ℝ) ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
            nlinarith)
        · refine mul_le_mul_of_nonneg_left ?_ (bot_le : (⊥ : ℝ≥0∞) ≤ _)
          exact FnLintegralLeHkSq h.memG (Work.FTS.EllipticEst.cut n)
            (Work.FTS.EllipticEst.cut_nonneg n) (Work.FTS.EllipticEst.cut_le_one n)
      refine final_step (a := α ^ 2) hAmono hBmono hAsup hBsup ?_ herr he0
      intro n
      exact le_trans (hcrux n) (hRHS n)
  rwa [hAc, hBc, hMc, hKn] at hgoal

end Work.FTS.EllipticEst.Cores.Pieces.AeGradRho
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.FOH.psiRho =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest.FOH

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

open MeasureTheory Set Filter
open scoped ENNReal Topology

variable {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}

/-! ## The three `∫⁻`-functionals of the unweighted (in `θ`) first-order estimate -/

/-- The unweighted-in-`θ` mass functional `∫⁻_z w² ∫⁻_θ Ψ²`. -/
noncomputable def Mu (Ψ : ℝ → ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
    (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Ψ z θ) ^ 2))


/-- The `σ`-weighted mass functional `∫⁻_z w² ∫⁻_θ Ψ² σ`. -/
noncomputable def Ys (Ψ : ℝ → ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
    (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
      ((Ψ z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ))

/-- The `θ`-slice of an honest datum is `C²` on the open interval. -/
theorem slice_contDiffOn (h : Hon α F Ψ) {z : ℝ} (hz : 0 < z) :
    ContDiffOn ℝ 2 (fun θ : ℝ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) := by
  have h1 : ContDiffOn ℝ 2 (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    h.sm 2
  have h2 : ContDiffOn ℝ 2 (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2)) := by fun_prop
  have h3 := h1.comp h2 (fun θ hθ => Set.mem_prod.mpr ⟨hz, hθ⟩)
  exact h3

/-- The `z`-variable is positive almost everywhere for `volume.restrict Iz`. -/
theorem ae_pos_Iz : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
  rw [HR2.restrict_Iz_eq_restrict_Ioi]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioi

/-! ## The unweighted constrained gap, integrated against `w²` -/


/-! ## The `σ`-weighted mass is controlled by the unweighted angular gradient -/


/-! ## The unweighted angular gradient is bounded by `HkSq α 0 F` -/

/-- The coefficient `K(α) = 13/2 + 3α² + (3/2)α(5+α)` of the radial weight transfer. -/
noncomputable def Kcoef (α : ℝ) : ℝ := 13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α))







/-! ## The `ρ`-norm of `Ψ` -/


end Work.FTS.EllipticEst.Honest.FOH
end
