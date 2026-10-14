import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Tactic.Have
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EllipticEst.H2W.Slot01W.SliceKit
import Submission.Work.FTS.EllipticEst.H2W.Slot01W.ZTBound
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgEngine
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.ZcutSmoothCompact
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.aeGradTrace0Left =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `0⁺` trace of `z ∂_z u`, from the a.e. mixed honesty

`aeGradTraceLeft_of_energy`: for `AeData α u G` with the *a.e.-in-`z`* slice honesty of the mixed
slot `z ∂_z∂_θ u` and its outer `z`-integrability (`IntegrableOn (sliceE u) Iz`), the slice
`θ ↦ z ∂_z u(z,θ)` tends to `0` at `0⁺` for a.e. `z > 0`.

This is the argument of `AngAWeak.aeGradTraceLeft` (the version whose outer honesty carries the
weight `w²`), with the outer hypothesis weakened to the unweighted integrability of `sliceE`,
which suffices: that hypothesis is used only to make `√sliceE` and the dominator `boundU`
locally integrable, which follows from `IntegrableOn (sliceE u) Iz` by Cauchy–Schwarz on the
finite interval `[a,b] ⊆ (0,∞)`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllipticEst.AngAWeak

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz

theorem aeGradTraceLeft_of_energy (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (hAe : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hGae : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) Iθ)
    (hE : MeasureTheory.IntegrableOn (sliceE u) Iz) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ => z * Work.Spaces.pz u z θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hsm := Work.FTS.EllipticEst.H2W.Ae.AeData.smooth hAe
  have hS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  obtain ⟨K, hKpos, hraw⟩ := sliceBoundaryLeftRaw
  have hθ1 : (1 : ℝ) ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by norm_num, by linarith [Real.pi_gt_three]⟩
  have hmemθ : ∀ n : ℕ, (1 / ((n : ℝ) + 1)) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro n
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hden1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
    have hden0 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    refine ⟨?_, ?_⟩
    · exact div_pos (by norm_num) hden0
    · have h1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_iff₀ hden0]
        simpa using hden1
      linarith [Real.pi_gt_three]
  have hθn : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) Filter.atTop
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Filter.Eventually.of_forall fun n => by rw [Set.mem_Ioi]; positivity⟩
  -- the candidate trace, as the limsup along the diagonal sequence
  set c0 : ℝ → ℝ := fun s =>
    Filter.limsup (fun n : ℕ => s * Work.Spaces.pz u s (1 / ((n : ℝ) + 1))) Filter.atTop
    with hc0def
  set f : ℝ → ℝ := fun s => c0 s / s with hfdef
  have hc0_apply : ∀ s : ℝ, c0 s =
      Filter.limsup (fun n : ℕ => s * Work.Spaces.pz u s (1 / ((n : ℝ) + 1))) Filter.atTop :=
    fun s => by simp only [hc0def]
  have hf_apply : ∀ s : ℝ, f s = c0 s / s := fun s => by simp only [hfdef]
  -- ## Step 1: measurability of `c0`
  have hγaesm : ∀ n : ℕ, AEMeasurable
      (fun s : ℝ => s * Work.Spaces.pz u s (1 / ((n : ℝ) + 1)))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    intro n
    exact ContinuousOn.aemeasurable
      (continuousOn_id.mul ((hS.pz).curry_z (hmemθ n)).continuousOn) measurableSet_Ioi
  have hc0aesm : AEMeasurable c0 (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    AEMeasurable.limsup hγaesm
  -- ## Step 2: the one-sided limit and the quadratic bound, on the honest set
  have hmain : ∀ s : ℝ,
      MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) s θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) Iθ → 0 < s →
      Filter.Tendsto (fun θ => Work.Spaces.Dz u s θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (c0 s)) ∧
        ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (Work.Spaces.Dz u s θ - c0 s) ^ 2
          ≤ K * θ ^ (1 + Work.Spaces.eta) * sliceE u s := by
    intro s hEs hs
    obtain ⟨c, hc, hb⟩ := sliceBoundaryLeft hS hs hKpos.le hraw hEs
    have hseq : Filter.Tendsto (fun n : ℕ => s * Work.Spaces.pz u s (1 / ((n : ℝ) + 1)))
        Filter.atTop (nhds c) := by
      simpa only [Work.Spaces.Dz, Function.comp_def] using hc.comp hθn
    have hc0 : c0 s = c := by
      rw [hc0_apply s]
      exact Filter.Tendsto.limsup_eq hseq
    constructor
    · rw [hc0]; exact hc
    · intro θ hθ
      rw [hc0]
      exact hb θ hθ
  -- ## Step 3: the pointwise domination of `|∂_z u(s,θ)|`
  have hΦnn : ∀ s : ℝ, 0 ≤ sliceE u s := sliceE_nonneg u
  have hbd : ∀ s : ℝ,
      MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) s θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) Iθ → 0 < s →
      ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |Work.Spaces.pz u s θ| ≤ boundU u K s := by
    intro s hEs hs θ hθ
    have h1 : (Work.Spaces.Dz u s 1 - c0 s) ^ 2 ≤ K * sliceE u s := by
      simpa using (hmain s hEs hs).2 1 hθ1
    have h2 : (Work.Spaces.Dz u s θ - c0 s) ^ 2
        ≤ K * (Real.pi / 2) ^ (1 + Work.Spaces.eta) * sliceE u s := by
      refine le_trans ((hmain s hEs hs).2 θ hθ) ?_
      have hpow : θ ^ (1 + Work.Spaces.eta) ≤ (Real.pi / 2) ^ (1 + Work.Spaces.eta) :=
        Real.rpow_le_rpow hθ.1.le (le_of_lt hθ.2) (by norm_num [Work.Spaces.eta])
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hKpos.le) (hΦnn s)
    exact pz_le_of_slice_bounds hs hθ hKpos (hΦnn s) h1 h2
  -- ## Step 4: the integrability of `√sliceE`, `boundU` and `f`
  have hsqrtPhiint : ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (fun s => Real.sqrt (sliceE u s)) (Set.Icc a b) :=
    fun a b ha hab =>
      (Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.GlueEnergy.integrableOn_sqrtSliceE_and_boundU_of_energy
        hS hE hKpos ha hab).1
  have hboundint : ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (boundU u K) (Set.Icc a b) :=
    fun a b ha hab =>
      (Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.GlueEnergy.integrableOn_sqrtSliceE_and_boundU_of_energy
        hS hE hKpos ha hab).2
  have hfint : ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn f (Set.Icc a b) := by
    intro a b ha hab
    have hbnd := hboundint a b ha hab
    have hsub : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun s hs => lt_of_lt_of_le ha hs.1
    have hGsub : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Icc a b)),
        MeasureTheory.IntegrableOn
          (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) s θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) Iθ :=
      MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono_set volume hsub) hGae
    refine Integrable.mono' hbnd ?_ ?_
    · have h1 : AEMeasurable (fun s : ℝ => c0 s / s)
          (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
        hc0aesm.div (ContinuousOn.aemeasurable continuousOn_id measurableSet_Ioi)
      refine (h1.aestronglyMeasurable.mono_measure
        (MeasureTheory.Measure.restrict_mono hsub le_rfl)).congr ?_
      filter_upwards with s
      exact (hf_apply s).symm
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc, hGsub]
        with s hs hsG
      have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
      have hΦ0 : 0 ≤ sliceE u s := hΦnn s
      have h1 : (Work.Spaces.Dz u s 1 - c0 s) ^ 2 ≤ K * sliceE u s := by
        simpa using (hmain s hsG hs0).2 1 hθ1
      have hKΦ : 0 ≤ K * sliceE u s := mul_nonneg hKpos.le hΦ0
      have hc0bd : |c0 s| ≤ |Work.Spaces.Dz u s 1| + Real.sqrt (K * sliceE u s) := by
        have h2abs : |Work.Spaces.Dz u s 1 - c0 s| ≤ Real.sqrt (K * sliceE u s) :=
          abs_le_of_sq_le_sq (by rw [Real.sq_sqrt hKΦ]; exact h1) (Real.sqrt_nonneg _)
        calc |c0 s| = |c0 s - Work.Spaces.Dz u s 1 + Work.Spaces.Dz u s 1| := by ring_nf
          _ ≤ |c0 s - Work.Spaces.Dz u s 1| + |Work.Spaces.Dz u s 1| := abs_add_le _ _
          _ = |Work.Spaces.Dz u s 1 - c0 s| + |Work.Spaces.Dz u s 1| := by rw [abs_sub_comm]
          _ ≤ Real.sqrt (K * sliceE u s) + |Work.Spaces.Dz u s 1| := by linarith
          _ = |Work.Spaces.Dz u s 1| + Real.sqrt (K * sliceE u s) := by ring
      have hDz1 : Work.Spaces.Dz u s 1 = s * Work.Spaces.pz u s 1 := rfl
      have hsqrtK : Real.sqrt (K * sliceE u s) = Real.sqrt K * Real.sqrt (sliceE u s) :=
        Real.sqrt_mul hKpos.le _
      have hMle : Real.sqrt K ≤ Real.sqrt K
          + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)) := by
        linarith [Real.sqrt_nonneg (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))]
      rw [hf_apply s, Real.norm_eq_abs, abs_div, abs_of_pos hs0, boundU]
      have h4 : |c0 s| / s ≤ (|Work.Spaces.Dz u s 1|
          + (Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)))
            * Real.sqrt (sliceE u s)) / s := by
        refine div_le_div_of_nonneg_right ?_ hs0.le
        rw [hsqrtK] at hc0bd
        have := mul_le_mul_of_nonneg_right hMle (Real.sqrt_nonneg (sliceE u s))
        linarith [hc0bd, this]
      have h5 : (|Work.Spaces.Dz u s 1| + (Real.sqrt K
            + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)))
            * Real.sqrt (sliceE u s)) / s
          = |Work.Spaces.pz u s 1| + (Real.sqrt K
            + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)))
            * (Real.sqrt (sliceE u s) / s) := by
        rw [hDz1, abs_mul, abs_of_pos hs0, add_div, mul_div_cancel_left₀ _ (ne_of_gt hs0),
          mul_div_assoc]
      rw [← h5]
      exact h4
  -- ## Step 5: the left trace of `u`
  have hex : ∀ z : ℝ, 0 < z → ∃ L : ℝ,
      Filter.Tendsto (fun θ => u z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L) := by
    intro z hz
    refine Work.FTS.EllipticEst.sliceLimitLeftExists (fun θ => u z θ)
      (fun n => Work.FTS.EllipticEst.Endpt.contDiffOn_slice_of_strip hsm hz n) ?_
    have h0 := Work.FTS.EllipticEst.Endpt.integrableOn_pthIter2_sEta_of_HkMem
      (Ψ := u) (Work.FTS.EllipticEst.H2W.Ae.AeData.memAng2 hAe) hz
    refine h0.congr (Filter.Eventually.of_forall (fun θ => ?_))
    show Work.Spaces.pthIter 2 u z θ ^ 2 * Work.FTS.EllipticEst.sEta θ
      = (deriv (fun t => deriv (fun θ' => u z θ') t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    rw [show Work.Spaces.pthIter 2 u z θ
      = deriv (fun t => deriv (fun θ' => u z θ') t) θ from rfl]
  set g : ℝ → ℝ := fun z => if hz : 0 < z then Classical.choose (hex z hz) else 0 with hgdef
  have hg_apply : ∀ z : ℝ, (hz : 0 < z) → g z = Classical.choose (hex z hz) := by
    intro z hz
    simp only [hgdef, dif_pos hz]
  have hglim : ∀ z : ℝ, 0 < z →
      Filter.Tendsto (fun θ => u z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (g z)) := by
    intro z hz
    rw [hg_apply z hz]
    exact Classical.choose_spec (hex z hz)
  have hgzero : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)), g z = 0 := by
    filter_upwards [Work.FTS.EllipticEst.Dispatch.aeLeftLimitD α u G hAe,
      MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hzlim hzpos
    exact tendsto_nhds_unique (hglim z hzpos) hzlim
  -- ## Step 6: the integral relation `∫_a^b f = g b - g a`
  have hrel : ∀ a b : ℝ, 0 < a → a < b → ∫ t in a..b, f t = g b - g a := by
    intro a b ha hab
    have hsub : Set.Ioc a b ⊆ Set.Ioi (0 : ℝ) := fun s hs => lt_trans ha hs.1
    have hGsub : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioc a b)),
        MeasureTheory.IntegrableOn
          (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) s θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) Iθ :=
      MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono_set volume hsub) hGae
    have hbndIoc : MeasureTheory.IntegrableOn (boundU u K) (Set.Ioc a b) :=
      (integrableOn_Icc_iff_integrableOn_Ioc (f := boundU u K) (a := a) (b := b)
        (by simp)).mp (hboundint a b ha hab)
    have hDCT : Filter.Tendsto
        (fun n : ℕ => ∫ s in Set.Ioc a b, Work.Spaces.pz u s (1 / ((n : ℝ) + 1)))
        Filter.atTop (nhds (∫ s in Set.Ioc a b, f s)) := by
      refine MeasureTheory.tendsto_integral_of_dominated_convergence
        (μ := MeasureTheory.volume.restrict (Set.Ioc a b))
        (F := fun n : ℕ => fun s : ℝ => Work.Spaces.pz u s (1 / ((n : ℝ) + 1)))
        (f := f) (bound := boundU u K) ?_ hbndIoc ?_ ?_
      · intro n
        exact (((hS.pz).curry_z (hmemθ n)).continuousOn.aestronglyMeasurable
          measurableSet_Ioi).mono_measure
          (MeasureTheory.Measure.restrict_mono hsub le_rfl)
      · intro n
        filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc, hGsub]
          with s hs hsG
        have hs0 : 0 < s := lt_trans ha hs.1
        rw [Real.norm_eq_abs]
        exact hbd s hsG hs0 _ (hmemθ n)
      · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc, hGsub]
          with s hs hsG
        have hs0 : 0 < s := lt_trans ha hs.1
        have h1 : Filter.Tendsto (fun θ => Work.Spaces.Dz u s θ)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (c0 s)) := (hmain s hsG hs0).1
        have h2 : Filter.Tendsto (fun n : ℕ => Work.Spaces.Dz u s (1 / ((n : ℝ) + 1)))
            Filter.atTop (nhds (c0 s)) := h1.comp hθn
        have h3 : Filter.Tendsto (fun n : ℕ =>
            Work.Spaces.Dz u s (1 / ((n : ℝ) + 1)) / s) Filter.atTop (nhds (c0 s / s)) :=
          h2.div_const s
        have hfun : (fun n : ℕ => Work.Spaces.pz u s (1 / ((n : ℝ) + 1)))
            = fun n : ℕ => Work.Spaces.Dz u s (1 / ((n : ℝ) + 1)) / s := by
          funext n
          rw [Work.Spaces.Dz, mul_div_cancel_left₀ _ (ne_of_gt hs0)]
        rw [hfun, hf_apply s]
        exact h3
    have hFTC : ∀ n : ℕ, u b (1 / ((n : ℝ) + 1)) - u a (1 / ((n : ℝ) + 1))
        = ∫ s in Set.Ioc a b, Work.Spaces.pz u s (1 / ((n : ℝ) + 1)) := by
      intro n
      have h := Work.FTS.EllipticEst.pzIter_slice_FTC_open hS 0 ha hab.le (hmemθ n)
      simpa only [Work.Spaces.pzIter_zero, Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero,
        intervalIntegral.integral_of_le hab.le] using h
    have hlimL : Filter.Tendsto
        (fun n : ℕ => u b (1 / ((n : ℝ) + 1)) - u a (1 / ((n : ℝ) + 1)))
        Filter.atTop (nhds (g b - g a)) :=
      ((hglim b (ha.trans hab)).comp hθn).sub ((hglim a ha).comp hθn)
    have hEqIoc : (∫ s in Set.Ioc a b, f s) = g b - g a := by
      refine tendsto_nhds_unique ?_ hlimL
      simpa only [hFTC] using hDCT
    rw [intervalIntegral.integral_of_le hab.le]
    exact hEqIoc
  -- ## Step 7: `f` vanishes a.e.
  have hintI : ∀ a b : ℝ, 0 < a → a < b → IntervalIntegrable f MeasureTheory.volume a b := by
    intro a b ha hab
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab.le]
    exact hfint a b ha hab
  have hstep : ∀ n : ℕ, ∀ᵐ z ∂(MeasureTheory.volume.restrict
      (Set.Ioi (1 / ((n : ℝ) + 1)))), f z = 0 := by
    intro n
    have hz0 : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      exact div_pos (by norm_num) (by linarith)
    refine Work.FTS.EllipticEst.Mine.CutoffPieces.ae_zero_of_primitive_const
      (f := f) (g := g) (z₀ := 1 / ((n : ℝ) + 1)) hz0 ?_ ?_ ?_
    · intro a b ha hab
      exact hintI a b (lt_of_lt_of_le hz0 ha) hab
    · have hle : MeasureTheory.volume.restrict (Set.Ioi (1 / ((n : ℝ) + 1)))
          ≤ MeasureTheory.volume.restrict (Set.Ioi 0) :=
        MeasureTheory.Measure.restrict_mono (fun z hz => hz0.trans hz) le_rfl
      exact MeasureTheory.ae_mono hle hgzero
    · intro a b ha hab
      exact hrel a b (lt_of_lt_of_le hz0 ha) hab
  have hunion : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)), f z = 0 := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    show ∀ᵐ z ∂MeasureTheory.volume, 0 < z → f z = 0
    rw [MeasureTheory.ae_iff]
    show MeasureTheory.volume {z : ℝ | ¬(0 < z → f z = 0)} = 0
    have hbad : MeasureTheory.volume {z : ℝ | 0 < z ∧ f z ≠ 0} = 0 := by
      refine le_antisymm ?_ bot_le
      have hsub : {z : ℝ | 0 < z ∧ f z ≠ 0} ⊆ ⋃ n : ℕ,
          {z : ℝ | z ∈ Set.Ioi (1 / ((n : ℝ) + 1)) ∧ f z ≠ 0} := by
        intro z hz
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hz.1
        exact Set.mem_iUnion.mpr ⟨n, hn, hz.2⟩
      calc MeasureTheory.volume {z : ℝ | 0 < z ∧ f z ≠ 0}
          ≤ MeasureTheory.volume (⋃ n : ℕ,
              {z : ℝ | z ∈ Set.Ioi (1 / ((n : ℝ) + 1)) ∧ f z ≠ 0}) :=
            MeasureTheory.measure_mono hsub
        _ ≤ ∑' n : ℕ, MeasureTheory.volume
              {z : ℝ | z ∈ Set.Ioi (1 / ((n : ℝ) + 1)) ∧ f z ≠ 0} :=
            MeasureTheory.measure_iUnion_le _
        _ = 0 := by
            refine ENNReal.tsum_eq_zero.mpr (fun n => ?_)
            have hn := hstep n
            rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi, MeasureTheory.ae_iff] at hn
            convert hn using 2
            ext z
            simp only [Set.mem_ofPred_eq, Set.mem_Ioi]
            tauto
    convert hbad using 2
    ext z
    simp only [Set.mem_ofPred_eq]
    tauto
  -- ## Step 8: conclude
  have hc0zero : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)), c0 z = 0 := by
    filter_upwards [hunion, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi]
      with z hz hzpos
    have hdiv : c0 z / z = 0 := by rw [← hf_apply z]; exact hz
    rcases div_eq_zero_iff.mp hdiv with h0 | h0
    · exact h0
    · exact absurd h0 (ne_of_gt hzpos)
  filter_upwards [hc0zero, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi, hGae]
    with z hz hzpos hzG
  have h1 := (hmain z hzG hzpos).1
  rw [hz] at h1
  simpa only [Work.Spaces.Dz] using h1

end Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.AngBW.slot01Bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.AngBW

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## Elementary facts on the angular interval -/

/-- `sin(2θ) ≥ 0` on `Iθ = [0,π/2]`. -/
theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-! ## `rpow` algebra on the angular weights -/

/-- `s ^ 2 * s ^ (-c) = s ^ (2 - c)` for `s ≥ 0` and `c < 2`. -/
private theorem rpow_two_mul_neg_lt_two {s : ℝ} (hs : 0 ≤ s) {c : ℝ} (hc : c < 2) :
    s ^ 2 * s ^ (-c) = s ^ (2 - c) := by
  rcases eq_or_lt_of_le hs with h | h
  · subst h
    have h2 : (0 : ℝ) < 2 - c := by linarith
    by_cases hc0 : c = 0
    · subst hc0; norm_num
    · rw [Real.zero_rpow (neg_ne_zero.mpr hc0), Real.zero_rpow (ne_of_gt h2), mul_zero]
  · rw [← Real.rpow_natCast s 2, ← Real.rpow_add h]; ring_nf

/-- `(s ^ (-c / 2)) ^ 2 = s ^ (-c)` for `s ≥ 0`. -/
private theorem sq_rpow_neg_half {s : ℝ} (hs : 0 ≤ s) (c : ℝ) :
    (s ^ (-(c / 2))) ^ 2 = s ^ (-c) := by
  rw [← Real.rpow_natCast (s ^ (-(c / 2))) 2, ← Real.rpow_mul hs]
  ring_nf

/-! ## The `(1,0)` mixed slot: weight identities -/

/-- `D_θ f = sin(2θ)·∂_θ f`. -/
private theorem mixed_zero_one_eq (f : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed 0 1 f = fun z θ => Real.sin (2 * θ) * Work.Spaces.pth f z θ := by
  funext z θ
  rfl

/-- The squared weight identity for the `(1,0)` slot:
`(D_θ f · Wt α)² = (∂_θ f)² w² sin(2θ)^{2-γ}` on the angular interval. -/
private theorem wt_sq_identity (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (f : ℝ → ℝ → ℝ) (z : ℝ)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.pth f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
  have hγ : 0 < Work.Spaces.gam α := Work.Spaces.gam_pos hα
  have hγ2 : Work.Spaces.gam α < 2 := by
    rw [Work.Spaces.gam]; linarith
  rw [mixed_zero_one_eq]
  simp only [Work.Spaces.Wt, Work.Spaces.wTheta]
  have h1 : (Real.sin (2 * θ) * Work.Spaces.pth f z θ
        * (Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2)))) ^ 2
      = (Real.sin (2 * θ)) ^ 2 * (Work.Spaces.pth f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2))) ^ 2 := by ring
  rw [h1, sq_rpow_neg_half hs (Work.Spaces.gam α), ← rpow_two_mul_neg_lt_two hs hγ2]
  ring

/-- The `(1,0)` slot of any function, as an iterated integral with the angular weight
`σ_γ = sin(2θ)^{2-γ}`. -/
private theorem L2Sq_mixed01_eq (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ)
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth f z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) := by
  rw [Work.Spaces.L2Sq]
  refine setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
  rw [show (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) from
    setIntegral_congr_fun measurableSet_Icc (fun θ hθ => wt_sq_identity α hα hα4 f z hθ)]
  rw [show (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
          * ((Work.Spaces.pth f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
        from setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)]
  rw [MeasureTheory.integral_const_mul]

/-- The left-hand side, rewritten as an iterated integral with the angular weight `σ_γ`. -/
private theorem LHS_eq (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (Ψ : ℝ → ℝ → ℝ) :
    Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 0 1 (Work.Spaces.pthIter 2 Ψ) z θ
        * Work.Spaces.Wt α z θ)
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 3 Ψ z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) := by
  rw [L2Sq_mixed01_eq α hα hα4 (Work.Spaces.pthIter 2 Ψ)]
  refine setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
  refine congrArg (fun t => (Work.Spaces.w z) ^ 2 * t) ?_
  refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
  simp only [Work.Spaces.pthIter_succ]


/-- The weight algebra for a slot: `(A · (w / s^{η/2}))² = A² · s^{-η} · w²`. -/
private theorem slot_sq_eq {η A wv s : ℝ} (hs : 0 ≤ s) :
    (A * (wv / s ^ (η / 2))) ^ 2 = A ^ 2 * s ^ (-η) * wv ^ 2 := by
  rw [div_eq_mul_inv, ← Real.rpow_neg hs (η / 2)]
  rw [show (A * (wv * s ^ (-(η / 2)))) ^ 2 = A ^ 2 * wv ^ 2 * (s ^ (-(η / 2))) ^ 2 from by ring]
  rw [sq_rpow_neg_half hs η]
  ring

/-! ## The target -/

theorem slot01Bound : ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 0 1 (Work.Spaces.pthIter 2 Ψ) z θ
          * Work.Spaces.Wt α z θ)
        ≤ K * ((∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
              Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
            + Work.Spaces.HkSq α 2 F) := by
  obtain ⟨K0, hK0pos, hK0⟩ := Work.H2W.slot01SliceBound
  obtain ⟨C1, hC1pos, hC1⟩ := Work.H2W.slot01ZTBound
  have hC1nn : 0 ≤ C1 := hC1pos.le
  have hK0nn : 0 ≤ K0 := hK0pos.le
  refine ⟨K0 * (1 + 3 * C1) + 1, by positivity, ?_⟩
  intro α F Ψ hα hα4 h
  have hsmΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  -- ### the pieces of the estimate, as functions of the radius `z`
  set JintF : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 2 F z θ with hJintF
  set Q : ℕ → ℝ → ℝ := fun j z => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 with hQ
  set Ps : ℕ → ℝ → ℝ := fun j z => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ with hPs
  set I : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 3 Ψ z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) with hI
  set Fs : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth F z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) with hFs
  set Zt : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
      (deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) with hZt
  set Dt : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
      (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) with hDt
  -- ### elementary nonnegativity
  have hJnn : ∀ z, 0 ≤ JintF z := fun z => by
    rw [hJintF]; beta_reduce
    exact MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 2 F z θ
  have hQnn : ∀ j z, 0 ≤ Q j z := fun j z => by
    rw [hQ]; beta_reduce
    exact MeasureTheory.integral_nonneg fun θ => sq_nonneg _
  -- ### the weight identity `w² · Ps j = Q j`
  have hQeq : ∀ j z, (Work.Spaces.w z) ^ 2 * Ps j z = Q j z := by
    intro j z
    rw [hPs, hQ, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae
      ((MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall ?_))
    intro θ hθ
    beta_reduce
    have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
    rw [slot_sq_eq (η := Work.Spaces.eta) hs, Work.FTS.EllipticEst.sEta]
    ring
  -- ### the source slot of `F` is dominated by the `ℋ²`-integrand of `F`
  have hFsQ : ∀ z ∈ Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * Fs z ≤ JintF z := by
    intro z hz
    rw [hFs, hJintF, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono_of_nonneg ?_ (h.memF.1 z hz) ?_
    · refine (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
        (Filter.Eventually.of_forall fun θ hθ => ?_)
      exact mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _))
    · refine (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
        (Filter.Eventually.of_forall fun θ hθ => ?_)
      beta_reduce
      have h1 := wt_sq_identity α hα hα4 F z hθ
      rw [show (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pth F z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
          = (Work.Spaces.pth F z θ) ^ 2 * (Work.Spaces.w z) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) from by ring]
      rw [← h1]
      exact Work.Spaces.sq_le_HkIntegrand_mixed α 2 F z θ 1 0 le_rfl (by norm_num)
  -- ### the a.e.-in-`z` domination `w² · I ≤ K0 · JintF + K0(1+3C1)(Q 0 + Q 1 + Q 2)`
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (Work.Spaces.w z) ^ 2 * I z
        ≤ K0 * JintF z + K0 * (1 + 3 * C1) * (Q 0 z + Q 1 z + Q 2 z) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ici,
      Filter.Eventually.of_forall (hK0 α F Ψ hα hα4 h), hC1 α F Ψ hα hα4 h]
      with z hz h1 h2
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · -- at `z = 0` the weight `w` vanishes, and the right-hand side is nonnegative
      subst hz0
      have hw0 : Work.Spaces.w (0 : ℝ) = 0 := by simp [Work.Spaces.w]
      have hMJ : 0 ≤ K0 * JintF 0 := mul_nonneg hK0nn (hJnn 0)
      have hK1 : 0 ≤ K0 * (1 + 3 * C1) := mul_nonneg hK0nn (by linarith)
      have hsum0 : 0 ≤ Q 0 0 + Q 1 0 + Q 2 0 := by
        have := hQnn 0 0; have := hQnn 1 0; have := hQnn 2 0; linarith
      have hMQ : 0 ≤ K0 * (1 + 3 * C1) * (Q 0 0 + Q 1 0 + Q 2 0) := mul_nonneg hK1 hsum0
      rw [hw0]
      simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
      linarith [hMJ, hMQ]
    · -- the honest case `z > 0`
      have h1z : I z ≤ K0 * (Fs z + Ps 0 z + Zt z + Dt z) := by
        simp only [hI, hFs, hPs, hZt, hDt]
        exact h1 hzpos
      have h2z := h2 hzpos
      have hw : (0 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
      have hZ := h2z.1
      have hD := h2z.2
      have hZ' : (Work.Spaces.w z) ^ 2 * Zt z ≤ C1 * (Q 1 z + Q 2 z) := by
        calc (Work.Spaces.w z) ^ 2 * Zt z
            ≤ (Work.Spaces.w z) ^ 2 * (C1 * (Ps 1 z + Ps 2 z)) :=
              mul_le_mul_of_nonneg_left hZ hw
          _ = C1 * (Q 1 z + Q 2 z) := by rw [← hQeq 1 z, ← hQeq 2 z]; ring
      have hD' : (Work.Spaces.w z) ^ 2 * Dt z ≤ C1 * Q 1 z := by
        calc (Work.Spaces.w z) ^ 2 * Dt z
            ≤ (Work.Spaces.w z) ^ 2 * (C1 * Ps 1 z) := mul_le_mul_of_nonneg_left hD hw
          _ = C1 * Q 1 z := by rw [← hQeq 1 z]; ring
      calc (Work.Spaces.w z) ^ 2 * I z
          ≤ (Work.Spaces.w z) ^ 2 * (K0 * (Fs z + Ps 0 z + Zt z + Dt z)) :=
            mul_le_mul_of_nonneg_left h1z hw
        _ = K0 * ((Work.Spaces.w z) ^ 2 * Fs z + (Work.Spaces.w z) ^ 2 * Ps 0 z
              + (Work.Spaces.w z) ^ 2 * Zt z + (Work.Spaces.w z) ^ 2 * Dt z) := by ring
        _ ≤ K0 * (JintF z + Q 0 z + C1 * (Q 1 z + Q 2 z) + C1 * Q 1 z) := by
            refine mul_le_mul_of_nonneg_left ?_ hK0nn
            linarith [hFsQ z hz, hQeq 0 z, hZ', hD']
        _ ≤ K0 * JintF z + K0 * (1 + 3 * C1) * (Q 0 z + Q 1 z + Q 2 z) := by
            have hinner : Q 0 z + C1 * (Q 1 z + Q 2 z) + C1 * Q 1 z
                ≤ (1 + 3 * C1) * (Q 0 z + Q 1 z + Q 2 z) := by
              have h3 : 0 ≤ C1 * (3 * Q 0 z + Q 1 z + 2 * Q 2 z) :=
                mul_nonneg hC1nn (by linarith [hQnn 0 z, hQnn 1 z, hQnn 2 z])
              nlinarith [h3, hQnn 0 z, hQnn 1 z, hQnn 2 z]
            calc K0 * (JintF z + Q 0 z + C1 * (Q 1 z + Q 2 z) + C1 * Q 1 z)
                = K0 * JintF z + K0 * (Q 0 z + C1 * (Q 1 z + Q 2 z) + C1 * Q 1 z) := by ring
              _ ≤ K0 * JintF z + K0 * ((1 + 3 * C1) * (Q 0 z + Q 1 z + Q 2 z)) :=
                  add_le_add le_rfl (mul_le_mul_of_nonneg_left hinner hK0nn)
              _ = K0 * JintF z + K0 * (1 + 3 * C1) * (Q 0 z + Q 1 z + Q 2 z) := by ring
  -- ### integrability of the dominating function
  have hIntJ : MeasureTheory.Integrable JintF
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := h.memF.2
  have hIntQ : ∀ j, j ≤ 2 → MeasureTheory.Integrable (Q j)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    intro j hj
    have hbase := Work.FTS.EllipticEst.integrableOn_slice_Iz α 2 ((hsmΨ.pth).pth) h.memB j hj
    refine hbase.congr ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ici] with z hz
    rw [hQ]
    beta_reduce
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · subst hz0
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
      simp [Work.Spaces.w]
    · refine MeasureTheory.integral_congr_ae
        (Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_))
      beta_reduce
      have hp : (z, θ) ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2) :=
        ⟨hzpos, hθ⟩
      have hcomm : Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
          = Work.Spaces.DzIter j (Work.Spaces.pthIter 2 Ψ) z θ :=
        Work.EllipticEst.H2W.pthIter2_DzIter_comm hsmΨ j hp
      rw [hcomm]
      rfl
  -- ### the integrated comparison
  have hIntQsum : MeasureTheory.Integrable (fun z => Q 0 z + Q 1 z + Q 2 z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    ((hIntQ 0 (by norm_num)).add (hIntQ 1 (by norm_num))).add (hIntQ 2 (by norm_num))
  have hMint : MeasureTheory.Integrable
      (fun z => K0 * JintF z + K0 * (1 + 3 * C1) * (Q 0 z + Q 1 z + Q 2 z))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    (hIntJ.const_mul K0).add (hIntQsum.const_mul (K0 * (1 + 3 * C1)))
  have hmain : ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * I z
      ≤ ∫ z in Work.Spaces.Iz,
          K0 * JintF z + K0 * (1 + 3 * C1) * (Q 0 z + Q 1 z + Q 2 z) :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (by
        rw [hI]; beta_reduce
        refine MeasureTheory.integral_nonneg_of_ae
          ((MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
            (Filter.Eventually.of_forall fun θ hθ => ?_))
        exact mul_nonneg (sq_nonneg _)
          (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _)))
      hMint hslice
  -- ### the right-hand side
  set L : ℕ → ℝ := fun j => Work.Spaces.L2Sq (fun z θ =>
      Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) with hLdef
  have hLnn : ∀ j, 0 ≤ L j := fun j => by
    rw [hLdef]; beta_reduce
    rw [Work.Spaces.L2Sq]
    exact MeasureTheory.integral_nonneg fun z =>
      MeasureTheory.integral_nonneg fun θ => sq_nonneg _
  have hQint : ∀ j, ∫ z in Work.Spaces.Iz, Q j z = L j := fun j => by
    rw [hQ]
    rw [hLdef]
    beta_reduce
    rw [Work.Spaces.L2Sq]
  have hJint : ∫ z in Work.Spaces.Iz, JintF z = Work.Spaces.HkSq α 2 F := rfl
  have hsum : (∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
        Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
      = L 0 + L 1 + L 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, hLdef]
  -- ### the value of the dominating integral
  have hE : ∫ z in Work.Spaces.Iz,
        (K0 * JintF z + K0 * (1 + 3 * C1) * (Q 0 z + Q 1 z + Q 2 z))
      = K0 * Work.Spaces.HkSq α 2 F + K0 * (1 + 3 * C1) * (L 0 + L 1 + L 2) := by
    rw [MeasureTheory.integral_add (f := fun z => K0 * JintF z)
      (g := fun z => K0 * (1 + 3 * C1) * (Q 0 z + Q 1 z + Q 2 z))
      (hIntJ.const_mul K0) (hIntQsum.const_mul (K0 * (1 + 3 * C1)))]
    rw [MeasureTheory.integral_const_mul K0 JintF,
      MeasureTheory.integral_const_mul (K0 * (1 + 3 * C1))
        (fun z => Q 0 z + Q 1 z + Q 2 z)]
    rw [MeasureTheory.integral_add (f := fun z => Q 0 z + Q 1 z) (g := fun z => Q 2 z)
      ((hIntQ 0 (by norm_num)).add (hIntQ 1 (by norm_num))) (hIntQ 2 (by norm_num))]
    rw [MeasureTheory.integral_add (f := fun z => Q 0 z) (g := fun z => Q 1 z)
      (hIntQ 0 (by norm_num)) (hIntQ 1 (by norm_num))]
    rw [hJint, hQint 0, hQint 1, hQint 2]
  -- ### assembly
  have hLHS : Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 0 1 (Work.Spaces.pthIter 2 Ψ) z θ
        * Work.Spaces.Wt α z θ)
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * I z := by
    rw [LHS_eq α hα hα4 Ψ]
  rw [hLHS, hsum]
  refine le_trans (le_trans hmain (le_of_eq hE)) ?_
  have hH0 : 0 ≤ Work.Spaces.HkSq α 2 F := Work.Spaces.HkSq_nonneg α 2 F
  have hS0 : 0 ≤ L 0 + L 1 + L 2 := by
    have := hLnn 0; have := hLnn 1; have := hLnn 2; linarith
  have hKC : 0 ≤ K0 * C1 := mul_nonneg hK0nn hC1nn
  -- `K0 ≤ K0 · (1 + 3 C1)`
  have hXK : K0 ≤ K0 * (1 + 3 * C1) := by nlinarith [hKC]
  have hA : K0 * Work.Spaces.HkSq α 2 F
      ≤ (K0 * (1 + 3 * C1)) * Work.Spaces.HkSq α 2 F :=
    mul_le_mul_of_nonneg_right hXK hH0
  nlinarith [hA, hS0, hH0]

end

end Work.FTS.EllipticEst.H2W.AngBW
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.slot11_fix.slot11_Acont_clean =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.slot11_fix

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **Glueing `Ioo`-regularity with the two endpoint values.**  If `f` is `C⁰` on `(0,π/2)`,
agrees there with a function `g` continuous on `[0,π/2]`, and has the same values as `g` at the two
endpoints, then `f` is continuous on `[0,π/2]`.

(Re-proved here: in the original file it is a local helper of `H2W/slot11_Acont.lean` whose import
cone is blocked.) -/
theorem continuousOn_Icc_of_eqOn_Ioo {f g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Icc 0 (Real.pi / 2)))
    (hf : ContinuousOn f (Set.Ioo 0 (Real.pi / 2)))
    (hEq : Set.EqOn f g (Set.Ioo 0 (Real.pi / 2)))
    (h0 : f 0 = g 0) (hpi : f (Real.pi / 2) = g (Real.pi / 2)) :
    ContinuousOn f (Set.Icc 0 (Real.pi / 2)) := by
  have hab : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hmem0 : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝[>] (0 : ℝ) := by
    rw [← nhdsWithin_Ioo_eq_nhdsGT hab]
    exact self_mem_nhdsWithin
  have hmempi : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝[<] (Real.pi / 2) := by
    rw [← nhdsWithin_Ioo_eq_nhdsLT hab]
    exact self_mem_nhdsWithin
  refine Work.H2W.continuousOn_Icc_of_limits hf ?_ ?_
  · have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝[Set.Icc 0 (Real.pi / 2)] (0 : ℝ) := by
      rw [← nhdsWithin_Ioo_eq_nhdsGT hab]
      exact nhdsWithin_mono 0 (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
    have hg0 : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 (g 0)) :=
      (hg.continuousWithinAt (Set.left_mem_Icc.mpr hab.le)).mono_left hle
    have hev : f =ᶠ[𝓝[>] (0 : ℝ)] g := Filter.eventually_of_mem hmem0 hEq
    have := Filter.Tendsto.congr' hev.symm hg0
    simpa only [h0] using this
  · have hle : 𝓝[<] (Real.pi / 2) ≤ 𝓝[Set.Icc 0 (Real.pi / 2)] (Real.pi / 2) := by
      rw [← nhdsWithin_Ioo_eq_nhdsLT hab]
      exact nhdsWithin_mono (Real.pi / 2) (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
    have hgpi : Tendsto g (𝓝[<] (Real.pi / 2)) (𝓝 (g (Real.pi / 2))) :=
      (hg.continuousWithinAt (Set.right_mem_Icc.mpr hab.le)).mono_left hle
    have hev : f =ᶠ[𝓝[<] (Real.pi / 2)] g := Filter.eventually_of_mem hmempi hEq
    have := Filter.Tendsto.congr' hev.symm hgpi
    simpa only [hpi] using this

/-- **Clean, buildable copy of `Work.FTS.EllipticEst.H2W.slot11_Acont`**
(`Submission/Work/FTS/EllipticEst/H2W/slot11_Acont.lean`, which cannot be built: its cone reaches
the stale `RPFresh/excess_finite` through `aSliceHonest`, and `ellHyp_L2Mem_*` through
`Fstar_DzIter_le_Psi`/`momentChainAe` — see
`Submission/Work/FTS/EllipticEst/H2W/NOTES_slot11_bound_BLOCKER.md`).  The same statement is also
`Work.H2W.weakSliceZContinuousAe` and `Work.H2W.weakSliceZContinuous` (a.e. form).

You are welcome to copy the proof from `slot11_Acont.lean` (30 KB, the assembly is
`exact ⟨hcontA, hDz2⟩`) — but *every* module you import must be one whose cone does not reach
`ellHyp_L2Mem_fields`, `ellHyp_L2Mem_pz_weighted`, `Tools/ellHyp_pz_honesty_fts`,
`Cert/HkMem_Gbar_sin`, `Cert/HkMem_Fstar_sin`, `RPFresh/excess_finite` or
`AgmonSlice/zsq_pzIter2_mixed_open` (that last one is broken only because
`Submission.Work.FTS.EllipticEst.propHk_fts` imports the *deleted* `TT/ESW/Pieces.lean`); where a
helper you need is trapped, re-prove it in this file.

Route (see `Submission/Work/H2W/weakSliceZContinuous.lean`'s header for the analysis):
* `slope(z) := lim_{θ→0⁺} (z²∂_z²Ψ)(z,θ)` equals `-[F_*(D_z²F)(z) + α²·F_*(D_z⁴Ψ)(z)]` for every
  `z > 0` (IBP with the adjoint kernel `sinθcos²θ`:
  `remov.SourceBound.sliceTendstoZeroOfMoment.auxMoment` / `sliceLzero1_moment`, plus
  `bslOp α (D_z^jΨ) = D_z^jF` and `z²∂_z² = D_z² - D_z`);
* both moments vanish for a.e. `z`: `F_*(D_z²F) = 0` a.e. is `H2W.Fstar_DzIter_two_F_ae` (clean),
  and `F_*(D_z⁴Ψ) = 0` a.e. is `H2W/FstarDzIterFourPsiAe.lean` (copy/adapt it: it is trapped only
  through its imports of `momentChainAe` / `aSliceHonest`);
* the *pointwise* version is NOT derivable from `EllWeakPos α 2` — keep the `∀ᵐ`;
* the second conjunct follows from the first plus `D_z²Ψ = z²∂_z²Ψ + D_zΨ` and
  `H2W.weakSliceContinuousKit` (clean), which gives the `D_zΨ`-slice continuity pointwise;
* the slice honesty needed to apply `weakSliceLimits` is the content of `H2W/aSliceHonest.lean`
  (equivalently `slot11_fix/slot11_Ahonest_clean` once that lands; re-derive it inline if it is not
  available yet).

## The proof actually written here

The whole analytic content is already available, `sorry`-free, in the clean twin tree
`Submission/Work/FTS/EllipticEst/H2W/Slot01W/` (which repoints every import of the blocked chain at
a currently buildable module — see `Slot01W/NOTES_slot01Weak.md`):

* the first conjunct is exactly `Work.H2W.aeSliceContASelf` (`Slot01W/ZTBound.lean`): it derives the
  `a.e.`-in-`z` vanishing of the `Lzero1`-moment of the `A`-slice `A := z²∂_z²Ψ` from the a.e.
  vanishing of `F_*(D_z²F)` and `F_*(D_z⁴Ψ)` (`Fstar_DzIter_two_F_ae`,
  `Slot01W.FstarDzIterFourAe`, `Lzero1A_moment_ae`) and then applies
  `remov.SourceBound.sliceTendstoZeroOfMoment` at `0⁺` and `H2W.weakSliceLimits` at `(π/2)⁻`;
* the second conjunct is `D_z²Ψ = D_zΨ + z²∂_z²Ψ` on the open interval: the `D_zΨ`-slice is
  continuous on `[0,π/2]` by `Work.H2W.weakSliceContinuousKit` (`Slot01W/SliceKit.lean`), the
  `A`-slice by the first conjunct, and the two endpoint values of `D_z²Ψ` are `0` (they are the
  `z`-derivatives of the identically vanishing slices `Ψ · 0`, `Ψ · (π/2)`).  The glueing of the
  `Ioo` identity with the endpoint values is the helper `continuousOn_Icc_of_eqOn_Ioo` above. -/
theorem slot11_Acont_clean : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z →
      ContinuousOn (fun θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (Set.Icc 0 (Real.pi / 2))
        ∧ ContinuousOn (fun θ => Work.Spaces.DzIter 2 Ψ z θ) (Set.Icc 0 (Real.pi / 2)) := by
  intro α F Ψ hα hα4 h
  -- the `A`-slice, a.e. in `z`
  filter_upwards [Work.H2W.aeSliceContASelf α F Ψ hα hα4 h] with z hA
  intro hz
  refine ⟨hA hz, ?_⟩
  -- the second conjunct: `D_z²Ψ = D_zΨ + z²∂_z²Ψ` on the open interval, endpoints `0`
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hdz : ContinuousOn (fun θ => Work.Spaces.Dz Ψ z θ) (Set.Icc 0 (Real.pi / 2)) :=
    (Work.H2W.weakSliceContinuousKit α F Ψ hα hα4 h z hz).2
  have hsum : ContinuousOn
      (fun θ => Work.Spaces.Dz Ψ z θ + z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      (Set.Icc 0 (Real.pi / 2)) := hdz.add (hA hz)
  refine continuousOn_Icc_of_eqOn_Ioo hsum ?_ ?_ ?_ ?_
  · exact ((hΨ.DzIter 2).curry_θ hz).continuousOn
  · -- the product rule `z²∂_z² = D_z² − D_z` on the open interval
    intro θ hθ
    have hh := Work.H2W.MomentAe.zsq_pzIter2_eq hΨ hz hθ
    linarith [hh]
  · -- left endpoint
    have hz1 : (fun z' : ℝ => Work.Spaces.DzIter 1 Ψ z' 0) = fun _ => (0 : ℝ) :=
      funext fun z' => Work.H2W.dz_zero_at_zero h z'
    have hDz2 : Work.Spaces.DzIter 2 Ψ z 0 = 0 := by
      show z * Work.Spaces.pz (Work.Spaces.DzIter 1 Ψ) z 0 = 0
      rw [show Work.Spaces.pz (Work.Spaces.DzIter 1 Ψ) z 0
          = deriv (fun z' : ℝ => Work.Spaces.DzIter 1 Ψ z' 0) z from rfl, hz1, deriv_const,
        mul_zero]
    rw [hDz2, Work.H2W.dz_zero_at_zero h z,
      Work.H2W.pzIter2_at_eq_zero h.zero z, mul_zero]
    ring
  · -- right endpoint
    have hz1 : (fun z' : ℝ => Work.Spaces.DzIter 1 Ψ z' (Real.pi / 2)) = fun _ => (0 : ℝ) :=
      funext fun z' => Work.H2W.dz_zero_at_pi_half h z'
    have hDz2 : Work.Spaces.DzIter 2 Ψ z (Real.pi / 2) = 0 := by
      show z * Work.Spaces.pz (Work.Spaces.DzIter 1 Ψ) z (Real.pi / 2) = 0
      rw [show Work.Spaces.pz (Work.Spaces.DzIter 1 Ψ) z (Real.pi / 2)
          = deriv (fun z' : ℝ => Work.Spaces.DzIter 1 Ψ z' (Real.pi / 2)) z from rfl, hz1,
        deriv_const, mul_zero]
    rw [hDz2, Work.H2W.dz_zero_at_pi_half h z,
      Work.H2W.pzIter2_at_eq_zero h.pi_half z, mul_zero]
    ring

end

end Work.FTS.EllipticEst.H2W.slot11_fix
end
-- ===== merged: Submission.Work.FTS.NonlinRows.Rl1.splitOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows.Rl1

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The open-quadrant slice API used by the split

The four elementary facts that the `SmoothQuad`-based split obtains from
`Work.FTS.Nonlinear.Pieces.differentiableAt_slice_z`/`_θ`/`pth_add_of_smoothQuad`/
`pz_add_of_smoothQuad`, in the (weaker) class `SmoothOpen` of the primed rows. -/

/-- The `z`-slice of a `SmoothOpen` function is differentiable at every `z > 0`, at every
`θ ∈ (0, π/2)`. -/
theorem openSlice_diffZ {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    DifferentiableAt ℝ (fun z' => f z' θ) z :=
  (hf.hasDerivAt_slice hθ hz).differentiableAt

/-- The `θ`-slice of a `SmoothOpen` function is differentiable at every `θ ∈ (0, π/2)`, at
every `z > 0`. -/
theorem openSlice_diffT {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    DifferentiableAt ℝ (fun θ' => f z θ') θ :=
  (((hf.curry_θ hz).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
    (isOpen_Ioo.mem_nhds hθ))

/-- `∂_θ` is additive on a sum of two `SmoothOpen` functions, on the open quadrant. -/
theorem openSlice_pth_add {f h : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hh : Work.FTS.EllipticEst.SmoothOpen h) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Work.Spaces.pth (fun z θ => f z θ + h z θ) z θ
      = Work.Spaces.pth f z θ + Work.Spaces.pth h z θ :=
  Work.FTS.Nonlinear.Pieces.pth_add_of_diff (openSlice_diffT hf hz hθ)
    (openSlice_diffT hh hz hθ)

/-- `∂_z` is additive on a sum of two `SmoothOpen` functions, on the open quadrant. -/
theorem openSlice_pz_add {f h : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hh : Work.FTS.EllipticEst.SmoothOpen h) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Work.Spaces.pz (fun z θ => f z θ + h z θ) z θ
      = Work.Spaces.pz f z θ + Work.Spaces.pz h z θ :=
  Work.FTS.Nonlinear.Pieces.pz_add_of_diff (openSlice_diffZ hf hz hθ)
    (openSlice_diffZ hh hz hθ)

theorem splitOpen {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hgs : Work.FTS.EllipticEst.SmoothOpen g) (hΦs : Work.FTS.EllipticEst.SmoothOpen Φs)
    (hΦg : Work.FTS.EllipticEst.SmoothOpen Φg)
    (hL : ∀ z : ℝ, 0 < z → Work.Construction.L12 (Work.Construction.Ftot α g) z
        = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 g z)
    (hFK : ∀ z : ℝ, 0 < z → Work.Construction.FK (Work.Construction.Ftot α g) z
        = Work.Construction.FK (Work.Construction.Fstar α) z + Work.Construction.FK g z)
    (hL12 : ∀ z : ℝ, 0 < z →
      DifferentiableAt ℝ (fun z' => Work.Construction.L12 g z') z) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.N α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) z θ
        = (Work.FTS.Nonlin.N1gg α g Φg z θ + Work.FTS.Nonlin.N1gs α g Φg z θ
            + Work.FTS.Nonlin.N1sg α Φs g z θ + Work.FTS.Nonlin.N1ss α Φs z θ)
          + (Work.FTS.Nonlin.N2gg α g Φg z θ + Work.FTS.Nonlin.N2gs α g Φg z θ
            + Work.FTS.Nonlin.N2sg α Φs g z θ + Work.FTS.Nonlin.N2ss α Φs z θ)
          + (Work.FTS.Nonlin.N3gg α g Φg z θ + Work.FTS.Nonlin.N3gs α g Φg z θ
            + Work.FTS.Nonlin.N3sg α Φs g z θ + Work.FTS.Nonlin.N3ss α Φs z θ)
          + (Work.FTS.Nonlin.N4gg α g z θ + Work.FTS.Nonlin.N4gs α g z θ
            + Work.FTS.Nonlin.N4sg α g z θ + Work.FTS.Nonlin.N4ss α z θ)
          + (Work.FTS.Nonlin.N5gg g z θ + Work.FTS.Nonlin.N5gs α g z θ
            + Work.FTS.Nonlin.N5sg α g z θ + Work.FTS.Nonlin.N5ss α z θ) := by
  intro z θ hq
  have hz : 0 < z := hq.1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := hq.2
  have hF : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  -- ## the identity of the straightened stream functions, near (in `z`) and at (in `θ`) the point
  have hsliceθ : (fun θ' => Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) z θ')
      = (fun θ' => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ'
          + Work.Construction.PhiTil α g Φg z θ') := by
    funext θ'
    simp only [Work.Construction.PhiTil, Work.Construction.Theta]
    rw [hL z hz]
    ring
  have hslicez : (fun z' => Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) z' θ)
      =ᶠ[𝓝 z] (fun z' => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z' θ
          + Work.Construction.PhiTil α g Φg z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hq.1] with z' hz'
    simp only [Work.Construction.PhiTil, Work.Construction.Theta]
    rw [hL z' hz']
    ring
  have hval : Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) z θ
      = Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
        + Work.Construction.PhiTil α g Φg z θ :=
    congrFun hsliceθ θ
  -- ## differentiability of the `z`- and `θ`-slices of the two pieces
  have hs2 : DifferentiableAt ℝ (fun θ' : ℝ => Work.Construction.s2 θ') θ := by
    have h : Work.Construction.s2 = fun θ' : ℝ => Real.sin (2 * θ') := rfl
    rw [h]
    exact Real.differentiableAt_sin.comp θ
      ((differentiableAt_const (2 : ℝ)).mul differentiableAt_id)
  have hPsi1 : Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs
      = fun z' θ' => Φs z' θ' - (1 / (4 * α)) * Work.Construction.s2 θ'
          * Work.Construction.L12 (Work.Construction.Fstar α) z' := rfl
  have hPsi2 : Work.Construction.PhiTil α g Φg
      = fun z' θ' => Φg z' θ' - (1 / (4 * α)) * Work.Construction.s2 θ'
          * Work.Construction.L12 g z' := rfl
  have hzs1 : DifferentiableAt ℝ
      (fun z' => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z' θ) z := by
    rw [hPsi1]
    exact (openSlice_diffZ hΦs hz hθ).sub
      ((differentiableAt_const (((1 : ℝ) / (4 * α)) * Work.Construction.s2 θ)).mul
        (Work.FTS.Nonlinear.Pieces.differentiableAt_L12_Fstar hα hα1 hz))
  have hzs2 : DifferentiableAt ℝ
      (fun z' => Work.Construction.PhiTil α g Φg z' θ) z := by
    rw [hPsi2]
    exact (openSlice_diffZ hΦg hz hθ).sub
      ((differentiableAt_const (((1 : ℝ) / (4 * α)) * Work.Construction.s2 θ)).mul
        (hL12 z hz))
  have hts1 : DifferentiableAt ℝ
      (fun θ' => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ') θ := by
    rw [hPsi1]
    exact (openSlice_diffT hΦs hz hθ).sub
      (((differentiableAt_const ((1 : ℝ) / (4 * α))).mul hs2).mul
        (differentiableAt_const _))
  have hts2 : DifferentiableAt ℝ
      (fun θ' => Work.Construction.PhiTil α g Φg z θ') θ := by
    rw [hPsi2]
    exact (openSlice_diffT hΦg hz hθ).sub
      (((differentiableAt_const ((1 : ℝ) / (4 * α))).mul hs2).mul
        (differentiableAt_const _))
  -- ## additivity of `∂_z` and `∂_θ` at the point
  have hpzP : Work.Spaces.pz (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ)) z θ
      = Work.Spaces.pz (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Spaces.pz (Work.Construction.PhiTil α g Φg) z θ := by
    have hderiv := hslicez.deriv_eq
    have hsum : Work.Spaces.pz (fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
          + Work.Construction.PhiTil α g Φg z θ) z θ
        = Work.Spaces.pz (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
          + Work.Spaces.pz (Work.Construction.PhiTil α g Φg) z θ :=
      Work.FTS.Nonlinear.Pieces.pz_add_of_diff hzs1 hzs2
    simp only [Work.Spaces.pz] at hsum hderiv ⊢
    exact hderiv.trans hsum
  have hpthP : Work.Spaces.pth (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ)) z θ
      = Work.Spaces.pth (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Spaces.pth (Work.Construction.PhiTil α g Φg) z θ := by
    have hderiv := congrArg (fun F : ℝ → ℝ => deriv F θ) hsliceθ
    have hsum : Work.Spaces.pth (fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
          + Work.Construction.PhiTil α g Φg z θ) z θ
        = Work.Spaces.pth (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
          + Work.Spaces.pth (Work.Construction.PhiTil α g Φg) z θ :=
      Work.FTS.Nonlinear.Pieces.pth_add_of_diff hts1 hts2
    simp only [Work.Spaces.pth] at hsum hderiv ⊢
    exact hderiv.trans hsum
  -- ## the additivity of the three operators
  have hRop : Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ)) z θ
      = Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Rop α (Work.Construction.PhiTil α g Φg) z θ := by
    simp only [Work.Construction.Rop]
    rw [hval, hpzP, hpthP]
    ring
  have hUop : Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ)) z θ
      = Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Uop α (Work.Construction.PhiTil α g Φg) z θ := by
    simp only [Work.Construction.Uop]
    rw [hval, hpzP]
    ring
  have hVop : Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ)) z θ
      = Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Vop (Work.Construction.PhiTil α g Φg) z θ := by
    simp only [Work.Construction.Vop]
    rw [hval, hpthP]
    ring
  -- ## additivity of `∂_θ` and `D_z` on `F = F_* + g`
  have hpthF : Work.Spaces.pth (Work.Construction.Ftot α g) z θ
      = Work.Spaces.pth (Work.Construction.Fstar α) z θ + Work.Spaces.pth g z θ :=
    openSlice_pth_add hF hgs hz hθ
  have hDzF : Work.Spaces.Dz (Work.Construction.Ftot α g) z θ
      = Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz g z θ :=
    Work.FTS.Nonlinear.Pieces.Dz_add_of_diff (openSlice_pz_add hF hgs hz hθ)
  -- ## the five groups
  have hN1 : Work.Construction.N1 α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) z θ
      = Work.FTS.Nonlin.N1gg α g Φg z θ + Work.FTS.Nonlin.N1gs α g Φg z θ
        + Work.FTS.Nonlin.N1sg α Φs g z θ + Work.FTS.Nonlin.N1ss α Φs z θ := by
    simp only [Work.Construction.N1, Work.FTS.Nonlin.N1gg, Work.FTS.Nonlin.N1gs,
      Work.FTS.Nonlin.N1sg, Work.FTS.Nonlin.N1ss, Work.FTS.Nonlin.PhiTg,
      Work.FTS.Nonlin.PhiTs, Work.Construction.Ftot]
    rw [hRop]
    ring
  have hN2 : Work.Construction.N2 α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) z θ
      = Work.FTS.Nonlin.N2gg α g Φg z θ + Work.FTS.Nonlin.N2gs α g Φg z θ
        + Work.FTS.Nonlin.N2sg α Φs g z θ + Work.FTS.Nonlin.N2ss α Φs z θ := by
    simp only [Work.Construction.N2, Work.FTS.Nonlin.N2gg, Work.FTS.Nonlin.N2gs,
      Work.FTS.Nonlin.N2sg, Work.FTS.Nonlin.N2ss, Work.FTS.Nonlin.PhiTg,
      Work.FTS.Nonlin.PhiTs]
    rw [hUop, hpthF]
    ring
  have hN3 : Work.Construction.N3 α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) z θ
      = Work.FTS.Nonlin.N3gg α g Φg z θ + Work.FTS.Nonlin.N3gs α g Φg z θ
        + Work.FTS.Nonlin.N3sg α Φs g z θ + Work.FTS.Nonlin.N3ss α Φs z θ := by
    simp only [Work.Construction.N3, Work.FTS.Nonlin.N3gg, Work.FTS.Nonlin.N3gs,
      Work.FTS.Nonlin.N3sg, Work.FTS.Nonlin.N3ss, Work.FTS.Nonlin.PhiTg,
      Work.FTS.Nonlin.PhiTs]
    rw [hVop, hDzF]
    ring
  have hN4 : Work.Construction.N4 α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) z θ
      = (Work.FTS.Nonlin.N4gg α g z θ + Work.FTS.Nonlin.N4gs α g z θ)
        + (Work.FTS.Nonlin.N4sg α g z θ + Work.FTS.Nonlin.N4ss α z θ) := by
    simp only [Work.Construction.N4, Work.FTS.Nonlin.N4gg, Work.FTS.Nonlin.N4gs,
      Work.FTS.Nonlin.N4sg, Work.FTS.Nonlin.N4ss, Work.Construction.Ftot]
    simp only [Work.FTS.Nonlinear.Pieces.Dth_eq_s2_mul]
    rw [hFK z hz, hpthF]
    ring
  have hN5 : Work.Construction.N5 α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) z θ
      = (Work.FTS.Nonlin.N5gg g z θ + Work.FTS.Nonlin.N5gs α g z θ)
        + (Work.FTS.Nonlin.N5sg α g z θ + Work.FTS.Nonlin.N5ss α z θ) := by
    simp only [Work.Construction.N5, Work.FTS.Nonlin.N5gg, Work.FTS.Nonlin.N5gs,
      Work.FTS.Nonlin.N5sg, Work.FTS.Nonlin.N5ss, Work.Construction.Ftot]
    rw [hFK z hz]
    ring
  rw [Work.Construction.N_eq_sum]
  simp only [Pi.add_apply, hN1, hN2, hN3, hN4, hN5]
  ring

end Work.FTS.NonlinRows.Rl1
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.Rl1.densNormCS =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.Rl1

/-! ## Cauchy–Schwarz for the `L₁₂` density

The a.e. domination `‖L₁₂dens h s‖ ≤ A s · B s` by a product of two nonnegative `L²((0,∞))`
functions gives the factorised `L¹`-bound
`∫₀^∞ ‖L₁₂dens h s‖ ≤ √(∫₀^∞ A²) · √(∫₀^∞ B²)`.

This is `Work.FTS.H2.CS1D` (one-dimensional Cauchy–Schwarz with the *unconditional*
integrability convention: when `‖L₁₂dens h‖` fails to be integrable, its integral is the junk
value `0` and the inequality is trivial) applied to the nonnegative function
`fun s => ‖L₁₂dens h s‖`, whose absolute value is itself.  The only point requiring care is
that the left-hand side of the goal is `∫ ‖…‖` and not `|∫ ‖…‖|`; they agree because
`∫ ‖…‖ ≥ 0` (`MeasureTheory.integral_nonneg`, no integrability needed). -/


end Work.FTS.Nonlinear.Pieces.Rl1
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.sgRowsPtwise =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.rl1Pieces

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-!
# The five `sg`-rows of `N`: the pointwise bound of the `rl¹`-integrand

`Work.FTS.Nonlinear.Pieces.rl1Pieces.Pgs` bounds the `rl¹`-norm of the five `gs`-pieces
`K θ · Nᵢ^{gs}`.  This file does the same for the four `sg`-pieces
`N₁^{sg}, N₂^{sg}, N₃^{sg}` (which carry the `Φ̃_*`-coefficient and the `g`-profile) and the
two pieces `N₄^{sg}, N₅^{sg}` of the `F_*`-block, but *pointwise*, in the form needed by the
`rl¹`-envelope: for `0 < α ≤ 1`, a `StarPkg` stream function `Φ_s` and every `r > 0`,
`θ ∈ Iθ`,

`|K θ · N₁^{sg}| ≤ 6 max Cs 0 α |g|`, `|K θ · N₂^{sg}| ≤ 24 max Cs 0 α |∂_θg|`,
`|K θ · N₃^{sg}| ≤ 6 max Cs 0 α² |D_zg|`,
`|K θ · N₄^{sg}| ≤ 3α (r/(1+r)²) |∂_θg|`, `|K θ · N₅^{sg}| ≤ 6α (r/(1+r)²) |g|`.

The three `Φ̃_*`-rows are the same pointwise input as in `Pgs`: `|ℛ(Φ̃_*)| ≤ max Cs 0·α` and
`|𝒱(Φ̃_*)| ≤ max Cs 0·α` (`rl1Tools.starPt`).  `𝒰(Φ̃_*)` is *not* directly bounded by
`StarPkg` (only `∂_θ𝒰` is), but the exact identity
`K θ · 𝒰(Ψ) = 3 cos³θ · (𝒱(Ψ) - ℛ(Ψ))` (`sg_K_mul_Uop_eq`, equivalent to
`𝒱 - ℛ = tan θ · 𝒰` times `K θ/ tan θ = 3cos³θ`) removes the `𝒰`-factor entirely, so the
`N₂^{sg}`-row costs only the factor `2·3·(1+1) = 12 ≤ 24`.  The `F_*`-rows use
`FK(F_*) = α·2z/(1+z)²` (`FstarPkg.FK_Fstar`) together with `|K θ| ≤ 3` and
`|sin| ≤ 1`.
-/

/-- `|K θ| ≤ 3` for every `θ`, where `K θ = 3 sin θ cos²θ`. -/
theorem sg_abs_K_le_three (θ : ℝ) : |Work.Spaces.K θ| ≤ 3 := by
  have hc2 : |Real.cos θ ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg (Real.cos θ))]
    exact Real.cos_sq_le_one θ
  have hs : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
  rw [Work.Spaces.K, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
  calc 3 * |Real.sin θ| * |Real.cos θ ^ 2| ≤ 3 * 1 * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hs (by norm_num)) hc2 (abs_nonneg _) (by norm_num)
    _ = 3 := by norm_num

/-- The product bound `|a · b| ≤ A · B` from `|a| ≤ A`, `|b| ≤ B` and `A ≥ 0`. -/
theorem sg_abs_mul_le {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hA : 0 ≤ A) :
    |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) hA

/-- **The `𝒰`-identity**: `K θ · 𝒰(Ψ) = 3 cos³θ · (𝒱(Ψ) - ℛ(Ψ))` whenever `cos θ ≠ 0`.

It is the product of `𝒱(Ψ) - ℛ(Ψ) = tan θ · 𝒰(Ψ)` (both sides are `-(sin θ/cos θ)·(3Ψ + αz∂_zΨ)`)
with `K θ / tan θ = 3 sin θ cos²θ · cos θ/sin θ = 3 cos³θ`; written as a polynomial identity
after multiplying by `cos θ`, so that no division by `sin θ` occurs. -/
theorem sg_K_mul_Uop_eq (α : ℝ) (Ψ : ℝ → ℝ → ℝ) {z θ : ℝ} (hc : Real.cos θ ≠ 0) :
    Work.Spaces.K θ * Work.Construction.Uop α Ψ z θ
      = 3 * Real.cos θ ^ 3 * (Work.Construction.Vop Ψ z θ
          - Work.Construction.Rop α Ψ z θ) := by
  simp only [Work.Spaces.K, Work.Construction.Uop, Work.Construction.Vop,
    Work.Construction.Rop, Real.tan_eq_sin_div_cos]
  field_simp
  ring

/-- **The `𝒰(Φ̃_*)`-row.**  `|K θ · 𝒰(Φ̃_*)| ≤ 6 max Cs 0 α` on `z > 0`, `θ ∈ Iθ`.

At `θ = π/2` both sides degenerate (`K (π/2) = 0`); otherwise `sg_K_mul_Uop_eq` turns the
left side into `3 cos³θ·|𝒱 - ℛ| ≤ 3·1·(max Cs 0 α + max Cs 0 α)`. -/
theorem sg_K_mul_Uop_bound {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) {z : ℝ} (hz : 0 < z) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.K θ * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ|
      ≤ 6 * max Cs 0 * α := by
  obtain ⟨hR, hV, -⟩ := Work.FTS.Nonlinear.Pieces.rl1Tools.starPt hα hs
  have hM : 0 ≤ max Cs 0 * α := mul_nonneg (le_max_right Cs 0) hα.le
  rcases eq_or_lt_of_le hθ.2 with hpi | hlt
  · rw [hpi, show Work.Spaces.K (Real.pi / 2) = 0 by
        simp [Work.Spaces.K, Real.cos_pi_div_two], zero_mul, abs_zero]
    linarith
  · have hcpos : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hlt⟩
    rw [sg_K_mul_Uop_eq α _ (ne_of_gt hcpos), abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
    have hc3 : |Real.cos θ ^ 3| ≤ 1 := by
      rw [abs_of_nonneg (pow_nonneg hcpos.le 3)]
      exact pow_le_one₀ hcpos.le (Real.cos_le_one θ)
    have h1 : |Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ| ≤ max Cs 0 * α :=
      hV z (le_of_lt hz) θ hθ
    have h2 : |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ| ≤ max Cs 0 * α :=
      hR z hz θ hθ
    have h3 : |Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ
        - Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ|
        ≤ max Cs 0 * α + max Cs 0 * α := by
      have h := abs_sub_le (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ) 0
        (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ)
      simp only [sub_zero, zero_sub, abs_neg] at h
      linarith
    calc 3 * |Real.cos θ ^ 3| * |Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ
          - Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ|
        ≤ 3 * 1 * (max Cs 0 * α + max Cs 0 * α) := by gcongr
      _ = 6 * max Cs 0 * α := by ring

/-- `|FK(F_*) r| = α · 2r/(1+r)²` for `r > 0` (`FstarPkg.FK_Fstar` plus `α·2r/(1+r)² ≥ 0`). -/
theorem sg_abs_FK_Fstar {α r : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hr : 0 < r) :
    |Work.Construction.FK (Work.Construction.Fstar α) r| = α * (2 * r / (1 + r) ^ 2) := by
  rw [Work.FTS.Nonlinear.FstarPkg.FK_Fstar hα hα1]
  exact abs_of_nonneg (by positivity)

theorem sgRowsPtwise {α Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {Φs g : Work.FTS.Galerkin.Fn}
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    (∀ r : ℝ, 0 < r → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.K θ * Work.FTS.Nonlin.N1sg α Φs g r θ| ≤ 6 * max Cs 0 * α * |g r θ|) ∧
    (∀ r : ℝ, 0 < r → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.K θ * Work.FTS.Nonlin.N2sg α Φs g r θ| ≤ 24 * max Cs 0 * α * |Work.Spaces.pth g r θ|) ∧
    (∀ r : ℝ, 0 < r → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.K θ * Work.FTS.Nonlin.N3sg α Φs g r θ| ≤ 6 * max Cs 0 * α ^ 2 * |Work.Spaces.Dz g r θ|) ∧
    (∀ r : ℝ, 0 < r → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.K θ * Work.FTS.Nonlin.N4sg α g r θ| ≤ 3 * α * (r / (1 + r) ^ 2) * |Work.Spaces.pth g r θ|) ∧
    (∀ r : ℝ, 0 < r → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.K θ * Work.FTS.Nonlin.N5sg α g r θ| ≤ 6 * α * (r / (1 + r) ^ 2) * |g r θ|) := by
  obtain ⟨hR, hV, -⟩ := Work.FTS.Nonlinear.Pieces.rl1Tools.starPt hα hs
  have hM : 0 ≤ max Cs 0 * α := mul_nonneg (le_max_right Cs 0) hα.le
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `N₁^{sg} = 2ℛ(Φ̃_*) g`
    intro r hr θ hθ
    have hK : |Work.Spaces.K θ| ≤ 3 := sg_abs_K_le_three θ
    have h1 : |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) r θ| ≤ max Cs 0 * α :=
      hR r hr θ hθ
    have hsplit : Work.Spaces.K θ * Work.FTS.Nonlin.N1sg α Φs g r θ
        = 2 * (Work.Spaces.K θ * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) r θ)
            * g r θ := by
      simp only [Work.FTS.Nonlin.N1sg]
      ring
    have h2 : |Work.Spaces.K θ * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) r θ|
        ≤ 3 * (max Cs 0 * α) := sg_abs_mul_le hK h1 (by norm_num)
    calc |Work.Spaces.K θ * Work.FTS.Nonlin.N1sg α Φs g r θ|
        = 2 * |Work.Spaces.K θ * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) r θ|
            * |g r θ| := by
          rw [hsplit, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ 2 * (3 * (max Cs 0 * α)) * |g r θ| := by gcongr
      _ = 6 * max Cs 0 * α * |g r θ| := by ring
  · -- `N₂^{sg} = -2𝒰(Φ̃_*) ∂_θg`
    intro r hr θ hθ
    have hU := sg_K_mul_Uop_bound hα hs hr hθ
    have hsplit : Work.Spaces.K θ * Work.FTS.Nonlin.N2sg α Φs g r θ
        = -(2 * (Work.Spaces.K θ * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ)
            * Work.Spaces.pth g r θ) := by
      simp only [Work.FTS.Nonlin.N2sg]
      ring
    calc |Work.Spaces.K θ * Work.FTS.Nonlin.N2sg α Φs g r θ|
        = 2 * |Work.Spaces.K θ * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ|
            * |Work.Spaces.pth g r θ| := by
          rw [hsplit, abs_neg, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ 2 * (6 * max Cs 0 * α) * |Work.Spaces.pth g r θ| := by gcongr
      _ ≤ 24 * max Cs 0 * α * |Work.Spaces.pth g r θ| := by
          nlinarith [hM, abs_nonneg (Work.Spaces.pth g r θ)]
  · -- `N₃^{sg} = -2α𝒱(Φ̃_*) D_zg`
    intro r hr θ hθ
    have hK : |Work.Spaces.K θ| ≤ 3 := sg_abs_K_le_three θ
    have h1 : |Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ| ≤ max Cs 0 * α :=
      hV r (le_of_lt hr) θ hθ
    have hsplit : Work.Spaces.K θ * Work.FTS.Nonlin.N3sg α Φs g r θ
        = -(2 * α * (Work.Spaces.K θ * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ)
            * Work.Spaces.Dz g r θ) := by
      simp only [Work.FTS.Nonlin.N3sg]
      ring
    have h2 : |Work.Spaces.K θ * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ|
        ≤ 3 * (max Cs 0 * α) := sg_abs_mul_le hK h1 (by norm_num)
    calc |Work.Spaces.K θ * Work.FTS.Nonlin.N3sg α Φs g r θ|
        = 2 * α * |Work.Spaces.K θ * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ|
            * |Work.Spaces.Dz g r θ| := by
          rw [hsplit, abs_neg, abs_mul, abs_mul,
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * α)]
      _ ≤ 2 * α * (3 * (max Cs 0 * α)) * |Work.Spaces.Dz g r θ| := by gcongr
      _ = 6 * max Cs 0 * α ^ 2 * |Work.Spaces.Dz g r θ| := by ring
  · -- `N₄^{sg} = -(1/2) FK(F_*) D_θg`
    intro r hr θ hθ
    have hK : |Work.Spaces.K θ| ≤ 3 := sg_abs_K_le_three θ
    have hFK : |Work.Construction.FK (Work.Construction.Fstar α) r|
        ≤ α * (2 * r / (1 + r) ^ 2) := le_of_eq (sg_abs_FK_Fstar hα hα1 hr)
    have hs2 : |Real.sin (2 * θ)| ≤ 1 := Real.abs_sin_le_one (2 * θ)
    calc |Work.Spaces.K θ * Work.FTS.Nonlin.N4sg α g r θ|
        = (1 / 2) * |Work.Spaces.K θ|
            * |Work.Construction.FK (Work.Construction.Fstar α) r|
            * (|Real.sin (2 * θ)| * |Work.Spaces.pth g r θ|) := by
          simp only [Work.FTS.Nonlin.N4sg, Work.Spaces.Dth, abs_mul, abs_neg,
            abs_of_nonneg (show (0 : ℝ) ≤ (1 / 2 : ℝ) by norm_num)]
          ring
      _ ≤ (1 / 2) * 3 * (α * (2 * r / (1 + r) ^ 2)) * (1 * |Work.Spaces.pth g r θ|) := by
          gcongr
      _ = 3 * α * (r / (1 + r) ^ 2) * |Work.Spaces.pth g r θ| := by ring
  · -- `N₅^{sg} = -sin²θ FK(F_*) g`
    intro r hr θ hθ
    have hK : |Work.Spaces.K θ| ≤ 3 := sg_abs_K_le_three θ
    have hFK : |Work.Construction.FK (Work.Construction.Fstar α) r|
        ≤ α * (2 * r / (1 + r) ^ 2) := le_of_eq (sg_abs_FK_Fstar hα hα1 hr)
    have hs2 : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
    calc |Work.Spaces.K θ * Work.FTS.Nonlin.N5sg α g r θ|
        = |Work.Spaces.K θ| * Real.sin θ ^ 2
            * |Work.Construction.FK (Work.Construction.Fstar α) r| * |g r θ| := by
          simp only [Work.FTS.Nonlin.N5sg, abs_mul, abs_neg,
            abs_of_nonneg (sq_nonneg (Real.sin θ))]
          ring
      _ ≤ 3 * 1 * (α * (2 * r / (1 + r) ^ 2)) * |g r θ| := by gcongr
      _ = 6 * α * (r / (1 + r) ^ 2) * |g r θ| := by ring

end

end Work.FTS.Nonlinear.Pieces.rl1Pieces
end
-- ===== merged: Submission.Work.FTS.OpenPkg.Pieces4 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The `N₀`-block (rows 1--7) -/








/-! ## The `N₁`-block (rows 8--11) -/





/-! ## The `N₂`-block (rows 12--15) -/





/-! ## The `N₃`-block (rows 16--19) -/





/-! ## The `N₄`-block (rows 20--23) -/





/-! ## The `N₅`-block (rows 24--26) -/





end Work.FTS.OpenPkg
end
end
