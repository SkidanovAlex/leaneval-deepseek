import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.EllipticEst.Core.sliceBoundaryLimit
import Submission.Work.FTS.EllipticEst.AngAWeak.aeGradTraceAe
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.GlueEnergy.integrableOn_sqrtSliceE_and_boundU_of_energy

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
