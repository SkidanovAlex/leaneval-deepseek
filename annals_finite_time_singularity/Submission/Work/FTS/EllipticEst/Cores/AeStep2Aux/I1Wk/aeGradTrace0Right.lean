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
# The `(π/2)⁻` trace of `z ∂_z u`, from the a.e. mixed honesty

`aeGradTraceRight_of_energy`: the mirror of `aeGradTrace0Left.aeGradTraceLeft_of_energy` at the
endpoint `(π/2)⁻`.
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

theorem aeGradTraceRight_of_energy (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (hAe : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hGae : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) Iθ)
    (hE : MeasureTheory.IntegrableOn (sliceE u) Iz) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ => z * Work.Spaces.pz u z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have hsm := Work.FTS.EllipticEst.H2W.Ae.AeData.smooth hAe
  have hS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  obtain ⟨K, hKpos, hraw⟩ := sliceBoundaryRightRaw
  have hθ1 : (1 : ℝ) ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by norm_num, by linarith [Real.pi_gt_three]⟩
  have hmemθ : ∀ n : ℕ, (Real.pi / 2 - 1 / ((n : ℝ) + 1)) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro n
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hden1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
    have hden0 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    have hsmall : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_iff₀ hden0]
      simpa using hden1
    refine ⟨?_, ?_⟩
    · linarith [Real.pi_gt_three, hsmall]
    · exact sub_lt_self _ (div_pos (by norm_num) hden0)
  have hθn : Filter.Tendsto (fun n : ℕ => Real.pi / 2 - 1 / ((n : ℝ) + 1)) Filter.atTop
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Filter.Eventually.of_forall fun n => ?_⟩
    · have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      simpa using tendsto_const_nhds.sub h
    · rw [Set.mem_Iio]
      exact sub_lt_self _ (div_pos (by norm_num) (by positivity))
  set c1 : ℝ → ℝ := fun s =>
    Filter.limsup (fun n : ℕ => s * Work.Spaces.pz u s (Real.pi / 2 - 1 / ((n : ℝ) + 1)))
    Filter.atTop with hc1def
  set f1 : ℝ → ℝ := fun s => c1 s / s with hf1def
  have hc1_apply : ∀ s : ℝ, c1 s =
      Filter.limsup (fun n : ℕ => s * Work.Spaces.pz u s (Real.pi / 2 - 1 / ((n : ℝ) + 1)))
      Filter.atTop := fun s => by simp only [hc1def]
  have hf1_apply : ∀ s : ℝ, f1 s = c1 s / s := fun s => by simp only [hf1def]
  -- ## Step 1: measurability of `c1`
  have hγaesm : ∀ n : ℕ, AEMeasurable
      (fun s : ℝ => s * Work.Spaces.pz u s (Real.pi / 2 - 1 / ((n : ℝ) + 1)))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    intro n
    exact ContinuousOn.aemeasurable
      (continuousOn_id.mul ((hS.pz).curry_z (hmemθ n)).continuousOn) measurableSet_Ioi
  have hc1aesm : AEMeasurable c1 (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    AEMeasurable.limsup hγaesm
  -- ## Step 2: the one-sided limit and the quadratic bound, on the honest set
  have hmain : ∀ s : ℝ,
      MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) s θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) Iθ → 0 < s →
      Filter.Tendsto (fun θ => Work.Spaces.Dz u s θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (c1 s)) ∧
        ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
          (Work.Spaces.Dz u s θ - c1 s) ^ 2
            ≤ K * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta) * sliceE u s := by
    intro s hEs hs
    obtain ⟨c, hc, hb⟩ := sliceBoundaryRight hS hs hKpos.le hraw hEs
    have hseq : Filter.Tendsto
        (fun n : ℕ => s * Work.Spaces.pz u s (Real.pi / 2 - 1 / ((n : ℝ) + 1)))
        Filter.atTop (nhds c) := by
      simpa only [Work.Spaces.Dz, Function.comp_def] using hc.comp hθn
    have hc1 : c1 s = c := by
      rw [hc1_apply s]
      exact Filter.Tendsto.limsup_eq hseq
    constructor
    · rw [hc1]; exact hc
    · intro θ hθ
      rw [hc1]
      exact hb θ hθ
  -- ## Step 3: the pointwise domination of `|∂_z u(s,θ)|`
  have hΦnn : ∀ s : ℝ, 0 ≤ sliceE u s := sliceE_nonneg u
  -- the reference angle `1` obeys `(π/2 - 1)^{1+η} ≤ 1`
  have href : ∀ s : ℝ, K * (Real.pi / 2 - 1) ^ (1 + Work.Spaces.eta) * sliceE u s
      ≤ K * sliceE u s := by
    intro s
    have h0 : (0 : ℝ) ≤ Real.pi / 2 - 1 := by linarith [Real.pi_gt_three]
    have h1 : Real.pi / 2 - 1 ≤ 1 := by linarith [Real.pi_lt_four]
    have hpow : (Real.pi / 2 - 1) ^ (1 + Work.Spaces.eta) ≤ 1 := by
      calc (Real.pi / 2 - 1) ^ (1 + Work.Spaces.eta)
          ≤ (1 : ℝ) ^ (1 + Work.Spaces.eta) :=
            Real.rpow_le_rpow h0 h1 (by norm_num [Work.Spaces.eta])
        _ = 1 := Real.one_rpow _
    calc K * (Real.pi / 2 - 1) ^ (1 + Work.Spaces.eta) * sliceE u s
        = K * ((Real.pi / 2 - 1) ^ (1 + Work.Spaces.eta) * sliceE u s) := by ring
      _ ≤ K * (1 * sliceE u s) := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hpow (hΦnn s)) hKpos.le
      _ = K * sliceE u s := by ring
  have hbd : ∀ s : ℝ,
      MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) s θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) Iθ → 0 < s →
      ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |Work.Spaces.pz u s θ| ≤ boundU u K s := by
    intro s hEs hs θ hθ
    have h1 : (Work.Spaces.Dz u s 1 - c1 s) ^ 2 ≤ K * sliceE u s :=
      le_trans ((hmain s hEs hs).2 1 hθ1) (href s)
    have h2 : (Work.Spaces.Dz u s θ - c1 s) ^ 2
        ≤ K * (Real.pi / 2) ^ (1 + Work.Spaces.eta) * sliceE u s := by
      refine le_trans ((hmain s hEs hs).2 θ hθ) ?_
      have hpow : (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)
          ≤ (Real.pi / 2) ^ (1 + Work.Spaces.eta) :=
        Real.rpow_le_rpow (by linarith [hθ.2]) (by linarith [hθ.1])
          (by norm_num [Work.Spaces.eta])
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hKpos.le) (hΦnn s)
    exact pz_le_of_slice_bounds hs hθ hKpos (hΦnn s) h1 h2
  -- ## Step 4: the integrability of `boundU` and `f1`
  have hboundint : ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (boundU u K) (Set.Icc a b) :=
    fun a b ha hab =>
      (Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.GlueEnergy.integrableOn_sqrtSliceE_and_boundU_of_energy
        hS hE hKpos ha hab).2
  have hfint : ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn f1 (Set.Icc a b) := by
    intro a b ha hab
    have hbnd := hboundint a b ha hab
    have hsub : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun s hs => lt_of_lt_of_le ha hs.1
    have hGsub : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Icc a b)),
        MeasureTheory.IntegrableOn
          (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) s θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) Iθ :=
      MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono_set volume hsub) hGae
    refine Integrable.mono' hbnd ?_ ?_
    · have h1 : AEMeasurable (fun s : ℝ => c1 s / s)
          (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
        hc1aesm.div (ContinuousOn.aemeasurable continuousOn_id measurableSet_Ioi)
      refine (h1.aestronglyMeasurable.mono_measure
        (MeasureTheory.Measure.restrict_mono hsub le_rfl)).congr ?_
      filter_upwards with s
      exact (hf1_apply s).symm
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc, hGsub]
        with s hs hsG
      have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
      have hΦ0 : 0 ≤ sliceE u s := hΦnn s
      have h1 : (Work.Spaces.Dz u s 1 - c1 s) ^ 2 ≤ K * sliceE u s :=
        le_trans ((hmain s hsG hs0).2 1 hθ1) (href s)
      have hKΦ : 0 ≤ K * sliceE u s := mul_nonneg hKpos.le hΦ0
      have hc1bd : |c1 s| ≤ |Work.Spaces.Dz u s 1| + Real.sqrt (K * sliceE u s) := by
        have h2abs : |Work.Spaces.Dz u s 1 - c1 s| ≤ Real.sqrt (K * sliceE u s) :=
          abs_le_of_sq_le_sq (by rw [Real.sq_sqrt hKΦ]; exact h1) (Real.sqrt_nonneg _)
        calc |c1 s| = |c1 s - Work.Spaces.Dz u s 1 + Work.Spaces.Dz u s 1| := by ring_nf
          _ ≤ |c1 s - Work.Spaces.Dz u s 1| + |Work.Spaces.Dz u s 1| := abs_add_le _ _
          _ = |Work.Spaces.Dz u s 1 - c1 s| + |Work.Spaces.Dz u s 1| := by rw [abs_sub_comm]
          _ ≤ Real.sqrt (K * sliceE u s) + |Work.Spaces.Dz u s 1| := by linarith
          _ = |Work.Spaces.Dz u s 1| + Real.sqrt (K * sliceE u s) := by ring
      have hDz1 : Work.Spaces.Dz u s 1 = s * Work.Spaces.pz u s 1 := rfl
      have hsqrtK : Real.sqrt (K * sliceE u s) = Real.sqrt K * Real.sqrt (sliceE u s) :=
        Real.sqrt_mul hKpos.le _
      have hMle : Real.sqrt K ≤ Real.sqrt K
          + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)) := by
        linarith [Real.sqrt_nonneg (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))]
      rw [hf1_apply s, Real.norm_eq_abs, abs_div, abs_of_pos hs0, boundU]
      have h4 : |c1 s| / s ≤ (|Work.Spaces.Dz u s 1|
          + (Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)))
            * Real.sqrt (sliceE u s)) / s := by
        refine div_le_div_of_nonneg_right ?_ hs0.le
        rw [hsqrtK] at hc1bd
        have := mul_le_mul_of_nonneg_right hMle (Real.sqrt_nonneg (sliceE u s))
        linarith [hc1bd, this]
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
  -- ## Step 5: the right trace of `u` vanishes identically
  have hglim : ∀ z : ℝ, 0 < z →
      Filter.Tendsto (fun θ => u z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
    fun z hz => (Work.FTS.EllipticEst.H2W.AeProof.AeSliceRightTendsto α u G hAe z hz).1
  -- ## Step 6: the integral relation `∫_a^b f1 = 0`
  have hrel : ∀ a b : ℝ, 0 < a → a < b → ∫ t in a..b, f1 t = 0 := by
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
        (fun n : ℕ => ∫ s in Set.Ioc a b,
          Work.Spaces.pz u s (Real.pi / 2 - 1 / ((n : ℝ) + 1)))
        Filter.atTop (nhds (∫ s in Set.Ioc a b, f1 s)) := by
      refine MeasureTheory.tendsto_integral_of_dominated_convergence
        (μ := MeasureTheory.volume.restrict (Set.Ioc a b))
        (F := fun n : ℕ => fun s : ℝ =>
          Work.Spaces.pz u s (Real.pi / 2 - 1 / ((n : ℝ) + 1)))
        (f := f1) (bound := boundU u K) ?_ hbndIoc ?_ ?_
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
            (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (c1 s)) :=
          (hmain s hsG hs0).1
        have h2 : Filter.Tendsto
            (fun n : ℕ => Work.Spaces.Dz u s (Real.pi / 2 - 1 / ((n : ℝ) + 1)))
            Filter.atTop (nhds (c1 s)) := h1.comp hθn
        have h3 : Filter.Tendsto (fun n : ℕ =>
            Work.Spaces.Dz u s (Real.pi / 2 - 1 / ((n : ℝ) + 1)) / s)
            Filter.atTop (nhds (c1 s / s)) := h2.div_const s
        have hfun : (fun n : ℕ => Work.Spaces.pz u s (Real.pi / 2 - 1 / ((n : ℝ) + 1)))
            = fun n : ℕ => Work.Spaces.Dz u s (Real.pi / 2 - 1 / ((n : ℝ) + 1)) / s := by
          funext n
          rw [Work.Spaces.Dz, mul_div_cancel_left₀ _ (ne_of_gt hs0)]
        rw [hfun, hf1_apply s]
        exact h3
    have hFTC : ∀ n : ℕ, u b (Real.pi / 2 - 1 / ((n : ℝ) + 1))
        - u a (Real.pi / 2 - 1 / ((n : ℝ) + 1))
        = ∫ s in Set.Ioc a b, Work.Spaces.pz u s (Real.pi / 2 - 1 / ((n : ℝ) + 1)) := by
      intro n
      have h := Work.FTS.EllipticEst.pzIter_slice_FTC_open hS 0 ha hab.le (hmemθ n)
      simpa only [Work.Spaces.pzIter_zero, Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero,
        intervalIntegral.integral_of_le hab.le] using h
    have hlimL : Filter.Tendsto
        (fun n : ℕ => u b (Real.pi / 2 - 1 / ((n : ℝ) + 1))
          - u a (Real.pi / 2 - 1 / ((n : ℝ) + 1)))
        Filter.atTop (nhds (0 - 0)) :=
      ((hglim b (ha.trans hab)).comp hθn).sub ((hglim a ha).comp hθn)
    have hEqIoc : (∫ s in Set.Ioc a b, f1 s) = 0 := by
      refine tendsto_nhds_unique
        (Filter.Tendsto.congr' (Filter.Eventually.of_forall fun n => (hFTC n).symm) hDCT) ?_
      simpa using hlimL
    rw [intervalIntegral.integral_of_le hab.le]
    exact hEqIoc
  -- ## Step 7: `f1` vanishes a.e.
  have hintI : ∀ a b : ℝ, 0 < a → a < b → IntervalIntegrable f1 MeasureTheory.volume a b := by
    intro a b ha hab
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab.le]
    exact hfint a b ha hab
  have hstep : ∀ n : ℕ, ∀ᵐ z ∂(MeasureTheory.volume.restrict
      (Set.Ioi (1 / ((n : ℝ) + 1)))), f1 z = 0 := by
    intro n
    have hz0 : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      exact div_pos (by norm_num) (by linarith)
    refine Work.FTS.EllipticEst.Mine.CutoffPieces.ae_zero_of_primitive_const
      (f := f1) (g := fun _ => (0 : ℝ)) (z₀ := 1 / ((n : ℝ) + 1)) hz0 ?_ ?_ ?_
    · intro a b ha hab
      exact hintI a b (lt_of_lt_of_le hz0 ha) hab
    · filter_upwards with z
      rfl
    · intro a b ha hab
      have h := hrel a b (lt_of_lt_of_le hz0 ha) hab
      simpa using h
  have hunion : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)), f1 z = 0 := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    show ∀ᵐ z ∂MeasureTheory.volume, 0 < z → f1 z = 0
    rw [MeasureTheory.ae_iff]
    show MeasureTheory.volume {z : ℝ | ¬(0 < z → f1 z = 0)} = 0
    have hbad : MeasureTheory.volume {z : ℝ | 0 < z ∧ f1 z ≠ 0} = 0 := by
      refine le_antisymm ?_ bot_le
      have hsub : {z : ℝ | 0 < z ∧ f1 z ≠ 0} ⊆ ⋃ n : ℕ,
          {z : ℝ | z ∈ Set.Ioi (1 / ((n : ℝ) + 1)) ∧ f1 z ≠ 0} := by
        intro z hz
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hz.1
        exact Set.mem_iUnion.mpr ⟨n, hn, hz.2⟩
      calc MeasureTheory.volume {z : ℝ | 0 < z ∧ f1 z ≠ 0}
          ≤ MeasureTheory.volume (⋃ n : ℕ,
              {z : ℝ | z ∈ Set.Ioi (1 / ((n : ℝ) + 1)) ∧ f1 z ≠ 0}) :=
            MeasureTheory.measure_mono hsub
        _ ≤ ∑' n : ℕ, MeasureTheory.volume
              {z : ℝ | z ∈ Set.Ioi (1 / ((n : ℝ) + 1)) ∧ f1 z ≠ 0} :=
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
  have hc1zero : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)), c1 z = 0 := by
    filter_upwards [hunion, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi]
      with z hz hzpos
    have hdiv : c1 z / z = 0 := by rw [← hf1_apply z]; exact hz
    rcases div_eq_zero_iff.mp hdiv with h0 | h0
    · exact h0
    · exact absurd h0 (ne_of_gt hzpos)
  filter_upwards [hc1zero, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi, hGae]
    with z hz hzpos hzG
  have h1 := (hmain z hzG hzpos).1
  rw [hz] at h1
  simpa only [Work.Spaces.Dz] using h1

end Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk
