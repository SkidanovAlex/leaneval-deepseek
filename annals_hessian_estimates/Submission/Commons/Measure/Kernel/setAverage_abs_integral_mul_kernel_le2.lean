import Mathlib
import Submission.Commons.Measure.EuclideanSpace.volume_ball_ratio

open MeasureTheory Metric Set Filter Function
open scoped Topology ENNReal RealInnerProductSpace InnerProductSpace Convolution Pointwise

namespace Commons.Measure.Kernel

/-- Volume of a sphere is zero for the Lebesgue measure. -/
theorem volume_sphere_eq_zero {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : r ≠ 0) :
    volume (Metric.sphere x r) = 0 :=
  Measure.addHaar_sphere_of_ne_zero volume x hr

/-- Open and closed balls of the same nonzero radius have the same Lebesgue volume. -/
theorem volume_closedBall_eq_volume_ball {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) {r : ℝ}
    (hr : r ≠ 0) : volume (Metric.closedBall x r) = volume (Metric.ball x r) := by
  rw [← Metric.ball_union_sphere,
    MeasureTheory.measure_union Metric.sphere_disjoint_ball.symm isClosed_sphere.measurableSet,
    volume_sphere_eq_zero x hr, add_zero]

/-- Translating a closed ball does not change its Lebesgue volume. -/
theorem volume_closedBall_vadd {n : ℕ} (a : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    volume (Metric.closedBall a r) = volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r) := by
  rw [show Metric.closedBall a r = a +ᵥ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r from by
    rw [Metric.vadd_closedBall]; simp]
  exact measure_vadd volume a _

/-- Pointwise bound for the kernel integral. -/
theorem abs_integral_kernel_le {n : ℕ}
    {k f : EuclideanSpace ℝ (Fin n) → ℝ} {x₀ z : EuclideanSpace ℝ (Fin n)} {ε C : ℝ}
    (hk : ∀ t, 0 ≤ k t) (hC : ∀ t, k t ≤ C) (hC0 : 0 ≤ C)
    (hks : ∀ t, k t ≠ 0 → t ∈ Metric.closedBall 0 ε)
    (hf : LocallyIntegrable f volume) :
    |∫ τ, k (x₀ + z - τ) * f τ| ≤ C * ∫ τ in Metric.closedBall (x₀ + z) ε, |f τ| := by
  have hsupp : ∀ y, |k y| ≤ C * (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) ε).indicator (fun _ => (1:ℝ)) y := by
    intro y
    rw [abs_of_nonneg (hk y)]
    by_cases hy : y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) ε
    · rw [Set.indicator_of_mem hy, mul_one]; exact hC y
    · rw [Set.indicator_of_notMem hy, mul_zero]
      have hz : k y = 0 := by
        by_contra h
        exact hy (hks y h)
      rw [hz]
  have hmemeq : ∀ τ : EuclideanSpace ℝ (Fin n),
      (x₀ + z - τ ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) ε) ↔ (τ ∈ Metric.closedBall (x₀ + z) ε) := by
    intro τ
    simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_sub_rev]
  have hint : Integrable (fun τ => C * (Metric.closedBall (x₀ + z) ε).indicator (fun τ => |f τ|) τ) volume := by
    have habs : Integrable (fun τ : EuclideanSpace ℝ (Fin n) => |f τ|) (volume.restrict (Metric.closedBall (x₀ + z) ε)) := by
      have hc : IntegrableOn f (Metric.closedBall (x₀ + z) ε) volume :=
        hf.integrableOn_isCompact (isCompact_closedBall _ _)
      simpa only [Real.norm_eq_abs] using hc.abs
    have h1 : Integrable ((Metric.closedBall (x₀ + z) ε).indicator (fun τ : EuclideanSpace ℝ (Fin n) => |f τ|)) volume :=
      (integrable_indicator_iff measurableSet_closedBall).2 habs
    exact h1.const_mul C
  calc |∫ τ, k (x₀ + z - τ) * f τ|
      ≤ ∫ τ, |k (x₀ + z - τ) * f τ| := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun τ => k (x₀ + z - τ) * f τ)
    _ = ∫ τ, |k (x₀ + z - τ)| * |f τ| := by
        congr 1; ext τ; rw [abs_mul]
    _ ≤ ∫ τ, C * (Metric.closedBall (x₀ + z) ε).indicator (fun τ => |f τ|) τ := by
        apply integral_mono_of_nonneg
        · filter_upwards with τ; positivity
        · exact hint
        · filter_upwards with τ
          have h := hsupp (x₀ + z - τ)
          by_cases hmem : x₀ + z - τ ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) ε
          · have hmem' : τ ∈ Metric.closedBall (x₀ + z) ε := (hmemeq τ).1 hmem
            rw [Set.indicator_of_mem hmem, mul_one] at h
            rw [Set.indicator_of_mem hmem']
            exact mul_le_mul_of_nonneg_right h (abs_nonneg _)
          · have hmem' : τ ∉ Metric.closedBall (x₀ + z) ε := fun hc => hmem ((hmemeq τ).2 hc)
            rw [Set.indicator_of_notMem hmem, mul_zero] at h
            rw [Set.indicator_of_notMem hmem', mul_zero]
            rw [show |k (x₀ + z - τ)| = 0 from le_antisymm h (abs_nonneg _), zero_mul]
    _ = C * ∫ τ in Metric.closedBall (x₀ + z) ε, |f τ| := by
        rw [MeasureTheory.integral_const_mul,
            MeasureTheory.integral_indicator measurableSet_closedBall]

/-- The function `z ↦ ∫⁻ τ in closedBall (x₀+z) ε, ofReal |f τ|` is a.e. measurable. -/
theorem aemeasurable_lintegral_closedBall {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x₀ : EuclideanSpace ℝ (Fin n)} {ε : ℝ}
    (hf : LocallyIntegrable f volume) :
    AEMeasurable (fun z : EuclideanSpace ℝ (Fin n) =>
      ∫⁻ τ in Metric.closedBall (x₀ + z) ε, ENNReal.ofReal (|f τ|)) volume := by
  have hcont : Continuous (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      p.2 - (x₀ + p.1)) := continuous_snd.sub (continuous_const.add continuous_fst)
  have hTmeas : MeasurableSet {p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
      p.2 ∈ Metric.closedBall (x₀ + p.1) ε} := by
    have hcl : IsClosed ((fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        p.2 - (x₀ + p.1)) ⁻¹' Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) ε) :=
      isClosed_closedBall.preimage hcont
    convert hcl.measurableSet using 1
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm,
      dist_zero_right, sub_zero]
  have hh : AEMeasurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (|f p.2|)) (volume.prod volume) :=
    ((hf.aestronglyMeasurable.aemeasurable.abs).comp_snd).ennreal_ofReal
  have hg : AEMeasurable ({p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
      p.2 ∈ Metric.closedBall (x₀ + p.1) ε}.indicator
      (fun p => ENNReal.ofReal (|f p.2|))) (volume.prod volume) :=
    hh.indicator hTmeas
  refine (hg.lintegral_prod_right').congr (Eventually.of_forall ?_)
  intro z
  show (∫⁻ y, {p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) | p.2 ∈ Metric.closedBall (x₀ + p.1) ε}.indicator (fun p => ENNReal.ofReal (|f p.2|)) (z, y)) = (∫⁻ τ in Metric.closedBall (x₀ + z) ε, ENNReal.ofReal (|f τ|))
  rw [← MeasureTheory.lintegral_indicator (s := Metric.closedBall (x₀ + z) ε)
    (measurableSet_closedBall)]
  apply lintegral_congr
  intro y
  classical
  rw [Set.indicator_apply, Set.indicator_apply]
  by_cases hy : y ∈ Metric.closedBall (x₀ + z) ε
  · rw [if_pos hy, if_pos (show (z, y) ∈ {p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) | p.2 ∈ Metric.closedBall (x₀ + p.1) ε} from hy)]
  · rw [if_neg hy, if_neg (show (z, y) ∉ {p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) | p.2 ∈ Metric.closedBall (x₀ + p.1) ε} from hy)]

theorem setLIntegral_setLIntegral_closedBall_le {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x₀ : EuclideanSpace ℝ (Fin n)} {s ε : ℝ}
    (hs : 0 < s) (hε : 0 < ε) (hf : LocallyIntegrable f volume) :
    (∫⁻ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s,
        ∫⁻ τ in Metric.closedBall (x₀ + z) ε, ENNReal.ofReal (|f τ|))
      ≤ volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε)
          * (∫⁻ τ in Metric.closedBall x₀ (s + ε), ENNReal.ofReal (|f τ|)) := by
  classical
  have hεne : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε) ≠ ∞ :=
    measure_ball_lt_top.ne
  have hTmeas : MeasurableSet {p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
      p.1 ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s ∧
      p.2 ∈ Metric.closedBall (x₀ + p.1) ε} := by
    rw [Set.ofPred_and]
    refine MeasurableSet.inter ?_ ?_
    · exact Metric.isOpen_ball.measurableSet.preimage measurable_fst
    · have hcont : Continuous (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          p.2 - (x₀ + p.1)) := continuous_snd.sub (continuous_const.add continuous_fst)
      have hcl : IsClosed ((fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          p.2 - (x₀ + p.1)) ⁻¹' Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) ε) :=
        isClosed_closedBall.preimage hcont
      convert hcl.measurableSet using 1
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm,
        dist_zero_right, sub_zero]
  have hh : AEMeasurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (|f p.2|)) (volume.prod volume) :=
    ((hf.aestronglyMeasurable.aemeasurable.abs).comp_snd).ennreal_ofReal
  have hGmeas : AEMeasurable (Function.uncurry (fun z τ : EuclideanSpace ℝ (Fin n) =>
      ({p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
          p.1 ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s ∧
          p.2 ∈ Metric.closedBall (x₀ + p.1) ε}.indicator
          (fun p => ENNReal.ofReal (|f p.2|))) (z, τ))) (volume.prod volume) :=
    hh.indicator hTmeas
  have hLHS : (∫⁻ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s,
        ∫⁻ τ in Metric.closedBall (x₀ + z) ε, ENNReal.ofReal (|f τ|))
      = ∫⁻ z, ∫⁻ τ, ({p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
          p.1 ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s ∧
          p.2 ∈ Metric.closedBall (x₀ + p.1) ε}.indicator
          (fun p => ENNReal.ofReal (|f p.2|))) (z, τ) := by
    rw [← MeasureTheory.lintegral_indicator (s := Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s)
      (Metric.isOpen_ball.measurableSet)]
    apply lintegral_congr
    intro z
    classical
    by_cases hz : z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s
    · rw [Set.indicator_of_mem hz,
        ← MeasureTheory.lintegral_indicator (s := Metric.closedBall (x₀ + z) ε)
          (measurableSet_closedBall)]
      apply lintegral_congr
      intro τ
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases hτ : τ ∈ Metric.closedBall (x₀ + z) ε
      · rw [if_pos hτ, if_pos (show (z, τ) ∈ {p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
            p.1 ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s ∧
            p.2 ∈ Metric.closedBall (x₀ + p.1) ε} from ⟨hz, hτ⟩)]
      · rw [if_neg hτ, if_neg (show (z, τ) ∉ {p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
            p.1 ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s ∧
            p.2 ∈ Metric.closedBall (x₀ + p.1) ε} from fun h => hτ h.2)]
    · rw [Set.indicator_of_notMem hz]
      have h0 : (∫⁻ τ, ({p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
            p.1 ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s ∧
            p.2 ∈ Metric.closedBall (x₀ + p.1) ε}.indicator
            (fun p => ENNReal.ofReal (|f p.2|))) (z, τ)) = 0 := by
        rw [show (0 : ℝ≥0∞) = ∫⁻ _τ : EuclideanSpace ℝ (Fin n), (0 : ℝ≥0∞) from by simp]
        apply lintegral_congr
        intro τ
        rw [Set.indicator_of_notMem]
        intro hmem; exact hz hmem.1
      rw [h0]
  rw [hLHS, MeasureTheory.lintegral_lintegral_swap hGmeas]
  have hinner : ∀ τ : EuclideanSpace ℝ (Fin n),
      (∫⁻ z, ({p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
          p.1 ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s ∧
          p.2 ∈ Metric.closedBall (x₀ + p.1) ε}.indicator
          (fun p => ENNReal.ofReal (|f p.2|))) (z, τ))
      = ENNReal.ofReal (|f τ|) *
          volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s ∩
            Metric.closedBall (τ - x₀) ε) := by
    intro τ
    have hS : {z : EuclideanSpace ℝ (Fin n) |
        z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s ∧ τ ∈ Metric.closedBall (x₀ + z) ε}
        = Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s ∩ Metric.closedBall (τ - x₀) ε := by
      ext z
      rw [Set.mem_ofPred_eq, Set.mem_inter_iff]
      constructor
      · rintro ⟨hz, hτ⟩
        refine ⟨hz, ?_⟩
        have h : τ - (x₀ + z) = -(z - (τ - x₀)) := by abel
        rw [Metric.mem_closedBall, dist_eq_norm] at hτ ⊢
        rwa [h, norm_neg] at hτ
      · rintro ⟨hz, hτ⟩
        refine ⟨hz, ?_⟩
        have h : τ - (x₀ + z) = -(z - (τ - x₀)) := by abel
        rw [Metric.mem_closedBall, dist_eq_norm] at hτ ⊢
        rwa [h, norm_neg]
    have : (∫⁻ z, ({p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
          p.1 ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s ∧
          p.2 ∈ Metric.closedBall (x₀ + p.1) ε}.indicator
          (fun p => ENNReal.ofReal (|f p.2|))) (z, τ))
        = ∫⁻ z, ENNReal.ofReal (|f τ|) *
            ({z : EuclideanSpace ℝ (Fin n) |
              z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s ∧
              τ ∈ Metric.closedBall (x₀ + z) ε}.indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞)) z := by
      apply lintegral_congr
      intro z
      by_cases hz : z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s ∧
          τ ∈ Metric.closedBall (x₀ + z) ε
      · rw [Set.indicator_of_mem (show (z, τ) ∈ {p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
            p.1 ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s ∧ p.2 ∈ Metric.closedBall (x₀ + p.1) ε} from hz),
            Set.indicator_of_mem (show z ∈ {z : EuclideanSpace ℝ (Fin n) |
            z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s ∧ τ ∈ Metric.closedBall (x₀ + z) ε} from hz)]
        try simp
      · rw [Set.indicator_of_notMem (show (z, τ) ∉ {p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
            p.1 ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s ∧ p.2 ∈ Metric.closedBall (x₀ + p.1) ε} from hz),
            Set.indicator_of_notMem (show z ∉ {z : EuclideanSpace ℝ (Fin n) |
            z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s ∧ τ ∈ Metric.closedBall (x₀ + z) ε} from hz)]
        try simp
    rw [this, hS]
    rw [MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (|f τ|))
      ((Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s ∩ Metric.closedBall (τ - x₀) ε).indicator
        (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞)) (by simp)]
    congr 1
    exact MeasureTheory.lintegral_indicator_one (measurableSet_ball.inter measurableSet_closedBall)
  have hpt : ∀ τ : EuclideanSpace ℝ (Fin n),
      ENNReal.ofReal (|f τ|) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s ∩
            Metric.closedBall (τ - x₀) ε)
      ≤ ENNReal.ofReal (|f τ|) * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε) *
          (Metric.closedBall x₀ (s + ε)).indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) τ) := by
    intro τ
    by_cases hτ : τ ∈ Metric.closedBall x₀ (s + ε)
    · rw [Set.indicator_of_mem hτ, Pi.one_apply, mul_one]
      exact mul_le_mul_of_nonneg_left
        (calc volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s ∩ Metric.closedBall (τ - x₀) ε)
            ≤ volume (Metric.closedBall (τ - x₀) ε) := measure_mono Set.inter_subset_right
          _ = volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) ε) := volume_closedBall_vadd (τ - x₀) ε
          _ = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε) := volume_closedBall_eq_volume_ball 0 hε.ne')
        (by positivity)
    · rw [Set.indicator_of_notMem hτ, mul_zero, mul_zero]
      rw [show Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s ∩ Metric.closedBall (τ - x₀) ε = ∅ from ?_,
        measure_empty, mul_zero]
      rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨hz, hzτ⟩
      apply hτ
      have hz' : ‖z‖ < s := by rwa [Metric.mem_ball, dist_zero_right] at hz
      have hzτ' : ‖z - (τ - x₀)‖ ≤ ε := by
        rw [Metric.mem_closedBall, dist_eq_norm] at hzτ; exact hzτ
      rw [Metric.mem_closedBall]
      have h1 : ‖τ - x₀ - z‖ ≤ ε := by
        rw [show τ - x₀ - z = -(z - (τ - x₀)) by abel, norm_neg]; exact hzτ'
      have h2 : ‖τ - x₀‖ ≤ ‖τ - x₀ - z‖ + ‖z‖ := by
        calc ‖τ - x₀‖ = ‖(τ - x₀ - z) + z‖ := congrArg (fun w => ‖w‖)
              (show τ - x₀ = (τ - x₀ - z) + z by abel)
          _ ≤ ‖τ - x₀ - z‖ + ‖z‖ := norm_add_le _ _
      rw [dist_eq_norm]
      linarith
  calc ∫⁻ τ, ∫⁻ z, ({p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
          p.1 ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s ∧
          p.2 ∈ Metric.closedBall (x₀ + p.1) ε}.indicator
          (fun p => ENNReal.ofReal (|f p.2|))) (z, τ)
      = ∫⁻ τ, ENNReal.ofReal (|f τ|) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s ∩
            Metric.closedBall (τ - x₀) ε) := by
        apply lintegral_congr; exact hinner
    _ ≤ ∫⁻ τ, ENNReal.ofReal (|f τ|) * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε) *
          (Metric.closedBall x₀ (s + ε)).indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) τ) := lintegral_mono hpt
    _ = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε) *
          (∫⁻ τ in Metric.closedBall x₀ (s + ε), ENNReal.ofReal (|f τ|)) := by
        rw [show (∫⁻ τ, ENNReal.ofReal (|f τ|) * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε) *
              (Metric.closedBall x₀ (s + ε)).indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) τ))
            = ∫⁻ τ, volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε) *
              (ENNReal.ofReal (|f τ|) * (Metric.closedBall x₀ (s + ε)).indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) τ) from by
          apply lintegral_congr; intro τ; ring]
        rw [MeasureTheory.lintegral_const_mul' (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε))
          (fun τ => ENNReal.ofReal (|f τ|) * (Metric.closedBall x₀ (s + ε)).indicator
            (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) τ) hεne]
        congr 1
        rw [← MeasureTheory.lintegral_indicator (s := Metric.closedBall x₀ (s + ε)) measurableSet_closedBall]
        apply lintegral_congr
        intro τ
        by_cases hτ : τ ∈ Metric.closedBall x₀ (s + ε)
        · rw [Set.indicator_of_mem hτ, Set.indicator_of_mem hτ, Pi.one_apply, mul_one]
        · rw [Set.indicator_of_notMem hτ, Set.indicator_of_notMem hτ, mul_zero]

/-- Open and closed balls of the same nonzero radius agree a.e. -/
theorem ae_eq_ball_closedBall {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : r ≠ 0) :
    Metric.ball x r =ᵐ[volume] Metric.closedBall x r := by
  rw [MeasureTheory.ae_eq_set]
  constructor
  · exact measure_mono_null (fun y hy => hy.2 (Metric.ball_subset_closedBall hy.1)) measure_empty
  · rw [show Metric.closedBall x r \ Metric.ball x r = Metric.sphere x r from ?_, volume_sphere_eq_zero x hr]
    ext y
    rw [Set.mem_sdiff, Metric.mem_sphere, Metric.mem_closedBall, Metric.mem_ball, dist_comm]
    constructor
    · rintro ⟨hcb, hnb⟩
      exact le_antisymm hcb (le_of_not_gt hnb)
    · intro hsp
      exact ⟨le_of_eq hsp, by rw [hsp]; exact lt_irrefl _⟩

/-- Scalar volume-ratio estimate. -/
theorem volume_ball_ratio_mul_pow_le {n : ℕ} {s ε : ℝ} (hε : 0 < ε) (hs : 0 < s) (hse : ε ≤ s) :
    (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε)).toReal * (s + ε) ^ n
      ≤ (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s)).toReal * (2 ^ n * ε ^ n) := by
  have hVb : (0:ℝ) < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin n)) hs).ne' measure_ball_lt_top.ne
  have hr := Commons.Measure.EuclideanSpace.volume_ball_ratio (n := n)
    (x₀ := (0:EuclideanSpace ℝ (Fin n))) (y := (0:EuclideanSpace ℝ (Fin n))) (r := s) (s := ε) hs hε
  have hVε : (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε)).toReal
      = (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s)).toReal * (ε / s) ^ n := by
    rw [div_eq_iff hVb.ne'] at hr
    rw [hr, mul_comm]
  have hle : (ε / s) ^ n * (s + ε) ^ n ≤ 2 ^ n * ε ^ n := by
    have h2 : (ε / s) * (s + ε) ≤ 2 * ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hs]
      nlinarith [hse]
    have h3 : (0:ℝ) ≤ (ε / s) * (s + ε) := by positivity
    calc (ε / s) ^ n * (s + ε) ^ n = ((ε / s) * (s + ε)) ^ n := by rw [mul_pow]
      _ ≤ (2 * ε) ^ n := pow_le_pow_left₀ h3 h2 n
      _ = 2 ^ n * ε ^ n := by rw [mul_pow]
  calc (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε)).toReal * (s + ε) ^ n
      = (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s)).toReal * (ε / s) ^ n * (s + ε) ^ n := by
        rw [hVε]
    _ = (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s)).toReal *
          ((ε / s) ^ n * (s + ε) ^ n) := by ring
    _ ≤ (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s)).toReal * (2 ^ n * ε ^ n) :=
        mul_le_mul_of_nonneg_left hle hVb.le

open MeasureTheory Metric Set Filter Function in
open scoped Topology ENNReal RealInnerProductSpace InnerProductSpace Convolution in
theorem setAverage_abs_integral_mul_kernel_le2 {n : ℕ}
    {k f : EuclideanSpace ℝ (Fin n) → ℝ} {x₀ : EuclideanSpace ℝ (Fin n)} {ε C R E₀ : ℝ}
    (hk : ∀ t, 0 ≤ k t) (hC : ∀ t, k t ≤ C) (hC0 : 0 ≤ C)
    (hε : 0 < ε) (hR : 0 < R) (hεR : ε ≤ R)
    (hks : ∀ t, k t ≠ 0 → t ∈ Metric.closedBall 0 ε)
    (hf : LocallyIntegrable f volume) (hE0 : 0 ≤ E₀)
    (hE : ∀ s' ∈ Set.Ioc (0:ℝ) R,
        (∫ w in Metric.ball x₀ s', |f w|) ≤ E₀ * s' ^ n)
    {s : ℝ} (hs : 0 < s) (hRs : s + ε ≤ R) :
    (⨍ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s,
        |∫ τ, k (x₀ + z - τ) * f τ|) ≤ 2 ^ n * C * E₀ * ε ^ n := by
  classical
  set B : Set (EuclideanSpace ℝ (Fin n)) := Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s with hB
  have hBmeas : MeasurableSet B := by rw [hB]; exact Metric.isOpen_ball.measurableSet
  have hBfin : volume B ≠ ∞ := by
    rw [hB]
    exact (lt_of_le_of_lt (measure_mono Metric.ball_subset_closedBall)
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) s).measure_lt_top).ne
  have hBfin_ball : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s) ≠ ∞ := by
    rw [← hB]; exact hBfin
  have hBpos : 0 < volume.real B := by
    rw [Measure.real_def, hB]
    exact ENNReal.toReal_pos (measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin n)) hs).ne' hBfin_ball
  -- geometric subset: for z in B, the support ball lies inside the large ball
  have hsubset : ∀ z ∈ B, Metric.closedBall (x₀ + z) ε ⊆ Metric.ball x₀ (s + ε) := by
    intro z hz τ hτ
    have hz' : z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s := by rwa [hB] at hz
    have hz2 : ‖z‖ < s := by rwa [Metric.mem_ball, dist_zero_right] at hz'
    rw [Metric.mem_closedBall, dist_eq_norm] at hτ
    rw [Metric.mem_ball, dist_eq_norm]
    have hτ' : ‖τ - x₀ - z‖ ≤ ε := by
      rwa [show τ - (x₀ + z) = τ - x₀ - z by abel] at hτ
    have h2 : ‖τ - x₀‖ ≤ ‖τ - x₀ - z‖ + ‖z‖ := by
      calc ‖τ - x₀‖ = ‖(τ - x₀ - z) + z‖ := congrArg (fun w => ‖w‖) (by abel)
        _ ≤ ‖τ - x₀ - z‖ + ‖z‖ := norm_add_le _ _
    linarith
  have hintball : IntegrableOn (fun τ => |f τ|) (Metric.ball x₀ (s + ε)) volume := by
    have hc : Integrable (fun τ : EuclideanSpace ℝ (Fin n) => |f τ|)
        (volume.restrict (Metric.closedBall x₀ (s + ε))) := by
      simpa only [Real.norm_eq_abs] using
        (hf.integrableOn_isCompact (isCompact_closedBall x₀ (s + ε))).abs
    exact IntegrableOn.mono_set hc Metric.ball_subset_closedBall
  have hKle : ∀ z ∈ B, (∫ τ in Metric.closedBall (x₀ + z) ε, |f τ|) ≤ E₀ * (s + ε) ^ n := by
    intro z hz
    calc ∫ τ in Metric.closedBall (x₀ + z) ε, |f τ|
        ≤ ∫ τ in Metric.ball x₀ (s + ε), |f τ| :=
          setIntegral_mono_set hintball (Filter.Eventually.of_forall (fun τ => abs_nonneg _))
            (Filter.Eventually.of_forall (fun τ hτ => hsubset z hz hτ))
      _ ≤ E₀ * (s + ε) ^ n := hE (s + ε) ⟨by linarith, hRs⟩
  rw [MeasureTheory.setAverage_eq, smul_eq_mul, inv_mul_le_iff₀ hBpos]
  by_cases hsε : s ≤ ε
  · have hbnd : ∀ z ∈ B, |∫ τ, k (x₀ + z - τ) * f τ| ≤ 2 ^ n * C * E₀ * ε ^ n := by
      intro z hz
      have hstep : |∫ τ, k (x₀ + z - τ) * f τ| ≤ C * (E₀ * (s + ε) ^ n) := by
        refine (abs_integral_kernel_le (k := k) (f := f) (x₀ := x₀) (z := z) (ε := ε) (C := C)
          hk hC hC0 hks hf).trans ?_
        exact mul_le_mul_of_nonneg_left (hKle z hz) hC0
      have h2 : (s + ε) ^ n ≤ (2 * ε) ^ n :=
        pow_le_pow_left₀ (by linarith) (by linarith) n
      calc |∫ τ, k (x₀ + z - τ) * f τ| ≤ C * (E₀ * (s + ε) ^ n) := hstep
        _ ≤ C * (E₀ * (2 * ε) ^ n) := by
            apply mul_le_mul_of_nonneg_left _ hC0
            exact mul_le_mul_of_nonneg_left h2 hE0
        _ = 2 ^ n * C * E₀ * ε ^ n := by rw [mul_pow]; ring
    calc ∫ z in B, |∫ τ, k (x₀ + z - τ) * f τ|
        ≤ ∫ z in B, (2 ^ n * C * E₀ * ε ^ n) := by
          apply integral_mono_of_nonneg
          · filter_upwards with z; exact abs_nonneg _
          · exact Measure.integrableOn_of_bounded hBfin aestronglyMeasurable_const
              (M := ‖2 ^ n * C * E₀ * ε ^ n‖) (Filter.Eventually.of_forall (fun z => le_refl _))
          · filter_upwards [MeasureTheory.ae_restrict_mem hBmeas] with z hz; exact hbnd z hz
      _ = (2 ^ n * C * E₀ * ε ^ n) * volume.real B := by
          rw [integral_const, MeasureTheory.measureReal_restrict_apply_univ, smul_eq_mul, mul_comm]
      _ = volume.real B * (2 ^ n * C * E₀ * ε ^ n) := by ring
  · push_neg at hsε
    have hKbnd : ∀ z, |∫ τ, k (x₀ + z - τ) * f τ| ≤
        C * (∫ τ in Metric.closedBall (x₀ + z) ε, |f τ|) :=
      fun z => abs_integral_kernel_le (k := k) (f := f) (x₀ := x₀) (z := z) (ε := ε) (C := C)
        hk hC hC0 hks hf
    have hKae : AEMeasurable (fun z : EuclideanSpace ℝ (Fin n) =>
        ∫ τ in Metric.closedBall (x₀ + z) ε, |f τ|) volume := by
      refine (aemeasurable_lintegral_closedBall (f := f) (x₀ := x₀) (ε := ε) hf).ennreal_toReal.congr
        (Eventually.of_forall (fun z => ?_))
      show (∫⁻ τ in Metric.closedBall (x₀ + z) ε, ENNReal.ofReal (|f τ|)).toReal
        = ∫ τ in Metric.closedBall (x₀ + z) ε, |f τ|
      have habs : Integrable (fun τ : EuclideanSpace ℝ (Fin n) => |f τ|)
          (volume.restrict (Metric.closedBall (x₀ + z) ε)) := by
        simpa only [Real.norm_eq_abs] using
          (hf.integrableOn_isCompact (isCompact_closedBall (x₀ + z) ε)).abs
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal habs
          (Eventually.of_forall (fun τ => abs_nonneg _)),
        ENNReal.toReal_ofReal (integral_nonneg (fun τ => abs_nonneg _))]
    have hK_int : Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
        ∫ τ in Metric.closedBall (x₀ + z) ε, |f τ|) (volume.restrict B) :=
      Measure.integrableOn_of_bounded hBfin hKae.aestronglyMeasurable (M := E₀ * (s + ε) ^ n)
        (by filter_upwards [MeasureTheory.ae_restrict_mem hBmeas] with z hz
            rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun τ => abs_nonneg _))]
            exact hKle z hz)
    have hKint : ∫ z in B, (∫ τ in Metric.closedBall (x₀ + z) ε, |f τ|) ≤
        (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε)).toReal * (E₀ * (s + ε) ^ n) := by
      have hεne : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε) ≠ ∞ :=
        measure_ball_lt_top.ne
      have hof : ENNReal.ofReal (∫ z in B, (∫ τ in Metric.closedBall (x₀ + z) ε, |f τ|))
          = ∫⁻ z in B, (∫⁻ τ in Metric.closedBall (x₀ + z) ε, ENNReal.ofReal (|f τ|)) := by
        rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hK_int
          (Eventually.of_forall (fun z => integral_nonneg (fun τ => abs_nonneg _)))]
        apply lintegral_congr
        intro z
        have habs : Integrable (fun τ : EuclideanSpace ℝ (Fin n) => |f τ|)
            (volume.restrict (Metric.closedBall (x₀ + z) ε)) := by
          simpa only [Real.norm_eq_abs] using
            (hf.integrableOn_isCompact (isCompact_closedBall (x₀ + z) ε)).abs
        exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal habs
          (Eventually.of_forall (fun τ => abs_nonneg _))
      have hbound : ∫⁻ z in B, (∫⁻ τ in Metric.closedBall (x₀ + z) ε, ENNReal.ofReal (|f τ|))
          ≤ ENNReal.ofReal ((volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε)).toReal *
              (E₀ * (s + ε) ^ n)) := by
        calc ∫⁻ z in B, (∫⁻ τ in Metric.closedBall (x₀ + z) ε, ENNReal.ofReal (|f τ|))
            ≤ volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε) *
                (∫⁻ τ in Metric.closedBall x₀ (s + ε), ENNReal.ofReal (|f τ|)) :=
              setLIntegral_setLIntegral_closedBall_le hs hε hf
          _ = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε) *
                ENNReal.ofReal (∫ τ in Metric.ball x₀ (s + ε), |f τ|) := by
              congr 1
              rw [← Measure.restrict_congr_set (ae_eq_ball_closedBall x₀ (by linarith : s + ε ≠ 0))]
              have habs : Integrable (fun τ : EuclideanSpace ℝ (Fin n) => |f τ|)
                  (volume.restrict (Metric.ball x₀ (s + ε))) := hintball
              exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal habs
                (Eventually.of_forall (fun τ => abs_nonneg _))).symm
          _ ≤ volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε) *
                ENNReal.ofReal (E₀ * (s + ε) ^ n) := by
              apply mul_le_mul_of_nonneg_left _ zero_le
              exact ENNReal.ofReal_le_ofReal (hE (s + ε) ⟨by linarith, hRs⟩)
          _ = ENNReal.ofReal ((volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε)).toReal *
                (E₀ * (s + ε) ^ n)) := by
              rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε)).toReal),
                ENNReal.ofReal_toReal hεne]
      have hle : ENNReal.ofReal (∫ z in B, (∫ τ in Metric.closedBall (x₀ + z) ε, |f τ|))
          ≤ ENNReal.ofReal ((volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε)).toReal *
              (E₀ * (s + ε) ^ n)) := by
        rw [hof]; exact hbound
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle
    have hVratio : (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε)).toReal * (s + ε) ^ n
        ≤ volume.real B * (2 ^ n * ε ^ n) := by
      exact volume_ball_ratio_mul_pow_le (n := n) hε hs (le_of_lt hsε)
    calc ∫ z in B, |∫ τ, k (x₀ + z - τ) * f τ|
        ≤ C * ∫ z in B, (∫ τ in Metric.closedBall (x₀ + z) ε, |f τ|) := by
          rw [← MeasureTheory.integral_const_mul]
          apply integral_mono_of_nonneg
          · filter_upwards with z; exact abs_nonneg _
          · exact hK_int.const_mul C
          · filter_upwards with z; exact hKbnd z
      _ ≤ C * ((volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε)).toReal * (E₀ * (s + ε) ^ n)) :=
          mul_le_mul_of_nonneg_left hKint hC0
      _ ≤ volume.real B * (2 ^ n * C * E₀ * ε ^ n) := by
          calc C * ((volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε)).toReal * (E₀ * (s + ε) ^ n))
              = C * E₀ * ((volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε)).toReal * (s + ε) ^ n) := by ring
            _ ≤ C * E₀ * (volume.real B * (2 ^ n * ε ^ n)) :=
                mul_le_mul_of_nonneg_left hVratio (by positivity)
            _ = volume.real B * (2 ^ n * C * E₀ * ε ^ n) := by ring

end Commons.Measure.Kernel
