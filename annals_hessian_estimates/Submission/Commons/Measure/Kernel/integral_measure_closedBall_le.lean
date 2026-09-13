import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Submission.Commons.Measure.Kernel.aemeasurable_toReal_measure_closedBall

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

open MeasureTheory Metric Set Filter Function
open scoped Topology ENNReal

namespace Commons.Measure.Kernel

/-- For a Haar measure `μ` on a finite dimensional real normed space, the measure of a closed
ball of positive radius `r` around any centre is the measure of the open ball of radius `r`
around the origin. -/
private lemma measure_closedBall_eq_measure_ball_haar {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (c : E) {r : ℝ} (hr : 0 < r) :
    μ (closedBall c r) = μ (ball (0 : E) r) := by
  rcases subsingleton_or_nontrivial E with hsub | hnt
  · haveI := hsub
    have h1 : closedBall c r = Set.univ := by
      ext x
      simp only [Set.mem_univ, iff_true, mem_closedBall]
      rw [Subsingleton.elim x c, dist_self]
      exact hr.le
    have h2 : ball (0 : E) r = Set.univ := by
      ext x
      simp only [Set.mem_univ, iff_true, mem_ball]
      rw [Subsingleton.elim x 0, dist_self]
      exact hr
    rw [h1, h2]
  · haveI := hnt
    rw [MeasureTheory.Measure.addHaar_closedBall_eq_addHaar_ball μ c r,
        MeasureTheory.Measure.addHaar_ball_center μ c r]

/-- Double-integral estimate in the "swapped" form needed for the kernel bound: integrating the
mass `μ (closedBall (x₀ + z) ε)` of a moving closed ball (`z` running through the open ball of
radius `s` around the origin) against the Lebesgue measure `volume` costs at most the volume of
the ball of radius `ε` times the total mass carried by `μ` on the ball of radius `s + ε` around
`x₀`. This is Tonelli's theorem together with the elementary observation that the fibre of the
map `(z, τ) ↦ (τ - x₀ - z)` over a point is contained in a ball of radius `ε`. -/
private lemma lintegral_ball_measure_closedBall_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [OpensMeasurableSpace (E × E)]
    (μ : Measure E) [IsFiniteMeasure μ]
    {x₀ : E} {s ε : ℝ} (hs : 0 < s) (hε : 0 < ε) :
    (∫⁻ z in ball (0 : E) s, μ (closedBall (x₀ + z) ε) ∂volume)
      ≤ volume (ball (0 : E) ε) * μ (closedBall x₀ (s + ε)) := by
  classical
  set Φ : E → E → ℝ≥0∞ := fun z τ =>
      ((ball (0 : E) s).indicator (fun _ => (1 : ℝ≥0∞)) z
        * (closedBall (x₀ + z) ε).indicator (fun _ => (1 : ℝ≥0∞)) τ) with hΦ
  set S : E → Set E := fun τ => {z | z ∈ ball (0 : E) s ∧ τ ∈ closedBall (x₀ + z) ε} with hS
  -- measurability of the "indicator part" of `Φ`
  have hTmeas : MeasurableSet {p : E × E | p.2 ∈ closedBall (x₀ + p.1) ε} := by
    have hcl : IsClosed {p : E × E | dist p.2 (x₀ + p.1) ≤ ε} :=
      isClosed_le (continuous_snd.dist (continuous_const.add continuous_fst)) continuous_const
    have hset : {p : E × E | p.2 ∈ closedBall (x₀ + p.1) ε}
        = {p : E × E | dist p.2 (x₀ + p.1) ≤ ε} := by
      ext p; simp only [Metric.mem_closedBall]
    rw [hset]
    exact hcl.measurableSet
  have hc_meas : Measurable (fun p : E × E =>
      (ball (0 : E) s).indicator (fun _ => (1 : ℝ≥0∞)) p.1
        * (closedBall (x₀ + p.1) ε).indicator (fun _ => (1 : ℝ≥0∞)) p.2) := by
    apply Measurable.mul
    · exact (measurable_const.indicator measurableSet_ball).comp measurable_fst
    · have hB : (fun p : E × E => (closedBall (x₀ + p.1) ε).indicator (fun _ => (1 : ℝ≥0∞)) p.2)
          = ({p : E × E | p.2 ∈ closedBall (x₀ + p.1) ε}).indicator (fun _ => (1 : ℝ≥0∞)) := by
        funext p
        simp only [Set.indicator_apply, Metric.mem_closedBall, Set.mem_ofPred_eq]
      rw [hB]
      exact measurable_const.indicator hTmeas
  have hΦ_ae : AEMeasurable (Function.uncurry Φ) (volume.prod μ) := by
    rw [hΦ]
    show AEMeasurable (fun p : E × E =>
        ((ball (0 : E) s).indicator (fun _ => (1 : ℝ≥0∞)) p.1
          * (closedBall (x₀ + p.1) ε).indicator (fun _ => (1 : ℝ≥0∞)) p.2)) (volume.prod μ)
    exact hc_meas.aemeasurable
  -- measurability of the fibres `S τ`
  have hSmeas : ∀ τ, MeasurableSet (S τ) := by
    intro τ
    have h2 : MeasurableSet {z : E | τ ∈ closedBall (x₀ + z) ε} := by
      have hcl : IsClosed {z : E | dist τ (x₀ + z) ≤ ε} :=
        isClosed_le ((continuous_const : Continuous fun _ : E => τ).dist
          (continuous_const.add continuous_id)) (continuous_const : Continuous fun _ : E => ε)
      have hset : {z : E | τ ∈ closedBall (x₀ + z) ε} = {z : E | dist τ (x₀ + z) ≤ ε} := by
        ext z; simp only [Metric.mem_closedBall]
      rw [hset]
      exact hcl.measurableSet
    have h : S τ = ball (0 : E) s ∩ {z : E | τ ∈ closedBall (x₀ + z) ε} := by
      rw [hS]
      ext z; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    rw [h]
    exact measurableSet_ball.inter h2
  -- Step A: rewrite the set integral as the double integral of `Φ`
  have hA : (∫⁻ z in ball (0 : E) s, μ (closedBall (x₀ + z) ε) ∂volume)
      = ∫⁻ z, ∫⁻ τ, Φ z τ ∂μ ∂volume := by
    rw [← lintegral_indicator (μ := volume) measurableSet_ball]
    apply lintegral_congr
    intro z
    by_cases hz : z ∈ ball (0 : E) s
    · rw [Set.indicator_of_mem hz, ← setLIntegral_one, ← lintegral_indicator (μ := μ) measurableSet_closedBall]
      apply lintegral_congr
      intro τ
      simp only [hΦ]
      rw [Set.indicator_of_mem hz]
      by_cases hτ : τ ∈ closedBall (x₀ + z) ε
      · rw [Set.indicator_of_mem hτ]; simp
      · rw [Set.indicator_of_notMem hτ]; simp
    · rw [Set.indicator_of_notMem hz]
      simp only [hΦ]
      simp [Set.indicator_of_notMem hz]
  -- Step B: Tonelli's theorem
  have hBswap : (∫⁻ z, ∫⁻ τ, Φ z τ ∂μ ∂volume) = ∫⁻ τ, ∫⁻ z, Φ z τ ∂volume ∂μ :=
    lintegral_lintegral_swap (μ := volume) (ν := μ) hΦ_ae
  -- Step C: the inner integral in the swapped order
  have hC : ∀ τ, ∫⁻ z, Φ z τ ∂volume = volume (S τ) := by
    intro τ
    have hstep : ∫⁻ z, Φ z τ ∂volume
        = ∫⁻ z, (S τ).indicator (fun _ => (1 : ℝ≥0∞)) z ∂volume := by
      apply lintegral_congr
      intro z
      simp only [hΦ]
      by_cases hz : z ∈ ball (0 : E) s
      · by_cases hτ : τ ∈ closedBall (x₀ + z) ε
        · have hzS : z ∈ S τ := by rw [hS]; exact ⟨hz, hτ⟩
          rw [Set.indicator_of_mem hz, Set.indicator_of_mem hτ, Set.indicator_of_mem hzS]
          simp
        · have hzS : z ∉ S τ := by rw [hS]; exact fun h => hτ h.2
          rw [Set.indicator_of_mem hz, Set.indicator_of_notMem hτ, Set.indicator_of_notMem hzS]
          simp
      · have hzS : z ∉ S τ := by rw [hS]; exact fun h => hz h.1
        rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hzS]
        simp
    rw [hstep]
    have hindone : ∫⁻ a, (S τ).indicator (fun _ => (1 : ℝ≥0∞)) a ∂volume = volume (S τ) := by
      rw [lintegral_indicator (μ := volume) (hSmeas τ) (fun _ => (1 : ℝ≥0∞))]
      simpa using setLIntegral_one (μ := volume) (S τ)
    exact hindone
  -- the fibres are contained in a ball of radius `ε`
  have hSsub : ∀ τ, S τ ⊆ closedBall (τ - x₀) ε := by
    intro τ z hz
    rw [hS] at hz
    obtain ⟨hz1, hz2⟩ := hz
    rw [Metric.mem_closedBall] at hz2 ⊢
    calc dist z (τ - x₀) = dist τ (x₀ + z) := by
          rw [← dist_add_right z (τ - x₀) x₀, sub_add_cancel, add_comm z x₀, dist_comm]
       _ ≤ ε := hz2
  have hSbound : ∀ τ, volume (S τ) ≤ volume (ball (0 : E) ε) := by
    intro τ
    calc volume (S τ) ≤ volume (closedBall (τ - x₀) ε) := measure_mono (hSsub τ)
      _ = volume (closedBall (0 : E) ε) := MeasureTheory.Measure.addHaar_closedBall_center volume (τ - x₀) ε
      _ = volume (ball (0 : E) ε) := measure_closedBall_eq_measure_ball_haar volume 0 hε
  -- Step D: pointwise bound
  have hD : ∀ τ, volume (S τ) ≤ volume (ball (0 : E) ε)
      * ((closedBall x₀ (s + ε)).indicator (fun _ => (1 : ℝ≥0∞)) τ) := by
    intro τ
    by_cases hτ : τ ∈ closedBall x₀ (s + ε)
    · rw [Set.indicator_of_mem hτ, mul_one]
      exact hSbound τ
    · have hempty : S τ = ∅ := by
        by_contra hne
        obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hne
        rw [hS] at hz
        obtain ⟨hz1, hz2⟩ := hz
        have h1 : dist τ (x₀ + z) ≤ ε := Metric.mem_closedBall.mp hz2
        have hd0 : dist (x₀ + z) x₀ = dist z 0 := by
          rw [add_comm x₀ z]
          simpa using dist_add_right z 0 x₀
        have h2 : dist (x₀ + z) x₀ < s := by
          rw [hd0]; exact Metric.mem_ball.mp hz1
        have h3 : dist τ x₀ < s + ε := by
          calc dist τ x₀ ≤ dist τ (x₀ + z) + dist (x₀ + z) x₀ := dist_triangle _ _ _
            _ < ε + s := add_lt_add_of_le_of_lt h1 h2
            _ = s + ε := add_comm _ _
        exact hτ (Metric.mem_closedBall.mpr h3.le)
      simp [hempty, Set.indicator_of_notMem hτ]
  calc (∫⁻ z in ball (0 : E) s, μ (closedBall (x₀ + z) ε) ∂volume)
      = ∫⁻ z, ∫⁻ τ, Φ z τ ∂μ ∂volume := hA
    _ = ∫⁻ τ, ∫⁻ z, Φ z τ ∂volume ∂μ := hBswap
    _ = ∫⁻ τ, volume (S τ) ∂μ := by
        apply lintegral_congr; intro τ; exact hC τ
    _ ≤ ∫⁻ τ, volume (ball (0 : E) ε)
          * ((closedBall x₀ (s + ε)).indicator (fun _ => (1 : ℝ≥0∞)) τ) ∂μ :=
        lintegral_mono fun τ => hD τ
    _ = volume (ball (0 : E) ε)
          * ∫⁻ τ, (closedBall x₀ (s + ε)).indicator (fun _ => (1 : ℝ≥0∞)) τ ∂μ := by
        rw [lintegral_const_mul'']
        exact (measurable_const.indicator measurableSet_closedBall).aemeasurable
    _ = volume (ball (0 : E) ε) * μ (closedBall x₀ (s + ε)) := by
        congr 1
        rw [lintegral_indicator (μ := μ) measurableSet_closedBall (fun _ => (1 : ℝ≥0∞))]
        rw [setLIntegral_one]

open MeasureTheory Metric Set Filter Function in
open scoped Topology ENNReal in
theorem integral_measure_closedBall_le {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsFiniteMeasure μ]
    {x₀ : EuclideanSpace ℝ (Fin n)} {s ε : ℝ} (hs : 0 < s) (hε : 0 < ε) :
    (∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s,
        (μ (Metric.closedBall (x₀ + z) ε)).toReal)
      ≤ (volume : Measure (EuclideanSpace ℝ (Fin n))).real
            (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε)
          * (μ (Metric.closedBall x₀ (s + ε))).toReal := by
  have hbound := lintegral_ball_measure_closedBall_le (E := EuclideanSpace ℝ (Fin n))
    (μ := μ) (x₀ := x₀) hs hε
  have hLL : (∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s,
        (μ (Metric.closedBall (x₀ + z) ε)).toReal)
      = (∫⁻ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s,
          μ (Metric.closedBall (x₀ + z) ε) ∂volume).toReal := by
    have hF_meas : AEMeasurable (fun z : EuclideanSpace ℝ (Fin n) =>
        μ (Metric.closedBall (x₀ + z) ε))
        (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s)) := by
      have h₁ : Measurable fun x : EuclideanSpace ℝ (Fin n) => μ (Metric.closedBall x ε) :=
        measurable_measure_closedBall μ ε
      have h₂ : Measurable fun z : EuclideanSpace ℝ (Fin n) => x₀ + z := by fun_prop
      exact (h₁.comp h₂).aemeasurable
    have hF_lt : ∀ᵐ z ∂(volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s)),
        μ (Metric.closedBall (x₀ + z) ε) < ∞ :=
      Filter.Eventually.of_forall fun z => measure_lt_top μ _
    exact integral_toReal hF_meas hF_lt
  rw [hLL]
  have hfin : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε)
      * μ (Metric.closedBall x₀ (s + ε)) ≠ ∞ :=
    ENNReal.mul_ne_top (ne_of_lt measure_ball_lt_top) (measure_ne_top μ _)
  calc (∫⁻ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s,
          μ (Metric.closedBall (x₀ + z) ε) ∂volume).toReal
      ≤ (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε)
          * μ (Metric.closedBall x₀ (s + ε))).toReal := ENNReal.toReal_mono hfin hbound
    _ = (volume : Measure (EuclideanSpace ℝ (Fin n))).real
            (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε)
          * (μ (Metric.closedBall x₀ (s + ε))).toReal := by
        rw [ENNReal.toReal_mul, measureReal_def]

end Commons.Measure.Kernel