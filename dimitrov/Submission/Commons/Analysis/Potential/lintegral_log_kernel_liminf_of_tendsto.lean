import Mathlib

namespace Commons.Analysis.Potential

open MeasureTheory Filter
open scoped ENNReal Topology

set_option linter.unusedVariables false

/-- Portmanteau / Fatou inequality for lower semicontinuous nonnegative functions.

If `μ` is a measure and `μs` a sequence of measures such that the measure of every open set
under `μ` is at most the liminf of its measures under `μs`, then the same inequality holds for
the lower Lebesgue integral of `ENNReal.ofReal f` for every lower semicontinuous `f ≥ 0`.

The proof is a layer-cake argument: for `t > 0` the superlevel set `{f > t}` is open, and
Fatou's lemma (in the form `lintegral_liminf_le`) controls the liminf of the integrals. -/
theorem lintegral_ofReal_le_liminf_of_lsc {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    [OpensMeasurableSpace Ω] {μ : Measure Ω} {μs : ℕ → Measure Ω}
    (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i => μs i G))
    {f : Ω → ℝ} (hf_nn : 0 ≤ f) (hf_lsc : LowerSemicontinuous f) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ
      ≤ atTop.liminf (fun i => ∫⁻ x, ENNReal.ofReal (f x) ∂(μs i)) := by
  have hkey : ∀ ν : Measure Ω, ∫⁻ x, ENNReal.ofReal (f x) ∂ν
      = ∫⁻ t in Set.Ioi (0:ℝ), ν {a | t < f a} :=
    fun ν => lintegral_eq_lintegral_meas_lt ν (Filter.Eventually.of_forall hf_nn)
      hf_lsc.measurable.aemeasurable
  rw [hkey μ]
  simp_rw [hkey]
  calc ∫⁻ t in Set.Ioi (0:ℝ), μ {a | t < f a}
      ≤ ∫⁻ t in Set.Ioi (0:ℝ), atTop.liminf (fun i => (μs i) {a | t < f a}) :=
        lintegral_mono (fun t => h_opens _ (hf_lsc.isOpen_preimage t))
    _ ≤ atTop.liminf (fun i => ∫⁻ t in Set.Ioi (0:ℝ), (μs i) {a | t < f a}) :=
        lintegral_liminf_le (fun n => Antitone.measurable
          (fun s t hst => measure_mono (fun ω hω => lt_of_le_of_lt hst hω)))

theorem lintegral_log_kernel_liminf_of_tendsto {K : Set ℂ} (hK : IsCompact K) {D : ℝ} (hD : 0 < D)
    (hDiam : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ D)
    (μ : MeasureTheory.ProbabilityMeasure K) (νn : ℕ → MeasureTheory.ProbabilityMeasure K)
    (hconv : Filter.Tendsto νn Filter.atTop (nhds μ))
    (hsmall : ∀ n (x : K), (νn n) {x} ≤ ((n : ENNReal) + 1)⁻¹) :
    MeasureTheory.lintegral (μ.prod μ)
        (fun z : K × K => ENNReal.ofReal (Real.log (D / ‖((z.1 : K) : ℂ) - ((z.2 : K) : ℂ)‖)))
      ≤ Filter.liminf (fun n => MeasureTheory.lintegral ((νn n).prod (νn n))
          (fun z : K × K => ENNReal.ofReal (Real.log (D / ‖((z.1 : K) : ℂ) - ((z.2 : K) : ℂ)‖))))
        Filter.atTop := by
  set g : K × K → ℝ := fun z => ‖((z.1 : K) : ℂ) - ((z.2 : K) : ℂ)‖ with hg
  set f : K × K → ℝ := fun z => Real.log (D / g z) with hf
  have hgnn : ∀ z : K × K, 0 ≤ g z := by
    intro z; rw [hg]; exact norm_nonneg _
  have hg_cont : Continuous g := by
    rw [hg]
    exact ((continuous_subtype_val.comp continuous_fst).sub
      (continuous_subtype_val.comp continuous_snd)).norm
  have hU : IsOpen {z : K × K | 0 < g z} := isOpen_Ioi.preimage hg_cont
  have hcontOn : ContinuousOn f {z : K × K | 0 < g z} := by
    rw [hf]
    have h1 : ContinuousOn (fun z : K × K => D / g z) {z : K × K | 0 < g z} :=
      continuousOn_const.div hg_cont.continuousOn (fun z hz => ne_of_gt hz)
    exact h1.log (fun z hz => ne_of_gt (div_pos hD hz))
  have hf_nn : 0 ≤ f := by
    intro z
    change 0 ≤ Real.log (D / g z)
    have hrD : g z ≤ D := by rw [hg]; exact hDiam _ z.1.2 _ z.2.2
    rcases eq_or_lt_of_le (hgnn z) with h0 | hpos
    · rw [← h0, div_zero]; simp
    · exact Real.log_nonneg ((one_le_div hpos).mpr hrD)
  have hf_lsc : LowerSemicontinuous f := by
    rw [lowerSemicontinuous_iff_isOpen_preimage]
    intro t
    by_cases ht : t < 0
    · have huniv : f ⁻¹' (Set.Ioi t) = Set.univ := by
        ext z
        simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_univ, iff_true]
        change t < Real.log (D / g z)
        have hz : 0 ≤ Real.log (D / g z) := hf_nn z
        linarith
      rw [huniv]; exact isOpen_univ
    · have ht0 : (0:ℝ) ≤ t := not_lt.mp ht
      have hsub : f ⁻¹' (Set.Ioi t) ⊆ {z : K × K | 0 < g z} := by
        intro z hz
        simp only [Set.mem_preimage, Set.mem_Ioi] at hz
        show 0 < g z
        by_contra h
        have hle : g z ≤ 0 := not_lt.mp h
        have hz0 : g z = 0 := le_antisymm hle (hgnn z)
        change t < Real.log (D / g z) at hz
        rw [hz0, div_zero, Real.log_zero] at hz
        linarith
      exact hcontOn.isOpen_preimage hU hsub isOpen_Ioi
  have hprod : Tendsto (fun n => (νn n).prod (νn n)) atTop (nhds (μ.prod μ)) :=
    (MeasureTheory.ProbabilityMeasure.continuous_prod.tendsto (μ, μ)).comp
      (hconv.prodMk_nhds hconv)
  have h_opens : ∀ G, IsOpen G →
      (μ.prod μ : Measure (K × K)) G
        ≤ atTop.liminf (fun i => ((νn i).prod (νn i) : Measure (K × K)) G) :=
    fun G hG => MeasureTheory.ProbabilityMeasure.le_liminf_measure_open_of_tendsto hprod hG
  exact lintegral_ofReal_le_liminf_of_lsc (μ := (μ.prod μ : Measure (K × K)))
    (μs := fun i => ((νn i).prod (νn i) : Measure (K × K))) h_opens hf_nn hf_lsc

end Commons.Analysis.Potential
