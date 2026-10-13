import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Honesty.lintegral_Ioo_triangle

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

-- Intended file: Submission/Work/FTS/PhiStar/Honesty/lintegral_Ioo_tail_swap.lean
-- Intended namespace: Work.FTS.PhiStar.Honesty (like its sibling lintegral_Ioo_triangle).
-- Adapt the PROVED sibling Submission/Work/FTS/PhiStar/Honesty/lintegral_Ioo_triangle.lean
-- (`Work.FTS.PhiStar.Honesty.lintegral_Ioo_triangle`), whose inner variable runs over `(0,z)`;
-- here it runs over `(z,∞)` and the outer variable over `(0,1)`.
open MeasureTheory Set Filter

/-- `AEMeasurable` on a restricted measure upgrades to `AEMeasurable` of the indicator. -/
private lemma aemeasurable_indicator_of_restrict_tail {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s : Set α} (hs : MeasurableSet s) {f : α → ENNReal}
    (h : AEMeasurable f (μ.restrict s)) : AEMeasurable (s.indicator f) μ := by
  obtain ⟨g, hg, hfg⟩ := h
  exact ⟨s.indicator g, hg.indicator hs, (ae_eq_restrict_iff_indicator_ae_eq hs).mp hfg⟩

/-- Tail triangle, first key pointwise identity: for `0 < z`, the step function `1_{z<t}` times
the `(0,∞)`-indicator of `G` is the `(z,∞)`-indicator of `G` (the constraint `t > 0` is
automatic from `t > z > 0`). -/
private lemma tail_swap_step_left {z : ℝ} (hz : 0 < z) (G : ℝ → ENNReal) (t : ℝ) :
    (if z < t then (1 : ENNReal) else 0) * (Set.Ioi (0 : ℝ)).indicator G t
      = (Set.Ioi z).indicator G t := by
  by_cases h : z < t
  · have h0 : t ∈ Set.Ioi (0 : ℝ) := lt_trans hz h
    have h1 : t ∈ Set.Ioi z := h
    rw [ite_eq_left h, one_mul, Set.indicator_of_mem h0, Set.indicator_of_mem h1]
  · have h1 : t ∉ Set.Ioi z := h
    rw [ite_eq_right h, zero_mul, Set.indicator_of_notMem h1]

/-- Tail triangle, second key pointwise identity: the `(0,1)`-indicator of `F` times the step
`1_{z<t}` is the indicator of the truncated `(0,1) ∩ (0,t)`. -/
private lemma tail_swap_step_right (F : ℝ → ENNReal) (t z : ℝ) :
    (Set.Ioo (0 : ℝ) 1).indicator F z * (if z < t then (1 : ENNReal) else 0)
      = (Set.Ioo (0 : ℝ) 1 ∩ Set.Iio t).indicator F z := by
  by_cases h : z ∈ Set.Ioo (0 : ℝ) 1 ∩ Set.Iio t
  · have hz1 : z ∈ Set.Ioo (0 : ℝ) 1 := (Set.mem_inter_iff z _ _).mp h |>.1
    have hz2 : z < t := Set.mem_Iio.mp ((Set.mem_inter_iff z _ _).mp h).2
    rw [Set.indicator_of_mem hz1, ite_eq_left hz2, mul_one, Set.indicator_of_mem h]
  · by_cases h2 : z < t
    · have hnot : z ∉ Set.Ioo (0 : ℝ) 1 :=
        fun hz1 => h ((Set.mem_inter_iff z _ _).mpr ⟨hz1, Set.mem_Iio.mpr h2⟩)
      rw [Set.indicator_of_notMem hnot, ite_eq_left h2, mul_one, Set.indicator_of_notMem h]
    · have h2' : ¬ z < t := h2
      rw [ite_eq_right h2', mul_zero, Set.indicator_of_notMem h]

/-- Tail triangle, third key pointwise identity: on `t > 0`, the `(0,∞)`-indicator of `G` times
an arbitrary factor agrees with the `(0,∞)`-indicator of the product `G t * ·`. -/
private lemma tail_swap_step_out (G : ℝ → ENNReal) (X : ℝ → ENNReal) (t : ℝ) :
    X t * (Set.Ioi (0 : ℝ)).indicator G t
      = (Set.Ioi (0 : ℝ)).indicator (fun t => G t * X t) t := by
  by_cases ht : t ∈ Set.Ioi (0 : ℝ)
  · have hG : (Set.Ioi (0 : ℝ)).indicator G t = G t := Set.indicator_of_mem ht G
    have hR : (Set.Ioi (0 : ℝ)).indicator (fun t => G t * X t) t = G t * X t :=
      Set.indicator_of_mem ht _
    rw [hG, hR, mul_comm]
  · have hG : (Set.Ioi (0 : ℝ)).indicator G t = 0 := Set.indicator_of_notMem ht G
    have hR : (Set.Ioi (0 : ℝ)).indicator (fun t => G t * X t) t = 0 :=
      Set.indicator_of_notMem ht _
    rw [hG, hR, mul_zero]

/-- Tonelli for the "tail triangle" `{(z,t) : 0 < z < 1, z < t}`: the iterated integral over
`z ∈ (0,1)`, `t ∈ (z,∞)` equals the iterated integral over `t > 0`, `z ∈ (0,1) ∩ (0,t)`. -/
theorem lintegral_Ioo_tail_swap {F G : ℝ → ENNReal}
    (hF : AEMeasurable F (MeasureTheory.volume.restrict (Set.Ioo 0 1)))
    (hG : AEMeasurable G (MeasureTheory.volume.restrict (Set.Ioi 0))) :
    (∫⁻ z in Set.Ioo (0 : ℝ) 1, F z * ∫⁻ t in Set.Ioi z, G t)
      = ∫⁻ t in Set.Ioi (0 : ℝ), G t * (∫⁻ z in (Set.Ioo (0 : ℝ) 1 ∩ Set.Iio t), F z) := by
  have hs : MeasurableSet (Set.Ioo (0 : ℝ) 1) := measurableSet_Ioo
  have ht0 : MeasurableSet (Set.Ioi (0 : ℝ)) := measurableSet_Ioi
  have hA : AEMeasurable (fun z : ℝ => (Set.Ioo (0 : ℝ) 1).indicator F z) volume :=
    aemeasurable_indicator_of_restrict_tail hs hF
  have hB : AEMeasurable (fun t : ℝ => (Set.Ioi (0 : ℝ)).indicator G t) volume :=
    aemeasurable_indicator_of_restrict_tail ht0 hG
  have hstep : Measurable
      (fun p : ℝ × ℝ => (if p.1 < p.2 then (1 : ENNReal) else 0)) :=
    Measurable.ite (isOpen_lt continuous_fst continuous_snd).measurableSet measurable_const
      measurable_const
  have hstepz : ∀ z : ℝ, Measurable (fun t : ℝ => (if z < t then (1 : ENNReal) else 0)) :=
    fun z => Measurable.ite measurableSet_Ioi measurable_const measurable_const
  have hstept : ∀ t : ℝ, Measurable (fun z : ℝ => (if z < t then (1 : ENNReal) else 0)) :=
    fun t => Measurable.ite measurableSet_Iio measurable_const measurable_const
  have hA' : AEMeasurable (fun p : ℝ × ℝ => (Set.Ioo (0 : ℝ) 1).indicator F p.1)
      (volume.prod volume) := hA.comp_fst
  have hB' : AEMeasurable (fun p : ℝ × ℝ => (Set.Ioi (0 : ℝ)).indicator G p.2)
      (volume.prod volume) := hB.comp_snd
  set Ψ : ℝ → ℝ → ENNReal := fun z t =>
    (Set.Ioo (0 : ℝ) 1).indicator F z
      * ((if z < t then (1 : ENNReal) else 0) * (Set.Ioi (0 : ℝ)).indicator G t) with hΨ
  have hAE : AEMeasurable (Function.uncurry Ψ) (volume.prod volume) := by
    rw [hΨ]
    exact AEMeasurable.mul hA' (hstep.aemeasurable.mul hB')
  have h1 : (∫⁻ z, ∫⁻ t, Ψ z t)
      = ∫⁻ z in Set.Ioo (0 : ℝ) 1, F z * ∫⁻ t in Set.Ioi z, G t := by
    have hpt : ∀ z : ℝ,
        ∫⁻ t, Ψ z t
          = (Set.Ioo (0 : ℝ) 1).indicator (fun z => F z * ∫⁻ t in Set.Ioi z, G t) z := by
      intro z
      by_cases hz : z ∈ Set.Ioo (0 : ℝ) 1
      · have hz0 : 0 < z := hz.1
        have hinner : AEMeasurable
            (fun t : ℝ => (if z < t then (1 : ENNReal) else 0)
              * (Set.Ioi (0 : ℝ)).indicator G t) volume :=
          (hstepz z).aemeasurable.mul hB
        calc ∫⁻ t, Ψ z t
            = (Set.Ioo (0 : ℝ) 1).indicator F z *
                ∫⁻ t, (if z < t then (1 : ENNReal) else 0)
                  * (Set.Ioi (0 : ℝ)).indicator G t := by
                simp only [hΨ]
                exact lintegral_const_mul'' _ hinner
          _ = (Set.Ioo (0 : ℝ) 1).indicator F z * ∫⁻ t, (Set.Ioi z).indicator G t := by
                congr 1
                exact lintegral_congr (fun t => tail_swap_step_left hz0 G t)
          _ = (Set.Ioo (0 : ℝ) 1).indicator F z * ∫⁻ t in Set.Ioi z, G t := by
                rw [lintegral_indicator measurableSet_Ioi G]
          _ = F z * ∫⁻ t in Set.Ioi z, G t := by rw [indicator_of_mem hz F]
          _ = (Set.Ioo (0 : ℝ) 1).indicator (fun z => F z * ∫⁻ t in Set.Ioi z, G t) z := by
                rw [indicator_of_mem hz]
      · have hzF : (Set.Ioo (0 : ℝ) 1).indicator F z = 0 := indicator_of_notMem hz F
        rw [indicator_of_notMem hz]
        simp only [hΨ, hzF, zero_mul, lintegral_zero]
    calc ∫⁻ z, ∫⁻ t, Ψ z t
        = ∫⁻ z, (Set.Ioo (0 : ℝ) 1).indicator (fun z => F z * ∫⁻ t in Set.Ioi z, G t) z :=
          lintegral_congr hpt
      _ = ∫⁻ z in Set.Ioo (0 : ℝ) 1, F z * ∫⁻ t in Set.Ioi z, G t := by
          rw [lintegral_indicator measurableSet_Ioo
            (fun z => F z * ∫⁻ t in Set.Ioi z, G t)]
  have h2 : (∫⁻ t, ∫⁻ z, Ψ z t)
      = ∫⁻ t in Set.Ioi (0 : ℝ), G t * (∫⁻ z in (Set.Ioo (0 : ℝ) 1 ∩ Set.Iio t), F z) := by
    have hpt : ∀ t : ℝ,
        ∫⁻ z, Ψ z t
          = (∫⁻ z in (Set.Ioo (0 : ℝ) 1 ∩ Set.Iio t), F z)
              * (Set.Ioi (0 : ℝ)).indicator G t := by
      intro t
      have hinner : AEMeasurable
          (fun z : ℝ => (Set.Ioo (0 : ℝ) 1).indicator F z
            * (if z < t then (1 : ENNReal) else 0)) volume :=
        hA.mul (hstept t).aemeasurable
      calc ∫⁻ z, Ψ z t
          = ∫⁻ z, ((Set.Ioo (0 : ℝ) 1).indicator F z * (if z < t then (1 : ENNReal) else 0))
              * (Set.Ioi (0 : ℝ)).indicator G t := by
              apply lintegral_congr
              intro z
              simp only [hΨ]
              exact (mul_assoc _ _ _).symm
        _ = (∫⁻ z, (Set.Ioo (0 : ℝ) 1).indicator F z * (if z < t then (1 : ENNReal) else 0))
              * (Set.Ioi (0 : ℝ)).indicator G t :=
              lintegral_mul_const'' _ hinner
        _ = (∫⁻ z, (Set.Ioo (0 : ℝ) 1 ∩ Set.Iio t).indicator F z)
              * (Set.Ioi (0 : ℝ)).indicator G t := by
              rw [lintegral_congr (fun z => tail_swap_step_right F t z)]
        _ = (∫⁻ z in (Set.Ioo (0 : ℝ) 1 ∩ Set.Iio t), F z)
              * (Set.Ioi (0 : ℝ)).indicator G t := by
              rw [lintegral_indicator (measurableSet_Ioo.inter measurableSet_Iio) F]
    calc ∫⁻ t, ∫⁻ z, Ψ z t
        = ∫⁻ t, (∫⁻ z in (Set.Ioo (0 : ℝ) 1 ∩ Set.Iio t), F z)
            * (Set.Ioi (0 : ℝ)).indicator G t :=
          lintegral_congr hpt
      _ = ∫⁻ t, (Set.Ioi (0 : ℝ)).indicator
            (fun t => G t * (∫⁻ z in (Set.Ioo (0 : ℝ) 1 ∩ Set.Iio t), F z)) t :=
          lintegral_congr (fun t => tail_swap_step_out G
            (fun s => ∫⁻ z in (Set.Ioo (0 : ℝ) 1 ∩ Set.Iio s), F z) t)
      _ = ∫⁻ t in Set.Ioi (0 : ℝ), G t * (∫⁻ z in (Set.Ioo (0 : ℝ) 1 ∩ Set.Iio t), F z) := by
          rw [lintegral_indicator measurableSet_Ioi]
  have hswap : (∫⁻ z, ∫⁻ t, Ψ z t) = ∫⁻ t, ∫⁻ z, Ψ z t :=
    lintegral_lintegral_swap (f := Ψ) hAE
  rw [← h1, hswap, h2]

end Work.FTS.PhiStar.Honesty
