import Mathlib

open MeasureTheory Filter Topology Set
open scoped ENNReal

noncomputable section

namespace Work.EKLRelCross

/-- **Single-function Lusin.**  For a finite Borel measure on a Polish space, a measurable
real function bounded on a measurable set `B` is continuous on a compact `K ⊆ B` of almost full
`B`-measure. -/
theorem lusin_alt {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [PolishSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → ℝ} (hf : Measurable f) {B : Set X} (hB : MeasurableSet B)
    (hbdd : ∃ C : ℝ, ∀ x ∈ B, |f x| ≤ C) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : Set X, K ⊆ B ∧ IsCompact K ∧ μ (B \ K) < ENNReal.ofReal δ ∧ ContinuousOn f K := by
  classical
  obtain ⟨C, hC⟩ := hbdd
  set g : X → ℝ := B.indicator f with hg
  have hgmeas : Measurable g := hf.indicator hB
  have hgbdd : ∀ x, ‖g x‖ ≤ max C 0 := by
    intro x
    by_cases hx : x ∈ B
    · rw [hg, Set.indicator_of_mem hx, Real.norm_eq_abs]
      exact le_trans (hC x hx) (le_max_left _ _)
    · rw [hg, Set.indicator_of_notMem hx, norm_zero]
      exact le_max_right _ _
  have hgint : Integrable g μ :=
    Integrable.of_bound hgmeas.aestronglyMeasurable _ (ae_of_all _ hgbdd)
  -- bounded continuous approximations of `g`
  have happrox : ∀ k : ℕ, ∃ G : BoundedContinuousFunction X ℝ, ∫⁻ x, ‖g x - G x‖ₑ ∂μ ≤ (1 / 2 : ℝ≥0∞) ^ k := by
    intro k
    obtain ⟨G, hG, _⟩ := hgint.exists_boundedContinuous_lintegral_sub_le
      (ε := (1 / 2 : ℝ≥0∞) ^ k) (pow_ne_zero _ (by norm_num))
    exact ⟨G, hG⟩
  choose G hG using happrox
  -- convergence in measure
  have hTim : TendstoInMeasure μ (fun k x => G k x) atTop g := by
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero ?_
    · have hle : ∀ k, eLpNorm (fun x => G k x - g x) 1 μ ≤ (1 / 2 : ℝ≥0∞) ^ k := by
        intro k
        rw [eLpNorm_one_eq_lintegral_enorm (f := fun x => G k x - g x)
          ((G k).continuous.aestronglyMeasurable.sub hgmeas.aestronglyMeasurable)]
        calc ∫⁻ x, ‖G k x - g x‖ₑ ∂μ = ∫⁻ x, ‖g x - G k x‖ₑ ∂μ := by
              apply lintegral_congr
              intro x
              rw [show G k x - g x = -(g x - G k x) by ring, enorm_neg]
          _ ≤ (1 / 2 : ℝ≥0∞) ^ k := hG k
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num))
        (fun k => bot_le) hle
  obtain ⟨ns, hnsmono, hnsae⟩ := hTim.exists_seq_tendsto_ae
  -- Egorov
  obtain ⟨A, hAmeas, hAle, hAunif⟩ :=
    tendstoUniformlyOn_of_ae_tendsto' (fun i => (G (ns i)).continuous.stronglyMeasurable)
      hgmeas.stronglyMeasurable hnsae (ε := ENNReal.ofReal (δ / 2)) (ENNReal.ofReal_pos.mpr (by linarith))
  -- inner regularity
  have hSmeas : MeasurableSet (Aᶜ ∩ B) := hAmeas.compl.inter hB
  have hSfin : μ (Aᶜ ∩ B) ≠ ⊤ :=
    ne_top_of_le_ne_top (measure_ne_top μ Set.univ) (measure_mono (Set.subset_univ _))
  obtain ⟨K, hKS, hKcpt, hKsdiff⟩ :=
    hSmeas.exists_isCompact_sdiff_lt (ε := ENNReal.ofReal (δ / 2)) hSfin
      (ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith)))
  refine ⟨K, fun x hx => (hKS hx).2, hKcpt, ?_, ?_⟩
  · have hsub : B \ K ⊆ A ∪ ((Aᶜ ∩ B) \ K) := by
      intro x hx
      obtain ⟨hxB, hxK⟩ := hx
      by_cases hxA : x ∈ A
      · exact Or.inl hxA
      · exact Or.inr ⟨⟨hxA, hxB⟩, hxK⟩
    calc μ (B \ K) ≤ μ (A ∪ ((Aᶜ ∩ B) \ K)) := measure_mono hsub
      _ ≤ μ A + μ ((Aᶜ ∩ B) \ K) := measure_union_le _ _
      _ < ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) :=
          ENNReal.add_lt_add_of_le_of_lt (measure_ne_top μ A) hAle hKsdiff
      _ = ENNReal.ofReal δ := by
          rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
          norm_num
  · have hunifK : TendstoUniformlyOn (fun i x => G (ns i) x) g atTop K :=
      hAunif.mono fun x hx => (hKS hx).1
    have hcontg : ContinuousOn g K := hunifK.continuousOn
      (Filter.Eventually.of_forall (fun i => (G (ns i)).continuous.continuousOn)).frequently
    refine hcontg.congr_mono (fun x hx => ?_) (Set.Subset.refl K)
    rw [hg, Set.indicator_of_mem (hKS hx).2]

end Work.EKLRelCross
