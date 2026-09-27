import Mathlib

/-!
# `Work.Mostow.ftbCountInter`

Counting bound for a fundamental domain, cut down by an invariant measurable set.

Let `G` be a countable group acting measurably on a measurable space `α`, preserving a measure
`μ`. Let `s` be a fundamental domain, `t` a measurable set and `T` a `G`-invariant measurable set
containing `t`. Suppose that for almost every `x ∈ s` the set `{g : G | g • x ∈ t}` is contained in
a finite set of cardinality at most `N`. Then `μ t ≤ N * μ (s ∩ T)`.

The proof is the standard "counting" computation: decomposing `t` along the translates of `s`
writes `μ t` as the integral over `s` of the multiplicity function
`x ↦ #{g : G | g • x ∈ t}`; this function is `≤ N` almost everywhere by hypothesis, and it vanishes
off the invariant set `T` (because `t ⊆ T` and `T` is `G`-invariant), so the integral is
concentrated on `s ∩ T`. -/

namespace Work.Mostow

open MeasureTheory
open scoped ENNReal Pointwise

theorem ftbCountInter {G α : Type*} [Group G] [MulAction G α] [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) [Countable G] [MeasurableConstSMul G α]
    [MeasureTheory.SMulInvariantMeasure G α μ]
    {s t T : Set α} (hs : MeasureTheory.IsFundamentalDomain G s μ) (ht : MeasurableSet t)
    (hT : MeasurableSet T) (hTinv : ∀ g : G, ∀ x : α, g • x ∈ T ↔ x ∈ T) (htT : t ⊆ T) (N : ℕ)
    (hcount : ∀ᵐ x ∂(μ.restrict s), ∃ F : Finset G, F.card ≤ N ∧ ∀ g : G, g • x ∈ t → g ∈ F) :
    μ t ≤ N * μ (s ∩ T) := by
  -- `g⁻¹ • t` is the preimage of `t` under `g • ·`, hence measurable.
  have hmeas : ∀ g : G, MeasurableSet (g⁻¹ • t) := fun g => by
    rw [← Set.preimage_smul]
    exact (measurable_const_smul g) ht
  -- (1) Decompose `t` along the translates of the fundamental domain.
  have hstep1 : μ t = ∑' g : G, (μ.restrict s) (g⁻¹ • t) := by
    rw [hs.measure_eq_tsum' t]
    refine tsum_congr fun g => ?_
    rw [Measure.restrict_apply₀' hs.nullMeasurableSet]
    exact (measure_inv_smul_inter μ g t s).symm
  -- (2) The sum of the measures is the integral of the multiplicity function.
  have hstep2 : ∑' g : G, (μ.restrict s) (g⁻¹ • t)
      = ∫⁻ x, ∑' g : G, (g⁻¹ • t).indicator (1 : α → ℝ≥0∞) x ∂(μ.restrict s) := by
    rw [lintegral_tsum (μ := μ.restrict s)
      (f := fun g x => (g⁻¹ • t).indicator (1 : α → ℝ≥0∞) x)
      (fun g => (Measurable.indicator measurable_const (hmeas g)).aemeasurable)]
    refine tsum_congr fun g => ?_
    rw [lintegral_indicator_one (hmeas g)]
  -- (3) The multiplicity function is bounded by `N` on the invariant set `T`, almost everywhere.
  have hbound : ∀ᵐ x ∂(μ.restrict s),
      (∑' g : G, (g⁻¹ • t).indicator (1 : α → ℝ≥0∞) x)
        ≤ (N : ℝ≥0∞) * T.indicator (1 : α → ℝ≥0∞) x := by
    filter_upwards [hcount] with x hx
    obtain ⟨F, hFcard, hF⟩ := hx
    by_cases hxT : x ∈ T
    · have hsuppF : ∀ g ∉ F, (g⁻¹ • t).indicator (1 : α → ℝ≥0∞) x = 0 := by
        intro g hg
        rw [Set.indicator_of_notMem]
        intro hmem
        rw [Set.mem_inv_smul_set_iff] at hmem
        exact hg (hF g hmem)
      have hle : (∑' g : G, (g⁻¹ • t).indicator (1 : α → ℝ≥0∞) x) ≤ (N : ℝ≥0∞) := by
        rw [tsum_eq_sum hsuppF]
        calc ∑ g ∈ F, (g⁻¹ • t).indicator (1 : α → ℝ≥0∞) x
            ≤ ∑ _g ∈ F, (1 : ℝ≥0∞) := Finset.sum_le_sum fun g _ => Set.indicator_le_self _ _ x
          _ = F.card := by simp
          _ ≤ N := by exact_mod_cast hFcard
      simpa [Set.indicator_of_mem hxT (1 : α → ℝ≥0∞)] using hle
    · have hzero : ∀ g : G, (g⁻¹ • t).indicator (1 : α → ℝ≥0∞) x = 0 := by
        intro g
        rw [Set.indicator_of_notMem]
        intro hmem
        rw [Set.mem_inv_smul_set_iff] at hmem
        exact hxT ((hTinv g x).1 (htT hmem))
      have hz : (∑' g : G, (g⁻¹ • t).indicator (1 : α → ℝ≥0∞) x) = 0 := by simp [hzero]
      have hTz : T.indicator (1 : α → ℝ≥0∞) x = 0 := Set.indicator_of_notMem hxT _
      rw [hz, hTz, mul_zero]
  -- (4) Integrate the bound.
  calc μ t = ∑' g : G, (μ.restrict s) (g⁻¹ • t) := hstep1
    _ = ∫⁻ x, ∑' g : G, (g⁻¹ • t).indicator (1 : α → ℝ≥0∞) x ∂(μ.restrict s) := hstep2
    _ ≤ ∫⁻ x, (N : ℝ≥0∞) * T.indicator (1 : α → ℝ≥0∞) x ∂(μ.restrict s) :=
        lintegral_mono_ae hbound
    _ = (N : ℝ≥0∞) * ∫⁻ x, T.indicator (1 : α → ℝ≥0∞) x ∂(μ.restrict s) :=
        lintegral_const_mul (N : ℝ≥0∞)
          (Measurable.indicator measurable_const hT)
    _ = (N : ℝ≥0∞) * (μ.restrict s) T := by rw [lintegral_indicator_one hT]
    _ = N * μ (s ∩ T) := by rw [Measure.restrict_apply hT, Set.inter_comm]

end Work.Mostow
