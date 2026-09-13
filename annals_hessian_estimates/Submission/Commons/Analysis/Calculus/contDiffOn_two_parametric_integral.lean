import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ParametricIntegral

namespace Commons.Analysis.Calculus

open MeasureTheory Filter Set
open scoped Topology ContDiff

section Helpers

variable {P X E : Type*}

/-- For a family `f : P → X → E` that is continuous on `s ×ˢ univ` with `X` compact, the
norm `‖f q x‖` is locally uniformly bounded in `q`. -/
lemma eventually_forall_norm_le_of_continuousOn_uncurry
    [TopologicalSpace P] [TopologicalSpace X] [CompactSpace X] [SeminormedAddCommGroup E]
    {s : Set P} {f : P → X → E} {p₀ : P} (hs : s ∈ 𝓝 p₀)
    (hf : ContinuousOn (Function.uncurry f) (s ×ˢ Set.univ)) :
    ∃ C : ℝ, ∀ᶠ q in 𝓝 p₀, ∀ x, ‖f q x‖ ≤ C := by
  have hp : p₀ ∈ s := mem_of_mem_nhds hs
  have hmk : ContinuousOn (fun q => ContinuousMap.mkD (f q) (0 : C(X, E))) s :=
    ContinuousMap.continuousOn_mkD_of_uncurry f 0 hf
  have hc0 : ContinuousAt (fun q => ContinuousMap.mkD (f q) (0 : C(X, E))) p₀ :=
    hmk.continuousAt hs
  have hslice0 : Continuous (f p₀) :=
    hf.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ⟨hp, trivial⟩)
  refine ⟨‖ContinuousMap.mkD (f p₀) (0 : C(X, E))‖ + 1, ?_⟩
  filter_upwards [hs, hc0.eventually (Metric.ball_mem_nhds _ zero_lt_one)] with q hq hd
  have hsliceq : Continuous (f q) :=
    hf.comp_continuous (continuous_const.prodMk continuous_id) (fun x => ⟨hq, trivial⟩)
  intro x
  have hqx : ContinuousMap.mkD (f q) (0 : C(X, E)) x = f q x :=
    ContinuousMap.mkD_apply_of_continuous hsliceq
  have h0x : ContinuousMap.mkD (f p₀) (0 : C(X, E)) x = f p₀ x :=
    ContinuousMap.mkD_apply_of_continuous hslice0
  have hd' : dist (f q x) (f p₀ x) < 1 := by
    rw [← hqx, ← h0x]
    exact ((ContinuousMap.dist_lt_iff zero_lt_one).mp hd) x
  have hb : ‖f p₀ x‖ ≤ ‖ContinuousMap.mkD (f p₀) (0 : C(X, E))‖ := by
    rw [← h0x]
    exact ContinuousMap.norm_coe_le_norm _ x
  calc ‖f q x‖ = ‖(f q x - f p₀ x) + f p₀ x‖ := by rw [sub_add_cancel]
    _ ≤ ‖f q x - f p₀ x‖ + ‖f p₀ x‖ := norm_add_le _ _
    _ = dist (f q x) (f p₀ x) + ‖f p₀ x‖ := by rw [dist_eq_norm]
    _ ≤ 1 + ‖ContinuousMap.mkD (f p₀) (0 : C(X, E))‖ := by
        have := le_of_lt hd'; linarith [hb]
    _ ≤ ‖ContinuousMap.mkD (f p₀) (0 : C(X, E))‖ + 1 := by linarith

/-- A slice of a jointly continuous family is continuous. -/
lemma continuous_slice_of_continuousOn_uncurry
    [TopologicalSpace P] [TopologicalSpace X] [SeminormedAddCommGroup E]
    {s : Set P} {f : P → X → E} {p : P} (hp : p ∈ s)
    (hf : ContinuousOn (Function.uncurry f) (s ×ˢ Set.univ)) :
    Continuous (f p) :=
  hf.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ⟨hp, trivial⟩)

/-- A slice of a jointly continuous family is continuous at any interior point. -/
lemma continuousAt_slice_of_continuousOn_uncurry
    [TopologicalSpace P] [TopologicalSpace X] [SeminormedAddCommGroup E]
    {s : Set P} {f : P → X → E} {p : P} {a : X}
    (hps : s ∈ 𝓝 p) (hf : ContinuousOn (Function.uncurry f) (s ×ˢ Set.univ)) :
    ContinuousAt (fun q => f q a) p :=
  ((hf.comp (continuous_id.prodMk continuous_const).continuousOn
    (fun _ hq => ⟨hq, trivial⟩)).continuousAt hps)

/-- A continuous slice of a jointly continuous family over a compact space is integrable. -/
lemma integrable_slice_of_continuousOn_uncurry
    [TopologicalSpace P] [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup E] {μ : Measure X} [IsFiniteMeasure μ]
    {s : Set P} {f : P → X → E} {p : P} (hp : p ∈ s)
    (hf : ContinuousOn (Function.uncurry f) (s ×ˢ Set.univ)) :
    Integrable (f p) μ := by
  have hc : Continuous (f p) := continuous_slice_of_continuousOn_uncurry hp hf
  refine Integrable.of_bound hc.aestronglyMeasurable_of_compactSpace
    ‖(⟨f p, hc⟩ : C(X, E))‖ ?_
  exact Filter.Eventually.of_forall fun x => ContinuousMap.norm_coe_le_norm (⟨f p, hc⟩ : C(X, E)) x

end Helpers

/-- If a two-parameter family `Φ₀` (together with its first and second derivatives in the first
variable) is jointly continuous on `s × univ`, and `μ` is a finite measure on a compact space `X`,
then `p ↦ ∫ x, Φ₀ p x ∂μ` is `C²` on `s`, with the derivatives obtained by differentiating under
the integral sign. -/
theorem contDiffOn_two_parametric_integral
    {P X : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [IsFiniteMeasure μ]
    {s : Set P} (hs : IsOpen s)
    (Φ₀ : P → X → ℝ) (Φ₁ : P → X → P →L[ℝ] ℝ)
    (Φ₂ : P → X → P →L[ℝ] (P →L[ℝ] ℝ))
    (h₀ : ContinuousOn (Function.uncurry Φ₀) (s ×ˢ Set.univ))
    (h₁ : ContinuousOn (Function.uncurry Φ₁) (s ×ˢ Set.univ))
    (h₂ : ContinuousOn (Function.uncurry Φ₂) (s ×ˢ Set.univ))
    (hd₁ : ∀ p ∈ s, ∀ x, HasFDerivAt (fun q => Φ₀ q x) (Φ₁ p x) p)
    (hd₂ : ∀ p ∈ s, ∀ x, HasFDerivAt (fun q => Φ₁ q x) (Φ₂ p x) p) :
    ContDiffOn ℝ 2 (fun p => ∫ x, Φ₀ p x ∂μ) s ∧
    (∀ p ∈ s, HasFDerivAt (fun p => ∫ x, Φ₀ p x ∂μ) (∫ x, Φ₁ p x ∂μ) p) ∧
    (∀ p ∈ s, HasFDerivAt (fun p => ∫ x, Φ₁ p x ∂μ) (∫ x, Φ₂ p x ∂μ) p) ∧
    (∀ p ∈ s, fderiv ℝ (fun p => ∫ x, Φ₀ p x ∂μ) p = ∫ x, Φ₁ p x ∂μ) ∧
    (∀ p ∈ s, fderiv ℝ (fun p => ∫ x, Φ₁ p x ∂μ) p = ∫ x, Φ₂ p x ∂μ) := by
  have hderiv₀ : ∀ p ∈ s, HasFDerivAt (fun p => ∫ x, Φ₀ p x ∂μ) (∫ x, Φ₁ p x ∂μ) p := by
    intro p hp
    obtain ⟨C, hC⟩ :=
      eventually_forall_norm_le_of_continuousOn_uncurry (E := P →L[ℝ] ℝ)
        (s := s) (hs.mem_nhds hp) h₁
    obtain ⟨V, hV, hVb⟩ := hC.exists_mem
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := μ)
      (F := Φ₀) (F' := Φ₁) (x₀ := p) (s := V ∩ s) (bound := fun _ => C)
      (Filter.inter_mem hV (hs.mem_nhds hp)) ?_ ?_ ?_ ?_ ?_ ?_
    · filter_upwards [hs.mem_nhds hp] with q hq
      exact (continuous_slice_of_continuousOn_uncurry (E := ℝ) hq h₀).aestronglyMeasurable_of_compactSpace
    · exact integrable_slice_of_continuousOn_uncurry (E := ℝ) hp h₀
    · exact (continuous_slice_of_continuousOn_uncurry (E := P →L[ℝ] ℝ) hp h₁).aestronglyMeasurable_of_compactSpace
    · filter_upwards with a
      intro q hq
      exact hVb q hq.1 a
    · exact integrable_const C
    · filter_upwards with a
      intro q hq
      exact hd₁ q hq.2 a
  have hderiv₁ : ∀ p ∈ s, HasFDerivAt (fun p => ∫ x, Φ₁ p x ∂μ) (∫ x, Φ₂ p x ∂μ) p := by
    intro p hp
    obtain ⟨C, hC⟩ :=
      eventually_forall_norm_le_of_continuousOn_uncurry (E := P →L[ℝ] (P →L[ℝ] ℝ))
        (s := s) (hs.mem_nhds hp) h₂
    obtain ⟨V, hV, hVb⟩ := hC.exists_mem
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := μ)
      (F := Φ₁) (F' := Φ₂) (x₀ := p) (s := V ∩ s) (bound := fun _ => C)
      (Filter.inter_mem hV (hs.mem_nhds hp)) ?_ ?_ ?_ ?_ ?_ ?_
    · filter_upwards [hs.mem_nhds hp] with q hq
      exact (continuous_slice_of_continuousOn_uncurry (E := P →L[ℝ] ℝ) hq h₁).aestronglyMeasurable_of_compactSpace
    · exact integrable_slice_of_continuousOn_uncurry (E := P →L[ℝ] ℝ) hp h₁
    · exact (continuous_slice_of_continuousOn_uncurry (E := P →L[ℝ] (P →L[ℝ] ℝ)) hp h₂).aestronglyMeasurable_of_compactSpace
    · filter_upwards with a
      intro q hq
      exact hVb q hq.1 a
    · exact integrable_const C
    · filter_upwards with a
      intro q hq
      exact hd₂ q hq.2 a
  have hF2contOn : ContinuousOn (fun p => ∫ x, Φ₂ p x ∂μ) s := by
    refine continuousOn_of_forall_continuousAt fun p hp => ?_
    obtain ⟨C, hC⟩ :=
      eventually_forall_norm_le_of_continuousOn_uncurry (E := P →L[ℝ] (P →L[ℝ] ℝ))
        (s := s) (hs.mem_nhds hp) h₂
    obtain ⟨V, hV, hVb⟩ := hC.exists_mem
    refine continuousAt_of_dominated (μ := μ) (x₀ := p) (F := Φ₂) (bound := fun _ => C)
      ?_ ?_ (integrable_const C) ?_
    · filter_upwards [hs.mem_nhds hp] with q hq
      exact (continuous_slice_of_continuousOn_uncurry (E := P →L[ℝ] (P →L[ℝ] ℝ)) hq h₂).aestronglyMeasurable_of_compactSpace
    · filter_upwards [hV] with q hq
      filter_upwards with a
      exact hVb q hq a
    · filter_upwards with a
      exact continuousAt_slice_of_continuousOn_uncurry (E := P →L[ℝ] (P →L[ℝ] ℝ)) (hs.mem_nhds hp) h₂
  refine ⟨?_, hderiv₀, hderiv₁, fun p hp => (hderiv₀ p hp).fderiv,
    fun p hp => (hderiv₁ p hp).fderiv⟩
  rw [IsOpen.contDiffOn_iff hs]
  intro p hp
  refine (contDiffAt_succ_iff_hasFDerivAt (n := 1)).mpr ?_
  refine ⟨fun p => ∫ x, Φ₁ p x ∂μ, ⟨s, hs.mem_nhds hp, fun x hx => hderiv₀ x hx⟩, ?_⟩
  refine (contDiffAt_succ_iff_hasFDerivAt (n := 0)).mpr ?_
  refine ⟨fun p => ∫ x, Φ₂ p x ∂μ, ⟨s, hs.mem_nhds hp, fun x hx => hderiv₁ x hx⟩, ?_⟩
  change ContDiffAt ℝ (0 : ℕ∞ω) (fun p => ∫ x, Φ₂ p x ∂μ) p
  rw [contDiffAt_zero]
  exact ⟨s, hs.mem_nhds hp, hF2contOn⟩

end Commons.Analysis.Calculus