import Mathlib
import Submission.Work.Mostow.volH_le_fundamentalDomain

/-!
# `volH_le_card_mul_of_ae_count`

`Work.Mostow.volH_le_card_mul_of_ae_count`: if `D` is a fundamental domain for a discrete subgroup
`Γ ≤ PO(n,1)` acting on `ℍⁿ = E n`, `F` is measurable, and for almost every `z ∈ D` at most `N`
of the images `γ • z` (`γ ∈ Γ`) lie in `F`, then `volH n F ≤ N * volH n D`.

The mathematical content is the standard "counting" estimate: decomposing `F` along the partition
of `ℍⁿ` by the translates of `D` turns `volH n F` into the integral over `D` of the multiplicity
function `z ↦ #{γ : γ • z ∈ F}`, which is bounded by `N` almost everywhere.

The abstract statement (for an arbitrary countable group acting measurably on a measure space,
with an invariant measure) is proved first as `Work.Mostow.measure_le_card_mul_of_ae_count`, and
the hyperbolic statement is the specialisation `Γ ↷ ℍⁿ`, `μ = volH n`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

variable {n : ℕ}

/-- **Counting bound.** Let a countable group `G` act measurably on a measurable space `α`,
preserving a measure `μ`, let `s` be a fundamental domain and `t` a measurable set such that for
almost every `x ∈ s` the set `{g : G | g • x ∈ t}` is contained in a finite set of cardinality
at most `N`. Then `μ t ≤ N * μ s`.

Proof: `μ t = ∑' g, (μ.restrict s) (g⁻¹ • t)` (`IsFundamentalDomain.measure_eq_tsum'` plus
`measure_inv_smul_inter`), each term is the integral of the indicator of `g⁻¹ • t` over
`μ.restrict s`, and `lintegral_tsum` turns the series into the integral of the multiplicity
function `∑' g, 1_{g⁻¹ • t}`, which is at most `N` almost everywhere by hypothesis (outside the
finite set the indicators vanish, `tsum_eq_sum`). -/
theorem measure_le_card_mul_of_ae_count {G α : Type*} [Group G] [MulAction G α]
    [MeasurableSpace α] (μ : Measure α) [Countable G] [MeasurableConstSMul G α]
    [SMulInvariantMeasure G α μ] {s t : Set α} (hs : IsFundamentalDomain G s μ)
    (ht : MeasurableSet t) (N : ℕ)
    (hcount : ∀ᵐ x ∂(μ.restrict s),
      ∃ F : Finset G, F.card ≤ N ∧ ∀ g : G, g • x ∈ t → g ∈ F) :
    μ t ≤ N * μ s := by
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
  -- (2) Sum of the measures = integral of the multiplicity function.
  have hstep2 : ∑' g : G, (μ.restrict s) (g⁻¹ • t)
      = ∫⁻ x, ∑' g : G, (g⁻¹ • t).indicator (1 : α → ℝ≥0∞) x ∂(μ.restrict s) := by
    rw [lintegral_tsum (μ := μ.restrict s)
      (f := fun g x => (g⁻¹ • t).indicator (1 : α → ℝ≥0∞) x)
      (fun g => (Measurable.indicator measurable_const (hmeas g)).aemeasurable)]
    refine tsum_congr fun g => ?_
    rw [lintegral_indicator_one (hmeas g)]
  -- (3) The multiplicity function is bounded by `N` almost everywhere.
  have hbound : ∀ᵐ x ∂(μ.restrict s),
      ∑' g : G, (g⁻¹ • t).indicator (1 : α → ℝ≥0∞) x ≤ N := by
    filter_upwards [hcount] with x hx
    obtain ⟨F, hFcard, hF⟩ := hx
    have hsupp : ∀ g ∉ F, (g⁻¹ • t).indicator (1 : α → ℝ≥0∞) x = 0 := by
      intro g hg
      rw [Set.indicator_of_notMem]
      intro hmem
      rw [Set.mem_inv_smul_set_iff] at hmem
      exact hg (hF g hmem)
    rw [tsum_eq_sum hsupp]
    calc ∑ g ∈ F, (g⁻¹ • t).indicator (1 : α → ℝ≥0∞) x
        ≤ ∑ _g ∈ F, (1 : ℝ≥0∞) := Finset.sum_le_sum fun g _ => Set.indicator_le_self _ _ x
      _ = F.card := by simp
      _ ≤ N := by exact_mod_cast hFcard
  calc μ t = ∑' g : G, (μ.restrict s) (g⁻¹ • t) := hstep1
    _ = ∫⁻ x, ∑' g : G, (g⁻¹ • t).indicator (1 : α → ℝ≥0∞) x ∂(μ.restrict s) := hstep2
    _ ≤ ∫⁻ _x, (N : ℝ≥0∞) ∂(μ.restrict s) := lintegral_mono_ae hbound
    _ = N * (μ.restrict s) Set.univ := lintegral_const N
    _ = N * μ s := by rw [Measure.restrict_apply_univ]

theorem volH_le_card_mul_of_ae_count (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1))
    (hdisc : IsDiscrete (SetLike.coe Γ))
    {D F : Set (Submission.Mostow.E n)}
    (hD : MeasureTheory.IsFundamentalDomain Γ D (Submission.Mostow.volH n))
    (hF : MeasurableSet F) (N : ℕ)
    (hcount : ∀ᵐ z ∂((Submission.Mostow.volH n).restrict D),
      ∃ s : Finset Γ, s.card ≤ N ∧ ∀ γ : Γ, (γ : LeanEval.Geometry.MostowRigidity.PO n 1) • z ∈ F → γ ∈ s) :
    Submission.Mostow.volH n F ≤ N * Submission.Mostow.volH n D := by
  have hId : HypIsoData n := HypIsoData.ofProp hI
  -- the `Γ`-action on `ℍⁿ`, inherited from the `PO(n,1)`-action
  letI : MulAction (PO n 1) (E n) :=
    { one_smul := fun u => poOneSMul u
      mul_smul := fun g h u => poMulSMul g h u }
  letI : MulAction Γ (E n) := inferInstance
  haveI : MeasurableConstSMul Γ (E n) :=
    ⟨fun c => (hId.contDiff_smul (c : PO n 1)).continuous.measurable⟩
  haveI : SMulInvariantMeasure Γ (E n) (volH n) :=
    ⟨fun c s hs => (hId.measurePreserving_smul (c : PO n 1)).measure_preimage hs.nullMeasurableSet⟩
  haveI : Countable Γ := countable_of_isDiscrete (PO n 1) hdisc
  exact measure_le_card_mul_of_ae_count (volH n) (s := D) (t := F) hD hF N hcount

end

end Work.Mostow
