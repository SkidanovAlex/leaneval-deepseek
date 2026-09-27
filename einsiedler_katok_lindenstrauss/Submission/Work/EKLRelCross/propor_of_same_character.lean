import Mathlib

/-!
# `Work.EKLRelCross.propor_of_same_character`

Any two non-zero Radon measures on a locally compact second countable group `G` which are
eigenmeasures with the *same* continuous character `χ : G → ℝ≥0∞` (i.e.
`μ.map (w * ·) = χ w • μ` and likewise for `ν`) are proportional:
`μ = c • ν` with `0 < c < ∞`.

## The mathematics

The proof is short once one notices that *twisting* an eigenmeasure by its character produces a
**left invariant** measure.  Indeed, since `μ.map (w * ·) = χ w • μ`, for measurable `A`
```
(∫ over w⁻¹A of χ dμ) = χ w * ∫ over A of χ dμ ,
```
i.e. `(χ · μ) (w • A) = (χ · μ) (A)`: the measure `μ.withDensity χ` is invariant under left
translations.  It is also finite on compacts (χ is bounded on compacts), hence a non-zero
multiple of Haar measure by uniqueness of Haar measure in a second countable group.  Applying
this to `μ` and to `ν` gives `μ.withDensity χ = a • H` and `ν.withDensity χ = b • H` with
`a, b ∈ (0,∞)` and the same Haar measure `H`, and multiplying by the density `χ⁻¹`
(which is legitimate because `χ` is everywhere non-zero and non-infinite, so that
`(σ.withDensity χ).withDensity χ⁻¹ = σ`) yields `μ = (a * b⁻¹) • ν`.
-/

namespace Work.EKLRelCross

open MeasureTheory

set_option linter.style.haveILetI false

/-- The character `χ` takes the value `1` at the identity. -/
private theorem chi_one {G : Type*} [Group G] (χ : G → ENNReal) (hχ0 : ∀ w, χ w ≠ 0)
    (hχt : ∀ w, χ w ≠ ⊤) (hχm : ∀ v w, χ (v * w) = χ v * χ w) : χ 1 = 1 := by
  have h : χ (1 * 1) = χ 1 * χ 1 := hχm 1 1
  rw [mul_one] at h
  have h2 : 1 * χ 1 = χ 1 * χ 1 := by rw [one_mul]; exact h
  exact ((ENNReal.mul_left_inj (hχ0 1) (hχt 1)).mp h2).symm

/-- `χ w⁻¹ = (χ w)⁻¹`. -/
private theorem chi_inv {G : Type*} [Group G] (χ : G → ENNReal)
    (hχm : ∀ v w, χ (v * w) = χ v * χ w) (hχ1 : χ 1 = 1) :
    ∀ w, χ w⁻¹ = (χ w)⁻¹ := by
  intro w
  have h : χ w⁻¹ * χ w = 1 := by rw [← hχm w⁻¹ w, inv_mul_cancel, hχ1]
  exact ENNReal.eq_inv_of_mul_eq_one_left h

/-- **Twisting an eigenmeasure by its character gives a left invariant measure.**
If `σ.map (w * ·) = χ w • σ` for all `w`, then `σ.withDensity χ` is invariant under left
translations. -/
private theorem withDensity_chi_isMulLeftInvariant {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (χ : G → ENNReal) (hχc : Continuous χ) (hχ0 : ∀ w, χ w ≠ 0) (hχt : ∀ w, χ w ≠ ⊤)
    (hχm : ∀ v w, χ (v * w) = χ v * χ w)
    (σ : Measure G) (hσ : ∀ w, σ.map (fun x => w * x) = χ w • σ) :
    (σ.withDensity χ).IsMulLeftInvariant := by
  have hχ1 : χ 1 = 1 := chi_one χ hχ0 hχt hχm
  have hχinv : ∀ w, χ w⁻¹ = (χ w)⁻¹ := chi_inv χ hχm hχ1
  have hχmeas : Measurable χ := hχc.measurable
  refine ⟨fun w => ?_⟩
  ext A hA
  rw [Measure.map_apply (measurable_const_mul w) hA]
  have hP : MeasurableSet ((fun x : G => w * x) ⁻¹' A) := measurable_const_mul w hA
  rw [withDensity_apply χ hP, withDensity_apply χ hA]
  rw [← lintegral_indicator hP χ, ← lintegral_indicator hA χ]
  -- write `σ` through the push-forward by `w⁻¹ * ·`
  have hσw : σ = χ w • (σ.map (fun x => w⁻¹ * x)) := by
    rw [hσ w⁻¹, hχinv w, smul_smul, ENNReal.mul_inv_cancel (hχ0 w) (hχt w), one_smul]
  conv_lhs => rw [hσw]
  rw [lintegral_smul_measure, smul_eq_mul]
  -- change variables `x ↦ w⁻¹ * x`
  rw [lintegral_map (hχmeas.indicator hP) (measurable_const_mul w⁻¹)]
  have hcongr : (fun x => Set.indicator ((fun x : G => w * x) ⁻¹' A) χ (w⁻¹ * x))
      = (fun x => Set.indicator A (fun y => χ (w⁻¹ * y)) x) := by
    funext y
    by_cases hy : y ∈ A
    · rw [Set.indicator_of_mem hy]
      have hmem : w⁻¹ * y ∈ (fun x : G => w * x) ⁻¹' A := by
        simp only [Set.mem_preimage]; rw [← mul_assoc, mul_inv_cancel, one_mul]; exact hy
      rw [Set.indicator_of_mem hmem]
    · rw [Set.indicator_of_notMem hy]
      have hmem : w⁻¹ * y ∉ (fun x : G => w * x) ⁻¹' A := by
        simp only [Set.mem_preimage]
        intro hh; exact hy (by rw [← mul_assoc, mul_inv_cancel, one_mul] at hh; exact hh)
      rw [Set.indicator_of_notMem hmem]
  rw [hcongr]
  have hcongr2 : (fun x => Set.indicator A (fun y => χ (w⁻¹ * y)) x)
      = (fun x => χ (w⁻¹) * Set.indicator A χ x) := by
    funext y
    by_cases hy : y ∈ A
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, hχm w⁻¹ y]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]
  rw [hcongr2, lintegral_const_mul _ (hχmeas.indicator hA)]
  rw [hχinv w, ← mul_assoc, ENNReal.mul_inv_cancel (hχ0 w) (hχt w), one_mul]

/-- **The twist is finite on compacts.**  `χ` is bounded on a compact set. -/
private theorem withDensity_chi_finiteOnCompacts {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G]
    [SecondCountableTopology G]
    (χ : G → ENNReal) (hχc : Continuous χ) (hχt : ∀ w, χ w ≠ ⊤)
    (σ : Measure G) (hσf : IsFiniteMeasureOnCompacts σ) :
    IsFiniteMeasureOnCompacts (σ.withDensity χ) := by
  haveI : IsFiniteMeasureOnCompacts σ := hσf
  haveI : SFinite σ := inferInstance
  refine ⟨fun K hK => ?_⟩
  rw [withDensity_apply' χ K]
  rcases Set.eq_empty_or_nonempty K with h | hne
  · rw [h]; simp
  · obtain ⟨x, _hxK, hxmax⟩ := hK.exists_isMaxOn hne hχc.continuousOn
    calc ∫⁻ a in K, χ a ∂σ ≤ ∫⁻ a in K, χ x ∂σ :=
          setLIntegral_mono measurable_const (fun a ha => hxmax ha)
      _ = χ x * σ K := setLIntegral_const K (χ x)
      _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr (hχt x)) hK.measure_lt_top

/-- Multiplying by the density `χ⁻¹` undoes the twist, because `χ` is everywhere non-zero. -/
private theorem withDensity_inv_chi {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [BorelSpace G]
    (χ : G → ENNReal) (hχc : Continuous χ) (hχ0 : ∀ w, χ w ≠ 0) (hχt : ∀ w, χ w ≠ ⊤)
    (σ : Measure G) :
    (σ.withDensity χ).withDensity χ⁻¹ = σ := by
  have hmulχ : (χ * χ⁻¹) = (1 : G → ENNReal) := by
    funext x; exact ENNReal.mul_inv_cancel (hχ0 x) (hχt x)
  rw [← withDensity_mul σ hχc.measurable hχc.measurable.inv, hmulχ, withDensity_one]

theorem propor_of_same_character {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G]
    (χ : G → ENNReal) (hχc : Continuous χ) (hχ0 : ∀ w, χ w ≠ 0) (hχt : ∀ w, χ w ≠ ⊤)
    (hχm : ∀ v w, χ (v * w) = χ v * χ w)
    (μ ν : MeasureTheory.Measure G) (hμf : MeasureTheory.IsFiniteMeasureOnCompacts μ)
    (hνf : MeasureTheory.IsFiniteMeasureOnCompacts ν) (hμn : μ ≠ 0) (hνn : ν ≠ 0)
    (hμq : ∀ w, μ.map (fun x => w * x) = χ w • μ)
    (hνq : ∀ w, ν.map (fun x => w * x) = χ w • ν) :
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ μ = c • ν := by
  have hfinμ : IsFiniteMeasureOnCompacts (μ.withDensity χ) :=
    withDensity_chi_finiteOnCompacts χ hχc hχt μ hμf
  have hfinν : IsFiniteMeasureOnCompacts (ν.withDensity χ) :=
    withDensity_chi_finiteOnCompacts χ hχc hχt ν hνf
  haveI : IsFiniteMeasureOnCompacts (μ.withDensity χ) := hfinμ
  haveI : IsFiniteMeasureOnCompacts (ν.withDensity χ) := hfinν
  haveI : (μ.withDensity χ).IsMulLeftInvariant :=
    withDensity_chi_isMulLeftInvariant χ hχc hχ0 hχt hχm μ hμq
  haveI : (ν.withDensity χ).IsMulLeftInvariant :=
    withDensity_chi_isMulLeftInvariant χ hχc hχ0 hχt hχm ν hνq
  -- uniqueness of Haar measure: both twists are multiples of the same Haar measure
  let K₀ : TopologicalSpace.PositiveCompacts G := Classical.arbitrary _
  have hμhaar : μ.withDensity χ = (μ.withDensity χ) K₀ • Measure.haarMeasure K₀ :=
    Measure.haarMeasure_unique _ K₀
  have hνhaar : ν.withDensity χ = (ν.withDensity χ) K₀ • Measure.haarMeasure K₀ :=
    Measure.haarMeasure_unique _ K₀
  set a : ENNReal := (μ.withDensity χ) K₀ with ha
  set b : ENNReal := (ν.withDensity χ) K₀ with hb
  have hbT : b ≠ ⊤ := by rw [hb]; exact K₀.isCompact.measure_lt_top.ne
  have haT : a ≠ ⊤ := by rw [ha]; exact K₀.isCompact.measure_lt_top.ne
  have hb0 : b ≠ 0 := by
    intro hb0
    apply hνn
    have hz : ν.withDensity χ = 0 := by rw [hνhaar, hb0, zero_smul]
    rw [← withDensity_inv_chi χ hχc hχ0 hχt ν, hz, withDensity_zero_left]
  have ha0 : a ≠ 0 := by
    intro ha0
    apply hμn
    have hz : μ.withDensity χ = 0 := by rw [hμhaar, ha0, zero_smul]
    rw [← withDensity_inv_chi χ hχc hχ0 hχt μ, hz, withDensity_zero_left]
  have hprop : μ.withDensity χ = (a * b⁻¹) • (ν.withDensity χ) := by
    ext A _
    rw [hμhaar, hνhaar]
    simp only [Measure.smul_apply, smul_eq_mul]
    rw [mul_assoc, ← mul_assoc b⁻¹ b (Measure.haarMeasure K₀ A),
        ENNReal.inv_mul_cancel hb0 hbT, one_mul]
  refine ⟨a * b⁻¹, mul_ne_zero ha0 (ENNReal.inv_ne_zero.mpr hbT),
    ENNReal.mul_ne_top haT (ENNReal.inv_ne_top.mpr hb0), ?_⟩
  calc μ = (μ.withDensity χ).withDensity χ⁻¹ :=
        (withDensity_inv_chi χ hχc hχ0 hχt μ).symm
    _ = ((a * b⁻¹) • (ν.withDensity χ)).withDensity χ⁻¹ := by rw [hprop]
    _ = (a * b⁻¹) • ((ν.withDensity χ).withDensity χ⁻¹) := withDensity_smul_measure _ _
    _ = (a * b⁻¹) • ν := by rw [withDensity_inv_chi χ hχc hχ0 hχt ν]

end Work.EKLRelCross
