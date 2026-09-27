import Mathlib
import Submission.Work.Topology.analyticSet_isCompact_inner
import Submission.Work.Topology.comap_code_mem_of_isCompact

namespace Work.Topology

open MeasureTheory Set
open scoped ENNReal

/-- The `Bool`-valued code of a point for the countable family `B`: its `n`-th coordinate is
`true` exactly on `B n`.  This is the indicator-function presentation of the code map, chosen so
that no `Decidable` instance appears in the definition. -/
private noncomputable def codeMap {X : Type*} (B : ℕ → Set X) (x : X) : ℕ → Bool :=
  fun n => Set.indicator (B n) (fun _ : X => (true : Bool)) x

private lemma codeMap_apply {X : Type*} (B : ℕ → Set X) (z : X) (n : ℕ) :
    codeMap B z n = Set.indicator (B n) (fun _ : X => (true : Bool)) z := rfl

private lemma codeMap_eq_true_iff {X : Type*} (B : ℕ → Set X) (z : X) (n : ℕ) :
    codeMap B z n = true ↔ z ∈ B n := by
  by_cases hz : z ∈ B n
  · rw [codeMap_apply, Set.indicator_of_mem hz]; simp [hz]
  · rw [codeMap_apply, Set.indicator_of_notMem hz]
    exact ⟨fun h => absurd h (by simp), fun h => absurd h hz⟩

private lemma codeMap_eq_iff {X : Type*} (B : ℕ → Set X) {x z : X} :
    codeMap B z = codeMap B x ↔ ∀ n, (z ∈ B n ↔ x ∈ B n) := by
  constructor
  · intro h n
    rw [← codeMap_eq_true_iff B z n, ← codeMap_eq_true_iff B x n, h]
  · intro h
    funext n
    rw [codeMap_apply, codeMap_apply]
    by_cases hz : z ∈ B n
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem ((h n).mp hz)]
    · have hx : x ∉ B n := fun hc => hz ((h n).mpr hc)
      rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hx]

private lemma codeMap_measurable {X : Type*} {m : MeasurableSpace X} {B : ℕ → Set X}
    (hB : ∀ n, @MeasurableSet X m (B n)) :
    @Measurable X (ℕ → Bool) m _ (codeMap B) := by
  unfold codeMap
  refine Measurable.of_eval (fun n => ?_)
  exact measurable_const.indicator (hB n)

private lemma codeMap_image_analytic {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [T2Space X] {B : ℕ → Set X} (hB : ∀ n, @MeasurableSet X (borel X) (B n))
    {H : Set X} (hH : @MeasurableSet X (borel X) H) :
    AnalyticSet (codeMap B '' H) := by
  letI : MeasurableSpace X := borel X
  haveI : BorelSpace X := ⟨rfl⟩
  refine MeasurableSet.analyticSet_image hH ?_
  exact codeMap_measurable hB

private lemma exists_pos_add_lt {a ε : ℝ≥0∞} (ha : a ≠ ⊤) (h : a < ε) :
    ∃ ε' : ℝ≥0∞, 0 < ε' ∧ a + ε' < ε := by
  obtain ⟨r, hr1, hr2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
  have hpos : 0 < ↑r - a := tsub_pos_of_lt hr1
  refine ⟨(↑r - a) / 2, ENNReal.half_pos (ne_of_gt hpos), ?_⟩
  have htop : ↑r - a ≠ ⊤ := ne_top_of_le_ne_top (by simp) tsub_le_self
  have hlt : (↑r - a) / 2 < ↑r - a := ENNReal.half_lt_self (ne_of_gt hpos) htop
  calc a + (↑r - a) / 2 < a + (↑r - a) := (ENNReal.add_lt_add_iff_left ha).mpr hlt
    _ = ↑r := add_tsub_cancel_of_le (le_of_lt hr1)
    _ < ε := hr2

private lemma one_sub_lt {u ε : ℝ≥0∞} (hu : u ≤ 1) (h : 1 - ε < u) : 1 - u < ε := by
  have h2 : (1 : ℝ≥0∞) < ε + u := ENNReal.lt_add_of_sub_lt_left (Or.inl (by simp)) h
  exact (ENNReal.sub_lt_iff_lt_left (ne_top_of_le_ne_top (by simp) hu) hu).mpr (by rwa [add_comm] at h2)

/-- **A large measurable, saturated subset of the saturation of a large Borel set.**

`A` is a countably generated sub-σ-algebra of the Borel σ-algebra of a Polish space, already
presented by a countable family `B` (`A = σ(range B)`); `H` is a Borel set carrying more than
`1 - ε` of the probability `μ`.  Then there is `Z ∈ A` with `μ Zᶜ < ε` which is a union of
`B`-codes (saturated) and lies inside the `A`-saturation of `H` (which is only analytic).

Route.  Let `p x := fun n => decide (x ∈ B n)` be the code map into the Cantor space `ℕ → Bool`
(`p` is Borel because `A ≤ borel` and `B n ∈ A`).  Put `S := p '' H` (analytic: `H` Borel and `p`
Borel-measurable) and `ν := μ.map p` (a probability measure).  Let `B₀ ⊇ S` be a Borel `ν`-hull
of `S` (a minimising Borel superset, which exists by continuity from above), and apply
`Work.Topology.analyticSet_isCompact_inner` to `S`, `B₀`, `ν` and a small `ε'`: it yields a
compact `K` with `K ⊆ S` and `ν B₀ ≤ ν K + ε'`.  Take `Z := p ⁻¹' K`.  Then `Z ∈ A` by
`Work.Topology.comap_code_mem_of_isCompact` (compact implies closed), `Z` is a union of
`p`-fibres (the saturation clause), `Z ⊆ p ⁻¹' (p '' H)` (the containment clause, since
`K ⊆ p '' H`), and `μ Zᶜ = ν Kᶜ ≤ ν B₀ᶜ + ε' ≤ (1 - μ H) + ε' < ε`.

This removes the coanalytic obstruction in the construction of the descending plaque algebra of
Pisa 7.37/7.38: it replaces the (a priori non-measurable) union of the good atoms by a measurable
one of the same measure — see `Submission/Work/EKLC6Core/PLAN_L1_desc_subordinate.md`, session 4. -/
theorem exists_measurable_saturated_large {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [T2Space X] [MeasurableSpace X] [BorelSpace X] {A : MeasurableSpace X}
    (hA : A ≤ borel X) {B : ℕ → Set X} (hB : ∀ n, @MeasurableSet X A (B n))
    {H : Set X} (hH : @MeasurableSet X (borel X) H)
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (ε : ENNReal) (hε : 0 < ε) (hHμ : 1 - ε < μ H) :
    ∃ Z : Set X, @MeasurableSet X A Z ∧
      Z ⊆ {x | ∃ y ∈ H, ∀ n : ℕ, (x ∈ B n ↔ y ∈ B n)} ∧
      (∀ x ∈ Z, ∀ z : X, (∀ n : ℕ, (z ∈ B n ↔ x ∈ B n)) → z ∈ Z) ∧
      μ Zᶜ < ε := by
  classical
  let p : X → (ℕ → Bool) := codeMap B
  have hp : ∀ n, {x : X | p x n = true} = B n := by
    intro n
    ext x
    exact codeMap_eq_true_iff B x n
  have hBm : ∀ n, @MeasurableSet X (borel X) (B n) := fun n => hA (B n) (hB n)
  have hpmA : @Measurable X (ℕ → Bool) A _ p := @codeMap_measurable X A B hB
  have hS : AnalyticSet (p '' H) := codeMap_image_analytic (B := B) (H := H) hBm hH
  have hPol : PolishSpace (ℕ → Bool) := PolishSpace.mk
  have hνprob : IsProbabilityMeasure (μ.map p) :=
    (Measure.isProbabilityMeasure_map_iff hpmA.aemeasurable).mpr inferInstance
  let ν : Measure (ℕ → Bool) := μ.map p
  have hνprob' : IsProbabilityMeasure ν := hνprob
  have hμHle : μ H ≤ 1 := by
    calc μ H ≤ μ univ := measure_mono (subset_univ H)
      _ = 1 := measure_univ
  have ha_lt : 1 - μ H < ε := one_sub_lt hμHle hHμ
  obtain ⟨ε', hε'pos, hε'lt⟩ :=
    exists_pos_add_lt (ne_top_of_le_ne_top (by simp) tsub_le_self) ha_lt
  -- A Borel `ν`-hull of the analytic set `p '' H`.
  let B₀ : Set (ℕ → Bool) := toMeasurable ν (p '' H)
  have hB₀meas : MeasurableSet B₀ := measurableSet_toMeasurable ν (p '' H)
  have hSB₀ : p '' H ⊆ B₀ := subset_toMeasurable ν (p '' H)
  have hmin : ∀ B' : Set (ℕ → Bool), MeasurableSet B' → p '' H ⊆ B' → ν B₀ ≤ ν B' := by
    intro B' _ hsub
    change ν (toMeasurable ν (p '' H)) ≤ ν B'
    rw [measure_toMeasurable]
    exact measure_mono hsub
  obtain ⟨K, hKc, hKS, hKle⟩ :=
    analyticSet_isCompact_inner ν hB₀meas hSB₀ hS hmin hε'pos
  refine ⟨p ⁻¹' K, ?_, ?_, ?_, ?_⟩
  · exact comap_code_mem_of_isCompact B hB p hp hKc
  · rintro x hx
    obtain ⟨y, hyH, hpy⟩ := hKS hx
    exact ⟨y, hyH, fun n => ((codeMap_eq_iff B).mp hpy n).symm⟩
  · rintro x hx z hz
    have h_eq : p z = p x := (codeMap_eq_iff B).mpr hz
    show p z ∈ K
    rw [h_eq]
    exact hx
  · have hKmeas : MeasurableSet K := hKc.isClosed.measurableSet
    have h1 : μ (p ⁻¹' K)ᶜ = ν Kᶜ := by
      rw [← Set.preimage_compl]
      exact (Measure.map_apply (μ := μ) hpmA hKmeas.compl).symm
    have h2 : ν Kᶜ ≤ ν B₀ᶜ + ε' := (measure_compl_le_add_iff hKmeas hB₀meas).mpr hKle
    have h3 : ν B₀ᶜ ≤ 1 - μ H := by
      have h4 : μ H ≤ ν B₀ := by
        have h5 : H ⊆ p ⁻¹' B₀ := fun y hy => subset_toMeasurable ν (p '' H) (mem_image_of_mem p hy)
        calc μ H ≤ μ (p ⁻¹' B₀) := measure_mono h5
          _ = ν B₀ := (Measure.map_apply (μ := μ) hpmA hB₀meas).symm
      calc ν B₀ᶜ = ν univ - ν B₀ := measure_compl hB₀meas (measure_ne_top ν B₀)
        _ = 1 - ν B₀ := by rw [measure_univ]
        _ ≤ 1 - μ H := tsub_le_tsub_left h4 1
    rw [h1]
    calc ν Kᶜ ≤ ν B₀ᶜ + ε' := h2
      _ ≤ (1 - μ H) + ε' := add_le_add h3 le_rfl
      _ < ε := hε'lt

end Work.Topology
