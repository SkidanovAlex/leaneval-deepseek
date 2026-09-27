import Mathlib
import Submission.Work.Mostow.gapA.fundamentalDomain_measure_eq_tsum_inv
import Submission.Work.Mostow.gapA.tsum_measure_inter_le

open MeasureTheory

set_option linter.style.haveILetI false

namespace Work.Mostow.gapA

/-- **Packing bound for the measure of a discrete set.**
Let a countable group `G` act measurably on `α` preserving `μ`, let `D` be a fundamental domain,
`T` a `G`-invariant set and `S ⊆ T` a null-measurable subset meeting every `G`-orbit in at most `K`
points.  Then `μ S ≤ K · μ (T ∩ D)`.

The proof splits `S ∩ g • D` over the fundamental domain and converts the resulting sum over `G`
into the integral of the counting function `z ↦ #{g : g • z ∈ S}`, which is bounded by `K`. -/
theorem packMeasureLe {G α : Type*} [Group G] [MulAction G α] [MeasurableSpace α] [Countable G]
    (μ : MeasureTheory.Measure α) [MeasureTheory.SMulInvariantMeasure G α μ]
    (hmeas : ∀ g : G, Measurable (fun x : α => g • x))
    {D T S : Set α} (K : ℕ)
    (hD : MeasureTheory.IsFundamentalDomain G D μ)
    (hT : ∀ g : G, ∀ x : α, x ∈ T ↔ g • x ∈ T)
    (hST : S ⊆ T) (hS : MeasureTheory.NullMeasurableSet S μ)
    (hK : ∀ z : α, {g : G | g • z ∈ S}.Finite ∧ {g : G | g • z ∈ S}.ncard ≤ K) :
    μ S ≤ K * μ (T ∩ D) := by
  haveI hMCS : MeasurableConstSMul G α := ⟨hmeas⟩
  -- each set `{x | g • x ∈ S}` is null-measurable
  have hF : ∀ g : G, NullMeasurableSet {x : α | g • x ∈ S} μ := fun g =>
    hS.preimage (measurePreserving_smul g μ).quasiMeasurePreserving
  -- the fundamental-domain decomposition of `μ S`
  have hB : μ S = ∑' g : G, μ ((T ∩ D) ∩ {x : α | g • x ∈ S}) :=
    fundamentalDomain_measure_eq_tsum_inv μ hD hT hST
  -- the packing bound for the multiplicity-`K` family `{x | g • x ∈ S}`
  have hA : ∀ U : Set α, MeasurableSet U →
      (∑' g : G, μ (U ∩ {x : α | g • x ∈ S})) ≤ (K : ENNReal) * μ U :=
    fun U hU => tsum_measure_inter_le μ K hF hK hU
  -- for every measurable `U ⊇ T ∩ D`
  have hstep : ∀ U : Set α, (T ∩ D) ⊆ U → MeasurableSet U →
      μ S ≤ (K : ENNReal) * μ U := by
    intro U hAU hU
    rw [hB]
    calc ∑' g : G, μ ((T ∩ D) ∩ {x : α | g • x ∈ S})
        ≤ ∑' g : G, μ (U ∩ {x : α | g • x ∈ S}) :=
          ENNReal.tsum_le_tsum fun g =>
            measure_mono (Set.inter_subset_inter_left _ hAU)
      _ ≤ (K : ENNReal) * μ U := hA U hU
  -- take a measurable superset of `T ∩ D` of the same measure
  have hfin := hstep (toMeasurable μ (T ∩ D)) (subset_toMeasurable μ (T ∩ D))
      (measurableSet_toMeasurable μ (T ∩ D))
  rwa [measure_toMeasurable] at hfin

end Work.Mostow.gapA
