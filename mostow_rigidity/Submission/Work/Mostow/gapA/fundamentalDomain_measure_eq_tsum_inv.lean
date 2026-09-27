import Mathlib

open scoped Pointwise

namespace Work.Mostow.gapA

/-- For a countable group `G` with an invariant measure `μ`, a fundamental domain `D`, a
`G`-invariant set `T` and a subset `S ⊆ T`, the measure of `S` is the sum, over `g : G`, of the
measure of the part of `D ∩ T` that is carried into `S` by `g`.

This is the `G`-invariant form of the standard "sum over the group" formula for fundamental
domains (`MeasureTheory.IsFundamentalDomain.measure_eq_tsum'`): the invariance of `T` turns the
`g`-indexed summand `μ (S ∩ g • D)` into `μ ((T ∩ D) ∩ {x | g • x ∈ S})`. -/
theorem fundamentalDomain_measure_eq_tsum_inv {G α : Type*} [Group G] [MulAction G α]
    [MeasurableSpace α] [Countable G] [MeasurableConstSMul G α]
    (μ : MeasureTheory.Measure α) [MeasureTheory.SMulInvariantMeasure G α μ]
    {D T S : Set α} (hD : MeasureTheory.IsFundamentalDomain G D μ)
    (hT : ∀ g : G, ∀ x : α, x ∈ T ↔ g • x ∈ T) (hST : S ⊆ T) :
    μ S = ∑' g : G, μ ((T ∩ D) ∩ {x : α | g • x ∈ S}) := by
  rw [hD.measure_eq_tsum' S]
  refine tsum_congr fun g => ?_
  -- `{x | g • x ∈ S} = g⁻¹ • S`
  have hA : {x : α | g • x ∈ S} = g⁻¹ • S := by
    ext x; rw [Set.mem_ofPred_eq, Set.mem_inv_smul_set_iff]
  -- the invariance of `T` makes the intersection with `T` redundant
  have hsub : {x : α | g • x ∈ S} ⊆ T := fun x hx => (hT g x).2 (hST hx)
  have hTDA : (T ∩ D) ∩ {x : α | g • x ∈ S} = D ∩ {x : α | g • x ∈ S} := by
    rw [Set.inter_comm T D, Set.inter_assoc, Set.inter_eq_right.mpr hsub]
  rw [hTDA, hA]
  -- `μ (D ∩ g⁻¹ • S) = μ (g • (D ∩ g⁻¹ • S)) = μ (g • D ∩ S) = μ (S ∩ g • D)`
  rw [← MeasureTheory.measure_smul (μ := μ) g (D ∩ g⁻¹ • S), Set.smul_set_inter, smul_inv_smul,
    Set.inter_comm]

end Work.Mostow.gapA
