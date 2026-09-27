import Mathlib
import Submission.Work.EKLComp.PlaqueToolkit

/-!
# `Work.EKLProd.null_transfer`

Transfer of `μ`-nullity to leafwise nullity along an orbit plaque.

`Work.EKLComp.leafwise_null_local` (in `PlaqueToolkit`) proves the local form of Pisa §8.9 for a
*measurable* `μ`-null set `N`.  Here the hypothesis is only that the restriction of `μ` to the
plaque `P = (u ↦ u • x₀) '' (V ε ∩ H)` gives `N` outer measure zero, with no measurability
assumption on `N`.  The bridge is Mathlib's `exists_measurable_superset_of_null`: a measurable
superset `M ⊇ N ∩ P` of `μ`-measure zero contains every point of `N ∩ P`, so the leafwise slice
`{u | u • x ∈ N ∩ P}` is contained in the `νH x`-null slice of `M ∩ P`, and monotonicity of the
outer measure finishes the argument.
-/

namespace Work.EKLProd

theorem null_transfer {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ] {H : Subgroup Work.EKLContract.SL3} {νH : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {XH : Set Work.EKLContract.X3} (hνH : Work.EKLContract.IsLeafwise μ H νH XH) {x₀ : Work.EKLContract.X3} {ε : ℝ} (hε : 0 < ε) (hHc : IsClosed (H : Set Work.EKLContract.SL3)) (hinj : ∀ h₁ ∈ H, ∀ h₂ ∈ H, h₁ • x₀ = h₂ • x₀ → h₁ = h₂) (hP : μ (Work.EKLComp.orbitPlaque H x₀ ε) ≠ 0) {N : Set Work.EKLContract.X3} (hN : (μ.restrict (Work.EKLComp.orbitPlaque H x₀ ε)) N = 0) :
    ∀ᵐ x ∂(μ.restrict (Work.EKLComp.orbitPlaque H x₀ ε)), νH x {u : Work.EKLContract.SL3 | u • x ∈ N ∩ Work.EKLComp.orbitPlaque H x₀ ε} = 0 := by
  -- the plaque is Borel, so restricting to it is harmless
  have hPmeas : MeasurableSet (Work.EKLComp.orbitPlaque H x₀ ε) :=
    Work.EKLProd.borelOrbitImage H hHc x₀ ε
  have hnull : μ (N ∩ Work.EKLComp.orbitPlaque H x₀ ε) = 0 := by
    rw [MeasureTheory.Measure.restrict_apply' hPmeas] at hN
    exact hN
  -- replace `N ∩ P` by a measurable `μ`-null superset `M`
  obtain ⟨M, hNM, hMmeas, hMzero⟩ := MeasureTheory.exists_measurable_superset_of_null hnull
  have hae := Work.EKLComp.leafwise_null_local hνH hε hHc hinj hP hMmeas hMzero
  filter_upwards [hae] with x hx
  have hsub : {u : Work.EKLContract.SL3 | u • x ∈ N ∩ Work.EKLComp.orbitPlaque H x₀ ε} ⊆
      {u : Work.EKLContract.SL3 | u • x ∈ M ∩ Work.EKLComp.orbitPlaque H x₀ ε} :=
    fun u hu => ⟨hNM ⟨hu.1, hu.2⟩, hu.2⟩
  exact le_antisymm (le_trans (MeasureTheory.measure_mono hsub) (le_of_eq hx)) zero_le

end Work.EKLProd
