import Mathlib
import Submission.Work.EKLRelCross.propor_aux
import Submission.Work.EKLRelCross.measurableSet_nu_compact_lt

namespace Work.EKLRelCross

open MeasureTheory

theorem ae_recurs_levels
    {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    {U : Subgroup Work.EKLContract.SL3}
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' : Set Work.EKLContract.X3} (hL : Work.EKLContract.IsLeafwise μ U ν X')
    {T : Work.EKLContract.X3 → Work.EKLContract.X3} (hT : MeasureTheory.MeasurePreserving T μ μ)
    {ι : Type} [Countable ι] {G : ι → Set Work.EKLContract.X3}
    (hGmeas : ∀ i, MeasurableSet (G i)) (hGcover : μ (⋃ i, G i)ᶜ = 0)
    {K : Set Work.EKLContract.SL3} (hK : IsCompact K) :
    ∀ᵐ x ∂μ, ∃ (i : ι) (M : ℕ), ∀ N : ℕ, ∃ n ≥ N,
      T^[n] x ∈ X' ∧ T^[n] x ∈ G i ∧ ν (T^[n] x) K < (M : ENNReal) := by
  classical
  -- The countable family of "levels": the `i`-th covering set intersected with the `M`-th
  -- truncation of the mass `ν x K` on the leafwise domain `X'`.
  set D : ι × ℕ → Set Work.EKLContract.X3 :=
    fun p => G p.1 ∩ {x : Work.EKLContract.X3 | x ∈ X' ∧ ν x K < (p.2 : ENNReal)} with hD
  have hDmeas : ∀ p : ι × ℕ, MeasurableSet (D p) := by
    rintro ⟨i, M⟩
    exact (hGmeas i).inter (measurableSet_nu_compact_lt hL hK (M : ENNReal))
  -- The union of the levels contains `(⋃ i, G i) ∩ X'`, hence is conull.
  have hsub : (⋃ i, G i) ∩ X' ⊆ ⋃ p : ι × ℕ, D p := by
    rintro x ⟨hxG, hxX⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxG
    have hlt : ν x K < ⊤ := by
      haveI := hL.radon x hxX
      exact hK.measure_lt_top
    obtain ⟨M, hM⟩ := ENNReal.exists_nat_gt hlt.ne
    exact Set.mem_iUnion.mpr ⟨(i, M), hi, hxX, hM⟩
  have hcover : μ (⋃ p : ι × ℕ, D p)ᶜ = 0 := by
    have h0 : μ ((⋃ i, G i) ∩ X')ᶜ = 0 := by
      rw [Set.compl_inter]
      refine le_antisymm ?_ zero_le
      calc μ ((⋃ i, G i)ᶜ ∪ X'ᶜ)
          ≤ μ (⋃ i, G i)ᶜ + μ X'ᶜ := measure_union_le _ _
        _ = 0 := by rw [hGcover, hL.conull, add_zero]
    exact measure_mono_null (Set.compl_subset_compl.mpr hsub) h0
  -- Poincaré recurrence with a uniform level.
  filter_upwards [ae_exists_level_frequently μ hT hDmeas hcover] with x hx
  obtain ⟨⟨i, M⟩, hM⟩ := hx
  exact ⟨i, M, fun N => by
    obtain ⟨n, hn, hxn⟩ := hM N
    exact ⟨n, hn, hxn.2.1, hxn.1, hxn.2.2⟩⟩

end Work.EKLRelCross
