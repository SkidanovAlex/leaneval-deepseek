import Mathlib

open MeasureTheory

namespace Work.Mostow.gapA

/-- The sum over `i` of the indicators `1_{s i}` evaluated at `a` equals the extended cardinality
of the set of indices `i` with `a ∈ s i`. -/
lemma tsum_indicator_eq_encard {ι α : Type*} (s : ι → Set α) (a : α) :
    (∑' i, (s i).indicator (1 : α → ENNReal) a) = (({i | a ∈ s i} : Set ι).encard : ENNReal) := by
  rw [← ENNReal.tsum_set_one ({i | a ∈ s i} : Set ι)]
  rw [tsum_subtype ({i | a ∈ s i} : Set ι) (fun _ => (1 : ENNReal))]
  apply tsum_congr
  intro i
  by_cases hi : a ∈ s i
  · rw [Set.indicator_of_mem hi, Set.indicator_of_mem (show i ∈ {i : ι | a ∈ s i} from hi)]; rfl
  · rw [Set.indicator_of_notMem hi, Set.indicator_of_notMem (show i ∉ {i : ι | a ∈ s i} from hi)]

theorem tsum_measure_inter_le {α ι : Type*} [MeasurableSpace α] [Countable ι]
    (μ : MeasureTheory.Measure α) (K : ℕ) {F : ι → Set α}
    (hF : ∀ i, MeasureTheory.NullMeasurableSet (F i) μ)
    (hK : ∀ z : α, {i : ι | z ∈ F i}.Finite ∧ {i : ι | z ∈ F i}.ncard ≤ K)
    {U : Set α} (hU : MeasurableSet U) :
    (∑' i : ι, μ (U ∩ F i)) ≤ (K : ENNReal) * μ U := by
  classical
  -- Pointwise bound: at every point `a`, the multiplicity of `a` among the `U ∩ F i` is at most
  -- `K * 1_U a`.
  have hkey : ∀ a : α,
      (∑' i : ι, (U ∩ F i).indicator (1 : α → ENNReal) a) ≤
        (K : ENNReal) * U.indicator (1 : α → ENNReal) a := by
    intro a
    by_cases ha : a ∈ U
    · rw [Set.indicator_of_mem ha]
      simp only [Pi.one_apply, mul_one]
      have hterm : ∀ i, (U ∩ F i).indicator (1 : α → ENNReal) a =
          (F i).indicator (1 : α → ENNReal) a := by
        intro i
        by_cases hi : a ∈ F i
        · rw [Set.indicator_of_mem (show a ∈ U ∩ F i from ⟨ha, hi⟩),
              Set.indicator_of_mem hi]
        · rw [Set.indicator_of_notMem (show a ∉ U ∩ F i from fun h => hi h.2),
              Set.indicator_of_notMem hi]
      simp_rw [hterm]
      rw [tsum_indicator_eq_encard]
      have hTfin : ({i : ι | a ∈ F i} : Set ι).Finite := (hK a).1
      have hTcard : ({i : ι | a ∈ F i} : Set ι).ncard ≤ K := (hK a).2
      have henc : ((({i : ι | a ∈ F i} : Set ι)).encard : ENNReal) =
          ((({i : ι | a ∈ F i} : Set ι)).ncard : ENNReal) := by
        rw [Set.ncard_eq_toFinset_card _ hTfin, Set.Finite.encard_eq_coe_toFinset_card hTfin]
        exact ENat.toENNReal_coe _
      rw [henc]
      exact Nat.cast_le.mpr hTcard
    · rw [Set.indicator_of_notMem ha, mul_zero]
      have hterm : ∀ i, (U ∩ F i).indicator (1 : α → ENNReal) a = 0 := by
        intro i
        rw [Set.indicator_of_notMem (show a ∉ U ∩ F i from fun h => ha h.1)]
      simp_rw [hterm]
      simp
  calc (∑' i : ι, μ (U ∩ F i))
      = ∑' i : ι, ∫⁻ a, (U ∩ F i).indicator (1 : α → ENNReal) a ∂μ :=
        tsum_congr fun i =>
          (lintegral_indicator_one₀ (hU.nullMeasurableSet.inter (hF i))).symm
    _ = ∫⁻ a, ∑' i : ι, (U ∩ F i).indicator (1 : α → ENNReal) a ∂μ :=
        (lintegral_tsum (fun i => AEMeasurable.indicator₀ aemeasurable_const
          (hU.nullMeasurableSet.inter (hF i)))).symm
    _ ≤ ∫⁻ a, (K : ENNReal) * U.indicator (1 : α → ENNReal) a ∂μ :=
        lintegral_mono hkey
    _ = (K : ENNReal) * μ U := by
        rw [lintegral_const_mul (K : ENNReal) (f := U.indicator (1 : α → ENNReal))
          (measurable_const.indicator hU)]
        simp only [lintegral_indicator_one hU]

end Work.Mostow.gapA
