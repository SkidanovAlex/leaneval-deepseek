import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.SliceMassUpgrade

/-- Upgrade of an almost-everywhere finiteness statement for a slice mass to a pointwise one,
using the two-sided growth bound `M z₂ ≤ 2 * M z₁ + K` (`K` finite) along `(0, ∞)`.

If some `z₀ > 0` had `M z₀ = ⊤`, then for every `z ∈ (0, z₀]` the bound
`⊤ = M z₀ ≤ 2 * M z + K` forces `M z = ⊤` (as `K < ⊤`), so the whole interval `(0, z₀]`
— of positive measure — would consist of points where `M` is infinite, contradicting
a.e. finiteness. -/
theorem sliceMass_ae_finite_upgrade {M : ℝ → ENNReal} {K : ENNReal} (hK : K < ⊤)
    (haefin : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)), M z < ⊤)
    (hup : ∀ z₁ z₂ : ℝ, 0 < z₁ → z₁ ≤ z₂ → M z₂ ≤ 2 * M z₁ + K) :
    ∀ z ∈ Set.Ioi 0, M z < ⊤ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨z₀, hz₀pos, hz₀top⟩ := hcon
  have hz₀eq : M z₀ = ⊤ := top_le_iff.mp hz₀top
  have hnull : (MeasureTheory.volume.restrict (Set.Ioi 0)) {z : ℝ | ¬ M z < ⊤} = 0 :=
    MeasureTheory.ae_iff.mp haefin
  have hsub : Set.Ioc 0 z₀ ⊆ {z : ℝ | ¬ M z < ⊤} := by
    intro z hz hzlt
    have hle := hup z z₀ hz.1 hz.2
    rw [hz₀eq] at hle
    have hsum : (2 : ENNReal) * M z + K = ⊤ := top_le_iff.mp hle
    rw [ENNReal.add_eq_top] at hsum
    rcases hsum with h2 | hKtop
    · rw [ENNReal.mul_eq_top] at h2
      rcases h2 with ⟨-, htop⟩ | ⟨htop, -⟩
      · exact absurd htop (ne_of_lt hzlt)
      · exact absurd htop (by norm_num)
    · exact absurd hKtop (ne_of_lt hK)
  have hzero : (MeasureTheory.volume.restrict (Set.Ioi 0)) (Set.Ioc 0 z₀) = 0 :=
    MeasureTheory.measure_mono_null hsub hnull
  have hpos : (MeasureTheory.volume.restrict (Set.Ioi 0)) (Set.Ioc 0 z₀) ≠ 0 := by
    rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioc]
    have hinter : Set.Ioc (0 : ℝ) z₀ ∩ Set.Ioi 0 = Set.Ioc 0 z₀ :=
      Set.inter_eq_left.mpr Set.Ioc_subset_Ioi_self
    rw [hinter, Real.volume_Ioc]
    exact ne_of_gt (by simpa using ENNReal.ofReal_pos.mpr hz₀pos)
  exact hpos hzero

end Work.FTS.ClassCHon.SliceMassUpgrade
