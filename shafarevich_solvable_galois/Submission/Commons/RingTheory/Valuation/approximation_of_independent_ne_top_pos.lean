import Mathlib
import Submission.Commons.RingTheory.Valuation.ValuationSubring.sup_eq_top_approximation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.RingTheory.Valuation

/-- **Weak approximation for two independent valuation subrings.**

If `C₁` and `C₂` are valuation subrings of a field `F`, both different from `⊤`, and no proper
valuation subring of `F` contains both, then the diagonal map `F → F/c₁m₁ × F/c₂m₂` is surjective:
for arbitrary elements `a₁`, `a₂` and arbitrary positive radii `γ₁`, `γ₂` there is a `z` that is
`γ₁`-close to `a₁` for the valuation of `C₁` and `γ₂`-close to `a₂` for the valuation of `C₂`.

The proof reduces to the "Chinese remainder" statement
`C₁ ⊔ C₂ = ⊤ → ∃ u w, v₁ u < v₁ c₁ ∧ v₂ w < v₂ c₂ ∧ u + w = 1`
(`Commons.RingTheory.Valuation.ValuationSubring.sup_eq_top_approximation`): choosing `cᵢ` with
`v₁ c₁ = γ₁ / v₁ (a₂ - a₁)` and `v₂ c₂ = γ₂ / v₂ (a₂ - a₁)` (possible since the valuations are
surjective) and setting `z = a₁ + (a₂ - a₁) · u` gives the claim. -/
theorem approximation_of_independent_ne_top_pos {F : Type*} [Field F] (C₁ C₂ : ValuationSubring F)
    (h₁ : C₁ ≠ ⊤) (h₂ : C₂ ≠ ⊤)
    (hind : ∀ D : ValuationSubring F, C₁ ≤ D → C₂ ≤ D → D = ⊤) (a₁ a₂ : F)
    (γ₁ : C₁.ValueGroup) (γ₂ : C₂.ValueGroup) (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) :
    ∃ z : F, C₁.valuation (z - a₁) < γ₁ ∧ C₂.valuation (z - a₂) < γ₂ := by
  by_cases ha : a₁ = a₂
  · refine ⟨a₁, ?_, ?_⟩
    · rw [sub_self, Valuation.map_zero]; exact hγ₁
    · rw [ha, sub_self, Valuation.map_zero]; exact hγ₂
  have hAB : C₁ ⊔ C₂ = ⊤ := hind (C₁ ⊔ C₂) le_sup_left le_sup_right
  have ht : a₂ - a₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  have hvt₁ : C₁.valuation (a₂ - a₁) ≠ 0 :=
    fun h => ht ((Valuation.zero_iff C₁.valuation).mp h)
  have hvt₂ : C₂.valuation (a₂ - a₁) ≠ 0 :=
    fun h => ht ((Valuation.zero_iff C₂.valuation).mp h)
  obtain ⟨c₁, hc₁⟩ := C₁.valuation_surjective (γ₁ / C₁.valuation (a₂ - a₁))
  obtain ⟨c₂, hc₂⟩ := C₂.valuation_surjective (γ₂ / C₂.valuation (a₂ - a₁))
  have hc₁ne : c₁ ≠ 0 := by
    intro h
    rw [h, Valuation.map_zero] at hc₁
    exact (div_ne_zero (ne_of_gt hγ₁) hvt₁) hc₁.symm
  have hc₂ne : c₂ ≠ 0 := by
    intro h
    rw [h, Valuation.map_zero] at hc₂
    exact (div_ne_zero (ne_of_gt hγ₂) hvt₂) hc₂.symm
  obtain ⟨u, w, hu, hw, huw⟩ :=
    ValuationSubring.sup_eq_top_approximation C₁ C₂ hAB h₁ h₂ c₁ c₂ hc₁ne hc₂ne
  refine ⟨a₁ + (a₂ - a₁) * u, ?_, ?_⟩
  · have hz : a₁ + (a₂ - a₁) * u - a₁ = (a₂ - a₁) * u := by ring
    rw [hz, Valuation.map_mul]
    have hpos : 0 < C₁.valuation (a₂ - a₁) := lt_of_le_of_ne' zero_le hvt₁
    calc C₁.valuation (a₂ - a₁) * C₁.valuation u
        < C₁.valuation (a₂ - a₁) * C₁.valuation c₁ := mul_lt_mul_of_pos_left hu hpos
      _ = γ₁ := by rw [hc₁, mul_div_cancel₀ γ₁ hvt₁]
  · have hz : a₁ + (a₂ - a₁) * u - a₂ = -((a₂ - a₁) * w) := by
      linear_combination (a₂ - a₁) * huw
    rw [hz, Valuation.map_neg, Valuation.map_mul]
    have hpos : 0 < C₂.valuation (a₂ - a₁) := lt_of_le_of_ne' zero_le hvt₂
    calc C₂.valuation (a₂ - a₁) * C₂.valuation w
        < C₂.valuation (a₂ - a₁) * C₂.valuation c₂ := mul_lt_mul_of_pos_left hw hpos
      _ = γ₂ := by rw [hc₂, mul_div_cancel₀ γ₂ hvt₂]

end Commons.RingTheory.Valuation
