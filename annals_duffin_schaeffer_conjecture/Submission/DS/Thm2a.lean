import Submission.DS.Bound

open scoped Nat ENNReal NNReal
open Set MeasureTheory
open DuffinSchaefferConjecture

namespace Submission.DS

/-- **Theorem 2(a)** (Catlin, convergence half): if `∑' q, ψ_star ψ q < ∞` then `𝒦 ψ`
has Lebesgue measure zero (and is measurable). -/
theorem theorem_2_a_core (ψ : ℕ+ → ℝ≥0) (hψ : (∑' q : ℕ+, ψ_star ψ q) < ∞) :
    MeasurableSet (𝒦 ψ) ∧ volume (𝒦 ψ) = 0 := by
  have hConv : Conv ψ := hψ
  constructor
  · exact measurableSet_K ψ
  · let L : Set ℝ := limsupDenoms (Cq (rho ψ))
    let A : ℕ+ → Set ℝ := fun q => Cq (rho ψ) q ∩ Set.Icc 0 1
    have hK01 : 𝒦 ψ ⊆ Set.Icc 0 1 := by
      intro x hx
      exact ((mem_K_iff ψ x).1 hx).1
    have hsubK : 𝒦 ψ ⊆ (L ∩ Set.Icc 0 1) ∪ ratSet := by
      intro x hx
      rcases K_subset_limsupC_union_rat ψ hConv hx with hxL | hxr
      · exact Or.inl ⟨by simpa [L] using hxL, hK01 hx⟩
      · exact Or.inr hxr
    have hLA : L ∩ Set.Icc 0 1 ⊆ limsupDenoms A := by
      intro x hx
      have hxinf : {q | x ∈ Cq (rho ψ) q}.Infinite := by
        simpa [L, limsupDenoms] using hx.1
      have hx01 : x ∈ Set.Icc 0 1 := hx.2
      refine Set.Infinite.mono ?_ hxinf
      intro q hq
      exact ⟨hq, hx01⟩
    have hsub2 : 𝒦 ψ ⊆ limsupDenoms A ∪ ratSet := by
      intro x hx
      rcases hsubK hx with hxLI | hxr
      · exact Or.inl (hLA hxLI)
      · exact Or.inr hxr
    have hsum_le : (∑' q : ℕ+, volume (A q)) ≤ (∑' q : ℕ+, (4 : ℝ≥0∞) * ψ_star ψ q) := by
      refine ENNReal.tsum_le_tsum ?_
      intro q
      simpa [A] using measure_Cq_inter_Icc_le ψ hConv q
    have hsum_fin : (∑' q : ℕ+, (4 : ℝ≥0∞) * ψ_star ψ q) < ∞ := by
      rw [ENNReal.tsum_mul_left]
      exact ENNReal.mul_lt_top (by norm_num : (4 : ℝ≥0∞) < ∞) hψ
    have hsum : (∑' q : ℕ+, volume (A q)) ≠ ∞ := ne_of_lt (hsum_le.trans_lt hsum_fin)
    have hvolA : volume (limsupDenoms A) = 0 := volume_infinite_mem_eq_zero hsum
    have hvolK : volume (𝒦 ψ) ≤ volume (limsupDenoms A) + volume ratSet := by
      exact (measure_mono hsub2).trans (measure_union_le (limsupDenoms A) ratSet)
    have hvol0 : volume (𝒦 ψ) ≤ 0 := by
      calc
        volume (𝒦 ψ) ≤ volume (limsupDenoms A) + volume ratSet := hvolK
        _ = 0 + 0 := by rw [hvolA, ratSet_volume_zero]
        _ = 0 := by simp
    exact le_antisymm hvol0 bot_le

end Submission.DS
