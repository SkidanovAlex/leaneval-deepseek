import Mathlib

namespace Work.WilE2

theorem exists_pos_lt_abs_of_isCompact {m : ℕ} {K : Set (Fin m → ℝ)} {ψ : (Fin m → ℝ) → ℝ}
    (hK : IsCompact K) (hψ : Continuous ψ) (h : ∀ z ∈ K, ψ z ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ K, δ < |ψ z| := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · subst hKe
    exact ⟨1, one_pos, by simp⟩
  · obtain ⟨x, hxK, hxmin⟩ := hK.exists_isMinOn hKne hψ.abs.continuousOn
    have hpos : 0 < |ψ x| := abs_pos.mpr (h x hxK)
    refine ⟨|ψ x| / 2, half_pos hpos, fun z hz => ?_⟩
    have hle : |ψ x| ≤ |ψ z| := hxmin hz
    linarith

end Work.WilE2
