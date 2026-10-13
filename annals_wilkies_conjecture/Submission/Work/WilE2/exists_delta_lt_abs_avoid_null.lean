import Mathlib
import Submission.Work.WilE2.exists_pos_lt_abs_of_isCompact

set_option linter.unusedVariables false

namespace Work.WilE2

theorem exists_delta_lt_abs_avoid_null {m : ℕ} (V : (Fin m → ℝ) → (Fin (m - 1) → ℝ))
    (g ψ : (Fin m → ℝ) → ℝ)
    (hV : ContDiff ℝ 1 V) (hg : ContDiff ℝ 1 g) (hψc : Continuous ψ)
    (hC : IsCompact {z | V z = 0})
    (hnd : ∀ z, V z = 0 → g z = 0 → ψ z ≠ 0)
    (K : Set ℝ) (hK : MeasureTheory.volume K = 0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ∉ K ∧ ∀ z, V z = 0 → g z = 0 → δ < |ψ z| := by
  -- The zero set `{V = 0} ∩ {g = 0}` is compact: `{V = 0}` is compact and `{g = 0}` is closed.
  have hgc : Continuous g := hg.continuous
  have hKc : IsCompact ({z : Fin m → ℝ | V z = 0} ∩ {z : Fin m → ℝ | g z = 0}) :=
    hC.inter_right (isClosed_eq hgc continuous_const)
  -- `ψ` is nonzero on this compact set, so `|ψ|` has a positive lower bound there.
  have hnd' : ∀ z ∈ ({z : Fin m → ℝ | V z = 0} ∩ {z : Fin m → ℝ | g z = 0}),
      ψ z ≠ 0 :=
    fun z hz => hnd z hz.1 hz.2
  obtain ⟨c, hcpos, hc⟩ := exists_pos_lt_abs_of_isCompact hKc hψc hnd'
  -- Since `K` is null, the interval `(0, c)` (of positive measure) is not contained in `K`.
  have hex : ∃ δ ∈ Set.Ioo (0 : ℝ) c, δ ∉ K := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    have hsub : Set.Ioo (0 : ℝ) c ⊆ K := h
    have hm : MeasureTheory.volume (Set.Ioo (0 : ℝ) c) ≤ MeasureTheory.volume K :=
      MeasureTheory.measure_mono hsub
    rw [hK] at hm
    rw [Real.volume_Ioo, sub_zero] at hm
    have hpos : (0 : ENNReal) < ENNReal.ofReal c := ENNReal.ofReal_pos.mpr hcpos
    exact (not_le_of_gt hpos) hm
  obtain ⟨δ, hδ, hδK⟩ := hex
  exact ⟨δ, hδ.1, hδK, fun z hVz hgz => lt_trans hδ.2 (hc z ⟨hVz, hgz⟩)⟩

end Work.WilE2
