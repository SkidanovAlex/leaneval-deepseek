import Mathlib

namespace Work.KMTAreas.A4

/--

**Small-log absorption.**  For every `c, ρ > 0` and `Cρ, Cg > 0` there is a constant
`K > 0` (depending only on `c, ρ, Cρ, Cg`) such that

  `1 ≤ Cg · K · x ^ (-(c / ρ))`  for all `x ∈ [1, Cρ)`.

Indeed the factor `x ^ (-(c / ρ))` is decreasing in `x`, so its minimum on `[1, Cρ)`
is approached at the right endpoint; taking `K = Cρ ^ (c / ρ) / Cg` gives
`Cg · K · x ^ (-(c / ρ)) = (Cρ / x) ^ (c / ρ) ≥ 1` because `Cρ / x > 1` and `c / ρ > 0`.

This is the elementary "absorb the logarithm" step: a negative power `x ^ (-(c/ρ))`
is bounded below by a positive constant on any half-open interval `[1, Cρ)`, hence
can be absorbed into a multiplicative constant.
-/
theorem smallLogAbsorb {c ρ Cρ Cg : ℝ} (hc : 0 < c) (hρ : 0 < ρ) (hCρ : 0 < Cρ) (hCg : 0 < Cg) :
    ∃ K : NNReal, 0 < K ∧ ∀ x : ℝ, 1 ≤ x → x < Cρ → 1 ≤ Cg * (K : ℝ) * x ^ (-(c / ρ)) := by
  have hpos : 0 < Cρ ^ (c / ρ) / Cg := div_pos (Real.rpow_pos_of_pos hCρ _) hCg
  refine ⟨Real.toNNReal (Cρ ^ (c / ρ) / Cg), ?_, ?_⟩
  · rw [Real.toNNReal_pos]; exact hpos
  · intro x hx1 hx2
    rw [Real.coe_toNNReal _ (le_of_lt hpos)]
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
    have hratio : 1 ≤ Cρ / x := by
      rw [le_div_iff₀ hxpos]; linarith
    have hexp : 0 < c / ρ := div_pos hc hρ
    have h1 : 1 ≤ (Cρ / x) ^ (c / ρ) := Real.one_le_rpow hratio (le_of_lt hexp)
    have hrw : (Cρ / x) ^ (c / ρ) = Cρ ^ (c / ρ) * x ^ (-(c / ρ)) := by
      rw [Real.div_rpow (le_of_lt hCρ) (le_of_lt hxpos), Real.rpow_neg (le_of_lt hxpos)]
      ring
    calc (1 : ℝ) ≤ (Cρ / x) ^ (c / ρ) := h1
      _ = Cρ ^ (c / ρ) * x ^ (-(c / ρ)) := hrw
      _ = Cg * (Cρ ^ (c / ρ) / Cg) * x ^ (-(c / ρ)) := by field_simp

end Work.KMTAreas.A4
