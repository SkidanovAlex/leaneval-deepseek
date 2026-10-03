import Mathlib
import Submission.Work.Parab.inversion.exists_norm_sub_le_of_asymptotic

namespace Work.Parab.coordData

/-- Reading off the error of the identity approximation from the asymptotic hypothesis: if
`Φ ζ` is within `1` of `ζ - a log(-ζ) - b` for all `ζ ∈ L` with `‖ζ‖ > R`, then for such `ζ`
with `‖ζ‖ ≥ 1` we have `‖Φ ζ - ζ‖ ≤ 1 + ‖a‖ (log ‖ζ‖ + π) + ‖b‖`. -/
theorem norm_Phi_sub_id_le {Φ : ℂ → ℂ} {L : Set ℂ} {a b : ℂ} {R : ℝ}
    (hR : ∀ ζ ∈ L, R < ‖ζ‖ → ‖Φ ζ - (ζ - a * Complex.log (-ζ) - b)‖ < 1) :
    ∀ ζ ∈ L, R < ‖ζ‖ → 1 ≤ ‖ζ‖ →
      ‖Φ ζ - ζ‖ ≤ 1 + ‖a‖ * (Real.log ‖ζ‖ + Real.pi) + ‖b‖ := by
  intro ζ hζL hRζ h1
  have hclose := hR ζ hζL hRζ
  -- `‖log (-ζ)‖ ≤ log ‖ζ‖ + π`
  have hlog := Work.Parab.inversion.norm_log_le_of_one_le (-ζ) (by simpa using h1)
  rw [norm_neg] at hlog
  -- decompose `Φ ζ - ζ` into the asymptotic error plus the logarithmic correction
  have hdecomp : Φ ζ - ζ
      = (Φ ζ - (ζ - a * Complex.log (-ζ) - b)) - (a * Complex.log (-ζ) + b) := by ring
  calc ‖Φ ζ - ζ‖
      = ‖(Φ ζ - (ζ - a * Complex.log (-ζ) - b)) - (a * Complex.log (-ζ) + b)‖ := by
        rw [hdecomp]
    _ ≤ ‖Φ ζ - (ζ - a * Complex.log (-ζ) - b)‖ + ‖a * Complex.log (-ζ) + b‖ :=
        norm_sub_le _ _
    _ ≤ 1 + ‖a‖ * (Real.log ‖ζ‖ + Real.pi) + ‖b‖ := by
        have h2 : ‖a * Complex.log (-ζ) + b‖ ≤ ‖a‖ * (Real.log ‖ζ‖ + Real.pi) + ‖b‖ := by
          have h3 := norm_add_le (a * Complex.log (-ζ)) b
          rw [norm_mul] at h3
          have h4 : ‖a‖ * ‖Complex.log (-ζ)‖ ≤ ‖a‖ * (Real.log ‖ζ‖ + Real.pi) :=
            mul_le_mul_of_nonneg_left hlog (norm_nonneg a)
          linarith
        linarith

end Work.Parab.coordData
