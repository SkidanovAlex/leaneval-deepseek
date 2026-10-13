import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- `π` must be the real number `Real.pi` (the file is built with `autoImplicit = false`,
-- so without this the notation is not even in scope).
open scoped Real

namespace Work.H2.T1Q

/-- In either singular window `θ ∈ (ζ/2, ζ)` or `θ ∈ (π/2 - ζ, π/2 - ζ/2)` (`ζ > 0`) one has
`|sin(2θ)| ≤ 2ζ`, hence `|sin(2θ)|·(2/ζ) ≤ 4`.

Both windows are images of `(ζ/2, ζ)` under `t ↦ t` resp. `t ↦ π/2 - t`, and on either the
argument `2θ` of the sine has modulus `≤ 2ζ`; the conclusion follows from `|sin x| ≤ |x|`. -/
theorem SinRatioBound {ζ θ : ℝ} (hζ : 0 < ζ)
    (h : (ζ / 2 < θ ∧ θ < ζ) ∨ (π / 2 - ζ < θ ∧ θ < π / 2 - ζ / 2)) :
    |Real.sin (2 * θ)| * (2 / ζ) ≤ 4 := by
  have hsin : |Real.sin (2 * θ)| ≤ 2 * ζ := by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · -- First window: `0 < 2θ < 2ζ`.
      have habs : |2 * θ| ≤ 2 * ζ := by
        rw [abs_of_pos (by linarith : (0 : ℝ) < 2 * θ)]
        linarith
      calc |Real.sin (2 * θ)| ≤ |2 * θ| := Real.abs_sin_le_abs
        _ ≤ 2 * ζ := habs
    · -- Second window: reflections of the first, `sin(π - x) = sin x`.
      have hkey : 2 * θ = π - 2 * (π / 2 - θ) := by ring
      have hsin2 : Real.sin (2 * θ) = Real.sin (2 * (π / 2 - θ)) := by
        rw [hkey, Real.sin_pi_sub]
      have habs : |2 * (π / 2 - θ)| ≤ 2 * ζ := by
        rw [abs_of_pos (by linarith : (0 : ℝ) < 2 * (π / 2 - θ))]
        linarith
      calc |Real.sin (2 * θ)| = |Real.sin (2 * (π / 2 - θ))| := by rw [hsin2]
        _ ≤ |2 * (π / 2 - θ)| := Real.abs_sin_le_abs
        _ ≤ 2 * ζ := habs
  have hfac : 0 ≤ 2 / ζ := by positivity
  calc |Real.sin (2 * θ)| * (2 / ζ) ≤ (2 * ζ) * (2 / ζ) :=
        mul_le_mul_of_nonneg_right hsin hfac
    _ = 4 := by field_simp; norm_num

end Work.H2.T1Q
