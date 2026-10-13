import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.Honest.I4SliceDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false

/-!
# The pointwise AM–GM of the honest `I₄` slice estimate

With `s = sin θ`, `c = cos θ`, `σ = sin(2θ)^{-99/100}` and
`Σ = (1-η) cos²θ + (3+η) sin²θ` (`η = 99/100`), the target inequality

`|s σ q Ψv| ≤ ½ Σ σ q² + 50 σ (Ψv / c)²`

is, after dividing by `σ > 0`, the statement that the quadratic form
`½ Σ q² - s q Ψv + 50 (Ψv/c)²` in `(q, Ψv)` is positive semidefinite, i.e. that

`s² ≤ 4 · (Σ/2) · (50/c²)`,  equivalently  `s² c² ≤ 100 Σ`,

which holds because `Σ ≥ 3 s²` and `c² ≤ 1`.

The elementary quadratic-AM–GM fact is proved first (`quad_amgm`); the target then follows by
multiplying by `σ > 0` and rewriting `(Ψv/c)² = Ψv²/c²`.
-/

/-- **Positive-semidefinite quadratic AM–GM.** If `A, C > 0` and `s ^ 2 ≤ 4*A*C`, then
`|s * x * y| ≤ A * x ^ 2 + C * y ^ 2` for all reals `x`, `y`.

Proof: multiply the completing-square identity
`4A (A x² - s x y + C y²) = (2 A x - s y)² + (4 A C - s²) y²` by `1/(4A) > 0`, and apply it
again with `x` replaced by `-x`. -/
theorem quad_amgm (A C s x y : ℝ) (hA : 0 < A) (hC : 0 < C) (hs : s ^ 2 ≤ 4 * A * C) :
    |s * x * y| ≤ A * x ^ 2 + C * y ^ 2 := by
  have key : ∀ u v : ℝ, s * u * v ≤ A * u ^ 2 + C * v ^ 2 := by
    intro u v
    have h4 : (0 : ℝ) < 4 * A := by linarith
    have hid : 4 * A * (A * u ^ 2 + C * v ^ 2 - s * u * v)
        = (2 * A * u - s * v) ^ 2 + (4 * A * C - s ^ 2) * v ^ 2 := by ring
    have hsq : 0 ≤ (2 * A * u - s * v) ^ 2 + (4 * A * C - s ^ 2) * v ^ 2 :=
      add_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (sq_nonneg _))
    have h0 : 0 ≤ 4 * A * (A * u ^ 2 + C * v ^ 2 - s * u * v) := by rw [hid]; exact hsq
    have h1 : 0 ≤ A * u ^ 2 + C * v ^ 2 - s * u * v := (mul_nonneg_iff_of_pos_left h4).mp h0
    linarith
  refine abs_le.mpr ⟨?_, ?_⟩
  · have h := key (-x) y
    nlinarith [h]
  · exact key x y

/-- The pointwise `I₄` AM–GM estimate. -/
theorem I4AMGM (θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (q Ψv : ℝ) :
    |Real.sin θ * I4sig θ * q * Ψv|
      ≤ (1 / 2) * I4Sig θ * I4sig θ * q ^ 2
        + 50 * I4sig θ * (Ψv / Real.cos θ) ^ 2 := by
  have hσ : 0 < I4sig θ := I4sig_pos hθ
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hsin : 0 ≤ Real.sin θ :=
    le_of_lt (Real.sin_pos_of_mem_Ioo ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩)
  -- `Sig ≥ 3 s²`
  have hSig : 3 * Real.sin θ ^ 2 ≤ I4Sig θ := by
    have hs := Real.sin_sq_add_cos_sq θ
    rw [I4Sig]
    nlinarith [sq_nonneg (Real.cos θ), sq_nonneg (Real.sin θ)]
  have hc2 : Real.cos θ ^ 2 ≤ 1 := Real.cos_sq_le_one θ
  have hApos : 0 < I4Sig θ / 2 := div_pos (I4Sig_pos θ) (by norm_num)
  have hCpos : 0 < 50 / Real.cos θ ^ 2 := div_pos (by norm_num) (pow_pos hcos 2)
  -- `s² ≤ 4 · (Σ/2) · (50/c²)`, i.e. `s² c² ≤ 100 Σ`
  have hsineq : Real.sin θ ^ 2 ≤ 4 * (I4Sig θ / 2) * (50 / Real.cos θ ^ 2) := by
    have hkeq : 4 * (I4Sig θ / 2) * (50 / Real.cos θ ^ 2)
        = 100 * I4Sig θ / Real.cos θ ^ 2 := by ring
    rw [hkeq, le_div_iff₀ (pow_pos hcos 2)]
    have h1 : Real.sin θ ^ 2 * Real.cos θ ^ 2 ≤ Real.sin θ ^ 2 := by
      have := mul_le_mul_of_nonneg_left hc2 (sq_nonneg (Real.sin θ))
      simpa using this
    have h2 : Real.sin θ ^ 2 ≤ 100 * I4Sig θ := by nlinarith [hsin, hSig]
    linarith
  have hmain := quad_amgm (I4Sig θ / 2) (50 / Real.cos θ ^ 2) (Real.sin θ) q Ψv
    hApos hCpos hsineq
  have hmain' : |Real.sin θ * q * Ψv|
      ≤ (1 / 2) * I4Sig θ * q ^ 2 + 50 * (Ψv / Real.cos θ) ^ 2 := by
    have hrw : (I4Sig θ / 2) * q ^ 2 + (50 / Real.cos θ ^ 2) * Ψv ^ 2
        = (1 / 2) * I4Sig θ * q ^ 2 + 50 * (Ψv / Real.cos θ) ^ 2 := by
      rw [div_pow]; ring
    rw [hrw] at hmain
    exact hmain
  calc |Real.sin θ * I4sig θ * q * Ψv|
      = I4sig θ * |Real.sin θ * q * Ψv| := by
        rw [show Real.sin θ * I4sig θ * q * Ψv = I4sig θ * (Real.sin θ * q * Ψv) by ring,
          abs_mul, abs_of_pos hσ]
    _ ≤ I4sig θ * ((1 / 2) * I4Sig θ * q ^ 2 + 50 * (Ψv / Real.cos θ) ^ 2) :=
        mul_le_mul_of_nonneg_left hmain' (le_of_lt hσ)
    _ = (1 / 2) * I4Sig θ * I4sig θ * q ^ 2
          + 50 * I4sig θ * (Ψv / Real.cos θ) ^ 2 := by ring

end Work.FTS.EllipticEst.Honest
