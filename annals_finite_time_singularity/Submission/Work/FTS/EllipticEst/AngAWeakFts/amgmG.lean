/-
Copyright: work module for the Elgindi finite-time singularity project.

# The weighted AM–GM bound for the cross term `G` of the `cos²(2θ)` Hardy argument

For every `η ≥ 0`, every `f : ℝ → ℝ` and every `θ ∈ Iθ = [0, π/2]`,

  `|G θ| ≤ ((1+η)/2) · L θ + (1/(2(1+η))) · D θ`,

where

* `G θ = f' θ · f θ · cos(2θ) · sin(2θ)^{-(1+η)}` is the cross term,
* `L θ = f θ² cos²(2θ) sin(2θ)^{-(2+η)}` is the left hand integrand,
* `D θ = f' θ² sin(2θ)^{-η}` is the right hand integrand.

The proof is the weighted AM–GM inequality `2uv ≤ t u² + v²/t` applied with
`u = |f θ cos(2θ)| sin(2θ)^{-(1+η/2)}` (so `u² = L θ`) and
`v = |f' θ| sin(2θ)^{-η/2}` (so `v² = D θ`), `t = 1 + η`.

Nothing about `f` is assumed: the inequality is pointwise and holds for arbitrary values of
`f θ` and `deriv f θ`.  The only rpow algebra needed is the multiplicativity of `x ^ (·)` at a
*nonnegative* base, which Mathlib provides as `Real.rpow_add'` and `Real.rpow_mul` — these have
no positivity requirement on the base, so the degenerate endpoints `θ = 0, π/2` (where
`sin(2θ) = 0`) need no separate treatment.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllipticEst.AngAWeakFts.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngAWeakFts

/-- The two-variable weighted AM–GM inequality: `|A·B| ≤ (t/2)A² + (1/(2t))B²` for `t > 0`.
It is `2uv ≤ t u² + v²/t` with `u = |A|`, `v = |B|`, read off the square `(t u - v)² ≥ 0`. -/
lemma amgm_abs_mul (t A B : ℝ) (ht : 0 < t) :
    |A * B| ≤ t / 2 * A ^ 2 + 1 / (2 * t) * B ^ 2 := by
  have htne : t ≠ 0 := ne_of_gt ht
  have hmain : 2 * |A| * |B| ≤ t * A ^ 2 + B ^ 2 / t := by
    have h2 : 2 * |A| * |B| * t ≤ t ^ 2 * A ^ 2 + B ^ 2 := by
      have h := two_mul_le_add_sq (t * |A|) |B|
      have hA : |A| * |A| = A * A := by rw [← pow_two, sq_abs, pow_two]
      have hB : |B| * |B| = B * B := by rw [← pow_two, sq_abs, pow_two]
      nlinarith [h, hA, hB]
    have h3 : (t ^ 2 * A ^ 2 + B ^ 2) / t = t * A ^ 2 + B ^ 2 / t := by field_simp
    rw [← h3]
    exact (le_div_iff₀ ht).mpr h2
  calc |A * B| = |A| * |B| := abs_mul A B
    _ ≤ t / 2 * A ^ 2 + 1 / (2 * t) * B ^ 2 := by
        have key : 2 * (t / 2 * A ^ 2 + 1 / (2 * t) * B ^ 2) = t * A ^ 2 + B ^ 2 / t := by
          field_simp
        linarith [hmain, key]

/-- The pointwise weighted AM–GM bound, in the raw variables
`s = sin(2θ)`, `c = cos(2θ)`, `x = f θ`, `y = f' θ`:

  `|y x c s^{-(1+η)}| ≤ ((1+η)/2) x² c² s^{-(2+η)} + (1/(2(1+η))) y² s^{-η}`

for `η ≥ 0` and `s ≥ 0`.  The square roots of the two summands are
`u = |x c| s^{-(1+η/2)}` and `v = |y| s^{-η/2}`. -/
lemma amgmG_aux (η s x y c : ℝ) (hη : 0 ≤ η) (hs : 0 ≤ s) :
    |y * x * c * s ^ (-(1 + η))|
      ≤ ((1 + η) / 2) * (x ^ 2 * c ^ 2 * s ^ (-(2 + η)))
        + (1 / (2 * (1 + η))) * (y ^ 2 * s ^ (-η)) := by
  have ht : 0 < 1 + η := by linarith
  set A := |x| * |c| * s ^ (-(1 + η / 2)) with hA
  set B := |y| * s ^ (-(η / 2)) with hB
  have hAn : 0 ≤ A := by
    rw [hA]; exact mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (Real.rpow_nonneg hs _)
  have hBn : 0 ≤ B := by
    rw [hB]; exact mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hs _)
  have hsa : |s ^ (-(1 + η / 2))| = s ^ (-(1 + η / 2)) := abs_of_nonneg (Real.rpow_nonneg hs _)
  have hsb : |s ^ (-(η / 2))| = s ^ (-(η / 2)) := abs_of_nonneg (Real.rpow_nonneg hs _)
  have hsum1 : s ^ (-(1 + η / 2) + -(η / 2)) = s ^ (-(1 + η / 2)) * s ^ (-(η / 2)) :=
    Real.rpow_add' hs (by linarith)
  have hG : |y * x * c * s ^ (-(1 + η))| = A * B := by
    have harg : -(1 + η) = -(1 + η / 2) + -(η / 2) := by ring
    rw [harg, hsum1, hA, hB]
    simp only [abs_mul, hsa, hsb]
    ring
  have hq : (s ^ (-(1 + η / 2))) ^ (2 : ℕ) = s ^ (-(2 + η)) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hs]
    congr 1
    ring
  have hA2 : A ^ 2 = x ^ 2 * c ^ 2 * s ^ (-(2 + η)) := by
    rw [hA, mul_pow, mul_pow, hq, sq_abs, sq_abs]
  have hq2 : (s ^ (-(η / 2))) ^ (2 : ℕ) = s ^ (-η) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hs]
    congr 1
    ring
  have hB2 : B ^ 2 = y ^ 2 * s ^ (-η) := by
    rw [hB, mul_pow, hq2, sq_abs]
  have hAB := amgm_abs_mul (1 + η) A B ht
  calc |y * x * c * s ^ (-(1 + η))| = A * B := hG
    _ = |A * B| := (abs_of_nonneg (mul_nonneg hAn hBn)).symm
    _ ≤ (1 + η) / 2 * A ^ 2 + 1 / (2 * (1 + η)) * B ^ 2 := hAB
    _ = ((1 + η) / 2) * (x ^ 2 * c ^ 2 * s ^ (-(2 + η)))
          + (1 / (2 * (1 + η))) * (y ^ 2 * s ^ (-η)) := by rw [hA2, hB2]

theorem amgmG (η : ℝ) (hη0 : 0 ≤ η) (f : ℝ → ℝ) :
    ∀ θ ∈ Work.Spaces.Iθ,
      |Work.FTS.EllipticEst.AngAWeak.hardyFtsG η f θ|
        ≤ ((1 + η) / 2) * Work.FTS.EllipticEst.AngAWeak.hardyFtsL η f θ
          + (1 / (2 * (1 + η))) * Work.FTS.EllipticEst.AngAWeak.hardyFtsD η f θ := by
  intro θ hθ
  unfold Work.FTS.EllipticEst.AngAWeak.hardyFtsG Work.FTS.EllipticEst.AngAWeak.hardyFtsL
    Work.FTS.EllipticEst.AngAWeak.hardyFtsD
  exact amgmG_aux η (Real.sin (2 * θ)) (f θ) (deriv f θ) (Real.cos (2 * θ))
    hη0 (Work.FTS.EllipticEst.AngAWeak.hardyFts_sin_nonneg hθ)

end Work.FTS.EllipticEst.AngAWeakFts
