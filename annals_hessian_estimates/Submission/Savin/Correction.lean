/-
# Restoring the `σ₂ = 1` constraint on a nearly-solution Hessian

In the proof of Savin's Proposition 4.1 (improvement of flatness) one produces, for a solution `Φ`
of `s2 (N + D²Φ) = 1`, a quadratic `Q` whose Hessian `M` solves the *linearised* equation
`tr (cofOp N ∘ M) = 0` (the equation of the limit, which is `s2 (N + ε • M) = 1` to first order in
`ε`).  To obtain an honest quadratic solution one corrects `M` by a multiple of the identity so
that `s2` returns to `1`:

  `s2 (N + ε • (M + λ • 1)) = 1`.

Since `s2 (T + μ • 1) = s2 T + 3 μ trOp T + 6 μ²` (`s2_sub_smul_one`), the equation for
`μ = ε λ` is the quadratic `6 μ² + 3 A μ + ε² s2 M = 0` with `A = trOp N + ε trOp M`, whose root
near `0` is `μ = (-3A + √(9A² - 24 ε² s2 M)) / 12`.  This file solves that equation exactly and
records the two facts needed downstream:

* `|λ| ≤ 2 ε |s2 M| / (3 A)` (so the correction disappears as `ε → 0`),
* `trOp (N + ε • (M + λ • 1)) = √(9A² - 24 ε² s2 M) / 3 > 0` (the positive branch is preserved).
-/
import Mathlib
import ChallengeDeps
import Submission.Savin.HolderScale

open Metric MeasureTheory Filter
open scoped BigOperators RealInnerProductSpace Topology ENNReal Pointwise

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

noncomputable section

/-- `s2` of a translation of the identity: `s2 (T + mu • 1) = s2 T + 3 mu trOp T + 6 mu ^ 2`. -/
theorem s2_add_smul_one (mu : ℝ) (T : ℝ⁴ →L[ℝ] ℝ⁴) :
    s2 (T + mu • (1 : ℝ⁴ →L[ℝ] ℝ⁴)) = s2 T + 3 * mu * trOp T + 6 * mu ^ 2 := by
  have hD : (-mu) • (1 : ℝ⁴ →L[ℝ] ℝ⁴) = -(mu • (1 : ℝ⁴ →L[ℝ] ℝ⁴)) :=
    neg_smul mu (1 : ℝ⁴ →L[ℝ] ℝ⁴)
  have h1 : T + mu • (1 : ℝ⁴ →L[ℝ] ℝ⁴) = T - (-mu) • (1 : ℝ⁴ →L[ℝ] ℝ⁴) := by
    rw [hD]; abel
  rw [h1, s2_sub_smul_one]; ring

/-- **Restoring the equation.**  Let `N` be a solution (`s2 N = 1`, `trOp N > 0`), `M` a symmetric
operator in the kernel of the linearised operator (`pairOp (cofOp N) M = 0`), and `ε ≥ 0`.  If the
discriminant is strictly positive, there is a correction `lam` with

  `s2 (N + ε • (M + lam • 1)) = 1`, `trOp (N + ε • (M + lam • 1)) > 0`,
  `|lam| ≤ 2 ε |s2 M| / (3 (trOp N + ε trOp M))`. -/
theorem exists_correct_s2 {N M : ℝ⁴ →L[ℝ] ℝ⁴} (hN : N.IsSymmetric) (hM : M.IsSymmetric)
    (hN1 : s2 N = 1) (htrN : 0 < trOp N) (hMC : pairOp (cofOp N) M = 0)
    {ε : ℝ} (hε : 0 ≤ ε) (hA : 0 < trOp N + ε * trOp M)
    (hD : 0 < 9 * (trOp N + ε * trOp M) ^ 2 - 24 * ε ^ 2 * s2 M) :
    ∃ lam : ℝ, s2 (N + ε • (M + lam • (1 : ℝ⁴ →L[ℝ] ℝ⁴))) = 1 ∧
      0 < trOp (N + ε • (M + lam • (1 : ℝ⁴ →L[ℝ] ℝ⁴))) ∧
      |lam| ≤ 2 * ε * |s2 M| / (3 * (trOp N + ε * trOp M)) := by
  rcases eq_or_lt_of_le hε with hε0 | hεpos
  · subst hε0
    have hN0 : N + (0 : ℝ) • (M + (0 : ℝ) • (1 : ℝ⁴ →L[ℝ] ℝ⁴)) = N := by
      conv_lhs => rw [zero_smul ℝ (M + (0 : ℝ) • (1 : ℝ⁴ →L[ℝ] ℝ⁴))]
      rw [add_zero]
    refine ⟨0, ?_, ?_, ?_⟩
    · rw [hN0]; exact hN1
    · rw [hN0]; exact htrN
    · rw [abs_zero]
      have hz : 2 * (0 : ℝ) * |s2 M| / (3 * (trOp N + 0 * trOp M)) = 0 := by ring
      rw [hz]
  · have hεne : ε ≠ 0 := ne_of_gt hεpos
    set A : ℝ := trOp N + ε * trOp M with hAdef
    rw [hAdef] at hA hD
    set s : ℝ := Real.sqrt (9 * A ^ 2 - 24 * ε ^ 2 * s2 M) with hsdef
    have hs_sq : s ^ 2 = 9 * A ^ 2 - 24 * ε ^ 2 * s2 M := by
      rw [hsdef]; exact Real.sq_sqrt hD.le
    have hspos : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.mpr hD
    set lam : ℝ := (-3 * A + s) / (12 * ε) with hlamdef
    have hT : N + ε • (M + lam • (1 : ℝ⁴ →L[ℝ] ℝ⁴))
        = (N + ε • M) + (ε * lam) • (1 : ℝ⁴ →L[ℝ] ℝ⁴) := by
      rw [smul_add, ← smul_smul]; abel
    have hNM : s2 (N + ε • M) = 1 + ε ^ 2 * s2 M := by
      rw [s2_add_expansion hN (hM.smul (by simp)), pairOp_smul, s2_smul, hMC, hN1]
      ring
    have htrNM : trOp (N + ε • M) = A := by
      rw [trOp_add, trOp_smul]
    have hs2 : s2 (N + ε • (M + lam • (1 : ℝ⁴ →L[ℝ] ℝ⁴)))
        = 1 + (ε ^ 2 * s2 M + 3 * (ε * lam) * A + 6 * (ε * lam) ^ 2) := by
      rw [hT, s2_add_smul_one, hNM, htrNM]
      ring
    refine ⟨lam, ?_, ?_, ?_⟩
    · rw [hs2]
      have hzero : ε ^ 2 * s2 M + 3 * (ε * lam) * A + 6 * (ε * lam) ^ 2 = 0 := by
        rw [hlamdef]
        field_simp
        nlinarith [hs_sq]
      linarith [hzero]
    · have htr : trOp (N + ε • (M + lam • (1 : ℝ⁴ →L[ℝ] ℝ⁴))) = A + ε * lam * 4 := by
        rw [hT, trOp_add, htrNM, trOp_smul, trOp_one]
      rw [htr]
      have hval : A + ε * lam * 4 = s / 3 := by
        rw [hlamdef]; field_simp; ring
      rw [hval]; linarith [hspos]
    · have hs3A : 0 < s + 3 * A := by linarith
      have hkey : s - 3 * A = -(24 * ε ^ 2 * s2 M) / (s + 3 * A) := by
        rw [eq_div_iff (ne_of_gt hs3A)]
        nlinarith [hs_sq]
      have hmain : |lam| = 2 * ε * |s2 M| / (s + 3 * A) := by
        rw [hlamdef]
        have h3 : (-3 * A + s) = s - 3 * A := by ring
        rw [h3, abs_div, abs_of_pos (by linarith : (0 : ℝ) < 12 * ε), hkey,
          abs_div, abs_neg, abs_of_pos hs3A, abs_mul,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ 24 * ε ^ 2)]
        field_simp
        ring
      rw [hmain]
      have h3A : 0 < 3 * A := by linarith
      have hab : (1 : ℝ) / (s + 3 * A) ≤ 1 / (3 * A) :=
        one_div_le_one_div_of_le h3A (by linarith)
      have hX : 0 ≤ 2 * ε * |s2 M| := by positivity
      calc 2 * ε * |s2 M| / (s + 3 * A)
          = 2 * ε * |s2 M| * (1 / (s + 3 * A)) := by ring
        _ ≤ 2 * ε * |s2 M| * (1 / (3 * A)) := mul_le_mul_of_nonneg_left hab hX
        _ = 2 * ε * |s2 M| / (3 * A) := by ring

end

end Submission
