import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.BoseB1Cube.CrudePlanAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB1Cube

set_option maxHeartbeats 1000000

/-!
# `Work.BoseB1Cube.countAbsorbArith` — the pure-real arithmetic of the count-absorption leaf (L2)

The scalar core of `Work.BoseB1Cube.CrudePlan.CountAbsorb` (FS's `U`-argument in linear form).
All hypotheses are of the shape produced at the state level:

* `hsig`    : `(μ/3)·⟨n₊·sig⟩ − μ²·⟨n₊·W⟩ ≤ P` (Jensen/`RPsi` on the `W = term1 + Δ3` split),
* `hsplit`  : `½·(W/ℓ³)·(n⟨n₊⟩ − ⟨n₊⟩) − 3·KU·⟨n₊⟩ ≤ ⟨n₊·sig⟩`,
* `hKUW`    : `KU·ℓ³ ≤ Cs·W` (`(KU/W)ℓ³ ≲ chiSupAbs²/π`),
* `hW`      : `π a ℓ³ ≤ W` (`W ≥ πaℓ³`, the Wiener/kinetic lower bound for `W`).

Mathematical content (all divisions cleared — no loss):

* from `hsplit`, multiplied by `2ℓ³`:  `W·(nN − K) ≤ 2ℓ³·(N·sig + 3·KU·K)`;
* from `hsig`,  multiplied by `3`:      `μ·(N·sig) ≤ 3·(P + μ²·N·W)`;
* from `hKUW`,  multiplied by `6μK`:    `6μK·ℓ³·KU ≤ 6μK·Cs·W`  (legitimate also for `KU < 0`,
  since `6μK ≥ 0` and `ℓ³ ≤ (Cs W)/KU` is not needed — only `KU·ℓ³ ≤ Cs·W` times a nonnegative factor
  is used, so a negative `KU` only makes the left side smaller),

giving  `μ·W·nN ≤ 6ℓ³P + 6μ²ℓ³NW + 6μK·Cs·W + μWK`.  Multiplying by `πa` and bounding the `P`-row
with `πaℓ³ ≤ W`,

    `π·W·(μ a n N) ≤ W·(6 + 7π + 6πCs)·(μ²aℓ³N + P + μaK)`,

and dividing by `πW > 0` (with `7 ≥ 1` and `6π ≤ 6 + 7π`) gives the claim

    `μ a n N ≤ (6/π + 6 + 1 + 6Cs)·(μ²aℓ³N + P + μaK)`.

Every step is a single multiplication of an available inequality by an explicit nonnegative factor;
the only scalar facts used are `π > 0`, `Cs ≥ 0`, and the nonnegativity of `W, μ, a, ℓ, N, K, P`.
-/

theorem countAbsorbArith {μ a ℓ W N K sig P KU Cs : ℝ} {n : ℕ}
    (hμ : 0 < μ) (ha : 0 < a) (hℓ : 0 < ℓ) (hN0 : 0 ≤ N) (hK0 : 0 ≤ K) (hP0 : 0 ≤ P)
    (hW : Real.pi * a * ℓ ^ 3 ≤ W)
    (hCs : 0 ≤ Cs)
    (hsig : (μ / 3) * (N * sig) - μ ^ 2 * (N * W) ≤ P)
    (hsplit : (1 / 2) * (W / ℓ ^ 3) * ((n : ℝ) * N - K) - 3 * KU * K ≤ N * sig)
    (hKUW : KU * ℓ ^ 3 ≤ Cs * W) :
    μ * a * (n : ℝ) * N
      ≤ (6 / Real.pi + 6 + 1 + 6 * Cs) * (μ ^ 2 * a * ℓ ^ 3 * N + P + μ * a * K) := by
  have hℓ3 : (0 : ℝ) < ℓ ^ 3 := by positivity
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hWnn : (0 : ℝ) ≤ W := le_trans (by positivity : (0 : ℝ) ≤ Real.pi * a * ℓ ^ 3) hW
  have hWpos : (0 : ℝ) < W := lt_of_lt_of_le (by positivity : (0 : ℝ) < Real.pi * a * ℓ ^ 3) hW
  -- (1) clear the `ℓ³` denominator of `hsplit`:  `W·(nN − K) ≤ 2ℓ³·(N·sig + 3·KU·K)`
  have hA1 : (1 / 2) * (W / ℓ ^ 3) * ((n : ℝ) * N - K) ≤ N * sig + 3 * KU * K := by
    linarith [hsplit]
  have hA2 := mul_le_mul_of_nonneg_left hA1 (by positivity : (0 : ℝ) ≤ 2 * ℓ ^ 3)
  have hAeq : (2 * ℓ ^ 3) * ((1 / 2) * (W / ℓ ^ 3) * ((n : ℝ) * N - K))
      = W * ((n : ℝ) * N - K) := by
    field_simp
  rw [hAeq] at hA2
  -- (2) clear the `1/3` in `hsig`:  `μ·(N·sig) ≤ 3·(P + μ²·N·W)`
  have hB : μ * (N * sig) ≤ 3 * (P + μ ^ 2 * (N * W)) := by linarith [hsig]
  -- (3) the cleared main inequality, from the three multiplications above
  have hMain : μ * W * ((n : ℝ) * N)
      ≤ 6 * ℓ ^ 3 * P + 6 * μ ^ 2 * ℓ ^ 3 * N * W + 6 * μ * K * Cs * W + μ * W * K := by
    have hA2μ : μ * (W * ((n : ℝ) * N - K)) ≤ μ * (2 * ℓ ^ 3 * (N * sig + 3 * KU * K)) :=
      mul_le_mul_of_nonneg_left hA2 (le_of_lt hμ)
    have hB2 : (2 * ℓ ^ 3) * (μ * (N * sig)) ≤ (2 * ℓ ^ 3) * (3 * (P + μ ^ 2 * (N * W))) :=
      mul_le_mul_of_nonneg_left hB (by positivity : (0 : ℝ) ≤ 2 * ℓ ^ 3)
    have hKUW2 : (6 * μ * K) * (KU * ℓ ^ 3) ≤ (6 * μ * K) * (Cs * W) :=
      mul_le_mul_of_nonneg_left hKUW (by positivity : (0 : ℝ) ≤ 6 * μ * K)
    nlinarith [hA2μ, hB2, hKUW2]
  -- (4) multiply by `π·a` and expand
  have hstar : Real.pi * a * (μ * W * ((n : ℝ) * N))
      ≤ Real.pi * a
          * (6 * ℓ ^ 3 * P + 6 * μ ^ 2 * ℓ ^ 3 * N * W + 6 * μ * K * Cs * W + μ * W * K) :=
    mul_le_mul_of_nonneg_left hMain (by positivity : (0 : ℝ) ≤ Real.pi * a)
  have hstar_exp : Real.pi * a * (μ * W * ((n : ℝ) * N))
      ≤ Real.pi * a * (6 * ℓ ^ 3 * P) + Real.pi * a * (6 * μ ^ 2 * ℓ ^ 3 * N * W)
        + Real.pi * a * (6 * μ * K * Cs * W) + Real.pi * a * (μ * W * K) := by
    nlinarith [hstar]
  -- (5) the four row bounds
  have hx1 : 6 * P * (Real.pi * a * ℓ ^ 3) ≤ 6 * P * W :=
    mul_le_mul_of_nonneg_left hW (by positivity : (0 : ℝ) ≤ 6 * P)
  have h6 : (6 : ℝ) ≤ 6 + 7 * Real.pi + 6 * Real.pi * Cs := by nlinarith [hpi, hCs]
  have hx2 : 6 * (W * P) ≤ (6 + 7 * Real.pi + 6 * Real.pi * Cs) * (W * P) :=
    mul_le_mul_of_nonneg_right h6 (mul_nonneg hWnn hP0)
  have b1 : Real.pi * a * (6 * ℓ ^ 3 * P) ≤ W * (6 + 7 * Real.pi + 6 * Real.pi * Cs) * P := by
    nlinarith [hx1, hx2]
  have hcoef2 : 6 * Real.pi ≤ 6 + 7 * Real.pi + 6 * Real.pi * Cs := by nlinarith [hpi, hCs]
  have hx3 : 6 * Real.pi * (W * (μ ^ 2 * a * ℓ ^ 3 * N))
      ≤ (6 + 7 * Real.pi + 6 * Real.pi * Cs) * (W * (μ ^ 2 * a * ℓ ^ 3 * N)) :=
    mul_le_mul_of_nonneg_right hcoef2 (mul_nonneg hWnn (by positivity))
  have b2 : Real.pi * a * (6 * μ ^ 2 * ℓ ^ 3 * N * W)
      ≤ W * (6 + 7 * Real.pi + 6 * Real.pi * Cs) * (μ ^ 2 * a * ℓ ^ 3 * N) := by
    nlinarith [hx3]
  have b3 : Real.pi * a * (6 * μ * K * Cs * W) ≤ 6 * Real.pi * Cs * W * (μ * a * K) :=
    le_of_eq (by ring)
  have hcoef4 : Real.pi ≤ 6 + 7 * Real.pi := by nlinarith [hpi]
  have hx4 : Real.pi * (W * (μ * a * K)) ≤ (6 + 7 * Real.pi) * (W * (μ * a * K)) :=
    mul_le_mul_of_nonneg_right hcoef4 (mul_nonneg hWnn (by positivity))
  have b4 : Real.pi * a * (μ * W * K) ≤ (6 + 7 * Real.pi) * W * (μ * a * K) := by
    nlinarith [hx4]
  -- (6) assemble at the scale `π·W`
  have hgoalR : W * (6 + 7 * Real.pi + 6 * Real.pi * Cs) * (μ ^ 2 * a * ℓ ^ 3 * N + P + μ * a * K)
      = W * (6 + 7 * Real.pi + 6 * Real.pi * Cs) * (μ ^ 2 * a * ℓ ^ 3 * N)
        + W * (6 + 7 * Real.pi + 6 * Real.pi * Cs) * P
        + (6 * Real.pi * Cs * W * (μ * a * K) + (6 + 7 * Real.pi) * W * (μ * a * K)) := by ring
  have hG2 : Real.pi * W * (μ * a * (n : ℝ) * N)
      ≤ W * (6 + 7 * Real.pi + 6 * Real.pi * Cs) * (μ ^ 2 * a * ℓ ^ 3 * N + P + μ * a * K) := by
    have h1 : Real.pi * W * (μ * a * (n : ℝ) * N)
        = Real.pi * a * (μ * W * ((n : ℝ) * N)) := by ring
    rw [h1, hgoalR]
    linarith [hstar_exp, b1, b2, b3, b4]
  -- (7) undo the scaling by `π·W > 0`
  have hCeq : Real.pi * W * (6 / Real.pi + 6 + 1 + 6 * Cs)
      = W * (6 + 7 * Real.pi + 6 * Real.pi * Cs) := by
    field_simp
    ring
  have hkey : Real.pi * W * (μ * a * (n : ℝ) * N)
      ≤ Real.pi * W
          * ((6 / Real.pi + 6 + 1 + 6 * Cs) * (μ ^ 2 * a * ℓ ^ 3 * N + P + μ * a * K)) := by
    have hh : Real.pi * W * ((6 / Real.pi + 6 + 1 + 6 * Cs)
          * (μ ^ 2 * a * ℓ ^ 3 * N + P + μ * a * K))
        = W * (6 + 7 * Real.pi + 6 * Real.pi * Cs)
            * (μ ^ 2 * a * ℓ ^ 3 * N + P + μ * a * K) := by
      rw [← mul_assoc, hCeq]
    rw [hh]
    exact hG2
  exact le_of_mul_le_mul_left hkey (by positivity : (0 : ℝ) < Real.pi * W)

end Work.BoseB1Cube
