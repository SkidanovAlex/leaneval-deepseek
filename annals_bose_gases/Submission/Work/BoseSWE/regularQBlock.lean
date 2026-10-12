import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseSWE

/-- The `Q`-block of the small-window ledger, in the *density-slot* form: all the `Q²`-terms are
rewarded once the **linear coefficient** of `Q` is nonnegative.  Concretely, the difference of the
two sides equals

  `Q * L + Q ^ 2 * (W / 4 + Δ / 2)`,  `L := C·a·T·V - Cp·a·(T+n)·V + W·(1-(n-T)/2) - Δ·(n-1/2)`,

and `L ≥ 0` is exactly `hC = 3·Cn·K + Cp·(1+2·Cn) ≤ C` together with `W ≤ K·a·V`, `Δ ≤ W`,
`n ≤ 2·Cn·T`: writing `S := W·(1-(n-T)/2) - Δ·(n-1/2)` one has `S ≥ -3·Cn·K·a·V·T`
(split on `n ≥ 1/2` and on the sign of `3/2 - 3n/2 + T/2` in the first case), whence

  `L ≥ (3·Cn·K + Cp·(1+2·Cn))·a·T·V - Cp·(1+2·Cn)·T·a·V + S ≥ 3·Cn·K·a·V·T - 3·Cn·K·a·V·T = 0`

(the `Cp`-column cancels exactly, and the surviving `3·Cn·K·a·T·V` is precisely what `S` pays).

(The hypothesis `Cn·T ≤ n` is not needed.) -/
theorem regularQBlock {V T a W Δ Q n Cp Cn K C : ℝ}
    (hV : 0 < V) (hT : 0 ≤ T) (ha : 0 ≤ a) (hW : 0 ≤ W) (hΔ0 : 0 ≤ Δ) (hΔW : Δ ≤ W)
    (hQ : 0 ≤ Q)
    (hCn : 0 ≤ Cn) (hn1 : Cn * T ≤ n) (hn2 : n ≤ 2 * Cn * T)
    (hWV : W ≤ K * a * V) (hCp : 0 ≤ Cp) (hK : 0 ≤ K)
    (hC : 3 * Cn * K + Cp * (1 + 2 * Cn) ≤ C) :
    Cp * a * (T + n) * Q * V + (1 / 2) * (n - T) * Q * W + Δ * n * Q
      ≤ C * a * T * Q * V + (1 / 4) * Q ^ 2 * W + W * Q + (1 / 2) * Δ * (Q ^ 2 + Q) := by
  have hSV : 0 ≤ 3 * Cn * K * a * V * T := by positivity
  -- the needed lower bound on `S = W·(1-(n-T)/2) - Δ·(n-1/2)`
  have hS : -(3 * Cn * K * a * V * T) ≤ W * (1 - (n - T) / 2) - Δ * (n - 1 / 2) := by
    rcases le_or_gt (1 / 2 : ℝ) n with hn | hn
    · have hΔ' : Δ * (n - 1 / 2) ≤ W * (n - 1 / 2) :=
        mul_le_mul_of_nonneg_right hΔW (by linarith)
      rcases le_or_gt (0 : ℝ) (3 / 2 - 3 * n / 2 + T / 2) with hβ | hβ
      · have hWβ : 0 ≤ W * (3 / 2 - 3 * n / 2 + T / 2) := mul_nonneg hW hβ
        nlinarith [hWβ, hΔ', hSV]
      · have hWβ : K * a * V * (3 / 2 - 3 * n / 2 + T / 2) ≤ W * (3 / 2 - 3 * n / 2 + T / 2) :=
          mul_le_mul_of_nonpos_right hWV (le_of_lt hβ)
        have hβ3 : 0 ≤ 3 / 2 - 3 * n / 2 + T / 2 + 3 * Cn * T := by nlinarith [hn2]
        have hKaV : 0 ≤ K * a * V := by positivity
        nlinarith [hWβ, hΔ', hβ3, hKaV]
    · have h1 : 0 ≤ W * (1 - (n - T) / 2) := mul_nonneg hW (by linarith)
      have h2 : 0 ≤ Δ * (1 / 2 - n) := mul_nonneg hΔ0 (by linarith)
      nlinarith [h1, h2, hSV]
  -- the two payments
  have hCS : (3 * Cn * K + Cp * (1 + 2 * Cn)) * (a * T * V) ≤ C * (a * T * V) :=
    mul_le_mul_of_nonneg_right hC (by positivity)
  have hCT : Cp * a * (T + n) * V ≤ Cp * (1 + 2 * Cn) * T * a * V := by
    have hTn : T + n ≤ (1 + 2 * Cn) * T := by nlinarith [hn2]
    have hCaV : 0 ≤ Cp * (a * V) := mul_nonneg hCp (mul_nonneg ha (le_of_lt hV))
    have h := mul_le_mul_of_nonneg_left hTn hCaV
    nlinarith [h]
  -- the coefficient of `Q` is nonnegative
  have hmain : 0 ≤ C * a * T * V - Cp * a * (T + n) * V + W * (1 - (n - T) / 2)
      - Δ * (n - 1 / 2) := by
    nlinarith [hCS, hCT, hS]
  -- assemble: `RHS - LHS = Q * (coefficient) + Q ^ 2 * (W / 4 + Δ / 2)`
  have hq1 : 0 ≤ Q * (C * a * T * V - Cp * a * (T + n) * V + W * (1 - (n - T) / 2)
      - Δ * (n - 1 / 2)) := mul_nonneg hQ hmain
  have hq2 : 0 ≤ Q ^ 2 * (W / 4 + Δ / 2) :=
    mul_nonneg (sq_nonneg Q) (by linarith)
  nlinarith [hq1, hq2]

end Work.BoseSWE
