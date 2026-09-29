import Mathlib
import Submission.Work.TMC16Core.Assembly.Consts

/-!
# The two numerical parameters of the non-resonant assembly

The non-resonant case of AJ §9 (`nr_case1_full`) needs

* an `A`-exponent deficit `εA` for the singular-point window of Lemma 9.2, and
* a window parameter `δ` for the same window,

chosen so that the *uniformity* rate `r = rateNR1 q n s c` (bounded only by `L/8 + L/100`)
enters the non-generation step (Lemma 9.3) with the least possible margin, while the
Cramer/decay step is fed the *Furman* slack `eps2 L = L/100` only.

`nrEpsA` is the maximum of the two lower bounds forced on `εA`:

* `(log (4(K+1)) + L + K r)/(K+1) + 2L/(K+1)^2` ensures the non-generation gap
  `4(K+1)·e^{L-εA} < e^{K(εA-r)}` (with a strict margin), and
* `csing L·(1/40 + 1/K) - eps2 L + L/(K+1)^2` ensures `δ ≥ 1/40 + 1/K`, which is what
  `Core.nr_ablock` needs (`δ ≥ 1/40` and `1 ≤ K(δ - 1/40)`),

and `nrDelta` is the corresponding window parameter `δ = (εA + eps2 L)/csing L`, so that
the `A`-window exponent `L - csing L·δ + eps2 L` is exactly `L - εA`.
-/

namespace Work.TMC16Core.Assembly

open Work.TMC16Core

noncomputable section

/-- The `A`-exponent deficit `εA` of the non-resonant assembly. -/
def nrEpsA (L r : ℝ) (K : ℕ) : ℝ :=
  max ((Real.log (4 * ((K : ℝ) + 1)) + L + (K : ℝ) * r) / ((K : ℝ) + 1)
        + 2 * L / ((K : ℝ) + 1) ^ 2)
      (csing L * (1 / 40 + 1 / (K : ℝ)) - eps2 L + L / ((K : ℝ) + 1) ^ 2)

/-- The window parameter `δ` of the non-resonant assembly. -/
def nrDelta (L r : ℝ) (K : ℕ) : ℝ := (nrEpsA L r K + eps2 L) / csing L

theorem nrDelta_spec {L r : ℝ} (hL : 0 < L) (K : ℕ) :
    csing L * nrDelta L r K - eps2 L = nrEpsA L r K := by
  rw [nrDelta, mul_div_cancel₀ _ (ne_of_gt (csing_pos hL))]
  ring

end

end Work.TMC16Core.Assembly

/-!
## Proof plan for `Work.TMC16Core.Assembly.nr_params`

Notation: `A := (log (4(K+1)) + L + K r)/(K+1) + 2L/(K+1)^2` and
`B := csing L * (1/40 + 1/K) - eps2 L + L/(K+1)^2`, so `nrEpsA L r K = max A B` and
`nrDelta L r K = (max A B + L/100)/(99L/100)`.  Write `e := r/L`.

From `hrlow` and `hrup`: `r ≤ (1/8+1/100) L = 0.135 L`, hence `e ≤ 0.135`, and
`200 (log Q + 1)/Q ≤ r ≤ 0.135 L`, hence `L ≥ 1481 (log Q + 1)/Q` (as `200/0.135 > 1481`).
From `hb'`: `3 b' ≥ s` (`omega`), so `b' Q ≥ s Q/3 = (K+1)/6` using `hK`; in particular
`Q ≤ (K+1)/6` and `(K+1)/(6K) ≥ 41/240` (from `hK40`).

Step 1 (`log (4(K+1)) ≤ 5*(log ((K+1)/6) + 1)`).  `log 4 ≤ 2`; `log (K+1) = log 6 +
log ((K+1)/6) ≤ 2 log ((K+1)/6)` because `6 ≤ (K+1)/6` for `K ≥ 40`.  Hence
`log (4(K+1)) ≤ 2 + 2 log ((K+1)/6) ≤ 5 (log ((K+1)/6) + 1)` as `log ((K+1)/6) ≥ 0`.

Step 2 (monotonicity of `x/(log x + 1)`).  For `1 ≤ x ≤ y`:
`log (y/x) ≤ y/x - 1` gives `x log y - x log x ≤ y - x`, so
`x (log y + 1) ≤ y + x log x ≤ y + y log x = y (log x + 1)` (using `log x ≥ 0`);
divide by `(log x + 1)(log y + 1) > 0`.

Step 3 (`log (4(K+1))/L ≤ 5 (K+1)/8889`).  Combine `1/L ≤ Q/(1481 (log Q + 1))` with
Steps 1--2 applied to `Q ≤ (K+1)/6`:
`log (4(K+1))/L ≤ log (4(K+1)) · Q/(1481 (log Q + 1))
 ≤ 5 (log ((K+1)/6) + 1) · ((K+1)/6)/(1481 (log ((K+1)/6) + 1)) = 5 (K+1)/8889`.

Step 4 (`A/L < 0.1615`, `B/L < 0.0502`).  Using Step 3 and `e ≤ 0.135`:
`A/L ≤ 5/8889 + (1 + 0.135 K)/(K+1) + 2/(K+1)^2 ≤ 5/8889 + 1/(K+1) + 0.135 + 2/(K+1)^2`
with `K ≥ 40`; `B/L = 99/100 (1/40 + 1/K) - 1/100 + 1/(K+1)^2 ≤ 2475/100000 + 99/(100 K) +
1/(K+1)^2`.

Step 5 (the nine clauses).
* `1/40 ≤ δ`: `δ ≥ (B + L/100)/(99L/100) = 1/40 + 1/K + (1/(99(K+1)^2))`.
* `δ ≤ 1/2`: `δ ≤ (0.1615 L + 0.01 L)/(0.99 L) < 1/2`.
* `1 ≤ K(δ - 1/40)`: from the previous display `δ - 1/40 ≥ 1/K`.
* `nrEpsA = csing * nrDelta - eps2`: `nrDelta_spec`.
* `r < nrEpsA`: `(K+1) A = log (4(K+1)) + L + K r + 2L/(K+1) > K r + L ≥ r` as `r ≤ 0.135 L`.
* `eps2 L < nrEpsA`: `nrEpsA ≥ B ≥ 99L/400 - L/100 = 59L/4000 > L/100`.
* the `log` clause: it is `(K+1) A > log (4(K+1)) + L + K r`, i.e. the margin `2L/(K+1)`.
* `δ ≤ b' Q/K`: this is `nrEpsA/L ≤ 99/100 · b' Q/K - 1/100`.  For the `B` branch this is
  immediate from Step 4 and `b' Q/K ≥ 41/240`.  For the `A` branch: multiply by `K+1` and
  use Step 3, `e ≤ 0.135` and `b' Q/K ≥ (K+1)/(6K)`; it suffices that
  `5 (K+1)/8889 ≤ 99/100 (K+1)^2/(6K) - 1/100 (K+1) - 1 - 0.135 K - 2/(K+1)`
  whose right-hand side is `≥ 0.02 K - 0.73`, and `5(K+1)/8889 ≤ 0.02K - 0.73` holds for
  `K ≥ 38`.
* the Cramer clause: it is `nrEpsA/L ≤ 1 - (1.01 · (3K/4) + (1/4)(K/4 - 1))/(K+1)`, whose
  right-hand side is `≥ 0.18`, while `nrEpsA/L ≤ 0.1615` by Step 4.
-/
