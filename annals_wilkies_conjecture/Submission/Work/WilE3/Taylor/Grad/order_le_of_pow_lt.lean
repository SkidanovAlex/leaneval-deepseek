import Mathlib
import Submission.Work.WilE3.Taylor.Grad.pos_factor_of_order
import Submission.Work.WilE3.Taylor.Grad.not_eventually_lt_mul
import Submission.Work.WilE3.Taylor.Grad.eventually_pow_lt_of_eventually_mul_pow

/-!
  annals_wilkies_conjecture, AREA E3: the order bookkeeping `order_le_of_pow_lt`.

  Let `G`, `F` be real analytic at `0` with finite orders of vanishing `n`, `k` (`analyticOrderAt`),
  and let them be positive on a right neighbourhood of `0`.  If for all small `t > 0`

  `(G t) ^ q < (F t) ^ (2 * p)`,

  then `2 * p * k ≤ q * n`.

  Indeed, write `G t = t ^ n * g t`, `F t = t ^ k * h t` with `g`, `h` analytic at `0` and
  `g 0 > 0`, `h 0 > 0` (the order hypotheses are exactly Mathlib's
  `AnalyticAt.analyticOrderAt_eq_natCast`; positivity of the units uses `hposG`, `hposF`).
  Dividing the inequality by `t ^ (q * n) > 0` turns it into

  `(g t) ^ q < t ^ (2 * p * k - q * n) * (h t) ^ (2 * p)`

  along `𝓝[>] 0`.  If `2 * p * k - q * n > 0` the right-hand side tends to `0` while the left-hand
  side tends to `(g 0) ^ q > 0`, an immediate contradiction.
-/

open Filter

namespace Work.WilE3.Taylor.Grad

/-- **Order bookkeeping for the power inequality.**  If two functions analytic at `0` with orders
`n` and `k` and positive on a right neighbourhood of `0` satisfy `G ^ q < F ^ (2 * p)` near `0⁺`,
then `2 * p * k ≤ q * n`. -/
theorem order_le_of_pow_lt {G F : ℝ → ℝ} {p q n k : ℕ}
    (hG : AnalyticAt ℝ G 0) (hF : AnalyticAt ℝ F 0)
    (hGord : analyticOrderAt G 0 = n) (hFord : analyticOrderAt F 0 = k)
    (hposG : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < G t)
    (hposF : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < F t)
    (hineq : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), (G t) ^ q < (F t) ^ (2 * p)) :
    2 * p * k ≤ q * n := by
  by_contra hcon
  simp only [not_le] at hcon
  -- Factor out the orders: `G t = t ^ n * g t`, `F t = t ^ k * h t` with `g 0, h 0 > 0`.
  obtain ⟨g, hga, hg0, hgG⟩ := pos_factor_of_order hG hGord hposG
  obtain ⟨h, hha, hh0, hhF⟩ := pos_factor_of_order hF hFord hposF
  -- Rewrite the inequality after dividing by `t ^ (q * n)`.
  have hdeq : 2 * p * k = q * n + (2 * p * k - q * n) := (Nat.add_sub_of_le hcon.le).symm
  have hineq' : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (g t) ^ q < t ^ (2 * p * k - q * n) * (h t) ^ (2 * p) :=
    eventually_pow_lt_of_eventually_mul_pow hdeq
      (hgG.filter_mono nhdsWithin_le_nhds) (hhF.filter_mono nhdsWithin_le_nhds) hineq
  -- But `LHS → (g 0) ^ q > 0` while `RHS → 0`.
  exact not_eventually_lt_mul (Nat.sub_pos_of_lt hcon) (pow_pos hg0 q)
    ((hga.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).pow q)
    ((hha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).pow (2 * p))
    hineq'

end Work.WilE3.Taylor.Grad
