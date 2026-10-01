/-
# ZeroFreeTables/HB95h3/h3_Tbracket — the `T`-bracket with the numeric factors

Assembly step of the `h = 3` engine: given the *generic* `T`-step
`h3_Tstep` (Heath-Brown's comparison, with denominators `a = 26/10` and `α = 26/10 + λ₁`)
and the multiplicate bookkeeping bounds `K1 ≥ m·(8/3)`, `K2, K4 ≥ m·Re P₃(α/(α+iT))`,
we deduce the bracketed inequality in which `K1, K2, K4` are the only quantities
carrying the external (level/character) dependence:

`-24480·K1 - 14900·K2 - 1250·K4 + 6000·Re P₃(α/(a+iT)) ≤ -24480·(m·(8/3))`.

The point is that the two identical `α`-denominator terms `14900 + 1250 = 16150` combine with
`0 ≤ Re P₃(α/(α+iT))` and `m ≥ 1` to beat the positive pole contribution `6000·Re P₃(α/(a+iT))`,
leaving exactly the `K1`-term on the right.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.HB95h3.Tstep

namespace Work.ZeroFreeTables.HB95h3

theorem h3_Tbracket {lam T m K1 K2 K4 : ℝ} (hlam0 : 0 ≤ lam) (hle : lam ≤ 348 / 1000) (hm : 1 ≤ m) (hK1 : m * (8 / 3) ≤ K1) (hK2 : m * Work.ZeroFreeTables.Table4.P3AB ((26 : ℝ) / 10 + lam) ((26 : ℝ) / 10 + lam) T ≤ K2) (hK4 : m * Work.ZeroFreeTables.Table4.P3AB ((26 : ℝ) / 10 + lam) ((26 : ℝ) / 10 + lam) T ≤ K4) : -24480 * K1 - 14900 * K2 - 1250 * K4 + 6000 * Work.ZeroFreeTables.Table4.P3AB ((26 : ℝ) / 10 + lam) ((26 : ℝ) / 10) T ≤ -24480 * (m * (8 / 3)) := by
  have hα : 0 < ((26 : ℝ) / 10) + lam := by linarith
  have hW : 0 ≤ Work.ZeroFreeTables.Table4.P3AB ((26 : ℝ) / 10 + lam) ((26 : ℝ) / 10 + lam) T :=
    Work.ZeroFreeTables.Table4.P3AB_nonneg _ _ _ hα hα le_rfl
  have hStep := h3_Tstep (T := T) hlam0 hle
  nlinarith [hK1, hK2, hK4, hStep, hW]

end Work.ZeroFreeTables.HB95h3
