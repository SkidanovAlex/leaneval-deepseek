import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Submission.Work.FTS.EllipticEst.TT.logCutDefs
import Submission.Work.FTS.EllipticEst.Blocks.logChiFamily

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Blocks

open scoped Real Topology
open Set Filter

/-- **The sharp, `n`-dependent commutator bound.**  If `K` bounds `|chi'|` globally then for
`z > 0`
`|z · (logChi n)'(z)| ≤ K / log((n:ℝ)+2)`.

This refines `abs_mul_deriv_logChi_le` (which replaces the denominator `log((n:ℝ)+2)` by the
weaker uniform lower bound `log 2`): the chain rule gives
`z · (logChi n)'(z) = chi'(log z / log((n:ℝ)+2)) / log((n:ℝ)+2)`, so the dependence on `n`
survives in the denominator and tends to `0`. -/
lemma abs_mul_deriv_logChi_le_sharp {K : ℝ}
    (hK : ∀ t : ℝ, |deriv Work.ChiExplicit.chi t| ≤ K) (n : ℕ) {z : ℝ} (hz : 0 < z) :
    |z * deriv (Work.FTS.EllipticEst.TT.logChi n) z| ≤ K / Real.log ((n : ℝ) + 2) := by
  have hc : 0 < Real.log ((n : ℝ) + 2) := Work.FTS.EllipticEst.TT.log_two_add_natCast_pos n
  set t := Real.log z / Real.log ((n : ℝ) + 2) with ht
  have heq : z * (deriv Work.ChiExplicit.chi t * (1 / (z * Real.log ((n : ℝ) + 2)))) =
      deriv Work.ChiExplicit.chi t / Real.log ((n : ℝ) + 2) := by
    field_simp
  rw [deriv_logChi_eq n hz, heq, abs_div, abs_of_pos hc]
  exact div_le_div_of_nonneg_right (hK t) hc.le

/-- **The logarithmic cut-off is eventually a small commutator.**

`logChi n z = chi (log z / log ((n:ℝ)+2))` with `chi = Work.ChiExplicit.chi` the explicit smooth
bump (`= 1` on `[-1,1]`, `= 0` off `(-2,2)`, values in `[0,1]`).  For `z > 0` its derivative is
`chi'(log z / log((n:ℝ)+2)) / (z · log((n:ℝ)+2))` (see `deriv_logChi_eq` in
`Submission.Work.FTS.EllipticEst.Blocks.logChiFamily`), so
`|z · (logChi n)'(z)| ≤ K/log((n:ℝ)+2)` with `K` a global bound of `|chi'|` (available as
`exists_bound_deriv_chi` in the same file), and `log((n:ℝ)+2) → ∞`.  Hence for all large `n` the
commutator `|z χ'|` is at most `1/8`, uniformly in `z > 0`.  (This smallness is what makes the
cut-off error absorbable in the proof of
`Work.FTS.EllipticEst.Blocks.DzAgmonLintegral_of_compact`.) -/
theorem AgmonSmallness :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ z : ℝ, 0 < z →
      |z * deriv (Work.FTS.EllipticEst.TT.logChi n) z| ≤ (1 / 8 : ℝ) := by
  obtain ⟨K, _hK0, hK⟩ := exists_bound_deriv_chi
  -- `log ((n:ℝ)+2) → ∞`, so beyond some `N₀` the denominator is at least `8K`.
  have hden : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_atTop_mono (fun n : ℕ => by
        have h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith) tendsto_natCast_atTop_atTop)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hden.eventually_ge_atTop (8 * K))
  refine ⟨N₀, fun n hn z hz => ?_⟩
  have hlog : 8 * K ≤ Real.log ((n : ℝ) + 2) := hN₀ n hn
  calc |z * deriv (Work.FTS.EllipticEst.TT.logChi n) z|
      ≤ K / Real.log ((n : ℝ) + 2) := abs_mul_deriv_logChi_le_sharp hK n hz
    _ ≤ 1 / 8 := by
        have hc : 0 < Real.log ((n : ℝ) + 2) :=
          Work.FTS.EllipticEst.TT.log_two_add_natCast_pos n
        rw [div_le_iff₀ hc]
        linarith

end Work.FTS.EllipticEst.Blocks
