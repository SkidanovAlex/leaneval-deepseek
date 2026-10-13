/-
# `phiABddDeriv` — `𝒜φ = VocabO.phiA α` has `22` bounded derivatives

The task: for `0 < α ≤ 1/5`,
`∃ K, 0 ≤ K ∧ BddDeriv 22 (VocabO.phiA α) K`, i.e. `|(d/dz)^k (phiA α) z| ≤ K` for every
`k ≤ 22` and every `z > 0`.

`phiA α z = α z² φ''(z) + (5+α) z φ'(z)` with `φ(z) = 2z/(1+z)²`.  Writing `u = 1/(1+z)`,

`phiA α z = (2α-10)u + (30-14α)u² + (24α-20)u³ - 12α u⁴`,

i.e. `phiA α = phiAseries α 0` (`Series/Deleg/phiASeriesDefs.lean`).  The point of this form
is that `(d/dz)^k (1+z)^m = (∏_{i<k}(m-i))·(1+z)^{m-k}` is an *explicit finite sum*, so the
`k`-th derivative of `phiA α` on `z > 0` is `phiAseries α k`, a closed form.

The proof is therefore: `phiA α = phiAseries α 0` (delegated `phiAeqSeries`),
`d/dz (phiAseries α k) = phiAseries α (k+1)` (delegated `hasDerivAtPhiAseries`), hence
`iteratedDeriv k (phiA α) = phiAseries α k` on `z > 0` by induction, and each summand of
`phiAseries α k` is bounded by `30 · 26^22` for `k ≤ 22` and `z > 0` (delegated
`phiAtermBound`).  The constant is crude, which is all `BddDeriv` needs.
-/
import Mathlib
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.PhiStar.StarDefs
import Submission.Work.FTS.PhiStar.Basic
import Submission.Work.FTS.PhiStar.Series.Deleg.phiASeriesDefs
import Submission.Work.FTS.PhiStar.Series.Deleg.phiAeqSeries
import Submission.Work.FTS.PhiStar.Series.Deleg.hasDerivAtPhiAseries
import Submission.Work.FTS.PhiStar.Series.Deleg.phiAtermBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Finset

namespace Work.FTS.PhiStar.Series.Deleg

/-- **The `k`-th derivative of `phiA α` on `z > 0` is the closed form `phiAseries α k`.**
By induction on `k`: `k = 0` is `phiAeqSeries`, and the step differentiates
`iteratedDeriv k (phiA α)` (which agrees with `phiAseries α k` on the open set `Ioi 0`,
a neighbourhood of `z`) using `hasDerivAtPhiAseries`. -/
theorem iteratedDeriv_phiA_eq_series (α : ℝ) :
    ∀ k : ℕ, ∀ z : ℝ, 0 < z →
      iteratedDeriv k (Work.FTS.VocabO.phiA α) z = phiAseries α k z := by
  intro k
  induction k with
  | zero =>
      intro z hz
      rw [iteratedDeriv_zero]
      exact phiAeqSeries α z (by intro h; rw [h] at hz; norm_num at hz)
  | succ k ih =>
      intro z hz
      have hz1 : z ≠ -1 := by intro h; rw [h] at hz; norm_num at hz
      have hev : iteratedDeriv k (Work.FTS.VocabO.phiA α) =ᶠ[𝓝 z] phiAseries α k := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
        exact ih w hw
      rw [iteratedDeriv_succ, hev.deriv_eq]
      exact (hasDerivAtPhiAseries α k hz1).deriv

/-- Each term of `phiAseries α k` is bounded by `30 · 26^22` for `k ≤ 22` and `z > 0`
(`phiAtermBound`), and there are four terms. -/
theorem abs_phiAseries_le (α : ℝ) (hα : 0 < α) (hα5 : α ≤ 1 / 5) {k : ℕ} (hk : k ≤ 22)
    {z : ℝ} (hz : 0 < z) : |phiAseries α k z| ≤ 1000 * 26 ^ 22 := by
  have hterm : ∀ n ∈ Finset.range 4,
      |phiAcoef α n * (∏ i ∈ Finset.range k, ((-(n : ℝ) - 1) - i))
        * (1 + z) ^ (-(n : ℤ) - 1 - (k : ℤ))| ≤ 30 * 26 ^ 22 :=
    fun n hn => phiAtermBound α hα hα5 n k (Finset.mem_range.mp hn) hk hz
  have hstep : |phiAseries α k z| ≤ ∑ n ∈ Finset.range 4, (30 * 26 ^ 22 : ℝ) := by
    have hsum : phiAseries α k z
        = ∑ n ∈ Finset.range 4, phiAcoef α n
            * (∏ i ∈ Finset.range k, ((-(n : ℝ) - 1) - i))
            * (1 + z) ^ (-(n : ℤ) - 1 - (k : ℤ)) := rfl
    rw [hsum]
    exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum hterm)
  have hsum4 : (∑ n ∈ Finset.range 4, (30 * 26 ^ 22 : ℝ)) = 120 * 26 ^ 22 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  calc |phiAseries α k z| ≤ ∑ n ∈ Finset.range 4, (30 * 26 ^ 22 : ℝ) := hstep
    _ = 120 * 26 ^ 22 := hsum4
    _ ≤ 1000 * 26 ^ 22 :=
        mul_le_mul_of_nonneg_right (by norm_num : (120 : ℝ) ≤ 1000) (by positivity)

/-- **The delegated target**: `𝒜φ = VocabO.phiA α` has all `22` first derivatives bounded
by the universal constant `1000·26^22`, for `0 < α ≤ 1/5`. -/
theorem phiABddDeriv (α : ℝ) (hα : 0 < α) (hα5 : α ≤ 1 / 5) :
    ∃ K : ℝ, 0 ≤ K ∧ Work.FTS.PhiStar.BddDeriv 22 (Work.FTS.VocabO.phiA α) K := by
  refine ⟨1000 * 26 ^ 22, by positivity, ?_⟩
  intro k hk z hz
  rw [iteratedDeriv_phiA_eq_series α k z hz]
  exact abs_phiAseries_le α hα hα5 hk hz

end Work.FTS.PhiStar.Series.Deleg
