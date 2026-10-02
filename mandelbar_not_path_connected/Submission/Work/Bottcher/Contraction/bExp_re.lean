/-
# The real part of the Böttcher exponent series

For the monic quartic `p_c = T_c ∘ T_c` (`pMap c`) of the tricorn family and a function
`L : ℂ → ℂ` which is a holomorphic *logarithm* of the normalised factor

`p_c z / z ^ 4 = 1 + O(1/z²)`

on the escape set `{G_c > 0}` (i.e. `exp (L z) = p_c z / z^4` there) and which vanishes at
infinity, the *Böttcher exponent series*

`S z = Σ_k 4^{-(k+1)} L (p_c^[k] z)`

has real part `G_c z - log ‖z‖`.  This is the "modulus" half of the Böttcher equation: writing
`φ z = z * exp (S z)`, it says `‖φ z‖ = exp (G_c z)`.

The proof has two ingredients.

* **Summability.**  Since `L → 0` at infinity (`Tendsto L (cocompact ℂ) (𝓝 0)`) and the
  `p_c`-orbit of an escaping point `z` tends to infinity (`tendsto_iterate_pMap_cocompact`), the
  terms are eventually dominated by the geometric sequence `4^{-(k+1)}`.
* **Telescoping.**  `‖exp (L w)‖ = exp (Re (L w))` and `exp (L w) = p_c w / w^4` give
  `Re (L w) = log ‖p_c w‖ - 4 log ‖w‖`, so the `N`-th partial sum of the real parts is
  `4^{-N} log ‖p_c^N z‖ - log ‖z‖`, which converges to `G_c z - log ‖z‖` by
  `tendsto_fourPow_inv_log_norm_pMap_iterate`.

The hypotheses `G_c 0 = 0` and `z ≠ 0` are needed to know that no iterate `p_c^k z` vanishes
(the Green function is positive along the orbit of `z`), so that all the factors above are
legitimate.  Neither `hLan` (analyticity of `L`) nor the full strength of `hz0` is used: the
statement is the interface the Böttcher existence argument needs.

Note for consumers: the version of this result stated for the hypothesis package
`IsNormLog` in `Submission/Work/Bottcher/Contraction/exists_analyticBottcher_of_mem_mandelbar`
is the special case where the three fields of `IsNormLog` are supplied to `hLan`, `hLexp`,
`hLt`; that file declares a *duplicate* of the name `bExp_re`, so a module importing both must
drop one of the two.
-/
import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.Green.green_pos_iff
import Submission.Work.Bottcher.Contraction.analyticOnNhd_bExp
import Submission.Work.Bottcher.Contraction.tendsto_fourPow_inv_log_norm_pMap_iterate

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Function
open scoped Topology

namespace Work.Bottcher.Contraction

open LeanEval.ComplexAnalysis (Tantibar)

-- `hLan` and `hz0` are part of the interface but not needed by the argument (the latter is
-- implied by the other hypotheses); silence the unused-variable linter for them.
set_option linter.unusedVariables false

theorem bExp_re (c : ℂ) {L : ℂ → ℂ}
    (hLan : AnalyticOnNhd ℂ L (Work.Bottcher.EscapeSet c))
    (hLexp : ∀ z : ℂ, 0 < Work.Bottcher.green c z →
      Complex.exp (L z) = Work.Bottcher.pMap c z / z ^ 4)
    (hLt : Filter.Tendsto L (Filter.cocompact ℂ) (nhds 0))
    (hc0 : Work.Bottcher.green c 0 = 0)
    {z : ℂ} (hz : 0 < Work.Bottcher.green c z) (hz0 : z ≠ 0) :
    (∑' k : ℕ, ((1 / 4 : ℝ) ^ (k + 1) : ℂ) * L ((Work.Bottcher.pMap c)^[k] z)).re
      = Work.Bottcher.green c z - Real.log ‖z‖ := by
  classical
  -- ## Green positivity and non-vanishing along the `p_c`-orbit of `z`
  have hgp : ∀ k : ℕ, 0 < Work.Bottcher.green c ((Work.Bottcher.pMap c)^[k] z) := by
    intro k
    rw [green_pMap_iterate c z k]
    exact mul_pos (pow_pos (by norm_num) k) hz
  have hne : ∀ k : ℕ, (Work.Bottcher.pMap c)^[k] z ≠ 0 := by
    intro k hk
    have h1 := hgp k
    rw [hk, hc0] at h1
    exact lt_irrefl 0 h1
  -- ## The real part of `L` at an escaping point
  have hre_norm : ∀ w : ℂ, 0 < Work.Bottcher.green c w →
      (L w).re = Real.log ‖Work.Bottcher.pMap c w / w ^ 4‖ := by
    intro w hw
    rw [← hLexp w hw, Complex.norm_exp, Real.log_exp]
  have hlog_div : ∀ w : ℂ, 0 < Work.Bottcher.green c w → w ≠ 0 →
      Real.log ‖Work.Bottcher.pMap c w / w ^ 4‖
        = Real.log ‖Work.Bottcher.pMap c w‖ - 4 * Real.log ‖w‖ := by
    intro w hw hw0
    have hpw0 : Work.Bottcher.pMap c w ≠ 0 := by
      intro h0
      have h1 := green_pMap c w
      rw [h0, hc0] at h1
      have h2 : (0 : ℝ) < 4 * Work.Bottcher.green c w := by linarith
      linarith
    rw [norm_div, norm_pow, Real.log_div (norm_ne_zero_iff.mpr hpw0)
      (pow_ne_zero 4 (norm_ne_zero_iff.mpr hw0)), Real.log_pow]
    push_cast
    ring
  have hterm_re : ∀ k : ℕ, (L ((Work.Bottcher.pMap c)^[k] z)).re
      = Real.log ‖(Work.Bottcher.pMap c)^[k + 1] z‖
        - 4 * Real.log ‖(Work.Bottcher.pMap c)^[k] z‖ := by
    intro k
    rw [hre_norm _ (hgp k), hlog_div _ (hgp k) (hne k), Function.iterate_succ_apply']
  -- ## The real part of a single term of the series
  have hf_re : ∀ k : ℕ,
      (((1 / 4 : ℝ) ^ (k + 1) : ℂ) * L ((Work.Bottcher.pMap c)^[k] z)).re
        = (1 / 4 : ℝ) ^ (k + 1) * Real.log ‖(Work.Bottcher.pMap c)^[k + 1] z‖
          - (1 / 4 : ℝ) ^ k * Real.log ‖(Work.Bottcher.pMap c)^[k] z‖ := by
    intro k
    rw [Complex.mul_re, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, hterm_re k, mul_sub]
    congr 1
    rw [pow_succ]
    ring
  -- ## Telescoping of the partial sums
  have htel : ∀ N : ℕ,
      (∑ k ∈ Finset.range N,
          (((1 / 4 : ℝ) ^ (k + 1) : ℂ) * L ((Work.Bottcher.pMap c)^[k] z))).re
        = ((4 : ℝ) ^ N)⁻¹ * Real.log ‖(Work.Bottcher.pMap c)^[N] z‖ - Real.log ‖z‖ := by
    intro N
    rw [Complex.re_sum]
    rw [Finset.sum_congr rfl (fun k _ => hf_re k)]
    have h := Finset.sum_range_sub
      (fun m : ℕ => (1 / 4 : ℝ) ^ m * Real.log ‖(Work.Bottcher.pMap c)^[m] z‖) N
    rw [h]
    simp only [Function.iterate_zero_apply, pow_zero, one_mul]
    rw [show (1 / 4 : ℝ) = ((4 : ℝ))⁻¹ by norm_num, inv_pow]
  -- ## The partial sums of real parts converge
  have hA : Tendsto
      (fun N : ℕ => (∑ k ∈ Finset.range N,
          (((1 / 4 : ℝ) ^ (k + 1) : ℂ) * L ((Work.Bottcher.pMap c)^[k] z))).re)
      atTop (nhds (Work.Bottcher.green c z - Real.log ‖z‖)) :=
    Filter.Tendsto.congr' (Eventually.of_forall fun N => (htel N).symm)
      ((tendsto_fourPow_inv_log_norm_pMap_iterate c z hz).sub
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => Real.log ‖z‖) atTop (nhds (Real.log ‖z‖))))
  -- ## Summability of the series
  have hsumm : Summable
      (fun k : ℕ => ((1 / 4 : ℝ) ^ (k + 1) : ℂ) * L ((Work.Bottcher.pMap c)^[k] z)) := by
    have hsmall : ∀ᶠ w : ℂ in Filter.cocompact ℂ, ‖L w‖ < 1 := by
      filter_upwards [hLt.eventually (Metric.ball_mem_nhds (0 : ℂ) one_pos)] with w hw
      simpa [dist_eq_norm] using hw
    have hiter : Tendsto (fun k : ℕ => (Work.Bottcher.pMap c)^[k] z) atTop
        (Filter.cocompact ℂ) := by
      have hT : Tendsto (fun n : ℕ => ‖(Tantibar c)^[n] z‖) atTop atTop :=
        (Work.Bottcher.Green.green_pos_iff c z).mp hz
      have h2 : Tendsto (fun k : ℕ => 2 * k) atTop atTop :=
        tendsto_atTop_atTop.mpr (fun b => ⟨b, fun a ha => by omega⟩)
      have hnorm : Tendsto (fun k : ℕ => ‖(Work.Bottcher.pMap c)^[k] z‖) atTop atTop := by
        refine (hT.comp h2).congr' (Eventually.of_forall (fun k => ?_))
        simp only [Function.comp_apply]
        rw [Work.Bottcher.pMap_iterate]
      exact tendsto_cocompact_of_tendsto_dist_comp_atTop 0 (by simpa using hnorm)
    have hbdd : ∀ᶠ k : ℕ in atTop, ‖L ((Work.Bottcher.pMap c)^[k] z)‖ < 1 :=
      hiter.eventually hsmall
    refine Summable.of_norm_bounded_eventually_nat (g := fun k : ℕ => (1 / 4 : ℝ) ^ k)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)) ?_
    filter_upwards [hbdd] with k hk
    have hcoef : ‖(((1 / 4 : ℝ) ^ (k + 1) : ℂ))‖ = (1 / 4 : ℝ) ^ (k + 1) := by
      rw [← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [norm_mul, hcoef]
    calc (1 / 4 : ℝ) ^ (k + 1) * ‖L ((Work.Bottcher.pMap c)^[k] z)‖
        ≤ (1 / 4 : ℝ) ^ (k + 1) * 1 := mul_le_mul_of_nonneg_left hk.le (by positivity)
      _ = (1 / 4 : ℝ) ^ (k + 1) := mul_one _
      _ ≤ (1 / 4 : ℝ) ^ k := pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ k)
  -- ## The partial sums converge to the series
  have hB : Tendsto
      (fun N : ℕ => (∑ k ∈ Finset.range N,
          (((1 / 4 : ℝ) ^ (k + 1) : ℂ) * L ((Work.Bottcher.pMap c)^[k] z))).re)
      atTop (nhds ((∑' k : ℕ,
        ((1 / 4 : ℝ) ^ (k + 1) : ℂ) * L ((Work.Bottcher.pMap c)^[k] z)).re)) := by
    have h := hsumm.hasSum.tendsto_sum_nat
    exact (Complex.continuous_re.tendsto
      (∑' k : ℕ, ((1 / 4 : ℝ) ^ (k + 1) : ℂ) * L ((Work.Bottcher.pMap c)^[k] z))).comp h
  exact tendsto_nhds_unique hB hA

end Work.Bottcher.Contraction
