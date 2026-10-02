/-
# The real part of the Böttcher exponent series on the critical domain

This is the `CritDomain` version of `Work.Bottcher.Contraction.bExp_re`: for `L` a holomorphic
logarithm of the *normalised factor* `normFactor c z = p_c z / z^4` on

`CritDomain c = {z | G_c 0 < G_c z}`

which vanishes at infinity, the Böttcher exponent series `bExp c L z = Σ_k 4^{-(k+1)} L (p_c^k z)`
has real part `G_c z - log ‖z‖`.

The argument is the same as for `bExp_re`: the real parts telescope along the `p_c`-orbit,

`Re L w = log ‖p_c w‖ - 4 log ‖w‖`  (because `‖exp (L w)‖ = ‖normFactor c w‖`),

so the `N`-th partial sum of the real parts equals `4^{-N} log ‖p_c^N z‖ - log ‖z‖`, which
converges to `G_c z - log ‖z‖` by `tendsto_fourPow_inv_log_norm_pMap_iterate`; summability
follows from `L → 0` at infinity and the orbit escaping to infinity.

The only difference from `bExp_re` is the bookkeeping of positivity: instead of the hypothesis
`G_c 0 = 0`, we use that `CritDomain c` is invariant under `p_c` and does not contain `0`, so no
iterate of `z` is `0` and the Green function is positive along the orbit.

Note: `hLan` (analyticity of `L`) is part of the interface but not used by the argument.
-/
import Mathlib
import Submission.Work.Bottcher.Contraction.exists_analyticBottcher_of_mem_mandelbar
import Submission.Work.Bottcher.Contraction.bExp_re
import Submission.Work.Bottcher.Contraction.tendsto_fourPow_inv_log_norm_pMap_iterate
import Submission.Work.Bottcher.CritBasic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Function
open scoped Topology

namespace Work.Bottcher.Contraction

-- `hLan` is part of the interface but not needed by the argument.
set_option linter.unusedVariables false

theorem bExp_re_CritDomain (c : ℂ) {L : ℂ → ℂ}
    (hLan : AnalyticOnNhd ℂ L (Work.Bottcher.CritDomain c))
    (hLexp : ∀ z : ℂ, z ∈ Work.Bottcher.CritDomain c →
      Complex.exp (L z) = Work.Bottcher.normFactor c z)
    (hLt : Filter.Tendsto L (Filter.cocompact ℂ) (nhds (0 : ℂ)))
    {z : ℂ} (hz : z ∈ Work.Bottcher.CritDomain c) :
    (Work.Bottcher.Contraction.bExp c L z).re
      = Work.Bottcher.green c z - Real.log ‖z‖ := by
  classical
  rw [bExp_def]
  -- ## Membership of the `p_c`-orbit of `z` in the critical domain
  have horb : ∀ k : ℕ, (Work.Bottcher.pMap c)^[k] z ∈ Work.Bottcher.CritDomain c :=
    fun k => Work.Bottcher.CritBasic.pMap_iterate_mem_CritDomain hz k
  -- ## Non-vanishing along the orbit (the critical domain does not contain `0`)
  have hne : ∀ k : ℕ, (Work.Bottcher.pMap c)^[k] z ≠ 0 :=
    fun k hk => Work.Bottcher.CritBasic.zero_notMem_CritDomain c (hk ▸ horb k)
  -- ## Positivity of the Green function along the orbit
  have hgz : 0 < Work.Bottcher.green c z := by
    have h0 : (0 : ℝ) ≤ Work.Bottcher.greenParam c := by
      rw [Work.Bottcher.greenParam_def]
      exact Work.Bottcher.Green.green_nonneg c 0
    have hlt := Work.Bottcher.mem_CritDomain.mp hz
    linarith
  have hgp : ∀ k : ℕ, 0 < Work.Bottcher.green c ((Work.Bottcher.pMap c)^[k] z) := by
    intro k
    rw [green_pMap_iterate c z k]
    exact mul_pos (pow_pos (by norm_num) k) hgz
  -- ## The real part of `L` at a point of the critical domain
  have hLexp' : ∀ w : ℂ, w ∈ Work.Bottcher.CritDomain c →
      Complex.exp (L w) = Work.Bottcher.pMap c w / w ^ 4 := by
    intro w hw
    simpa only [Work.Bottcher.normFactor] using hLexp w hw
  have hre_norm : ∀ w : ℂ, w ∈ Work.Bottcher.CritDomain c →
      (L w).re = Real.log ‖Work.Bottcher.pMap c w / w ^ 4‖ := by
    intro w hw
    rw [← hLexp' w hw, Complex.norm_exp, Real.log_exp]
  have hlog_div : ∀ w : ℂ, w ∈ Work.Bottcher.CritDomain c → w ≠ 0 →
      Real.log ‖Work.Bottcher.pMap c w / w ^ 4‖
        = Real.log ‖Work.Bottcher.pMap c w‖ - 4 * Real.log ‖w‖ := by
    intro w hw hw0
    have hpw0 : Work.Bottcher.pMap c w ≠ 0 :=
      fun h0 => Work.Bottcher.CritBasic.zero_notMem_CritDomain c
        (h0 ▸ Work.Bottcher.CritBasic.pMap_mem_CritDomain hw)
    rw [norm_div, norm_pow, Real.log_div (norm_ne_zero_iff.mpr hpw0)
      (pow_ne_zero 4 (norm_ne_zero_iff.mpr hw0)), Real.log_pow]
    push_cast
    ring
  have hterm_re : ∀ k : ℕ, (L ((Work.Bottcher.pMap c)^[k] z)).re
      = Real.log ‖(Work.Bottcher.pMap c)^[k + 1] z‖
        - 4 * Real.log ‖(Work.Bottcher.pMap c)^[k] z‖ := by
    intro k
    rw [hre_norm _ (horb k), hlog_div _ (horb k) (hne k), Function.iterate_succ_apply']
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
      ((tendsto_fourPow_inv_log_norm_pMap_iterate c z hgz).sub
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => Real.log ‖z‖) atTop (nhds (Real.log ‖z‖))))
  -- ## Summability of the series
  have hsumm : Summable
      (fun k : ℕ => ((1 / 4 : ℝ) ^ (k + 1) : ℂ) * L ((Work.Bottcher.pMap c)^[k] z)) := by
    have hsmall : ∀ᶠ w : ℂ in Filter.cocompact ℂ, ‖L w‖ < 1 := by
      filter_upwards [hLt.eventually (Metric.ball_mem_nhds (0 : ℂ) one_pos)] with w hw
      simpa [dist_eq_norm] using hw
    have hbdd : ∀ᶠ k : ℕ in atTop, ‖L ((Work.Bottcher.pMap c)^[k] z)‖ < 1 :=
      (tendsto_iterate_pMap_cocompact c hgz).eventually hsmall
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
