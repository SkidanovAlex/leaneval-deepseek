import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Escape.Defs
import Submission.Work.Escape.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Function
open scoped Topology ComplexConjugate

namespace Work.Bottcher.Core

open LeanEval.ComplexAnalysis (Tantibar)
open Work.Bottcher

/-! ## Auxiliary objects

`logOrbitNorm c z n = log ‖p_c^n z‖` is the quantity whose exponential is the norm of the
`n`-th partial Böttcher product.  The main result of the file is that its (scaled) limit is the
Green function, so that `‖bottcher c z‖ = exp (green c z)`. -/

/-- The logarithm of the norm of the `n`-th iterate of `p_c` at `z`. -/
noncomputable def logOrbitNorm (c z : ℂ) (n : ℕ) : ℝ := Real.log ‖(pMap c)^[n] z‖

@[simp] theorem logOrbitNorm_zero (c z : ℂ) : logOrbitNorm c z 0 = Real.log ‖z‖ := by
  simp [logOrbitNorm]

/-! ## The normalised factor converges to `1` along an escaping orbit -/

/-- The algebraic identity behind the asymptotic of the normalised factor. -/
theorem normFactor_sub_one (c w : ℂ) (hw : w ≠ 0) :
    normFactor c w - 1 = (2 * conj c * w ^ 2 + ((conj c) ^ 2 + c)) / w ^ 4 := by
  rw [normFactor, pMap_apply]
  field_simp
  ring

/-- Quantitative bound for `‖normFactor c w - 1‖`; the two terms on the right tend to `0` as
`‖w‖ → ∞`. -/
theorem norm_normFactor_sub_one_le (c w : ℂ) (hw : w ≠ 0) :
    ‖normFactor c w - 1‖ ≤ 2 * ‖c‖ / ‖w‖ ^ 2 + (‖c‖ ^ 2 + ‖c‖) / ‖w‖ ^ 4 := by
  have hnum : ‖2 * conj c * w ^ 2 + ((conj c) ^ 2 + c)‖
      ≤ 2 * ‖c‖ * ‖w‖ ^ 2 + (‖c‖ ^ 2 + ‖c‖) := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · have h : ‖2 * conj c * w ^ 2‖ = 2 * ‖c‖ * ‖w‖ ^ 2 := by
        simp only [norm_mul, norm_pow, Complex.norm_conj, Complex.norm_ofNat]
      exact le_of_eq h
    · calc ‖(conj c) ^ 2 + c‖ ≤ ‖(conj c) ^ 2‖ + ‖c‖ := norm_add_le _ _
        _ = ‖c‖ ^ 2 + ‖c‖ := by rw [norm_pow, Complex.norm_conj]
  rw [normFactor_sub_one c w hw, norm_div, norm_pow]
  calc ‖2 * conj c * w ^ 2 + ((conj c) ^ 2 + c)‖ / ‖w‖ ^ 4
      ≤ (2 * ‖c‖ * ‖w‖ ^ 2 + (‖c‖ ^ 2 + ‖c‖)) / ‖w‖ ^ 4 :=
        div_le_div_of_nonneg_right hnum (by positivity)
    _ = 2 * ‖c‖ / ‖w‖ ^ 2 + (‖c‖ ^ 2 + ‖c‖) / ‖w‖ ^ 4 := by
        have hw' : (‖w‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hw
        field_simp

/-- Along an orbit whose norms escape to infinity, the normalised factor tends to `1`. -/
theorem normFactor_tendsto_one (c z : ℂ)
    (hz : ∀ n : ℕ, (pMap c)^[n] z ≠ 0)
    (hu : Tendsto (fun n : ℕ => ‖(pMap c)^[n] z‖) atTop atTop) :
    Tendsto (fun n : ℕ => normFactor c ((pMap c)^[n] z)) atTop (nhds 1) := by
  have hsq : Tendsto (fun x : ℝ => x ^ 2) atTop atTop :=
    tendsto_atTop_atTop.mpr (fun b => ⟨max b 1, fun a ha => by
      have hb : b ≤ a := (le_max_left b 1).trans ha
      have h1 : (1 : ℝ) ≤ a := (le_max_right b 1).trans ha
      nlinarith [hb, h1]⟩)
  have h2 : Tendsto (fun n : ℕ => ‖(pMap c)^[n] z‖ ^ 2) atTop atTop := hsq.comp hu
  have h4 : Tendsto (fun n : ℕ => ‖(pMap c)^[n] z‖ ^ 4) atTop atTop := by
    refine Filter.Tendsto.congr' (Filter.Eventually.of_forall (fun n => ?_)) (hsq.comp h2)
    show (‖(pMap c)^[n] z‖ ^ 2) ^ 2 = ‖(pMap c)^[n] z‖ ^ 4
    ring
  have hg : Tendsto (fun n : ℕ => 2 * ‖c‖ / ‖(pMap c)^[n] z‖ ^ 2
        + (‖c‖ ^ 2 + ‖c‖) / ‖(pMap c)^[n] z‖ ^ 4) atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ => 2 * ‖c‖ / ‖(pMap c)^[n] z‖ ^ 2) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop h2
    have h2' : Tendsto (fun n : ℕ => (‖c‖ ^ 2 + ‖c‖) / ‖(pMap c)^[n] z‖ ^ 4) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop h4
    simpa using h1.add h2'
  have hle : ∀ᶠ n : ℕ in atTop, ‖normFactor c ((pMap c)^[n] z) - 1‖
      ≤ 2 * ‖c‖ / ‖(pMap c)^[n] z‖ ^ 2 + (‖c‖ ^ 2 + ‖c‖) / ‖(pMap c)^[n] z‖ ^ 4 :=
    Filter.Eventually.of_forall (fun n => norm_normFactor_sub_one_le c _ (hz n))
  have hz0 : Tendsto (fun n : ℕ => ‖normFactor c ((pMap c)^[n] z) - 1‖) atTop (nhds 0) :=
    squeeze_zero' (Filter.Eventually.of_forall (fun n => norm_nonneg _)) hle hg
  have hz1 : Tendsto (fun n : ℕ => normFactor c ((pMap c)^[n] z) - 1) atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hz0
  have hfin : Tendsto (fun n : ℕ => (normFactor c ((pMap c)^[n] z) - 1) + 1) atTop
      (nhds (0 + 1)) :=
    hz1.add (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (nhds 1))
  simpa using hfin

/-! ## The main theorem -/

theorem norm_bottcher_eq_exp_green (c z : ℂ)
    (h : Filter.Tendsto (fun n : ℕ => ‖(LeanEval.ComplexAnalysis.Tantibar c)^[n] z‖) Filter.atTop Filter.atTop)
    (hg : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n *
      Work.Escape.logPos ‖(LeanEval.ComplexAnalysis.Tantibar c)^[n] z‖) Filter.atTop
      (nhds (Work.Bottcher.green c z)))
    (hz : ∀ n : ℕ, (Work.Bottcher.pMap c)^[n] z ≠ 0) :
    ‖Work.Bottcher.bottcher c z‖ = Real.exp (Work.Bottcher.green c z) := by
  have hz0 : z ≠ 0 := by simpa using hz 0
  -- the norms of the `p_c`-iterates escape to infinity
  have h2N : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
    tendsto_atTop_atTop.mpr (fun b => ⟨b, fun a ha => by omega⟩)
  have hu : Tendsto (fun n : ℕ => ‖(pMap c)^[n] z‖) atTop atTop := by
    have hsub : Tendsto (fun N : ℕ => ‖(Tantibar c)^[2 * N] z‖) atTop atTop := h.comp h2N
    refine Filter.Tendsto.congr' (Filter.Eventually.of_forall (fun N => ?_)) hsub
    show ‖(Tantibar c)^[2 * N] z‖ = ‖(pMap c)^[N] z‖
    rw [Work.Bottcher.pMap_iterate]
  -- `log (normFactor)` tends to `0`
  have hNF := normFactor_tendsto_one c z hz hu
  have hlog : Tendsto (fun n : ℕ => Complex.log (normFactor c ((pMap c)^[n] z))) atTop (nhds 0) := by
    have hc := hNF.clog Complex.one_mem_slitPlane
    simpa using hc
  -- the Böttcher series is summable
  have hev : ∀ᶠ n : ℕ in atTop, ‖Complex.log (normFactor c ((pMap c)^[n] z))‖ ≤ 1 := by
    filter_upwards [hlog.eventually (Metric.ball_mem_nhds (0 : ℂ) one_pos)] with n hn
    rw [dist_zero_right] at hn
    linarith
  have hbdd : ∀ᶠ n : ℕ in atTop, ‖bottcherTerm c n z‖ ≤ (1 / 4 : ℝ) ^ (n + 1) := by
    filter_upwards [hev] with n hn
    rw [bottcherTerm, norm_mul, ← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    nlinarith [hn, show (0 : ℝ) ≤ (1 / 4 : ℝ) ^ (n + 1) by positivity]
  have hsum : Summable (fun n : ℕ => bottcherTerm c n z) := by
    have hgeo : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ (n + 1)) := by
      have hbase := summable_geometric_of_norm_lt_one (x := (1 / 4 : ℝ)) (by norm_num)
      simpa [pow_succ, mul_comm] using hbase.mul_left (1 / 4 : ℝ)
    apply Summable.of_norm_bounded_eventually hgeo
    rw [Nat.cofinite_eq_atTop]
    exact hbdd
  -- partial sums converge to the series
  have hS : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, bottcherTerm c n z) atTop
      (nhds (bottcherSeries c z)) := by
    simpa [bottcherSeries] using hsum.hasSum.tendsto_sum_nat
  -- partial products converge to the Böttcher coordinate
  have hpart : Tendsto (fun N : ℕ => bottcherPartial c N z) atTop (nhds (bottcher c z)) := by
    have hcont : Tendsto Complex.exp (nhds (bottcherSeries c z))
        (nhds (Complex.exp (bottcherSeries c z))) := Complex.continuous_exp.continuousAt
    have hexp := hcont.comp hS
    have hmul : Tendsto (fun N : ℕ => z * Complex.exp (∑ n ∈ Finset.range N, bottcherTerm c n z))
        atTop (nhds (z * Complex.exp (bottcherSeries c z))) := hexp.const_mul z
    simpa [bottcherPartial, bottcher] using hmul
  have hnormpart : Tendsto (fun N : ℕ => ‖bottcherPartial c N z‖) atTop (nhds ‖bottcher c z‖) := by
    have hcont : Tendsto (fun w : ℂ => ‖w‖) (nhds (bottcher c z)) (nhds ‖bottcher c z‖) :=
      continuous_norm.continuousAt
    exact hcont.comp hpart
  -- telescoping: `‖bottcherPartial c N z‖ = exp (4^{-N} log ‖p_c^N z‖)`
  have hre : ∀ n : ℕ, (bottcherTerm c n z).re
      = (1 / 4 : ℝ) ^ (n + 1) * (logOrbitNorm c z (n + 1) - 4 * logOrbitNorm c z n) := by
    intro n
    have hnf : normFactor c ((pMap c)^[n] z) = (pMap c)^[n + 1] z / ((pMap c)^[n] z) ^ 4 := by
      rw [normFactor, Function.iterate_succ_apply']
    have h1 : (‖(pMap c)^[n + 1] z‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr (hz (n + 1))
    have h2 : (‖(pMap c)^[n] z‖ : ℝ) ^ 4 ≠ 0 := pow_ne_zero 4 (norm_ne_zero_iff.mpr (hz n))
    have hlogdiv : Real.log ‖normFactor c ((pMap c)^[n] z)‖
        = logOrbitNorm c z (n + 1) - 4 * logOrbitNorm c z n := by
      rw [hnf, norm_div, norm_pow, Real.log_div h1 h2, Real.log_pow]
      simp only [logOrbitNorm]
      ring
    rw [bottcherTerm, Complex.mul_re, ← Complex.ofReal_pow, Complex.ofReal_re,
      Complex.ofReal_im, Complex.log_re, hlogdiv]
    ring
  have htel : ∀ N : ℕ, ‖bottcherPartial c N z‖
      = Real.exp ((1 / 4 : ℝ) ^ N * logOrbitNorm c z N) := by
    intro N
    have hsum_re : (∑ n ∈ Finset.range N, bottcherTerm c n z).re
        = (1 / 4 : ℝ) ^ N * logOrbitNorm c z N - logOrbitNorm c z 0 := by
      rw [Complex.re_sum]
      have h2 : ∀ n : ℕ, (1 / 4 : ℝ) ^ (n + 1)
            * (logOrbitNorm c z (n + 1) - 4 * logOrbitNorm c z n)
          = (1 / 4 : ℝ) ^ (n + 1) * logOrbitNorm c z (n + 1)
            - (1 / 4 : ℝ) ^ n * logOrbitNorm c z n := by
        intro n
        rw [pow_succ]
        ring
      rw [Finset.sum_congr rfl (fun n _ => hre n),
        Finset.sum_congr rfl (fun n _ => h2 n)]
      have h := Finset.sum_range_sub (fun m => (1 / 4 : ℝ) ^ m * logOrbitNorm c z m) N
      simpa using h
    calc ‖bottcherPartial c N z‖
        = ‖z‖ * Real.exp ((1 / 4 : ℝ) ^ N * logOrbitNorm c z N - Real.log ‖z‖) := by
          rw [bottcherPartial, norm_mul, Complex.norm_exp, hsum_re, logOrbitNorm_zero]
      _ = Real.exp (Real.log ‖z‖)
            * Real.exp ((1 / 4 : ℝ) ^ N * logOrbitNorm c z N - Real.log ‖z‖) := by
          rw [Real.exp_log (norm_pos_iff.mpr hz0)]
      _ = Real.exp ((1 / 4 : ℝ) ^ N * logOrbitNorm c z N) := by
          rw [← Real.exp_add]
          congr 1
          ring
  -- the scaled logarithms converge to the Green function
  have hgreen : Tendsto (fun N : ℕ => (1 / 4 : ℝ) ^ N * logOrbitNorm c z N) atTop
      (nhds (green c z)) := by
    have hg2 : Tendsto (fun N : ℕ => (1 / 2 : ℝ) ^ (2 * N)
        * Work.Escape.logPos ‖(Tantibar c)^[2 * N] z‖) atTop (nhds (green c z)) := hg.comp h2N
    refine Filter.Tendsto.congr' ?_ hg2
    filter_upwards [hu.eventually (eventually_ge_atTop (1 : ℝ))] with N hN
    simp only [logOrbitNorm]
    rw [← Work.Bottcher.pMap_iterate c z N, Work.Escape.logPos_eq_log hN]
    rw [show (1 / 2 : ℝ) ^ (2 * N) = (1 / 4 : ℝ) ^ N by rw [pow_mul]; norm_num]
  have hexpg : Tendsto (fun N : ℕ => Real.exp ((1 / 4 : ℝ) ^ N * logOrbitNorm c z N)) atTop
      (nhds (Real.exp (green c z))) := by
    have hcont : Tendsto Real.exp (nhds (green c z)) (nhds (Real.exp (green c z))) :=
      Real.continuous_exp.continuousAt
    exact hcont.comp hgreen
  have hA : Tendsto (fun N : ℕ => ‖bottcherPartial c N z‖) atTop (nhds (Real.exp (green c z))) :=
    Filter.Tendsto.congr' (Filter.Eventually.of_forall (fun N => (htel N).symm)) hexpg
  exact tendsto_nhds_unique hnormpart hA

end Work.Bottcher.Core
