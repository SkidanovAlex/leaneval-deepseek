import Mathlib
import Submission.Work.NAKANE.Defs
import Submission.Work.Bottcher.Core.analyticAt_bottcher
import Submission.Work.Bottcher.Inverse.eq_bottcher_of_analytic_far

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Function Set
open scoped Topology ComplexConjugate

set_option autoImplicit false

namespace Work.NAKANE.BottcherFar

noncomputable section

/-! ## Elementary joint continuities

The Böttcher product formula

`bottcher c z = z * exp (Σ_n 4^{-(n+1)} log (normFactor c ((pMap c)^[n] z)))`

is a limit of the continuous partial products `bottcherPartial c N z`, and on the far region
`{escapeRadius c < ‖z‖}` the series of logarithms is uniformly dominated by the summable sequence
`(15/8) (1/4)^n` (`Work.Bottcher.Core.norm_term_le`).  The pieces of the joint continuity are
collected here: the joint continuity of `(c,z) ↦ pMap c z`, of its iterates, of `normFactor` at
points with nonzero second coordinate, and hence of each term of the series (using that the
argument of `Complex.log` lies in `Complex.slitPlane`, where `log` is continuous, and that
`Complex.log` is *not* continuous on the negative real axis). -/

/-- `(c, w) ↦ p_c w = (w^2 + c̄)^2 + c` is jointly continuous. -/
theorem continuous_joint_pMap :
    Continuous (fun q : ℂ × ℂ => Work.Bottcher.pMap q.1 q.2) := by
  have h : (fun q : ℂ × ℂ => Work.Bottcher.pMap q.1 q.2)
      = fun q => (q.2 ^ 2 + conj q.1) ^ 2 + q.1 := by
    funext q; rw [Work.Bottcher.pMap_apply]
  rw [h]
  fun_prop

/-- The parametrised iterate `(c, w) ↦ (p_c)^[n] w` is jointly continuous. -/
theorem continuous_joint_iterate (n : ℕ) :
    Continuous (fun q : ℂ × ℂ => (Work.Bottcher.pMap q.1)^[n] q.2) := by
  induction n with
  | zero => exact continuous_snd
  | succ n ih =>
    refine (continuous_joint_pMap.comp (continuous_fst.prodMk ih)).congr (fun q => ?_)
    simp [Function.comp_apply, Function.iterate_succ_apply']

/-- `(c, w) ↦ normFactor c w` is jointly continuous at every point whose second coordinate is
nonzero (where the division `p_c w / w^4` makes sense). -/
theorem continuousAt_joint_normFactor {c w : ℂ} (hw : w ≠ 0) :
    ContinuousAt (fun q : ℂ × ℂ => Work.Bottcher.normFactor q.1 q.2) (c, w) := by
  have hnum : ContinuousAt (fun q : ℂ × ℂ => Work.Bottcher.pMap q.1 q.2) (c, w) :=
    continuous_joint_pMap.continuousAt
  have hden : ContinuousAt (fun q : ℂ × ℂ => q.2 ^ 4) (c, w) := by fun_prop
  have hne : (fun q : ℂ × ℂ => q.2 ^ 4) (c, w) ≠ 0 := by simp [hw]
  exact hnum.div hden hne

/-! ## Joint continuity of the terms of the Böttcher series -/

/-- On the far region `{escapeRadius c < ‖z‖}` the whole `p_c`-orbit of `z` stays in the far
region (`Work.Bottcher.Inverse.escapeRadius_lt_norm_pMap_iterate`), so every factor
`normFactor c ((pMap c)^[n] z)` lies in `Complex.slitPlane`, where `Complex.log` is continuous.
Hence the `n`-th term `bottcherTerm c n z` of the Böttcher series is jointly continuous at every
point of the far region. -/
theorem continuousAt_joint_bottcherTerm {c z : ℂ}
    (hz : Work.Bottcher.escapeRadius c < ‖z‖) (n : ℕ) :
    ContinuousAt (fun q : ℂ × ℂ => Work.Bottcher.bottcherTerm q.1 n q.2) (c, z) := by
  have hlt := Work.Bottcher.Inverse.escapeRadius_lt_norm_pMap_iterate c hz n
  have hpos := Work.Bottcher.Core.escapeRadius_pos c
  have hv0 : (Work.Bottcher.pMap c)^[n] z ≠ 0 := by
    intro h; rw [h, norm_zero] at hlt; linarith
  have hG : ContinuousAt
      (fun p : ℂ × ℂ => (p.1, (Work.Bottcher.pMap p.1)^[n] p.2)) (c, z) :=
    (continuous_fst.prodMk (continuous_joint_iterate n)).continuousAt
  have h1 : ContinuousAt
      (fun q : ℂ × ℂ => Work.Bottcher.normFactor q.1 ((Work.Bottcher.pMap q.1)^[n] q.2)) (c, z) :=
    (continuousAt_joint_normFactor (c := c)
      (w := (Work.Bottcher.pMap c)^[n] z) hv0).comp
      (f := fun p : ℂ × ℂ => (p.1, (Work.Bottcher.pMap p.1)^[n] p.2)) (x := (c, z)) hG
  have hmem : Work.Bottcher.normFactor c ((Work.Bottcher.pMap c)^[n] z) ∈ Complex.slitPlane := by
    refine Work.Bottcher.Core.normFactor_mem_slitPlane c _ ?_
    have h2 : 1 + ‖c‖ ≤ Work.Bottcher.escapeRadius c := by
      rw [Work.Bottcher.escapeRadius]; nlinarith [norm_nonneg c]
    linarith
  have h2 : ContinuousAt
      (fun q : ℂ × ℂ =>
        Complex.log (Work.Bottcher.normFactor q.1 ((Work.Bottcher.pMap q.1)^[n] q.2)))
      (c, z) := h1.clog hmem
  exact h2.const_mul (((1 / 4 : ℝ) ^ (n + 1) : ℂ))

/-- The Böttcher series is jointly continuous on the far region, as the locally uniformly
convergent sum of its jointly continuous terms: the uniform majorant `(15/8) (1/4)^n` is summable
and bounds the `n`-th term on the whole far region (`Work.Bottcher.Core.norm_term_le`, using the
invariance of the far region under the orbit). -/
theorem continuousOn_joint_bottcherSeries :
    ContinuousOn (fun q : ℂ × ℂ => Work.Bottcher.bottcherSeries q.1 q.2)
      {p : ℂ × ℂ | Work.Bottcher.escapeRadius p.1 < ‖p.2‖} := by
  refine continuousOn_tsum (u := fun n : ℕ => (15 / 8) * (1 / 4 : ℝ) ^ n) ?_ ?_ ?_
  · intro n p hp
    exact (continuousAt_joint_bottcherTerm hp n).continuousWithinAt
  · exact (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) < 1)).mul_left (15 / 8)
  · intro n p hp
    have hpe : Work.Bottcher.escapeRadius p.1 < ‖p.2‖ := hp
    have hp' : 1 + ‖p.1‖ ≤ ‖p.2‖ := by
      have h2 : 1 + ‖p.1‖ ≤ Work.Bottcher.escapeRadius p.1 := by
        rw [Work.Bottcher.escapeRadius]; nlinarith [norm_nonneg p.1]
      linarith
    exact Work.Bottcher.Core.norm_term_le p.1 p.2 hp' n

/-! ## The main theorem -/

/-- **Joint continuity of the explicit product formula on the far region.**
`(c,z) ↦ Work.Bottcher.bottcher c z = z * exp (Σ_n 4^{-(n+1)} log (p_c^n z / (p_c^n z)^4))`
is continuous on the set `{(c,z) | escapeRadius c < ‖z‖}` (`escapeRadius c = 2 * (1 + ‖c‖)`).

For `‖z‖ > escapeRadius c` the whole `p_c`-orbit of `z` stays in the far region
(`Work.Bottcher.Inverse.escapeRadius_lt_norm_pMap_iterate`), and there every factor
`normFactor c w = p_c w / w^4` satisfies `‖normFactor c w - 1‖ ≤ 1/2` (indeed `= 1 + O(1/‖w‖)`), so
`Complex.log` is continuous at each factor and every term of the series is continuous in `(c,z)`;
the series is locally uniformly dominated (`Work.Bottcher.Core.norm_tsum_bottcherTerm_le`,
`Work.Bottcher.Inverse.norm_bottcherSeries_le_far`) because on a compact piece of the domain
`‖p_c^n z‖` grows like `‖z‖^{4^n}` with a uniform lower bound.  Conclude by local uniform
convergence of the partial products `bottcherPartial c N z`
(`Work.Bottcher.Series.tendsto_bottcherPartial`), each of which is continuous. -/
theorem continuousOn_jointBottcher :
    ContinuousOn Work.NAKANE.jointBottcher
      {p : ℂ × ℂ | Work.Bottcher.escapeRadius p.1 < ‖p.2‖} := by
  have hser := continuousOn_joint_bottcherSeries
  have hexp : ContinuousOn (fun q : ℂ × ℂ => Complex.exp (Work.Bottcher.bottcherSeries q.1 q.2))
      {p : ℂ × ℂ | Work.Bottcher.escapeRadius p.1 < ‖p.2‖} :=
    Complex.continuous_exp.comp_continuousOn hser
  have hfst : ContinuousOn (fun q : ℂ × ℂ => q.2)
      {p : ℂ × ℂ | Work.Bottcher.escapeRadius p.1 < ‖p.2‖} := continuous_snd.continuousOn
  exact hfst.mul hexp

end

end Work.NAKANE.BottcherFar
