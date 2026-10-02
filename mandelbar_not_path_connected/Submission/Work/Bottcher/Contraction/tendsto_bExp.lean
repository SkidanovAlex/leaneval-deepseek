/-
# `tendsto_bExp`: the Böttcher-type series of a function vanishing at infinity

Let `p_c = pMap c = T_c ∘ T_c` be the holomorphic second iterate of the tricorn map,
a monic quartic.  If `L : ℂ → ℂ` vanishes at infinity (`Tendsto L (cocompact ℂ) (𝓝 0)`,
no continuity needed), then the series

`z ↦ ∑'_k 4^{-(k+1)} · L (p_c^[k] z)`

vanishes at infinity as well.  The point is that the `p_c`-orbit of a point `z` of large
modulus stays large (indeed never comes closer to the origin than `z` itself), so that
*every* term of the series is small, and the geometric weights `4^{-(k+1)}` have total
mass `1/3`.
-/
import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Escape.escape_step

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Bottcher.Contraction

open Filter Function
open scoped Topology ComplexConjugate

open LeanEval.ComplexAnalysis (Tantibar)

/-! ## The escape radius of `pMap c` -/

/-- The escape radius `2 * (1 + ‖c‖)` of the tricorn family dominates its growth constant
`max 2 ‖c‖`. -/
lemma max_two_norm_le_escapeRadius (c : ℂ) : max 2 ‖c‖ ≤ Work.Bottcher.escapeRadius c := by
  rw [Work.Bottcher.escapeRadius]
  have h : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  exact max_le (by linarith) (by linarith)

/-- **The orbit of `T_c` never comes closer to the origin than the starting point.**  If
`‖z‖ ≥ max 2 ‖c‖` then `‖z‖ ≤ ‖(T_c)^[n] z‖` for every `n`.  (This is just the sharp escape
criterion `Work.Escape.escape_step`, iterated.) -/
lemma norm_le_norm_iterate_Tantibar (c z : ℂ) (hz : max 2 ‖c‖ ≤ ‖z‖) (n : ℕ) :
    ‖z‖ ≤ ‖(Tantibar c)^[n] z‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hw : max 2 ‖c‖ ≤ ‖(Tantibar c)^[n] z‖ := le_trans hz ih
    have hstep : ‖(Tantibar c)^[n] z‖ ≤ ‖Tantibar c ((Tantibar c)^[n] z)‖ :=
      Work.Escape.escape_step (Tantibar c) 2 ‖c‖ (Work.Escape.monicGrowth_Tantibar c) le_rfl
        (le_trans (le_max_left _ _) hw) (le_trans (le_max_right _ _) hw)
    exact le_trans ih (by simpa only [Function.iterate_succ_apply'] using hstep)

/-- Same statement for the holomorphic second iterate `pMap c = T_c^[2]`. -/
lemma norm_le_norm_iterate_pMap (c z : ℂ) (hz : max 2 ‖c‖ ≤ ‖z‖) (k : ℕ) :
    ‖z‖ ≤ ‖(Work.Bottcher.pMap c)^[k] z‖ := by
  rw [Work.Bottcher.pMap_iterate]
  exact norm_le_norm_iterate_Tantibar c z hz (2 * k)

/-! ## The main estimate -/

/-- The geometric weights `4^{-(k+1)}` have total mass `1/3`. -/
lemma tsum_four_pow_succ : (∑' k : ℕ, ((1 / 4 : ℝ) ^ (k + 1))) = 1 / 3 := by
  rw [show (fun k : ℕ => (1 / 4 : ℝ) ^ (k + 1)) = (fun k => (1 / 4 : ℝ) * (1 / 4) ^ k) from
    funext (fun k => by rw [pow_succ'])]
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

theorem tendsto_bExp (c : ℂ) {L : ℂ → ℂ} (hLt : Filter.Tendsto L (Filter.cocompact ℂ) (nhds 0)) :
    Filter.Tendsto
      (fun z : ℂ => ∑' k : ℕ, ((1 / 4 : ℝ) ^ (k + 1) : ℂ) * L ((Work.Bottcher.pMap c)^[k] z))
      (Filter.cocompact ℂ) (nhds 0) := by
  refine Metric.tendsto_nhds.mpr (fun ε hε => ?_)
  rw [Filter.eventually_iff]
  -- `L` is small outside a ball of radius `r`
  have hball : {w : ℂ | ‖L w‖ < ε} ∈ Filter.cocompact ℂ := by
    rw [← Filter.eventually_iff]
    filter_upwards [Metric.tendsto_nhds.mp hLt ε hε] with w hw
    rwa [dist_zero_right] at hw
  obtain ⟨r, hr⟩ := (Metric.mem_cocompact_iff_closedBall_compl_subset (0 : ℂ)).mp hball
  -- everything outside the ball of radius `max r (escapeRadius c)` works
  refine Metric.mem_cocompact_of_closedBall_compl_subset (0 : ℂ)
    ⟨max r (Work.Bottcher.escapeRadius c), ?_⟩
  rintro z hz
  rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hz
  simp only [Set.mem_ofPred_eq, dist_zero_right]
  -- `hz : max r (escapeRadius c) < ‖z‖`
  have hzr : r < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hz
  have hzc : max 2 ‖c‖ ≤ ‖z‖ :=
    le_trans (max_two_norm_le_escapeRadius c) (le_trans (le_max_right _ _) hz.le)
  have hiter : ∀ k : ℕ, ‖z‖ ≤ ‖(Work.Bottcher.pMap c)^[k] z‖ :=
    fun k => norm_le_norm_iterate_pMap c z hzc k
  -- every term of the series is small
  have hLk : ∀ k : ℕ, ‖L ((Work.Bottcher.pMap c)^[k] z)‖ < ε := by
    intro k
    apply hr
    rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le]
    exact lt_of_lt_of_le hzr (hiter k)
  -- the geometric majorant
  have hgeo : Summable (fun k : ℕ => (1 / 4 : ℝ) ^ (k + 1)) := by
    have h0 : Summable (fun k : ℕ => (1 / 4 : ℝ) ^ k) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    simpa only [pow_succ'] using h0.mul_left (1 / 4 : ℝ)
  have hterm_le : ∀ k : ℕ,
      ‖((1 / 4 : ℝ) ^ (k + 1) : ℂ) * L ((Work.Bottcher.pMap c)^[k] z)‖
        ≤ (1 / 4 : ℝ) ^ (k + 1) * ε := by
    intro k
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]
    exact mul_le_mul_of_nonneg_left (hLk k).le (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) _)
  have hsumm : Summable
      (fun k : ℕ => ‖((1 / 4 : ℝ) ^ (k + 1) : ℂ) * L ((Work.Bottcher.pMap c)^[k] z)‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hterm_le (hgeo.mul_right ε)
  calc ‖∑' k : ℕ, ((1 / 4 : ℝ) ^ (k + 1) : ℂ) * L ((Work.Bottcher.pMap c)^[k] z)‖
      ≤ ∑' k : ℕ, ‖((1 / 4 : ℝ) ^ (k + 1) : ℂ) * L ((Work.Bottcher.pMap c)^[k] z)‖ :=
        norm_tsum_le_tsum_norm hsumm
    _ ≤ ∑' k : ℕ, (1 / 4 : ℝ) ^ (k + 1) * ε :=
        Summable.tsum_le_tsum hterm_le hsumm (hgeo.mul_right ε)
    _ = (∑' k : ℕ, (1 / 4 : ℝ) ^ (k + 1)) * ε := tsum_mul_right
    _ = ε / 3 := by rw [tsum_four_pow_succ]; ring
    _ < ε := by linarith

end Work.Bottcher.Contraction
