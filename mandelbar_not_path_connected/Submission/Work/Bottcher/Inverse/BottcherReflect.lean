/-
# Elementary reflection / far-region lemmas for the inverse Böttcher theory

Support file for `Work.Bottcher.Inverse.injOn_analyticBottcher` (injectivity of an
analytic Böttcher coordinate of the tricorn quartic `p_c = T_c ∘ T_c`).

The tricorn map `T_c(z) = z̄² + c` is *even* (`T_c(-z) = T_c z`), hence so is the quartic
`p_c`; the Green function `G_c` is even as well, and the product-formula Böttcher
coordinate `bottcher c` is *odd* on the plane.  These are the symmetric inputs used by
the injectivity argument.

Also collected here: the fact that the closed far region `{‖z‖ ≥ escapeRadius c}` lies in
the escape set, the convergence `p_c^n z → ∞` for escaping `z`, the factorisation
`p_c u - p_c v = (u-v)(u+v)(u²+v²+2c̄)`, and the explicit radius `farR c` used for the
"far region injectivity".
-/
import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.Green.green_comm
import Submission.Work.Bottcher.Green.green_pos_iff
import Submission.Work.Bottcher.Core.eq_bottcher_of_analytic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Function
open scoped Topology ComplexConjugate

namespace Work.Bottcher.Inverse

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

noncomputable section

/-! ## Evenness of the dynamics -/

theorem Tantibar_neg (c z : ℂ) : Tantibar c (-z) = Tantibar c z := by
  simp [LeanEval.ComplexAnalysis.Tantibar]

theorem pMap_neg (c z : ℂ) : Work.Bottcher.pMap c (-z) = Work.Bottcher.pMap c z := by
  rw [Work.Bottcher.pMap_apply, Work.Bottcher.pMap_apply]; ring

theorem Tantibar_iterate_add_one_neg (c z : ℂ) (m : ℕ) :
    (Tantibar c)^[m + 1] (-z) = (Tantibar c)^[m + 1] z := by
  have h : (Tantibar c)^[m + 1] (-z) = (Tantibar c)^[m] (Tantibar c (-z)) :=
    Function.iterate_succ_apply (Tantibar c) m (-z)
  rw [h, Tantibar_neg, ← Function.iterate_succ_apply (Tantibar c) m z]

theorem pMap_iterate_add_one_neg (c z : ℂ) (m : ℕ) :
    (Work.Bottcher.pMap c)^[m + 1] (-z) = (Work.Bottcher.pMap c)^[m + 1] z := by
  have h : (Work.Bottcher.pMap c)^[m + 1] (-z)
      = (Work.Bottcher.pMap c)^[m] (Work.Bottcher.pMap c (-z)) :=
    Function.iterate_succ_apply (Work.Bottcher.pMap c) m (-z)
  rw [h, pMap_neg, ← Function.iterate_succ_apply (Work.Bottcher.pMap c) m z]

/-- The Green function of the tricorn is even: `G_c(-z) = G_c(z)`. -/
theorem green_neg (c z : ℂ) : Work.Bottcher.green c (-z) = Work.Bottcher.green c z := by
  refine tendsto_nhds_unique (Work.Bottcher.Green.tendsto_greenIter_Tantibar c (-z)) ?_
  refine (Work.Bottcher.Green.tendsto_greenIter_Tantibar c z).congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Work.Escape.greenIter]
  rw [Tantibar_iterate_add_one_neg]

/-! ## Oddness of the product-formula Böttcher coordinate -/

theorem normFactor_iterate_neg (c z : ℂ) (n : ℕ) :
    Work.Bottcher.normFactor c ((Work.Bottcher.pMap c)^[n] (-z))
      = Work.Bottcher.normFactor c ((Work.Bottcher.pMap c)^[n] z) := by
  rcases n with _ | m
  · simp only [Function.iterate_zero_apply]
    rw [Work.Bottcher.normFactor, Work.Bottcher.normFactor, pMap_neg]
    congr 1
    ring
  · rw [pMap_iterate_add_one_neg]

theorem bottcherTerm_neg (c z : ℂ) (n : ℕ) :
    Work.Bottcher.bottcherTerm c n (-z) = Work.Bottcher.bottcherTerm c n z := by
  rw [Work.Bottcher.bottcherTerm, Work.Bottcher.bottcherTerm, normFactor_iterate_neg]

theorem bottcherSeries_neg (c z : ℂ) :
    Work.Bottcher.bottcherSeries c (-z) = Work.Bottcher.bottcherSeries c z := by
  rw [Work.Bottcher.bottcherSeries, Work.Bottcher.bottcherSeries]
  exact tsum_congr (fun n => bottcherTerm_neg c z n)

theorem bottcher_neg (c z : ℂ) :
    Work.Bottcher.bottcher c (-z) = -Work.Bottcher.bottcher c z := by
  rw [Work.Bottcher.bottcher, Work.Bottcher.bottcher, bottcherSeries_neg]
  ring

/-! ## The far region is escaping -/

/-- Every point of the closed far region `{‖z‖ ≥ escapeRadius c}` has positive Green
function, i.e. is escaping. -/
theorem green_pos_of_escapeRadius_le (c z : ℂ)
    (hz : Work.Bottcher.escapeRadius c ≤ ‖z‖) : 0 < Work.Bottcher.green c z := by
  refine (Work.Bottcher.Green.green_pos_iff c z).mpr ?_
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le (Work.Bottcher.Core.escapeRadius_pos c) hz
  have hpow : Tendsto (fun n : ℕ => (2 : ℝ) ^ n * ‖z‖) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_mul_const hzpos
  exact tendsto_atTop_mono
    (fun n => (Work.Bottcher.Core.escapeRadius_le_norm_Tantibar_iterate c hz n).2) hpow

/-- Along the `p_c`-orbit of an escaping point the cocompact filter is reached. -/
theorem tendsto_iterate_pMap_cocompact (c : ℂ) {z : ℂ} (hz : 0 < Work.Bottcher.green c z) :
    Tendsto (fun k : ℕ => (Work.Bottcher.pMap c)^[k] z) atTop (cocompact ℂ) := by
  apply tendsto_cocompact_of_tendsto_dist_comp_atTop (0 : ℂ)
  have hT := (Work.Bottcher.Green.green_pos_iff c z).mp hz
  have h2 : Tendsto (fun k : ℕ => 2 * k) atTop atTop :=
    tendsto_atTop_atTop.mpr (fun b => ⟨b, fun a ha => by omega⟩)
  refine (hT.comp h2).congr' (Eventually.of_forall (fun k => ?_))
  simp only [Function.comp_apply, dist_zero_right]
  rw [Work.Bottcher.pMap_iterate]

/-! ## The Green function along the `p_c`-orbit -/

/-- `G_c(p_c z) = 4 G_c z`, the Green-function equation of the second iterate. -/
theorem green_pMap (c z : ℂ) :
    Work.Bottcher.green c (Work.Bottcher.pMap c z) = 4 * Work.Bottcher.green c z := by
  rw [Work.Bottcher.pMap_eq_iterate_two, Function.iterate_succ_apply',
    Function.iterate_one, Work.Bottcher.Green.green_comm, Work.Bottcher.Green.green_comm]
  ring

/-- `G_c(p_c^k z) = 4^k G_c z`. -/
theorem green_pMap_iterate (c z : ℂ) (k : ℕ) :
    Work.Bottcher.green c ((Work.Bottcher.pMap c)^[k] z) = 4 ^ k * Work.Bottcher.green c z := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', green_pMap, ih, pow_succ]
      ring

/-! ## Factorisation of the quartic -/

/-- `p_c u - p_c v = (u-v)(u+v)(u²+v²+2c̄)`. -/
theorem pMap_sub_pMap (c u v : ℂ) :
    Work.Bottcher.pMap c u - Work.Bottcher.pMap c v
      = (u - v) * (u + v) * (u ^ 2 + v ^ 2 + 2 * (starRingEnd ℂ) c) := by
  rw [Work.Bottcher.pMap_apply, Work.Bottcher.pMap_apply]; ring

/-! ## The explicit far radius -/

/-- The explicit far radius `4096 (‖c‖² + 3‖c‖ + 1)` used for the injectivity on the far
region.  It dominates `escapeRadius c`, the radii `64(1+‖c‖)+64` and `128(1+‖c‖)+128` of
the Böttcher series estimates, and the constant `‖c‖²+3‖c‖+1`. -/
def farR (c : ℂ) : ℝ := 4096 * (‖c‖ ^ 2 + 3 * ‖c‖ + 1)

theorem farR_pos (c : ℂ) : 0 < farR c := by
  have h : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  rw [farR]; positivity

theorem le_farR_64 (c : ℂ) : 64 * (1 + ‖c‖) + 64 ≤ farR c := by
  have h : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  rw [farR]; nlinarith [sq_nonneg ‖c‖]

theorem le_farR_128 (c : ℂ) : 128 * (1 + ‖c‖) + 128 ≤ farR c := by
  have h : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  rw [farR]; nlinarith [sq_nonneg ‖c‖]

theorem escapeRadius_le_farR (c : ℂ) : Work.Bottcher.escapeRadius c ≤ farR c := by
  have h : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  rw [farR, Work.Bottcher.escapeRadius]; nlinarith [sq_nonneg ‖c‖]

theorem one_le_farR (c : ℂ) : 1 ≤ farR c := by
  have h : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  rw [farR]; nlinarith [sq_nonneg ‖c‖]

theorem K_le_farR (c : ℂ) : ‖c‖ ^ 2 + 3 * ‖c‖ + 1 ≤ farR c := by
  have h : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  rw [farR]; nlinarith [sq_nonneg ‖c‖]

end

end Work.Bottcher.Inverse
