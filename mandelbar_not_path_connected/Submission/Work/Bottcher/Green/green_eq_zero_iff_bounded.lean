import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Escape.Basic
import Submission.Work.Escape.geom_le_norm_iterate
import Submission.Work.Escape.tendsto_greenIter

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The zero locus of the Green function of the tricorn

`G_c(z) = 0` if and only if the `T_c`-orbit of `z` is bounded, i.e. if and only if
`z` lies in the filled tricorn `K_c`.  This is the standard characterization of the
filled Julia set as the zero locus of the Green function.

The Green function of the escape chapter is the `limUnder` of the partial Green
functions `greenIter (T_c) 2 z`; by `Work.Escape.tendsto_greenIter` this is an
honest limit.  The two implications are:
* bounded orbit `→ G = 0`: the partial Green functions are bounded by
  `2^{-n} log⁺ M` and hence converge to `0`;
* `G = 0` `→` bounded orbit: if the orbit is unbounded then some iterate `W`
  enters the escaping region, and the quantitative growth estimate
  `Work.Escape.geom_le_norm_iterate` gives `greenIter ≥ 2^{-N} log(‖W‖/2) > 0`
  from that index on, so the limit cannot be `0`.
-/

namespace Work.Bottcher.Green

open Filter Function
open scoped Topology
open LeanEval.ComplexAnalysis (Tantibar)

/-- The Green function is the limit of the partial Green functions (definitional). -/
theorem green_eq_limUnder (c z : ℂ) :
    green c z = Filter.limUnder Filter.atTop (Work.Escape.greenIter (Tantibar c) 2 z) := rfl

/-- The partial Green functions genuinely converge to the Green function. -/
theorem tendsto_greenIter_green (c z : ℂ) :
    Filter.Tendsto (Work.Escape.greenIter (Tantibar c) 2 z) Filter.atTop
      (nhds (green c z)) :=
  Work.Escape.tendsto_greenIter (Tantibar c) 2 ‖c‖ (Work.Escape.monicGrowth_Tantibar c) le_rfl z

/-- **Bounded orbits have Green function zero.** -/
theorem green_eq_zero_of_bounded (c z : ℂ)
    (h : ∃ M : ℝ, ∀ n : ℕ, ‖(Tantibar c)^[n] z‖ ≤ M) : green c z = 0 := by
  obtain ⟨M, hM⟩ := h
  have hconv := tendsto_greenIter_green c z
  have hM1 : (1 : ℝ) ≤ max M 1 := le_max_right _ _
  have hle : ∀ n : ℕ, Work.Escape.greenIter (Tantibar c) 2 z n ≤
      ((2 : ℝ) ^ n)⁻¹ * Real.log (max M 1) := fun n =>
    Work.Escape.greenIter_le_of_norm_le (d := 2) (z := z) (n := n) hM1
      ((hM n).trans (le_max_left _ _))
  have hupper : Filter.Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹ * Real.log (max M 1))
      Filter.atTop (nhds 0) := by
    have hgeom : Filter.Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹) Filter.atTop (nhds 0) := by
      have h := tendsto_pow_atTop_nhds_zero_of_lt_one (show (0 : ℝ) ≤ 1 / 2 by norm_num)
        (show (1 / 2 : ℝ) < 1 by norm_num)
      simpa [inv_pow] using h
    simpa using hgeom.mul_const (Real.log (max M 1))
  have h0 : Filter.Tendsto (Work.Escape.greenIter (Tantibar c) 2 z) Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun n => Work.Escape.greenIter_nonneg _ _ _ _) hle
  exact tendsto_nhds_unique hconv h0

theorem green_eq_zero_iff_bounded (c z : ℂ) :
    Work.Bottcher.green c z = 0 ↔
      ∃ M : ℝ, ∀ n : ℕ, ‖(LeanEval.ComplexAnalysis.Tantibar c)^[n] z‖ ≤ M := by
  refine ⟨fun h0 => ?_, fun h => green_eq_zero_of_bounded c z h⟩
  by_contra hcon
  have hconv := tendsto_greenIter_green c z
  rw [h0] at hconv
  -- some iterate of `z` enters the escaping region
  obtain ⟨N, hN⟩ : ∃ N : ℕ, max 2 ‖c‖ < ‖(Tantibar c)^[N] z‖ := by
    by_contra hc
    exact hcon ⟨max 2 ‖c‖, fun n => le_of_not_gt (fun hlt => hc ⟨n, hlt⟩)⟩
  set W : ℂ := (Tantibar c)^[N] z with hWdef
  have hW2 : 2 < ‖W‖ := (le_max_left 2 ‖c‖).trans_lt hN
  have hWmem : W ∈ Work.Escape.escapeRegion ‖c‖ := hN
  have hδpos : 0 < ((2 : ℝ) ^ N)⁻¹ * Real.log (‖W‖ / 2) := by
    have h1 : (1 : ℝ) < ‖W‖ / 2 := by linarith
    exact mul_pos (by positivity) (Real.log_pos h1)
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      ((2 : ℝ) ^ N)⁻¹ * Real.log (‖W‖ / 2) ≤ Work.Escape.greenIter (Tantibar c) 2 z n := by
    rw [eventually_atTop]
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = N + k := ⟨n - N, by omega⟩
    have hiter : (Tantibar c)^[N + k] z = (Tantibar c)^[k] W := by
      rw [hWdef, Nat.add_comm N k, Function.iterate_add_apply]
    have hgeo : 2 * (‖W‖ / 2) ^ 2 ^ k ≤ ‖(Tantibar c)^[k] W‖ :=
      Work.Escape.geom_le_norm_iterate (Tantibar c) 2 ‖c‖ (Work.Escape.monicGrowth_Tantibar c)
        le_rfl hWmem k
    have hpos : 0 < 2 * (‖W‖ / 2) ^ 2 ^ k := by
      have h : (0 : ℝ) < ‖W‖ / 2 := by linarith [norm_nonneg W]
      positivity
    have hlog : Real.log (2 * (‖W‖ / 2) ^ 2 ^ k) ≤
        Work.Escape.logPos ‖(Tantibar c)^[k] W‖ :=
      (Real.log_le_log hpos hgeo).trans (Work.Escape.log_le_logPos (lt_of_lt_of_le hpos hgeo))
    have hWne : ‖W‖ / 2 ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < ‖W‖ / 2)
    have hlogeq : Real.log (2 * (‖W‖ / 2) ^ 2 ^ k) =
        Real.log 2 + (2 : ℝ) ^ k * Real.log (‖W‖ / 2) := by
      rw [Real.log_mul (by norm_num) (pow_ne_zero _ hWne), Real.log_pow]
      push_cast
      ring
    have hcancel : ((2 : ℝ) ^ (N + k))⁻¹ * (2 : ℝ) ^ k = ((2 : ℝ) ^ N)⁻¹ := by
      rw [pow_add, mul_inv, mul_assoc,
        inv_mul_cancel₀ (pow_ne_zero k (by norm_num : (2 : ℝ) ≠ 0)), mul_one]
    rw [Work.Escape.greenIter_def, hiter]
    calc ((2 : ℝ) ^ N)⁻¹ * Real.log (‖W‖ / 2)
        ≤ ((2 : ℝ) ^ (N + k))⁻¹ * ((2 : ℝ) ^ k * Real.log (‖W‖ / 2)) :=
          le_of_eq (by rw [← mul_assoc, hcancel])
      _ ≤ ((2 : ℝ) ^ (N + k))⁻¹ *
            (Real.log 2 + (2 : ℝ) ^ k * Real.log (‖W‖ / 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
      _ = ((2 : ℝ) ^ (N + k))⁻¹ * Real.log (2 * (‖W‖ / 2) ^ 2 ^ k) := by rw [hlogeq]
      _ ≤ ((2 : ℝ) ^ (N + k))⁻¹ * Work.Escape.logPos ‖(Tantibar c)^[k] W‖ :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
  have hle := ge_of_tendsto hconv hev
  linarith

end Work.Bottcher.Green
