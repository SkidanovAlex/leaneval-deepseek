import Mathlib
import Submission.Work.Escape.Basic
import Submission.Work.Escape.tendsto_greenIter
import Submission.Work.Escape.geom_le_norm_iterate
import Submission.Work.Escape.norm_le_norm_iterate

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The zero locus of the Green function is the filled Julia set

For a map `f : ℂ → ℂ` with monic degree-`d` growth `MonicGrowth f d A` and `d ≥ 2`, the Green
function `green f d z = lim_n d^{-n} log⁺ ‖f^[n] z‖` vanishes exactly on the filled Julia set
`filledJulia f = {z | the orbit of z is bounded}`.

The two implications:

* **bounded orbit `→ G = 0`.**  If `‖f^[n] z‖ ≤ M` for all `n`, then
  `0 ≤ greenIter f d z n ≤ d^{-n} log⁺ M`, and the right hand side tends to `0`; by
  `tendsto_greenIter` the limit `green f d z` is the limit of `greenIter f d z`, hence `0`.

* **`G = 0` `→` bounded orbit.**  If the orbit is unbounded, some iterate `W = f^[N] z` enters
  the escaping region `{max 2 A < ‖·‖}`.  The quantitative growth estimate
  `geom_le_norm_iterate` gives `2 (‖W‖/2)^{d^k} ≤ ‖f^[k] W‖`, so from index `N` on
  `greenIter f d z (N+k) ≥ d^{-N} log(‖W‖/2) > 0`, and therefore `green f d z > 0`.
-/

open Filter Function
open scoped Topology

noncomputable section

namespace Work.Escape

/-- **Bounded orbits have vanishing partial Green functions.**  If the orbit of `z` is bounded
then `greenIter f d z n = d^{-n} log⁺ ‖f^[n] z‖ → 0`. -/
theorem tendsto_greenIter_zero_of_mem_filledJulia (f : ℂ → ℂ) (d : ℕ) (hd : 2 ≤ d) {z : ℂ}
    (hz : z ∈ filledJulia f) : Filter.Tendsto (greenIter f d z) Filter.atTop (nhds 0) := by
  obtain ⟨M, hM⟩ := norm_le_of_mem_filledJulia hz
  have h2d : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
  have hM1 : (1 : ℝ) ≤ max M 1 := le_max_right _ _
  have hle : ∀ n : ℕ, greenIter f d z n ≤ ((d : ℝ) ^ n)⁻¹ * Real.log (max M 1) := fun n =>
    greenIter_le_of_norm_le (d := d) (z := z) (n := n) hM1
      ((hM n).trans (le_max_left _ _))
  have hupper : Filter.Tendsto (fun n : ℕ => ((d : ℝ) ^ n)⁻¹ * Real.log (max M 1))
      Filter.atTop (nhds 0) := by
    have hgeom : Filter.Tendsto (fun n : ℕ => ((d : ℝ) ^ n)⁻¹) Filter.atTop (nhds 0) := by
      have h := tendsto_pow_atTop_nhds_zero_of_lt_one
        (show (0 : ℝ) ≤ ((d : ℝ))⁻¹ by positivity)
        (inv_lt_one_of_one_lt₀ (by linarith : (1 : ℝ) < (d : ℝ)))
      simpa [inv_pow] using h
    simpa using hgeom.mul_const (Real.log (max M 1))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun n => greenIter_nonneg f d z n) hle

/-- **The Green function vanishes on the filled Julia set.** -/
theorem green_eq_zero_of_mem_filledJulia (f : ℂ → ℂ) (d : ℕ) (A : ℝ) (h : MonicGrowth f d A)
    (hd : 2 ≤ d) {z : ℂ} (hz : z ∈ filledJulia f) : green f d z = 0 := by
  have hconv := tendsto_greenIter f d A h hd z
  have h0 := tendsto_greenIter_zero_of_mem_filledJulia f d hd hz
  exact tendsto_nhds_unique hconv h0

/-- **The Green function is positive off the filled Julia set.**  If the orbit of `z` is
unbounded, then some iterate `W = f^[N] z` lies in the escaping region, and the geometric lower
bound for escaping orbits forces `greenIter f d z n ≥ d^{-N} log(‖W‖/2) > 0` for all `n ≥ N`,
so the limit `green f d z` is positive. -/
theorem green_pos_of_not_mem_filledJulia (f : ℂ → ℂ) (d : ℕ) (A : ℝ) (h : MonicGrowth f d A)
    (hd : 2 ≤ d) {z : ℂ} (hz : z ∉ filledJulia f) : 0 < green f d z := by
  have hconv := tendsto_greenIter f d A h hd z
  have h2d : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdpos
  -- an unbounded orbit crosses the escape radius at some index `N`
  obtain ⟨N, hN⟩ : ∃ N : ℕ, max 2 A < ‖(f^[N]) z‖ := by
    by_contra hc
    refine hz ?_
    rw [mem_filledJulia]
    refine isBounded_iff_forall_norm_le.mpr ⟨max 2 A, fun x hx => ?_⟩
    obtain ⟨n, rfl⟩ := hx
    exact le_of_not_gt fun hlt => hc ⟨n, hlt⟩
  set W : ℂ := (f^[N]) z with hWdef
  have hW2 : 2 < ‖W‖ := two_lt_norm_of_mem_escapeRegion hN
  have hWmem : W ∈ escapeRegion A := hN
  have hδpos : 0 < ((d : ℝ) ^ N)⁻¹ * Real.log (‖W‖ / 2) := by
    have h1 : (1 : ℝ) < ‖W‖ / 2 := by linarith
    exact mul_pos (by positivity) (Real.log_pos h1)
  -- the quantitative lower bound on the partial Green functions
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      ((d : ℝ) ^ N)⁻¹ * Real.log (‖W‖ / 2) ≤ greenIter f d z n := by
    rw [eventually_atTop]
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = N + k := ⟨n - N, by omega⟩
    have hiter : (f^[N + k]) z = (f^[k]) W := by
      rw [hWdef, Nat.add_comm N k, Function.iterate_add_apply]
    have hgeo : 2 * (‖W‖ / 2) ^ d ^ k ≤ ‖(f^[k]) W‖ :=
      geom_le_norm_iterate f d A h hd hWmem k
    have hpos : 0 < 2 * (‖W‖ / 2) ^ d ^ k := by
      have h' : (0 : ℝ) < ‖W‖ / 2 := by linarith [norm_nonneg W]
      positivity
    have hlog : Real.log (2 * (‖W‖ / 2) ^ d ^ k) ≤ logPos ‖(f^[k]) W‖ :=
      (Real.log_le_log hpos hgeo).trans (log_le_logPos (lt_of_lt_of_le hpos hgeo))
    have hWne : ‖W‖ / 2 ≠ 0 := ne_of_gt (by linarith [norm_nonneg W] : (0 : ℝ) < ‖W‖ / 2)
    have hlogeq : Real.log (2 * (‖W‖ / 2) ^ d ^ k) =
        Real.log 2 + (d : ℝ) ^ k * Real.log (‖W‖ / 2) := by
      rw [Real.log_mul (by norm_num) (pow_ne_zero _ hWne), Real.log_pow]
      push_cast
      ring
    have hcancel : ((d : ℝ) ^ (N + k))⁻¹ * (d : ℝ) ^ k = ((d : ℝ) ^ N)⁻¹ := by
      rw [pow_add, mul_inv, mul_assoc, inv_mul_cancel₀ (pow_ne_zero k hdne), mul_one]
    rw [greenIter_def, hiter]
    calc ((d : ℝ) ^ N)⁻¹ * Real.log (‖W‖ / 2)
        ≤ ((d : ℝ) ^ (N + k))⁻¹ * ((d : ℝ) ^ k * Real.log (‖W‖ / 2)) :=
          le_of_eq (by rw [← mul_assoc, hcancel])
      _ ≤ ((d : ℝ) ^ (N + k))⁻¹ *
            (Real.log 2 + (d : ℝ) ^ k * Real.log (‖W‖ / 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
      _ = ((d : ℝ) ^ (N + k))⁻¹ * Real.log (2 * (‖W‖ / 2) ^ d ^ k) := by rw [hlogeq]
      _ ≤ ((d : ℝ) ^ (N + k))⁻¹ * logPos ‖(f^[k]) W‖ :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
  have hle := ge_of_tendsto hconv hev
  linarith

/-- **The Green function vanishes exactly on the filled Julia set.** -/
theorem green_eq_zero_iff (f : ℂ → ℂ) (d : ℕ) (A : ℝ) (h : MonicGrowth f d A) (hd : 2 ≤ d)
    (z : ℂ) : green f d z = 0 ↔ z ∈ filledJulia f := by
  refine ⟨fun h0 => ?_, fun hz => green_eq_zero_of_mem_filledJulia f d A h hd hz⟩
  by_contra hz
  exact absurd h0 (ne_of_gt (green_pos_of_not_mem_filledJulia f d A h hd hz))

end Work.Escape
