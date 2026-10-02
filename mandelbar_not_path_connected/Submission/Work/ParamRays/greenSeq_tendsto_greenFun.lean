/-
# The normalized logarithms converge to the Green function on the escaping set

For the antiholomorphic unicritical family `T_c(z) = (conj z)^2 + c` the Green function is
defined as the `limsup`

`greenFun c w = limsup_n 2^{-n} log⁺ ‖T_c^[n] w‖`,

but on the escaping set the `limsup` is in fact a limit:

`greenSeq c z n = 2^{-n} log⁺ ‖T_c^[n] z‖ ⟶ greenFun c z`  whenever `Escaping c z`.

The argument is to wait until the orbit has passed the escape radius: if
`max 2 ‖c‖ < ‖T_c^[N] z‖` then the telescoping identity
(`Work.ParamRays.greenSeq_eq_log_add_sum`) and the absolute convergence of the telescoping
series (`Work.ParamRays.summable_orbitLog`) show that the *shifted* normalized logarithms
converge to `greenFun c (orbit c z N)`; the shift is undone by the scaling relation
`greenSeq c (T_c^[N] z) j = 2^N · greenSeq c z (j + N)` and the orbit formula
`greenFun c (T_c^[N] z) = 2^N · greenFun c z`.

## Main results

* `Work.ParamRays.tendsto_greenSeq_of_lt` : for `max 2 ‖c‖ < ‖w‖` the normalized
  logarithms converge to `greenFun c w`.
* `Work.ParamRays.greenSeq_tendsto_greenFun` : on the escaping set, `greenSeq c z`
  converges to `greenFun c z`.
-/
import Mathlib
import Submission.Work.ParamRays.Green
import Submission.Work.ParamRays.Basic
import Submission.Work.ParamRays.greenFun_eq_log_add_tsum
import Submission.Work.ParamRays.greenFun_orbit

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Finset
open scoped Real Topology

namespace Work.ParamRays

/-- **The normalized logarithms converge when the orbit starts outside the escape radius.**
For `max 2 ‖c‖ < ‖w‖` the telescoping identity `greenSeq c w N = log ‖w‖ + ∑_{i<N} (…)`
together with the absolute convergence of the telescope
(`summable_orbitLog`) shows that `greenSeq c w` converges, and its limit is `greenFun c w`
by `greenFun_eq_log_add_tsum`. -/
theorem tendsto_greenSeq_of_lt (c w : ℂ) (h : max 2 ‖c‖ < ‖w‖) :
    Filter.Tendsto (greenSeq c w) Filter.atTop (nhds (greenFun c w)) := by
  have hsum := summable_orbitLog c w h
  have hlim : Filter.Tendsto (fun N : ℕ => Real.log ‖w‖ + ∑ i ∈ Finset.range N,
      ((2 : ℝ) ^ (i + 1))⁻¹ * Real.log (‖orbit c w (i + 1)‖ / ‖orbit c w i‖ ^ 2))
      Filter.atTop (nhds (Real.log ‖w‖ + ∑' n : ℕ, ((2 : ℝ) ^ (n + 1))⁻¹ *
        Real.log (‖orbit c w (n + 1)‖ / ‖orbit c w n‖ ^ 2))) :=
    hsum.hasSum.tendsto_sum_nat.const_add _
  have h2 : Filter.Tendsto (greenSeq c w) Filter.atTop
      (nhds (Real.log ‖w‖ + ∑' n : ℕ, ((2 : ℝ) ^ (n + 1))⁻¹ *
        Real.log (‖orbit c w (n + 1)‖ / ‖orbit c w n‖ ^ 2))) :=
    hlim.congr fun N => (greenSeq_eq_log_add_sum c w h N).symm
  simpa only [greenFun_eq_log_add_tsum c w h] using h2

/-- **The normalized logarithms converge to the Green function on the escaping set.**
If the orbit of `z` tends to infinity then `2^{-n} log⁺ ‖T_c^[n] z‖ ⟶ greenFun c z`. -/
theorem greenSeq_tendsto_greenFun (c z : ℂ) (hz : Work.ParamRays.Escaping c z) :
    Filter.Tendsto (Work.ParamRays.greenSeq c z) Filter.atTop
      (nhds (Work.ParamRays.greenFun c z)) := by
  -- the orbit eventually passes the escape radius
  obtain ⟨N, hN⟩ : ∃ N : ℕ, max 2 ‖c‖ < ‖orbit c z N‖ := by
    rw [Escaping, Filter.tendsto_atTop_atTop] at hz
    obtain ⟨i, hi⟩ := hz (max 2 ‖c‖ + 1)
    exact ⟨i, lt_of_lt_of_le (lt_add_one _) (hi i le_rfl)⟩
  -- from there on the normalized logarithms do converge
  have hconv : Filter.Tendsto (greenSeq c (orbit c z N)) Filter.atTop
      (nhds (greenFun c (orbit c z N))) := tendsto_greenSeq_of_lt c _ hN
  -- the shift relation between the two sequences of normalized logarithms
  have hshift : ∀ j : ℕ, greenSeq c (orbit c z N) j = (2 : ℝ) ^ N * greenSeq c z (j + N) := by
    intro j
    have horb : orbit c (orbit c z N) j = orbit c z (j + N) := by
      rw [← orbit_add, Nat.add_comm]
    calc greenSeq c (orbit c z N) j
        = ((2 : ℝ) ^ j)⁻¹ * log⁺ ‖orbit c z (j + N)‖ := by rw [greenSeq, horb]
      _ = ((2 : ℝ) ^ j)⁻¹ * ((2 : ℝ) ^ N * ((2 : ℝ) ^ N)⁻¹) *
            log⁺ ‖orbit c z (j + N)‖ := by rw [mul_inv_cancel₀ (by positivity), mul_one]
      _ = (2 : ℝ) ^ N * (((2 : ℝ) ^ (j + N))⁻¹ * log⁺ ‖orbit c z (j + N)‖) := by
            rw [pow_add, mul_inv]; ring
      _ = (2 : ℝ) ^ N * greenSeq c z (j + N) := by rw [greenSeq]
  rw [greenFun_orbit c z N] at hconv
  have hconv' : Filter.Tendsto (fun j : ℕ => (2 : ℝ) ^ N * greenSeq c z (j + N)) Filter.atTop
      (nhds ((2 : ℝ) ^ N * greenFun c z)) := hconv.congr fun j => hshift j
  have h3 : Filter.Tendsto (fun j : ℕ => greenSeq c z (j + N)) Filter.atTop
      (nhds (greenFun c z)) := by
    have hp : ((2 : ℝ) ^ N) ≠ 0 := by positivity
    have h4 := hconv'.const_mul (((2 : ℝ) ^ N)⁻¹)
    simpa only [← mul_assoc, inv_mul_cancel₀ hp, one_mul] using h4
  exact (Filter.tendsto_add_atTop_iff_nat N).mp h3

end Work.ParamRays
