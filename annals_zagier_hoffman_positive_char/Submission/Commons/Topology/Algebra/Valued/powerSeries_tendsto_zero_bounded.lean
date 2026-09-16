import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Topology.Algebra.Valued.ValuedField

open Filter
open scoped WithZero Topology

namespace Commons.Topology.Algebra.Valued

/-- If `log x ≤ m` then `x ≤ exp m` in `ℤᵐ⁰` (the case `x = 0` being trivial since `0` is the
bottom element). -/
lemma le_exp_of_log_le {x : ℤᵐ⁰} {m : ℤ} (h : WithZero.log x ≤ m) : x ≤ WithZero.exp m := by
  rcases eq_or_ne x 0 with hx | hx
  · rw [hx]; exact bot_le
  · rw [← WithZero.exp_log hx]; exact WithZero.exp_le_exp.mpr h

/-- If the coefficients of a power series over a `ℤᵐ⁰`-valued field tend to `0` (the Tate
condition), then they are bounded above in the value group. -/
theorem powerSeries_tendsto_zero_bounded (K : Type*) [Field K] [Valued K ℤᵐ⁰]
    (f : PowerSeries K)
    (hf : ∀ N : ℤ, ∀ᶠ n in atTop, Valued.v (PowerSeries.coeff n f) < WithZero.exp (-N)) :
    ∃ M : ℤ, ∀ n : ℕ, Valued.v (PowerSeries.coeff n f) ≤ WithZero.exp M := by
  obtain ⟨n0, hn0⟩ := eventually_atTop.1 (hf 0)
  refine ⟨max (WithZero.log ((Finset.range n0).sup
    (fun n => Valued.v (PowerSeries.coeff n f)))) 0, fun n => ?_⟩
  rcases lt_or_ge n n0 with hn | hn
  · have hle : Valued.v (PowerSeries.coeff n f) ≤
        (Finset.range n0).sup (fun n => Valued.v (PowerSeries.coeff n f)) :=
      Finset.le_sup (f := fun n => Valued.v (PowerSeries.coeff n f)) (Finset.mem_range.2 hn)
    exact hle.trans (le_exp_of_log_le (le_max_left _ _))
  · have hv : Valued.v (PowerSeries.coeff n f) ≤ WithZero.exp (0 : ℤ) := by
      simpa using (hn0 n hn).le
    exact hv.trans (WithZero.exp_le_exp.mpr (le_max_right _ _))

end Commons.Topology.Algebra.Valued
