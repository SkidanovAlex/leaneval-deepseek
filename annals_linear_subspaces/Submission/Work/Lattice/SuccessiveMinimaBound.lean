import Mathlib
import Submission.Commons.Analysis.Real.prod_le_of_le_first
import Submission.Commons.Analysis.Real.le_rpow_of_pow_mul_le
import Submission.Commons.Lattice.Minkowski.minkowski_second_upper

/-!
# Successive minima above the first one are bounded by the covolume and the first minimum

For a full-rank lattice `L ≤ E` (`finrank ℤ L = d`), the product of the successive minima is
bounded by Minkowski's second theorem (`Commons.Lattice.Minkowski.minkowski_second_upper`), and
`λ_1` is the smallest of them.  Hence, if `λ_1 ≥ c`, every `λ_k` is bounded by an explicit
constant depending only on `d`, the covolume and `c`:

* `successiveMinimum_le_of_prod_le` — the arithmetic core (with the product bound as hypothesis);
* `successiveMinimum_le_of_covol` — the covolume form via Minkowski-2-upper.

This is the step "`λ_1(Λ_t) ≥ c` ⟹ `λ_d(Λ_t) ≤ C`" recorded in the ROADMAP (session 161):
it is what turns the lower bound on the first successive minimum (the good-time output) into the
bounded smallness needed by the full-lattice extraction of Prop 5.

Module `Submission.Work.Lattice.SuccessiveMinimaBound`, namespace
`Submission.SuccessiveMinimaBound`.
-/

noncomputable section

open Module Real MeasureTheory
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Submission.SuccessiveMinimaBound

open Commons.Lattice.SuccessiveMinima
open Commons.Lattice.Minkowski

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Successive minima from the product bound and `λ_1`.**  If `c ≤ λ_1(L)` and
`∏_{i<d} λ_{i+1}(L) ≤ C`, then `λ_{k+1}(L) ≤ (C / c^k)^{1/(d−k)}`. -/
theorem successiveMinimum_le_of_prod_le (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (hfin : Module.finrank ℤ L = d) {c C : ℝ} (hc : 0 < c)
    (hmin : c ≤ successiveMinimum L 1)
    (hprod : ∏ i : Fin d, successiveMinimum L (i.val + 1) ≤ C) (k : Fin d) :
    successiveMinimum L (k.val + 1) ≤ (C / c ^ k.val) ^ (1 / (((d - k.val : ℕ)) : ℝ)) := by
  have hmin' : ∀ i : Fin d, c ≤ successiveMinimum L (i.val + 1) := by
    intro i
    refine le_trans hmin (successiveMinimum_mono L (i := 1) (j := i.val + 1) ?_ ?_)
    · exact Nat.succ_le_succ (Nat.zero_le i.val)
    · rw [hfin]; exact Nat.succ_le_of_lt i.isLt
  have hmono : Monotone (fun i : Fin d => successiveMinimum L (i.val + 1)) := by
    intro i j hij
    refine successiveMinimum_mono L (i := i.val + 1) (j := j.val + 1) ?_ ?_
    · exact Nat.succ_le_succ hij
    · rw [hfin]; exact Nat.succ_le_of_lt j.isLt
  have hkey := Commons.Analysis.Real.prod_le_of_le_first
    (fun i : Fin d => successiveMinimum L (i.val + 1)) hc hmin' hmono hprod k
  have hk : 0 < d - k.val := Nat.sub_pos_of_lt k.isLt
  have hx : 0 < successiveMinimum L (k.val + 1) :=
    Commons.Lattice.SuccessiveMinima.positive L (k.val + 1) (Nat.succ_pos k.val)
      (by rw [hfin]; exact Nat.succ_le_of_lt k.isLt)
  have hc' : 0 < c ^ k.val := pow_pos hc k.val
  exact Commons.Analysis.Real.le_rpow_of_pow_mul_le hc' hk hx hkey

/-- **The covolume form.**  With Minkowski's second theorem,
`λ_{k+1}(L) ≤ ((2^{2d}·covol L)/vol(B₁) / c^k)^{1/(d−k)}` whenever `c ≤ λ_1(L)`. -/
theorem successiveMinimum_le_of_covol (hd : 0 < d) (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (hfin : Module.finrank ℤ L = d) {c : ℝ} (hc : 0 < c)
    (hmin : c ≤ successiveMinimum L 1) (k : Fin d) :
    successiveMinimum L (k.val + 1) ≤
      (((2 : ℝ) ^ (2 * d) * ZLattice.covolume L) /
        (ENNReal.toReal (volume (Metric.closedBall (0 : E) 1)) * c ^ k.val)) ^
        (1 / (((d - k.val : ℕ)) : ℝ)) := by
  haveI : Nontrivial E := by
    by_contra h
    have : Subsingleton E := not_nontrivial_iff_subsingleton.mp h
    have h0 : d = 0 := by
      rw [← hfin]
      exact Module.finrank_zero_of_subsingleton
    omega
  have hvol : 0 < ENNReal.toReal (volume (Metric.closedBall (0 : E) 1)) := by
    rw [ENNReal.toReal_pos_iff]
    exact ⟨Metric.measure_closedBall_pos volume 0 zero_lt_one,
      Bornology.IsBounded.measure_lt_top (Metric.isBounded_closedBall (x := (0 : E)) (r := 1))⟩
  have hmink := minkowski_second_upper (d := d) hd L hfin
  have hprod : ∏ i : Fin d, successiveMinimum L (i.val + 1) ≤
      ((2 : ℝ) ^ (2 * d) * ZLattice.covolume L) /
        ENNReal.toReal (volume (Metric.closedBall (0 : E) 1)) := by
    rw [le_div_iff₀ hvol]
    exact hmink
  have hthis := successiveMinimum_le_of_prod_le L hfin hc hmin hprod k
  rwa [div_div] at hthis

end Submission.SuccessiveMinimaBound

end
