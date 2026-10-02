import Mathlib
import Submission.Work.FatouParabolic2.Defs
import Submission.Work.FatouParabolic.Reduction
import Submission.Work.FatouParabolic.Critical.deriv_iterate_tsq_eq_zero_iff
import Submission.Work.FatouParabolic.Critical.tsq_iterate_of_Tantibar_eq_zero
import Submission.Work.FatouParabolic.Poly.tsq_iterate_isPolynomialMap

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology
open Filter

namespace Work.FatouParabolic2

open LeanEval.ComplexAnalysis (Tantibar)

noncomputable section

/-- **Fatou's result for the tricorn, pointwise simple case.**  Let `z` be a parabolic point of
`T_c` of period `m` (`Work.Landing.IsParabolic c m z`: `(T_c)^[m] z = z` and the multiplier of the
holomorphic return map `(Tsq c)^[m] = (T_c)^[2m]` at `z` is `1`), at which that return map is
*simple* (`iteratedDeriv 2 ((Tsq c)^[m]) z ≠ 0`).  Then, from the simple case
`FatouParabolicInput_simple` of Fatou's classical input on parabolic cycles, the point `z` lies in
the closure of the critical orbit of `T_c`.

Proof route (a verbatim replay of `Work.FatouParabolic.parabolicCycleInOmegaLimit`, file
`Submission/Work/FatouParabolic/Reduction.lean`, with the input consumed in its simple form):

* `hz` gives `0 < m`, `(T_c)^[m] z = z` and `deriv ((Tsq c)^[m]) z = 1`; putting
  `G := (Tsq c)^[m]`, one has `G z = z` (`(Tsq c)^[m] = (T_c)^[2m] = ((T_c)^[m])^[2]`) and
  `G` is a polynomial map of degree `4^m ≥ 2`
  (`Work.FatouParabolic.Poly.tsq_iterate_isPolynomialMap`);
* `hFatou G z _ _ _ hsimp` yields a critical point `w` of `G` whose `G`-orbit converges to `z`;
* `Work.FatouParabolic.Critical.deriv_iterate_tsq_eq_zero_iff` puts some `(Tsq c)^[j] w`
  (`j < m`) at `0` or at a `T_c`-preimage of `0`; from there the `G`-orbit lies in the critical
  orbit of `T_c` (`Work.FatouParabolic.tsq_iterate_zero_mem`,
  `Work.FatouParabolic.tsq_iterate_of_preimage_zero_mem`, both in `Reduction.lean`), so `z` lies in
  its closure (`mem_closure_of_tendsto`). -/
theorem parabolicCycleInOmegaLimit_pointwise (hFatou : FatouParabolicInput_simple) {c z : ℂ}
    {m : ℕ} (hz : Work.Landing.IsParabolic c m z)
    (hsimp : iteratedDeriv 2 ((Work.Landing.Tsq c)^[m]) z ≠ 0) :
    z ∈ closure (Set.range (fun n : ℕ => (LeanEval.ComplexAnalysis.Tantibar c)^[n] c)) := by
  obtain ⟨hmpos, hmfix⟩ := hz.1
  obtain hmult := hz.2
  set S : Set ℂ := Set.range (fun n : ℕ => (Tantibar c)^[n] c) with hS
  -- `G = (Tsq c)^[m]` is a polynomial map of degree `4^m ≥ 2` with `G z = z`, `G' z = 1`
  have hGpoly : Work.FatouParabolic.IsPolynomialMapOfDegreeAtLeastTwo ((Work.Landing.Tsq c)^[m]) :=
    Work.FatouParabolic.Poly.tsq_iterate_isPolynomialMap c (Nat.succ_le_of_lt hmpos)
  have hGfix : (Work.Landing.Tsq c)^[m] z = z :=
    calc (Work.Landing.Tsq c)^[m] z = (Tantibar c)^[2 * m] z :=
          Work.LANDCL.Critical.Tsq_iterate_apply c m z
      _ = (Tantibar c)^[m] ((Tantibar c)^[m] z) := by
          rw [show 2 * m = m + m from by ring, Function.iterate_add_apply]
      _ = (Tantibar c)^[m] z := congrArg ((Tantibar c)^[m]) hmfix
      _ = z := hmfix
  have hGderiv : deriv ((Work.Landing.Tsq c)^[m]) z = 1 := hmult
  -- Fatou's theorem (simple case): a critical point of `G` in the basin of `z`
  obtain ⟨w, hwcrit, hwbasin⟩ := hFatou _ _ hGpoly hGfix hGderiv hsimp
  obtain ⟨j, hjrange, hjcase⟩ :=
    (Work.FatouParabolic.Critical.deriv_iterate_tsq_eq_zero_iff c).mp hwcrit
  rw [Finset.mem_range] at hjrange
  -- the `G`-orbit of `w` eventually lies in the critical orbit of `T_c`
  have htail : ∀ᶠ n : ℕ in atTop, ((Work.Landing.Tsq c)^[m])^[n] w ∈ S := by
    rw [Filter.eventually_atTop]
    refine ⟨j + 1, fun n hn => ?_⟩
    set u : ℂ := (Work.Landing.Tsq c)^[j] w with hu
    have hmn : j < m * n := by
      have h1 : j + 1 ≤ n := hn
      have h2 : n ≤ m * n := Nat.le_mul_of_pos_left n hmpos
      omega
    have hk : 1 ≤ m * n - j := by omega
    have hiter : ((Work.Landing.Tsq c)^[m])^[n] w = (Work.Landing.Tsq c)^[m * n] w := by
      rw [Function.iterate_mul]
    rw [hiter, show m * n = (m * n - j) + j from by omega,
      Function.iterate_add_apply]
    rcases hjcase with h0 | hpre
    · rw [← hu, h0]
      exact Work.FatouParabolic.tsq_iterate_zero_mem c hk
    · rw [← hu]
      exact Work.FatouParabolic.tsq_iterate_of_preimage_zero_mem hpre hk
  exact mem_closure_of_tendsto hwbasin htail

end

end Work.FatouParabolic2
