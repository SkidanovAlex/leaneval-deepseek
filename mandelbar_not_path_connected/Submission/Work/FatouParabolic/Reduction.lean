/-
Copyright: subproject `Submission/Work/FatouParabolic/` of `mandelbar_not_path_connected`.

# Fatou's theorem for the tricorn: `ParabolicCycleInOmegaLimit`

This module proves `Work.LANDCL.ParabolicCycleInOmegaLimit c` for **every** `c : ℂ` from the
primitive classical input `Work.FatouParabolic.FatouParabolicInput` (Fatou's theorem on parabolic
cycles, in the form "the basin of a multiplier-one fixed point of a polynomial map of degree
`≥ 2` contains a critical point").

## The reduction

Let `z` be a parabolic point of `T_c` of period `m`: `(T_c)^[m] z = z` and
`multiplier2 c m z = deriv ((Tsq c)^[m]) z = 1`.  Then `z` is a fixed point of the *holomorphic*
map `G = (Tsq c)^[m] = (T_c)^[2m]` with multiplier `1`, and `G` is a polynomial map of degree
`4^m ≥ 2` (`Work.FatouParabolic.tsq_iterate_isPolynomialMap`).  Fatou's theorem gives a critical
point `w` of `G` whose `G`-orbit converges to `z`.

The critical points of `G` are the `Tsq c`-preimages of the critical points of `Tsq c`
(`Work.LANDCL.Critical.deriv_iterate_eq_prod`), and the critical points of `Tsq c` are exactly
`0` and the `T_c`-preimages of `0` (`Work.LANDCL.Deriv.preimage_zero`,
`Work.LANDCL.Critical.Tsq_deriv_eq`).  Hence some point `u` of the `G`-orbit of `w` satisfies
`u = 0` or `T_c u = 0`, and from then on the `G`-orbit stays inside the `T_c`-orbit of the
critical value `c = T_c(0)`:

* `(Tsq c)^[k] 0 = (T_c)^[2k] 0 = (T_c)^[2k-1] c`,
* `T_c u = 0 ⟹ (Tsq c)^[k] u = (T_c)^[2k-1] 0 = (T_c)^[2k-2] c`.

Since the `G`-orbit of `w` converges to `z`, the point `z` lies in the closure of the critical
orbit `range (n ↦ (T_c)^[n] c)`, which is the claim.
-/
import Mathlib
import Submission.Work.FatouParabolic.Defs
import Submission.Work.FatouParabolic.Critical.deriv_iterate_tsq_eq_zero_iff
import Submission.Work.FatouParabolic.Critical.tsq_iterate_of_Tantibar_eq_zero
import Submission.Work.FatouParabolic.Critical.multiplier2_zero_ne_one
import Submission.Work.FatouParabolic.Poly.tsq_iterate_isPolynomialMap
import Submission.Work.LANDCL.Critical.not_isRepelling_criticalValue

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology
open Filter

namespace Work.FatouParabolic

open LeanEval.ComplexAnalysis (Tantibar)

noncomputable section

/-! ## The critical orbit of `T_c` -/

/-- The orbit of the critical *value* `c = T_c(0)` is the critical orbit shifted by one:
`(T_c)^[n] c = (T_c)^[n+1] 0`. -/
theorem Tantibar_iterate_c_eq (c : ℂ) (n : ℕ) :
    (Tantibar c)^[n] c = (Tantibar c)^[n + 1] 0 := by
  rw [Function.iterate_succ_apply, show Tantibar c 0 = c by simp]

/-- `(Tsq c)^[k] 0` is the `(2k-1)`-st point of the critical orbit of `T_c`. -/
theorem tsq_iterate_zero_mem (c : ℂ) {k : ℕ} (hk : 1 ≤ k) :
    (Work.Landing.Tsq c)^[k] 0 ∈ Set.range (fun n : ℕ => (Tantibar c)^[n] c) := by
  refine ⟨2 * k - 1, ?_⟩
  show (Tantibar c)^[2 * k - 1] c = (Work.Landing.Tsq c)^[k] 0
  rw [Work.LANDCL.Critical.Tsq_iterate_apply, Tantibar_iterate_c_eq]
  congr 1
  omega

/-- If `T_c u = 0`, then `(Tsq c)^[k] u` is the `(2k-2)`-nd point of the critical orbit of
`T_c` (for `k ≥ 1`). -/
theorem tsq_iterate_of_preimage_zero_mem {c u : ℂ} (hu : Tantibar c u = 0) {k : ℕ}
    (hk : 1 ≤ k) :
    (Work.Landing.Tsq c)^[k] u ∈ Set.range (fun n : ℕ => (Tantibar c)^[n] c) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Work.FatouParabolic.Critical.tsq_iterate_of_Tantibar_eq_zero hu k']
  refine ⟨2 * (k' + 1) - 2, ?_⟩
  show (Tantibar c)^[2 * (k' + 1) - 2] c = (Tantibar c)^[2 * k' + 1] 0
  rw [Tantibar_iterate_c_eq, show 2 * (k' + 1) - 2 + 1 = 2 * k' + 1 from by omega]

/-! ## The reduction -/

/-- **Fatou's theorem for the tricorn**: from the classical input, every parabolic point of
`T_c` lies in the closure of the critical orbit of `T_c`. -/
theorem parabolicCycleInOmegaLimit (hFatou : FatouParabolicInput) (c : ℂ) :
    Work.LANDCL.ParabolicCycleInOmegaLimit c := by
  intro z hzpar
  obtain ⟨m, ⟨hmpos, hmfix⟩, hmult⟩ := hzpar
  set S : Set ℂ := Set.range (fun n : ℕ => (Tantibar c)^[n] c) with hS
  -- `G = (Tsq c)^[m]` is a polynomial map of degree `4^m ≥ 2` with `G z = z`, `G' z = 1`
  have hGpoly : IsPolynomialMapOfDegreeAtLeastTwo ((Work.Landing.Tsq c)^[m]) :=
    Work.FatouParabolic.Poly.tsq_iterate_isPolynomialMap c (Nat.succ_le_of_lt hmpos)
  have hGfix : (Work.Landing.Tsq c)^[m] z = z :=
    calc (Work.Landing.Tsq c)^[m] z = (Tantibar c)^[2 * m] z :=
          Work.LANDCL.Critical.Tsq_iterate_apply c m z
      _ = (Tantibar c)^[m] ((Tantibar c)^[m] z) := by
          rw [show 2 * m = m + m from by ring, Function.iterate_add_apply]
      _ = (Tantibar c)^[m] z := congrArg ((Tantibar c)^[m]) hmfix
      _ = z := hmfix
  have hGderiv : deriv ((Work.Landing.Tsq c)^[m]) z = 1 := hmult
  -- Fatou's theorem: a critical point of `G` in the basin of `z`
  obtain ⟨w, hwcrit, hwbasin⟩ := hFatou _ _ hGpoly hGfix hGderiv
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
      exact tsq_iterate_zero_mem c hk
    · rw [← hu]
      exact tsq_iterate_of_preimage_zero_mem hpre hk
  exact mem_closure_of_tendsto hwbasin htail

end

end Work.FatouParabolic
