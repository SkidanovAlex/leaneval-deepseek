/-
Copyright: subproject `Submission/Work/FatouParabolic/` of `mandelbar_not_path_connected`.

# A critical point of the second return map in the basin of `z₁`, with no topological input

At a root-parabolic parameter `c` (`d : Work.EL.RootParabolic c`) the input bundle already
contains the whole critical-orbit convergence

`d.crit : (F c)^[n] c → z₁` and `(F c)^[n] c ≠ z₁`,

where `F c = (Tsq c)^[5] = (T_c)^[10]`, `T_c(z) = z̄² + c`, and `Tsq c = (T_c)²`.  From this
alone one gets a critical point of `F c` in the basin of `z₁`, with no appeal to the
petal/Liouville machinery of `Core/Main.lean` and no simple-connectivity hypothesis:

* `F c = (Tsq c)^[5]` is **critical at every `w` with `(T_c)^[9] w = 0`**: by the chain rule the
  derivative of an iterate of `Tsq c` is the product of `deriv (Tsq c)` along the `Tsq c`-orbit
  (`Work.FatouParabolic.Critical.deriv_iterate_tsq_eq_zero_iff`), and the `j = 4` factor is
  `deriv (Tsq c) ((Tsq c)^[4] w) = deriv (Tsq c) ((T_c)^[8] w) = 0` because
  `deriv (Tsq c) u = 0` whenever `T_c u = 0` (here `T_c ((T_c)^[8] w) = (T_c)^[9] w = 0`);
* such a `w` **exists**, since `T_c` is onto (`z ↦ z̄² + c` is `conj` followed by a square and a
  translation, and every complex number is a square), so every iterate `(T_c)^[n]` is onto;
* such a `w` lies in the **basin of `z₁`**: `(F c) w = (T_c)^[10] w = T_c ((T_c)^[9] w) = T_c 0 = c`,
  so the `F c`-orbit of `w` is the critical orbit `c, (F c) c, (F c)^2 c, …` shifted by one step,
  hence converges to `z₁` by `d.crit.1`.

This is the "cheaper side note" of `NOTES_LEAD_mandelbar_gaps2.md` §2.2: the root-parabolic
consumer of `Work.FatouParabolic.Core.exists_criticalPoint_in_basin_of_rootParabolic` needs
neither `ParabolicBasinSimplyConnected` (which is false for the full basin) nor the core.
-/
import Mathlib
import Submission.Work.FatouParabolic.Core.Defs
import Submission.Work.FatouParabolic.Critical.deriv_iterate_tsq_eq_zero_iff
import Submission.Work.FatouParabolic.Critical.tsq_iterate_of_Tantibar_eq_zero
import Submission.Work.ELTop.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouParabolic.Core

open LeanEval.ComplexAnalysis (Tantibar)

/-! ## Surjectivity of the antiholomorphic quadratic -/

/-- **`T_c(z) = z̄² + c` is onto.**  Given `y`, take a square root `s` of `y - c` (every complex
number is a square) and then `z = conj s`: `z̄² + c = s² + c = y`. -/
theorem surjective_Tantibar (c : ℂ) : Function.Surjective (Tantibar c) := by
  intro y
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s ^ 2 = y - c := by
    obtain ⟨s, hs⟩ := (isSquare_iff_exists_sq (y - c)).mp (Complex.isSquare (y - c))
    exact ⟨s, hs.symm⟩
  refine ⟨star s, ?_⟩
  have h : Tantibar c (star s) = s ^ 2 + c := by
    rw [LeanEval.ComplexAnalysis.Tantibar]; simp
  rw [h, hs]
  ring

/-- Every point has a backwards orbit of arbitrary length under `T_c` landing at the critical
point `0`: for each `n` there is `w` with `(T_c)^[n] w = 0`.  Induction on `n`, using that
`T_c` is onto. -/
theorem exists_iterate_Tantibar_eq_zero (c : ℂ) (n : ℕ) :
    ∃ w : ℂ, (Tantibar c)^[n] w = 0 := by
  induction n with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
      obtain ⟨u, hu⟩ := ih
      obtain ⟨w, hw⟩ := surjective_Tantibar c u
      exact ⟨w, by rw [Function.iterate_succ_apply, hw, hu]⟩

/-! ## The nine-step preimages of the critical point are critical points of `F c`,
and their orbits are the critical orbit -/

/-- `(Tsq c)^[4]` is the eighth iterate of `T_c`. -/
private theorem tsq_four (c : ℂ) :
    (Work.Landing.Tsq c)^[4] = (Tantibar c)^[8] := by
  rw [Work.LANDCL.Critical.Tsq_eq_Tantibar_iterate_two, ← Function.iterate_mul]

/-- **A preimage of `0` under `(T_c)^[9]` is a critical point of `F c = (Tsq c)^[5]`.**

The `j = 4` factor of the product formula for `deriv ((Tsq c)^[5])` is
`deriv (Tsq c) ((Tsq c)^[4] w) = deriv (Tsq c) ((T_c)^[8] w)`, which vanishes because
`T_c ((T_c)^[8] w) = (T_c)^[9] w = 0`. -/
theorem deriv_F_eq_zero_of_iterate_Tantibar_eq_zero {c w : ℂ}
    (hw : (Tantibar c)^[9] w = 0) : deriv (Work.EL.F c) w = 0 := by
  have h9 : Tantibar c ((Work.Landing.Tsq c)^[4] w) = 0 := by
    rw [tsq_four]
    exact (Function.iterate_succ_apply' (Tantibar c) 8 w).symm.trans hw
  exact (Work.FatouParabolic.Critical.deriv_iterate_tsq_eq_zero_iff c (w := w) (m := 5)).mpr
    ⟨4, by decide, Or.inr h9⟩

/-- **The `F c`-image of a point with `(T_c)^[9] w = 0` is the critical value `c`**, so that the
`F c`-orbit of `w` is the critical orbit shifted by one step:
`(F c)^[n+1] w = (F c)^[n] c`.

Indeed `F c = (T_c)^[10]`, so `(F c) w = T_c ((T_c)^[9] w) = T_c 0 = c`. -/
theorem F_apply_eq_c_of_iterate_Tantibar_eq_zero {c w : ℂ}
    (hw : (Tantibar c)^[9] w = 0) : (Work.EL.F c) w = c := by
  show (Work.Landing.Tsq c)^[5] w = c
  rw [Work.LANDCL.Critical.Tsq_iterate_apply]
  show Tantibar c ((Tantibar c)^[9] w) = c
  rw [hw]
  simp [LeanEval.ComplexAnalysis.Tantibar]

/-! ## The main result -/

/-- **Fatou's theorem at a root-parabolic parameter, from the critical orbit alone.**  Let
`d : Work.EL.RootParabolic c` be a root-parabolic parameter of the tricorn: `z₁ = d.z₁` is a
simple parabolic point of `T_c` (period `5`, second-return multiplier `1`), and the critical
orbit of the second return map `F c = (T_c)^[10]` converges to `z₁` without attaining it
(`d.crit`).  Then the basin of `z₁` contains a critical point of `F c`.

The witness is any `w` with `(T_c)^[9] w = 0`, which exists because `T_c` is onto
(`surjective_Tantibar`).  Such a `w` is a critical point of `F c = (Tsq c)^[5]`
(`deriv_F_eq_zero_of_iterate_Tantibar_eq_zero`), and `(F c) w = c`
(`F_apply_eq_c_of_iterate_Tantibar_eq_zero`), so `(F c)^[n+1] w = (F c)^[n] c → z₁` by
`d.crit.1`; hence `w` lies in the basin of `z₁` by `Filter.tendsto_add_atTop_iff_nat`.

Note that no simple-connectivity hypothesis on the basin is used, and the petal/Liouville core
is not needed: this is the root-parabolic case of `FatouParabolicInput`, where the critical
orbit is part of the input bundle. -/
theorem exists_criticalPoint_in_basin_of_rootParabolic_of_crit {c : ℂ}
    (d : Work.EL.RootParabolic c) :
    ∃ w : ℂ, Work.FatouParabolic.IsCriticalPoint (Work.EL.F c) w ∧
      w ∈ Work.FatouParabolic.basin (Work.EL.F c) d.z₁ := by
  -- a nine-step `T_c`-preimage of the critical point `0`
  obtain ⟨w, hw⟩ := exists_iterate_Tantibar_eq_zero c 9
  refine ⟨w, deriv_F_eq_zero_of_iterate_Tantibar_eq_zero hw, ?_⟩
  -- the `F c`-orbit of `w` is the critical orbit shifted by one step
  have hFw : (Work.EL.F c) w = c := F_apply_eq_c_of_iterate_Tantibar_eq_zero hw
  have hshift : ∀ n : ℕ, (Work.EL.F c)^[n+1] w = (Work.EL.F c)^[n] c := by
    intro n
    rw [Function.iterate_succ_apply, hFw]
  rw [Work.FatouParabolic.mem_basin]
  have ht : Filter.Tendsto (fun n : ℕ => (Work.EL.F c)^[n] c) Filter.atTop (nhds d.z₁) :=
    d.crit.1
  have ht2 : Filter.Tendsto (fun n : ℕ => (Work.EL.F c)^[n+1] w) Filter.atTop (nhds d.z₁) := by
    simpa only [hshift] using ht
  exact (Filter.tendsto_add_atTop_iff_nat 1).mp ht2

end Work.FatouParabolic.Core
