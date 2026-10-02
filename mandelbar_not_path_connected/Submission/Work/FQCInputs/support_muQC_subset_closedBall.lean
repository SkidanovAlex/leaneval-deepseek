/-
# `Work.FQCInputs.support_muQC_subset_closedBall`

The Beltrami coefficient `Work.FQC.muQC d fl hpetal.Pg t` of the quasiconformal deformation of the
attracting Écalle cylinder is supported in the parabolic basin of the fundamental domain `Pg`,
which in turn is bounded by the escape radius `max 2 ‖c‖`.  This file makes that containment
available *publicly* (the corresponding facts in `Submission/Work/FQC/muQC_admissible_pg.lean`
are `private`), so that downstream users of the deformation can quote it.

The argument, verbatim in spirit:

* `support (muQC …) ⊆ basin d Pg`: off the basin the coefficient is literally `0`
  (`muQC_of_notMem`);
* `basin d Pg ⊆ closedBall 0 (max 2 ‖c‖)`: a point of `Pg` lies in the attracting petal `Pa`
  (`PetalInput.Pg_sub`), its `F c = (T_c)^[10]`-orbit converges, hence its `T_c`-orbit is bounded
  (`orbit_bounded_of_tendsto_F`), hence bounded by the escape radius
  (`Work.ParamRays.norm_le_max_of_bounded`).  Every backwards step `‖w‖² - ‖c‖ ≤ ‖T_c w‖`
  propagates this bound all the way back to the starting point.
-/
import Mathlib
import Submission.Work.FQCInputs.Defs
import Submission.Work.FQC.muQC_admissible_pg
import Submission.Work.FQC.muQC_aux_beltrami
import Submission.Work.ParamRays.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology ComplexConjugate
open MeasureTheory Filter Set Function
open Classical

set_option linter.unusedVariables false

noncomputable section

namespace Work.FQCInputs

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.EL (RootParabolic F K)
open Work.FQC

/-! ## 1. Bounded orbits of the petal

A point whose `F c = (T_c)^[10]`-orbit converges to `z₁` has a bounded `T_c`-orbit: writing the
`T_c`-time `n` as `r + 10 * q` with `r ≤ 9` reduces it to `q` steps of the convergent orbit
followed by at most nine uncontrolled steps, each of which is bounded by the quadratic recursion
`x ↦ x² + ‖c‖`. -/

/-- An explicit bound for the `r`-th iterate of a point of norm `≤ B`: the recursion
`x ↦ x² + ‖c‖` (started at `max B 1` so that it is monotone in `r`). -/
private def orbitBound (c : ℂ) (B : ℝ) : ℕ → ℝ
  | 0 => max B 1
  | (r+1) => (orbitBound c B r)^2 + ‖c‖

private theorem orbitBound_one_le (c : ℂ) (B : ℝ) : ∀ r, 1 ≤ orbitBound c B r := by
  intro r
  induction r with
  | zero => exact le_max_right B 1
  | succ r ih =>
      have hc0 : (0:ℝ) ≤ ‖c‖ := norm_nonneg c
      show 1 ≤ (orbitBound c B r)^2 + ‖c‖
      nlinarith [sq_nonneg (orbitBound c B r), ih]

private theorem orbitBound_step_le (c : ℂ) (B : ℝ) (r : ℕ) :
    orbitBound c B r ≤ orbitBound c B (r+1) := by
  have hc0 : (0:ℝ) ≤ ‖c‖ := norm_nonneg c
  have h1 : 1 ≤ orbitBound c B r := orbitBound_one_le c B r
  show orbitBound c B r ≤ (orbitBound c B r)^2 + ‖c‖
  nlinarith

private theorem orbitBound_mono (c : ℂ) (B : ℝ) : Monotone (orbitBound c B) := by
  intro r s hrs
  induction s, hrs using Nat.le_induction with
  | base => exact le_rfl
  | succ s hrs ih => exact le_trans ih (orbitBound_step_le c B s)

private theorem norm_iterate_le_orbitBound (c : ℂ) (w : ℂ) {B : ℝ} (hB : ‖w‖ ≤ B) :
    ∀ r, ‖(Tantibar c)^[r] w‖ ≤ orbitBound c B r := by
  intro r
  induction r with
  | zero => exact le_trans hB (le_max_left B 1)
  | succ r ih =>
      have hstep : ‖(Tantibar c)^[r+1] w‖ ≤ ‖(Tantibar c)^[r] w‖^2 + ‖c‖ := by
        rw [Function.iterate_succ_apply']
        exact Work.ParamRays.norm_Tantibar_le c _
      have hmono : ‖(Tantibar c)^[r] w‖^2 ≤ (orbitBound c B r)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) ih 2
      show ‖(Tantibar c)^[r+1] w‖ ≤ (orbitBound c B r)^2 + ‖c‖
      linarith

/-- A point whose orbit under the holomorphic return map `F c = (T_c)^[10]` converges (to the
parabolic point) has a bounded orbit under `T_c` itself. -/
private theorem orbit_bounded_of_tendsto_F {c z : ℂ} {w : ℂ}
    (h : Tendsto (fun q : ℕ => (F c)^[q] z) atTop (nhds w)) :
    Work.ParamRays.BoundedOrbit c z := by
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ q : ℕ, ‖(F c)^[q] z‖ ≤ B := by
    obtain ⟨R, hR⟩ := (Metric.isBounded_range_of_tendsto (fun q : ℕ => (F c)^[q] z) h
      ).subset_closedBall (0:ℂ)
    exact ⟨R, fun q => by
      have h1 := hR (Set.mem_range_self q)
      rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h1⟩
  refine ⟨orbitBound c B 9, fun n => ?_⟩
  show ‖(Tantibar c)^[n] z‖ ≤ orbitBound c B 9
  set q := n / 10 with hq
  set r := n % 10 with hr
  have hr10 : r ≤ 9 := by omega
  have hkey : (Tantibar c)^[n] z = (Tantibar c)^[r] ((F c)^[q] z) := by
    have hn : n = r + 10 * q := by omega
    rw [hn, Function.iterate_add_apply, Function.iterate_mul, ← F_eq_iterate c]
  rw [hkey]
  exact le_trans (norm_iterate_le_orbitBound c _ (hB q) r) (orbitBound_mono c B hr10)

/-- All points of the attracting petal have bounded orbits under `T_c`. -/
private theorem pa_boundedOrbit {c : ℂ} (d : RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁) {z : ℂ}
    (hz : z ∈ fl.Pa) : Work.ParamRays.BoundedOrbit c z :=
  orbit_bounded_of_tendsto_F (fl.tendsto_Pa z hz)

/-- Every point of the fundamental domain `Pg` lies within the escape radius `max 2 ‖c‖`. -/
private theorem norm_le_max_of_mem_Pg {c : ℂ} (d : RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)
    (hfl : PetalInput d fl) {z : ℂ} (hz : z ∈ hfl.Pg) :
    ‖z‖ ≤ max 2 ‖c‖ :=
  Work.ParamRays.norm_le_max_of_bounded c z (pa_boundedOrbit d fl (hfl.Pg_sub hz))

/-! ## 2. The basin is bounded by the escape radius -/

/-- The backwards step: if `‖T_c w‖ ≤ max 2 ‖c‖` then also `‖w‖ ≤ max 2 ‖c‖`, because the
escape radius `N = max 2 ‖c‖` satisfies `N + ‖c‖ ≤ N²`. -/
private theorem norm_le_max2_of_norm_Tantibar_le {c w : ℂ}
    (h : ‖Tantibar c w‖ ≤ max 2 ‖c‖) : ‖w‖ ≤ max 2 ‖c‖ := by
  have hN : (0:ℝ) ≤ max 2 ‖c‖ := le_trans (by norm_num) (le_max_left 2 ‖c‖)
  have h4 : (2:ℝ) ≤ max 2 ‖c‖ := le_max_left 2 ‖c‖
  have h2 : ‖c‖ ≤ max 2 ‖c‖ := le_max_right 2 ‖c‖
  have h3 : max 2 ‖c‖ + ‖c‖ ≤ (max 2 ‖c‖)^2 := by nlinarith [norm_nonneg c]
  have hsq : ‖w‖^2 ≤ (max 2 ‖c‖)^2 := by
    have h1 := Work.ParamRays.norm_sq_sub_le_norm_Tantibar c w
    nlinarith [norm_nonneg w]
  have h5 := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (norm_nonneg w), abs_of_nonneg hN] at h5

/-- The parabolic basin of `Pg` is bounded by the escape radius. -/
private theorem basin_subset_closedBall {c : ℂ} (d : RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁) (hfl : PetalInput d fl) :
    basin d hfl.Pg ⊆ Metric.closedBall 0 (max 2 ‖c‖) := by
  intro z hz
  obtain ⟨n, hn⟩ := hz
  have hmain : ∀ j, j ≤ n → ‖(Tantibar c)^[n - j] z‖ ≤ max 2 ‖c‖ := by
    intro j
    induction j with
    | zero => intro _; simpa using norm_le_max_of_mem_Pg d fl hfl hn
    | succ j ih =>
        intro hj
        have hj' : j ≤ n := by omega
        have hk : n - j = (n - (j+1)) + 1 := by omega
        have hT : (Tantibar c)^[n - j] z = Tantibar c ((Tantibar c)^[n - (j+1)] z) := by
          rw [hk, Function.iterate_succ_apply']
        exact norm_le_max2_of_norm_Tantibar_le (by rw [← hT]; exact ih hj')
  have hfin := hmain n le_rfl
  rw [Nat.sub_self, Function.iterate_zero_apply] at hfin
  rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero]

/-- The support of `muQC` is contained in the parabolic basin of `Pg`. -/
private theorem support_muQC_subset_basin {c : ℂ} (d : RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)
    (hfl : PetalInput d fl) (t : ℝ) :
    Function.support (muQC d fl hfl.Pg t) ⊆ basin d hfl.Pg := by
  intro z hz
  by_contra h
  exact hz (muQC_of_notMem d h)

/-! ## 3. The public statement -/

theorem support_muQC_subset_closedBall {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (hpetal : Work.FQC.PetalInput d fl) (t : ℝ) :
    Function.support (Work.FQC.muQC d fl hpetal.Pg t) ⊆ Metric.closedBall 0 (max 2 ‖c‖) :=
  Subset.trans (support_muQC_subset_basin d fl hpetal t) (basin_subset_closedBall d fl hpetal)

end Work.FQCInputs

end
