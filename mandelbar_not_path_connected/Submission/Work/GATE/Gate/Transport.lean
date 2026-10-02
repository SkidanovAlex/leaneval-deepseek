/-
# The gate transport (G4): the angle of a parameter in a tongue lies in the `α`-window

This module proves the design's `G4` of §2.3 from the named `G1`+`G2` residual `BranchData` and
the `G3` base `BaseWindow`:

* `deviation_iterate` — the `m`-fold branch transport: the `α`-displacement of the Böttcher
  argument is divided by `1024^m` (`extAngle e = α + (ϑ_e p_e - α)/1024^m`);
* `gate_window` — the window conclusion: if the base point `p` sits in the `α`-window
  (`|deviation φ α p| < windowEps`, which at `c₀` is `A1`, `Submission/Work/GATE/Nest/`), then the
  parameter `e = Λ^[m] p` has `|Work.ParamRays.extAngle e - α| < Work.Final.windowEps`.
-/
import Submission.Work.GATE.Defs
import Submission.Work.GATE.Gate.Defs
import Submission.Work.ParamRays.PhiUnique

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.GATE

open LeanEval.ComplexAnalysis (Mandelbar)

variable {φ : ℂ → ℂ} {α : ℝ}

namespace BranchData

/-- **The level relation of the branch.**  If the Böttcher coordinate satisfies the functional
equation `φ (F z) = (φ z)^1024` on the tube (the `10`-fold iterate of the antiholomorphic Böttcher
functional equation `φ (T z) = conj (φ z)^2`), then `Λ` is a genuine inverse branch of `F` in the
Böttcher coordinate: `(φ (Λ z))^1024 = φ z`.  So the named residual `BranchData` is a statement
about an inverse branch of the return map, not only about the argument. -/
theorem cpow (bd : BranchData φ α)
    (hfun : ∀ z ∈ bd.S, φ (bd.F z) = (φ z) ^ 1024) {z : ℂ} (hz : z ∈ bd.S) :
    (φ (bd.Λ z)) ^ 1024 = φ z := by
  rw [← hfun (bd.Λ z) (bd.hmem z hz), bd.hright z hz]

/-- The tube is invariant under every iterate of the branch. -/
theorem iterate_mem (bd : BranchData φ α) {p : ℂ} (hp : p ∈ bd.S) (k : ℕ) :
    bd.Λ^[k] p ∈ bd.S := by
  induction k with
  | zero => simpa using hp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact bd.hmem _ ih

end BranchData

/-- **The `m`-fold branch transport of the Böttcher argument**: the `α`-displacement is divided by
`1024^m`.  This is the design's `G4` formula
`extAngle e = α + (ϑ_e p_e - α)/1024^m`. -/
theorem deviation_iterate (bd : BranchData φ α) {p : ℂ} (hp : p ∈ bd.S) (m : ℕ) :
    deviation φ α (bd.Λ^[m] p) = deviation φ α p / (1024 : ℝ) ^ m := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', bd.hdev _ (bd.iterate_mem hp k), ih, pow_succ]
    ring

/-- The transported deviation is smaller than the base deviation. -/
theorem abs_deviation_iterate_lt (bd : BranchData φ α) {p : ℂ} (hp : p ∈ bd.S) (m : ℕ)
    {δ : ℝ} (hδ : 0 ≤ δ) (h : |deviation φ α p| < δ) :
    |deviation φ α (bd.Λ^[m] p)| < δ := by
  rw [deviation_iterate bd hp m, abs_div, abs_of_pos (pow_pos (by norm_num : (0:ℝ) < 1024) m)]
  have h1 : (1 : ℝ) ≤ (1024 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  have h2 : |deviation φ α p| / (1024 : ℝ) ^ m ≤ |deviation φ α p| := by
    rw [div_le_iff₀ (pow_pos (by norm_num : (0:ℝ) < 1024) m)]
    nlinarith [abs_nonneg (deviation φ α p)]
  linarith

/-- `windowEps = 1/2048` is below `1/4`, the half-width on which the `α`-relative lifting of the
Böttcher argument is valid. -/
theorem windowEps_lt_quarter : Work.Final.windowEps < 1 / 4 := by
  rw [Work.Final.windowEps, Work.Landing.windowEps]; norm_num

/-- **The gate window (the design's `G4` conclusion).**  Let `bd : BranchData φ α` be the
`α`-Böttcher branch along the critical orbit (the named `G1`+`G2` residual), let
`bw : BaseWindow bd e` be the `G3` data (`e = Λ^[m] p` with the base point `p` of the tube), and
suppose the base point's Böttcher argument is within `windowEps` of `α` and that `φ` is the
critical Böttcher coordinate of the parameter `e` (`Φ e = φ e`, Böttcher's theorem).  Then the
*external angle* of the parameter `e` is within `windowEps` of `α`. -/
theorem gate_window {e : ℂ} (bd : BranchData φ α) (bw : BaseWindow bd e)
    (hα0 : 1 / 4 < α) (hα1 : α < 3 / 4) (hΦ : Work.ParamRays.Phi e = φ e) :
    |Work.ParamRays.extAngle e - α| < Work.Final.windowEps := by
  have hwin_quarter : |deviation φ α bw.p| < 1 / 4 :=
    lt_trans bw.hwin windowEps_lt_quarter
  have hsmall : |deviation φ α e| < 1 / 4 := by
    rw [bw.hbase]
    exact abs_deviation_iterate_lt bd bw.hpS bw.m (by norm_num) hwin_quarter
  have h1 : toIcoMod one_pos 0 (bAngle φ e) = α + deviation φ α e := by
    rw [← toIcoMod_liftAngle φ α e]
    exact toIcoMod_eq_alpha_add_deviation hα0 hα1 hsmall
  have hext : Work.ParamRays.extAngle e = α + deviation φ α e := by
    simpa [Work.ParamRays.extAngle, bAngle, hΦ] using h1
  rw [hext, add_sub_cancel_left]
  rw [bw.hbase]
  exact abs_deviation_iterate_lt bd bw.hpS bw.m (le_of_lt Work.GATE.windowEps_pos) bw.hwin

end Work.GATE
