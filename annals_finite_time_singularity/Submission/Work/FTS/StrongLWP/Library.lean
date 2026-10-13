/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongLWP/Library.lean` — the strong-route API over the existing library

The monotonicity of `ℋ^k`-membership in the order `k`, and the two conversions
`SmoothQuad ⟹ SmoothOpen` and `RegQ ⟹ HQo`, already exist in the workspace:

* `Work.Coercivity.HkMem_mono` — the one-step version `ℋ^{k+1} ⟹ ℋ^k` (for `SmoothNbhd` data);
* `Work.FTS.GalerkinFix.RegQ.regQ_mono` — `RegQ α k f → RegQ α k' f` for `k' ≤ k`;
* `Work.FTS.OpenPkg.HQo_of_RegQ` — `RegQ α k f → HQo α k f`.

This module collects them into the names the strong-route chapters use, adds the general
`k' ≤ k` form of the `ℋ^k`-monotonicity (by iterating the one-step lemma), and records the
consequence `GalClass α g → HQo α 6 g` that lets the order-`6` Galerkin data feed the estimates
which `FTS/IPGen` states on `HQo`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.NormNum.Ineq
import Submission.Work.FTS.StrongLWP.Basic
import Submission.Work.Coercivity.HkMem_mono
import Submission.Work.FTS.GalerkinFix.RegQ.regQ_mono
import Submission.Work.FTS.OpenPkg.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongLWP

open Work.FTS.Galerkin (Fn Fam slice gdot)

set_option autoImplicit false

/-! ## General monotonicity of `ℋ^k`-membership -/

/-- **`ℋ^k`-membership descends in the order**, for data smooth on a neighbourhood of the closed
quadrant (`SmoothNbhd`, which makes every atom of `HkIntegrand` measurable).

This is the general `k' ≤ k` form; its one-step instance is the frozen
`Work.Coercivity.HkMem_mono`. -/
theorem HkMem_mono {α : ℝ} {k k' : ℕ} (hkk : k' ≤ k) {f : Fn}
    (hsm : Work.Spaces.SmoothNbhd f) (hm : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α k' f := by
  induction k generalizing k' with
  | zero =>
      obtain rfl : k' = 0 := Nat.le_zero.mp hkk
      exact hm
  | succ k ih =>
      rcases Nat.eq_or_lt_of_le hkk with hEq | hLt
      · subst hEq; exact hm
      · exact ih (Nat.lt_succ_iff.mp hLt) (Work.Coercivity.HkMem_mono α k hsm hm)

/-! ## The class conversions -/

/-- **`RegQ α k f → RegQ α k' f` for `k' ≤ k`** (re-export of
`Work.FTS.GalerkinFix.RegQ.regQ_mono`).  In particular `RegQ α 6 g → RegQ α 4 g`, which is how
the order-`6` datum of the strong route feeds the `ℋ⁴`-level classes (`GalClass`, `UnifIP`). -/
theorem RegQ_mono {α : ℝ} {k k' : ℕ} (hkk : k' ≤ k) {f : Fn}
    (h : Work.FTS.Nonlin.RegQ α k f) : Work.FTS.Nonlin.RegQ α k' f :=
  Work.FTS.GalerkinFix.RegQ.regQ_mono h hkk

/-- The order-`6`-to-order-`4` instance of `RegQ_mono`. -/
theorem RegQ_six_to_four {α : ℝ} {f : Fn} (h : Work.FTS.Nonlin.RegQ α 6 f) :
    Work.FTS.Nonlin.RegQ α 4 f :=
  RegQ_mono (k := 6) (k' := 4) (by norm_num) h

/-- **`RegQ ⟹ HQo`** (re-export of `Work.FTS.OpenPkg.HQo_of_RegQ`): the interior `C^∞` class
`SmoothOpen` of the estimates replaces the neighbourhood class `SmoothQuad`. -/
theorem RegQ_toHQo {α : ℝ} {k : ℕ} {f : Fn} (h : Work.FTS.Nonlin.RegQ α k f) :
    Work.FTS.VocabO.HQo α k f :=
  Work.FTS.OpenPkg.HQo_of_RegQ h

/-- **The order-`6` Galerkin class gives `HQo α 6`**, the class in which the corrected
`N4Extra'`-type hypotheses of `FTS/IPGen` are stated. -/
theorem GalClass_toHQo {α : ℝ} {g : Fn} (h : Work.FTS.Nonlin.GalClass α g) :
    Work.FTS.VocabO.HQo α 6 g :=
  RegQ_toHQo h.reg

end Work.FTS.StrongLWP
