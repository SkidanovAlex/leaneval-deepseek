import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseSym.Interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The pointwise absolute value as a map on `L²(Conf N)`

This module provides the map `Φ : L2 N → L2 N` sending an `L²` element to the
`L²` element of its pointwise absolute value, together with the three facts the
bosonic reduction needs: `Φ u` is a.e. equal to `x ↦ |u x|`, it preserves the
`L²` norm, and it is `1`-Lipschitz (Kato's inequality at the level of the
`L²` norm — the pointwise inequality `‖|u|-|v|‖ ≤ ‖u-v‖`).

All three are instances of the general theory of `Lp` spaces over a lattice
with solid norm: `Lp ℝ 2 μ` is a lattice-ordered group, `|f|` is the pointwise
absolute value (`Lp.coeFn_abs`), its norm is unchanged (`norm_abs_eq_norm`),
and the absolute value map is `1`-Lipschitz (`norm_abs_sub_abs`).
-/

namespace Work.BoseSym.Abs

open MeasureTheory

/-- There is a map `Φ` on `L²(Conf N)` acting as the pointwise absolute value;
it is norm preserving and `1`-Lipschitz. -/
theorem exists_lp_abs (N : ℕ) : ∃ Φ : L2 N → L2 N,
      (∀ u : L2 N, AEEq N (Φ u) (fun x => |(u : Conf N → ℝ) x|)) ∧
      (∀ u : L2 N, ‖Φ u‖ = ‖u‖) ∧
      (∀ u v : L2 N, ‖Φ u - Φ v‖ ≤ ‖u - v‖) := by
  refine ⟨fun u => |u|, fun u => Lp.coeFn_abs u, fun u => norm_abs_eq_norm u,
    fun u v => norm_abs_sub_abs u v⟩

end Work.BoseSym.Abs
