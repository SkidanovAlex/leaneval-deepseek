import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseSym.Interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# BoseSym.Form — the `gSq` integral identity

`gSq p = ∑_{j : GIdx N} ‖p.2 j‖²` is the squared norm of the gradient part of an
ambient point `p : Amb N = L²(Conf N) × ∏_{j : GIdx N} L²(Conf N)`.  On
configuration space `Conf N = Fin N → E3` the measure is Lebesgue measure, so
each `L²` norm squared is an integral of a pointwise square, and a finite sum of
integrals is the integral of the finite sum:

  `gSq p = ∫ x, ∑_{j : GIdx N} (p.2 j x)²`.

The two ingredients of the proof:

* `Lp` is an inner product space with `⟪u, v⟫ = ∫ x, ⟪u x, v x⟫`
  (`MeasureTheory.L2.inner_def`), so for `u : L²` the identity
  `‖u‖² = RCLike.re ⟪u, u⟫` (`InnerProductSpace.norm_sq_eq_re_inner`) turns the
  norm square into a real integral of a pointwise square;
* `MeasureTheory.integral_finsetSum` turns the finite sum of integrals into the
  integral of the finite sum, the summands being integrable by
  `MeasureTheory.MemLp.integrable_sq` applied to `MeasureTheory.Lp.memLp`.
-/

namespace Work.BoseSym.Form

open MeasureTheory
open scoped Topology Real

noncomputable section

set_option autoImplicit false

theorem gSq_eq_integral {N : ℕ} (p : Amb N) :
    gSq p = intC N (fun x => ∑ j : GIdx N, ((p.2 j : Conf N → ℝ) x) ^ 2) := by
  -- each `L²` norm square is the integral of the pointwise square
  have hsq : ∀ j : GIdx N, ‖p.2 j‖ ^ 2 = ∫ x, ((p.2 j : Conf N → ℝ) x) ^ 2 := by
    intro j
    rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℝ), MeasureTheory.L2.inner_def]
    simp only [Real.inner_apply, RCLike.re_to_real, sq]
  simp only [gSq, intC]
  rw [Finset.sum_congr rfl (fun j _ => hsq j)]
  -- a finite sum of integrals is the integral of the finite sum
  rw [integral_finsetSum]
  intro j _
  exact MemLp.integrable_sq (Lp.memLp (p.2 j))

end

end Work.BoseSym.Form
