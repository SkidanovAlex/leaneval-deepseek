import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseRowsL.LatticeCoulomb.kernelDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsL.LatticeCoulomb.cellOddMoments`

The two **odd-moment vanishings** of the unit cell `ucell 0 = [-1/2,1/2]³`, used to justify
that the cell expansion of `cos(2π⟪q,z⟫)` has no sine (resp. no linear) correction:

`∫_{ucell 0} sin(2π⟪q,z⟫) dq = 0`  and  `∫_{ucell 0} cos(2π⟪q,z⟫) • q dq = 0`.

Both integrands are **odd** under `q ↦ -q` (the sine because `sin` is odd and the inner
product changes sign, the second because `cos` is even and `(-q) = -q`), while the cell is
invariant under `q ↦ -q`.  The general principle is packaged once, for a function with
values in an arbitrary real normed space, in `setIntegral_eq_zero_of_neg` below, via
`MeasureTheory.integral_neg_eq_self` (Lebesgue measure is invariant under negation) and
`MeasureTheory.integral_neg`.
-/

open MeasureTheory Metric
open scoped Real BigOperators Topology

namespace Work.BoseRowsL.LatticeCoulomb

set_option autoImplicit false

/-- **Odd integrands integrate to zero over a symmetric set.**  If `s ⊆ E3` is
negation-invariant, `s` is measurable and `g (-q) = -g q` for all `q`, then `∫_s g = 0`.

The proof passes to the indicator `s.indicator g`, which is odd on all of `E3`: writing
`I` for its integral, `I = ∫ (s.indicator g) (-q) dq = ∫ -(s.indicator g) dq = -I` by
`integral_neg_eq_self` and `integral_neg`, and `I = -I` forces `I = 0` since a real normed
space is torsion free. -/
private lemma setIntegral_eq_zero_of_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E3} (hs : ∀ q : E3, -q ∈ s ↔ q ∈ s) (hs' : MeasurableSet s)
    {g : E3 → E} (hodd : ∀ q : E3, g (-q) = -g q) : ∫ q in s, g q = 0 := by
  have hind : ∀ q : E3, s.indicator g (-q) = -s.indicator g q := by
    intro q
    by_cases hq : q ∈ s
    · rw [Set.indicator_of_mem ((hs q).mpr hq), Set.indicator_of_mem hq, hodd q]
    · rw [Set.indicator_of_notMem (fun h => hq ((hs q).mp h)), Set.indicator_of_notMem hq,
        neg_zero]
  have h := integral_neg_eq_self (s.indicator g) volume
  rw [funext hind, integral_neg] at h
  rw [← integral_indicator hs']
  exact (@self_eq_neg E _ (IsAddTorsionFree.of_isTorsionFree ℝ E)
    (∫ q, s.indicator g q)).mp h.symm

/-- The unit cell `ucell 0` is invariant under `q ↦ -q`. -/
private lemma neg_mem_ucell_zero (q : E3) : -q ∈ ucell 0 ↔ q ∈ ucell 0 := by
  simp [ucell]

/-- **The odd moments of the unit cell vanish.**

* `∫_{ucell 0} sin(2π⟪q,z⟫) dq = 0`: the integrand is odd.
* `∫_{ucell 0} cos(2π⟪q,z⟫) • q dq = 0`: the vector integrand is odd. -/
theorem cellOddMoments (z : E3) :
    (∫ q in ucell 0, Real.sin (2 * Real.pi * inner ℝ q z) = 0) ∧
    (∫ q in ucell 0, (Real.cos (2 * Real.pi * inner ℝ q z)) • q = 0) := by
  refine ⟨setIntegral_eq_zero_of_neg neg_mem_ucell_zero (ucell_measurableSet 0)
      (fun q => ?_), setIntegral_eq_zero_of_neg neg_mem_ucell_zero (ucell_measurableSet 0)
      (fun q => ?_)⟩
  · rw [inner_neg_left, mul_neg, Real.sin_neg]
  · rw [inner_neg_left, mul_neg, Real.cos_neg, smul_neg]

end Work.BoseRowsL.LatticeCoulomb
