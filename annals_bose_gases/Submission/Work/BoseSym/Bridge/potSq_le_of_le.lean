import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseSym.Interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseSym.Bridge

open MeasureTheory Filter

/-- Monotonicity of the weighted quadratic form `potSq` in the weight:

if `V x ≤ V' x` for all `x`, `V` is pointwise nonnegative, and `V'` is
pointwise bounded above by a nonnegative constant `c`, then for every ambient
state `p` the potential energy `∫ V u²` is at most `∫ V' u²`.

The hypotheses `h0` and `hb` are what make the two integrands integrable:
they give `0 ≤ V x ≤ V' x ≤ c`, hence
`0 ≤ V x · u² x ≤ V' x · u² x ≤ c · u² x` with `u² ∈ L¹` (because `u ∈ L²`),
so the two functions are dominated by the integrable function `c · u²`.  The
integral inequality is then the pointwise one. -/
theorem potSq_le_of_le {N : ℕ} {V V' : Work.BoseSym.Conf N → ℝ} {c : ℝ}
    (hle : ∀ x, V x ≤ V' x) (h0 : ∀ x, 0 ≤ V x) (hc0 : 0 ≤ c) (hb : ∀ x, V' x ≤ c)
    (hVm : Work.BoseSym.AEMeas N V) (hV'm : Work.BoseSym.AEMeas N V')
    (p : Work.BoseSym.Amb N) :
    Work.BoseSym.potSq V p ≤ Work.BoseSym.potSq V' p := by
  -- `0 ≤ V' x`: `V'` dominates the nonnegative `V`.
  have hV'0 : ∀ x, 0 ≤ V' x := fun x => (h0 x).trans (hle x)
  -- the function part of `p` lies in `L²`, whence its square is integrable
  -- and almost everywhere strongly measurable.
  have hu : MemLp ((p.1 : Work.BoseSym.Conf N → ℝ)) 2 (Work.BoseSym.volC N) :=
    Lp.memLp p.1
  have hsq : Integrable (fun x => ((p.1 : Work.BoseSym.Conf N → ℝ) x) ^ 2) :=
    hu.integrable_sq
  have hu2 : AEStronglyMeasurable (fun x => ((p.1 : Work.BoseSym.Conf N → ℝ) x) ^ 2)
      (Work.BoseSym.volC N) := hu.aestronglyMeasurable.pow 2
  -- the dominating integrable function `c · u²`
  have hcu : Integrable (fun x => c * ((p.1 : Work.BoseSym.Conf N → ℝ) x) ^ 2) :=
    hsq.const_mul c
  -- `V' · u²` is integrable, dominated by `c · u²`
  have hV'i : Integrable (fun x => V' x * ((p.1 : Work.BoseSym.Conf N → ℝ) x) ^ 2) := by
    refine Integrable.mono' hcu (hV'm.aestronglyMeasurable.mul hu2) (Filter.Eventually.of_forall fun x => ?_)
    have hnn : 0 ≤ V' x * ((p.1 : Work.BoseSym.Conf N → ℝ) x) ^ 2 :=
      mul_nonneg (hV'0 x) (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact mul_le_mul_of_nonneg_right (hb x) (sq_nonneg _)
  -- `V · u²` is integrable, dominated by `c · u²`
  have hVi : Integrable (fun x => V x * ((p.1 : Work.BoseSym.Conf N → ℝ) x) ^ 2) := by
    refine Integrable.mono' hcu (hVm.aestronglyMeasurable.mul hu2) (Filter.Eventually.of_forall fun x => ?_)
    have hnn : 0 ≤ V x * ((p.1 : Work.BoseSym.Conf N → ℝ) x) ^ 2 :=
      mul_nonneg (h0 x) (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact mul_le_mul_of_nonneg_right ((hle x).trans (hb x)) (sq_nonneg _)
  -- the pointwise inequality integrates
  rw [Work.BoseSym.potSq, Work.BoseSym.potSq]
  exact integral_mono hVi hV'i (fun x => mul_le_mul_of_nonneg_right (hle x) (sq_nonneg _))

end Work.BoseSym.Bridge
