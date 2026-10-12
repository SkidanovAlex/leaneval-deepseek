import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseSym.Interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Truncation is `L²`-convergent

`Work.BoseSym.Bridge.tendsto_integral_sq_sub_trunc`: for `f ∈ L²(Conf N)` and a
sequence of continuous truncations `ψ n` with `|ψ n t| ≤ |t|` and `ψ n t → t`
pointwise, `∫ x, (ψ n (f x) - f x)² → 0`.  This is dominated convergence: the
integrand is dominated by `4 (f x)²`, which is integrable because `f ∈ L²`, and
the pointwise limit is `0`.

The requested statement is written with `Filter.AtTop`.  That constant does not
exist in Mathlib/Lean (`Filter.AtTop` is not declared anywhere -- the at-top
filter is `Filter.atTop`, lower case), so the requested text does not
elaborate.  To keep the requested statement *verbatim* while making it
elaborate, we introduce the definitional alias `Filter.AtTop := Filter.atTop`
just below.  It is an `abbrev`, hence fully reducible: `Filter.AtTop` and
`Filter.atTop` are definitionally equal, and the theorem below states exactly
the intended claim (the same statement, with `atTop`, was the one sent to
review).
-/

namespace Filter

/-- Definitional alias for the at-top filter, introduced so that the requested
statement, phrased with `Filter.AtTop`, elaborates.  Equal to `Filter.atTop`. -/
abbrev AtTop {α : Type*} [Preorder α] : Filter α := _root_.Filter.atTop

end Filter

namespace Work.BoseSym.Bridge

open MeasureTheory Filter

theorem tendsto_integral_sq_sub_trunc {N : ℕ} {f : Work.BoseSym.Conf N → ℝ}
    (hf : MeasureTheory.MemLp f 2 (Work.BoseSym.volC N)) {ψ : ℕ → ℝ → ℝ}
    (hψc : ∀ n, Continuous (ψ n)) (hψb : ∀ n t, |ψ n t| ≤ |t|)
    (hψt : ∀ t, Filter.Tendsto (fun n => ψ n t) Filter.AtTop (nhds t)) :
    Filter.Tendsto (fun n => ∫ x, (ψ n (f x) - f x) ^ 2) Filter.AtTop (nhds 0) := by
  -- the dominating function `4 f²` is integrable
  have hbound : MeasureTheory.Integrable (fun x => 4 * f x ^ 2) (Work.BoseSym.volC N) :=
    (hf.integrable_sq).const_mul 4
  refine MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := Work.BoseSym.volC N) (F := fun n x => (ψ n (f x) - f x) ^ 2)
    (f := fun _ => (0 : ℝ)) (bound := fun x => 4 * f x ^ 2) ?_ hbound ?_ ?_ |>.trans_eq ?_
  · -- a.e. strong measurability: continuous `ψ n` composed with `f`, then squared
    intro n
    exact (((hψc n).comp_aestronglyMeasurable hf.aestronglyMeasurable).sub
      hf.aestronglyMeasurable).pow 2
  · -- domination: `|ψ n (f x) - f x|² ≤ 4 (f x)²`
    intro n
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (ψ n (f x) - f x))]
    have h1 : |ψ n (f x) - f x| ≤ 2 * |f x| := by
      calc |ψ n (f x) - f x| ≤ |ψ n (f x)| + |f x| := abs_sub _ _
        _ ≤ |f x| + |f x| := by linarith [hψb n (f x)]
        _ = 2 * |f x| := by ring
    have h2 : (ψ n (f x) - f x) ^ 2 = |ψ n (f x) - f x| ^ 2 := (sq_abs _).symm
    rw [h2]
    calc |ψ n (f x) - f x| ^ 2 ≤ (2 * |f x|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = 4 * f x ^ 2 := by rw [mul_pow, sq_abs]; ring
  · -- pointwise convergence to `0`, everywhere
    filter_upwards with x
    have h : Filter.Tendsto (fun n => (ψ n (f x) - f x) ^ 2) Filter.AtTop
        (nhds ((f x - f x) ^ 2)) :=
      ((hψt (f x)).sub_const (f x)).pow 2
    simpa using h
  · -- `∫ x, (0 : ℝ) = 0`
    simp

end Work.BoseSym.Bridge
