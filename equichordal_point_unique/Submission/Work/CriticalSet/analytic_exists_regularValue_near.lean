import Mathlib
import Submission.Work.CriticalSet.Defs
import Submission.Work.CriticalSet.countable_criticalValues

namespace Work.CriticalSet

/-- **Regular values of a nowhere-locally-constant holomorphic function are dense** (the Sard
substitute in the holomorphic setting).

Let `f : ℂ → ℂ` be complex analytic on an open set `U` and nowhere locally constant on `U`.  Then
arbitrarily close to any point `a : ℂ` there is a value `y` which is not attained at any critical
point of `f`: every `z ∈ U` with `f z = y` has `deriv f z ≠ 0`.  In particular the preimages of `y`
inside `U` are simple (transverse) zeros of `f - y`.

Proof strategy.  Let `S := {z : ℂ | z ∈ U ∧ deriv f z = 0}` be the critical set.  For `z ∈ U`,
`deriv f` is not eventually `0` at `z`: otherwise `deriv f` vanishes on a ball around `z` inside `U`
and `IsOpen.is_const_of_deriv_eq_zero` makes `f` constant there, contradicting the hypothesis.  As
`deriv f` is analytic on `U` (`AnalyticOnNhd.deriv`, using `CompleteSpace ℂ`), the second alternative
of `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero` applied to `deriv f` at `z` gives a
neighbourhood of `z` meeting `S` at most in `z`, i.e. `IsDiscreteIn S U` (equivalently: the zero set
of the analytic function `deriv f` is discrete).  Then `S` is countable by
`Work.CriticalSet.countable_of_isDiscreteIn` (from `Submission.Work.CriticalSet.countable_criticalValues`,
using that `ℂ` is second countable), hence so is `f '' S`, so `(f '' S)ᶜ` is dense
(`Set.Countable.dense_compl ℝ`), and `Dense.exists_mem_open` with the open nonempty set
`Metric.ball a ε` produces `y` with `dist y a < ε` and `y ∉ f '' S`.  Such a `y` is not attained at a
critical point: if `z ∈ U`, `f z = y` and `deriv f z = 0`, then `z ∈ S` and `y ∈ f '' S`. -/
theorem analytic_exists_regularValue_near {U : Set ℂ} {f : ℂ → ℂ} (hU : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) (hnlc : ∀ z ∈ U, ¬ ∀ᶠ w in nhds z, f w = f z) {a : ℂ} {ε : ℝ}
    (hε : 0 < ε) :
    ∃ y : ℂ, dist y a < ε ∧ ∀ z ∈ U, f z = y → deriv f z ≠ 0 := by
  -- The critical set of `f` inside `U`: the zero set of the analytic function `deriv f`.
  have hdiscrete : IsDiscreteIn {z : ℂ | z ∈ U ∧ deriv f z = 0} U := by
    intro z hz
    -- `deriv f` is analytic at `z`, so its zero set is either a neighbourhood of `z` or has `z`
    -- as an isolated point.
    have hdz : AnalyticAt ℂ (deriv f) z := (hf z hz).deriv
    rcases hdz.eventually_eq_zero_or_eventually_ne_zero with hzero | hne
    · -- First alternative: `deriv f` vanishes near `z`, so `f` is constant near `z`.
      exfalso
      obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hzero
      obtain ⟨r', hr', hr'sub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz)
      have hρpos : 0 < min r r' := lt_min hr hr'
      have hball_sub : Metric.ball z (min r r') ⊆ U :=
        fun w hw => hr'sub (Metric.ball_subset_ball (min_le_right _ _) hw)
      have hzero_on : Metric.ball z (min r r') ⊆ {w | deriv f w = 0} :=
        fun w hw => hrsub (Metric.ball_subset_ball (min_le_left _ _) hw)
      obtain ⟨c, hc⟩ := IsOpen.exists_is_const_of_deriv_eq_zero (f := f)
        (s := Metric.ball z (min r r')) Metric.isOpen_ball
        (convex_ball z (min r r')).isPreconnected (hf.differentiableOn.mono hball_sub) hzero_on
      exact hnlc z hz (by
        filter_upwards [Metric.ball_mem_nhds z hρpos] with w hw
        rw [hc w hw, hc z (Metric.mem_ball_self hρpos)])
    · -- Second alternative: `deriv f` does not vanish on a punctured neighbourhood of `z`.
      rw [eventually_nhdsWithin_iff] at hne
      obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hne
      exact ⟨Metric.ball z r, Metric.ball_mem_nhds z hr, fun w hw => by
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff] at hw ⊢
        by_contra hwz
        exact hrsub hw.2 hwz hw.1.2⟩
  -- A set discrete in `U` is countable in the second countable space `ℂ`.
  have hcount : ({z : ℂ | z ∈ U ∧ deriv f z = 0} : Set ℂ).Countable :=
    countable_of_isDiscreteIn hdiscrete (fun z hz => hz.1)
  -- Hence the critical values are countable, so their complement is dense.
  have hfS : (f '' {z : ℂ | z ∈ U ∧ deriv f z = 0}).Countable := hcount.image f
  have hdense : Dense ((f '' {z : ℂ | z ∈ U ∧ deriv f z = 0})ᶜ) := hfS.dense_compl ℝ
  obtain ⟨y, hyS, hyball⟩ :=
    hdense.exists_mem_open Metric.isOpen_ball ⟨a, Metric.mem_ball_self hε⟩
  exact ⟨y, Metric.mem_ball.mp hyball, fun z hz hzy hcrit => hyS ⟨z, ⟨hz, hcrit⟩, hzy⟩⟩

end Work.CriticalSet
