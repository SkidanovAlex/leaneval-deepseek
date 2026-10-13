/-
# `linvI_smooth` — smoothness of the zero-moment Dirichlet inverse `LinvI h`

`LinvI h θ = ∫_0^θ Linv h θ'` is the *primitive* of `Linv h`, so the fundamental theorem of
calculus gives it one order more smoothness than `Linv h`: if `Linv h` is `C^∞` on the open
interval `(0, π/2)`, then so is `LinvI h` (`deriv (LinvI h) = Linv h` there).

Two hypotheses are used, and both are needed:

* `hsm` — `ContDiffOn ℝ ∞ (Linv h) (Ioo 0 (π/2))`, i.e. the integrand is smooth;
* `hbdd` — a *local* bound `|Linv h| ≤ M` on `(0, t)` for every `t < π/2`, which is exactly
  what makes the integral `∫_0^θ Linv h` a genuine (non-junk) integral and not the `0` that
  Lean's Bochner integral assigns to a non-integrable function.  (A bound on all of
  `(0, π/2)` is *not* available in the intended application, where `Linv h` may blow up at
  `π/2`.)

Nothing about the smoothness of the *source* `h` is used, and no algebraic structure of
`Linv` beyond its continuity: the statement is the general fact "the primitive of a locally
bounded `C^∞` function is `C^∞`", instantiated at `Linv h`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.PhiStar.Linv23Aux.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Linv23Aux

set_option autoImplicit false

/-- **Fundamental theorem of calculus for `LinvI h`.**  If `Linv h` is `C^∞` on `(0, π/2)`
and locally bounded at `0⁺` (bounded on every `(0, t)` with `t < π/2`), then at every
`x ∈ (0, π/2)` the primitive `LinvI h = ∫_0^x Linv h` has derivative `Linv h x`.

The local bound is what gives `IntervalIntegrable (Linv h) volume 0 x`: on `(0, x]` the
integrand is dominated by the constant bounding it on `(0, t)` for some `t ∈ (x, π/2)`, and it
is measurable there because it is continuous on the open interval. -/
private lemma hasDerivAt_LinvI_of {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ Work.Stability.smoothOrder (Work.FTS.PhiStar.Linv h)
      (Set.Ioo 0 (Real.pi / 2)))
    (hbdd : ∀ t : ℝ, 0 < t → t < Real.pi / 2 →
      ∃ M : ℝ, ∀ θ ∈ Set.Ioo 0 t, |Work.FTS.PhiStar.Linv h θ| ≤ M)
    {x : ℝ} (hx : x ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (Work.FTS.PhiStar.LinvI h) (Work.FTS.PhiStar.Linv h x) x := by
  have hcont : ContinuousOn (Work.FTS.PhiStar.Linv h) (Set.Ioo 0 (Real.pi / 2)) :=
    hsm.continuousOn
  -- a point `t` strictly between `x` and `π/2`, on `(0, t)` we have a bound for `Linv h`
  have ht0 : 0 < (x + Real.pi / 2) / 2 := by linarith [hx.1, Real.pi_pos]
  have htπ : (x + Real.pi / 2) / 2 < Real.pi / 2 := by linarith [hx.2]
  have hxt : x < (x + Real.pi / 2) / 2 := by linarith [hx.2]
  obtain ⟨M, hM⟩ := hbdd ((x + Real.pi / 2) / 2) ht0 htπ
  -- the integrand is interval integrable on `[0, x]`
  have hInt : IntervalIntegrable (Work.FTS.PhiStar.Linv h) volume 0 x := by
    rw [intervalIntegrable_iff, uIoc_of_le (le_of_lt hx.1)]
    refine IntegrableOn.of_bound ?_ ?_ M ?_
    · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
    · exact (hcont.mono (fun y hy =>
        ⟨hy.1, lt_of_le_of_lt hy.2 hx.2⟩)).aestronglyMeasurable measurableSet_Ioc
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
      rw [Real.norm_eq_abs]
      exact hM y ⟨hy.1, lt_of_le_of_lt hy.2 hxt⟩
  have hmeas : StronglyMeasurableAtFilter (Work.FTS.PhiStar.Linv h) (𝓝 x) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hcont x hx
  have hcontAt : ContinuousAt (Work.FTS.PhiStar.Linv h) x :=
    hcont.continuousAt (isOpen_Ioo.mem_nhds hx)
  change HasDerivAt (fun u => ∫ y in (0 : ℝ)..u, Work.FTS.PhiStar.Linv h y)
    (Work.FTS.PhiStar.Linv h x) x
  exact intervalIntegral.integral_hasDerivAt_right hInt hmeas hcontAt

/-- `LinvI h = ∫_0^θ Linv h` is `C^∞` on `(0, π/2)` whenever the integrand `Linv h` is, with
a local bound at `0⁺` making the integral genuine.

Proof: on the open interval the derivative of `LinvI h` is `Linv h` (the FTC above), so
`LinvI h` is `C^∞` by `contDiffOn_infty_iff_deriv_of_isOpen`, the derivative being the
`C^∞` function `Linv h` itself. -/
theorem linvI_smooth {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ Work.Stability.smoothOrder (Work.FTS.PhiStar.Linv h)
      (Set.Ioo 0 (Real.pi / 2)))
    (hbdd : ∀ t : ℝ, 0 < t → t < Real.pi / 2 →
      ∃ M : ℝ, ∀ θ ∈ Set.Ioo 0 t, |Work.FTS.PhiStar.Linv h θ| ≤ M) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Work.FTS.PhiStar.LinvI h)
      (Set.Ioo 0 (Real.pi / 2)) := by
  rw [show Work.Stability.smoothOrder = (∞ : ℕ∞ω) from rfl,
    contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨fun x hx => (hasDerivAt_LinvI_of hsm hbdd hx).differentiableAt.differentiableWithinAt,
    hsm.congr fun x hx => (hasDerivAt_LinvI_of hsm hbdd hx).deriv⟩

end Work.FTS.PhiStar.Linv23Aux
