import Mathlib
import Submission.Lib.Unif2.PackagingOpen
import Submission.Lib.Unif2.Work.Parabolic.harmonicOnX_comp_biholomorph
import Submission.Lib.Unif2.Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn

namespace Work.BasinSC.StepOneCrit

open scoped Manifold ContDiff Topology
open Classical

/-- A complex diffeomorphism `e : U → W` between two open subsets of `ℂ`, read at the level of `ℂ`
as a function, is analytic with nowhere vanishing derivative on `U`.

Suggested route: take `Φ z := if hz : z ∈ U then ↑(e ⟨z, hz⟩) else 0` (add `open Classical` for
the decidability, or use `Function.extend`) and show that near a point `x ∈ U` it agrees with the
chart representation of `e`; the latter is analytic by
`Work.Parabolic.analyticAt_chart_representation_infty` (module
`Submission.Lib.Unif2.Work.Parabolic.harmonicOnX_comp_biholomorph`) applied to `e.contMDiff` at
`⟨x, hx⟩ : U`.  Identify the charts of an open subset with the coercion via
`Submission.opens_chartAt_apply`, `Submission.opens_chartAt_symm_apply_cast` (module
`Submission.Lib.Unif2.PackagingOpen`).  For `deriv Φ x ≠ 0` use
`Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn` (module
`Submission.Lib.Unif2.Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn`) with a radius `r`
such that `Metric.ball x r ⊆ U` (from `Metric.isOpen_iff.mp U.2 x hx`), using injectivity of `Φ` on
`U` (both coercions `U → ℂ`, `W → ℂ` are injective and `e` is a bijection). -/
theorem exists_analytic_diffeomorph_opens {U W : TopologicalSpace.Opens ℂ}
    (e : Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) U W
      ((⊤ : ℕ∞) : WithTop ℕ∞)) :
    ∃ Φ : ℂ → ℂ,
      (∀ z (hz : z ∈ (U : Set ℂ)), Φ z = ((e ⟨z, hz⟩ : W) : ℂ)) ∧
      (∀ x : ℂ, x ∈ (U : Set ℂ) → AnalyticAt ℂ Φ x) ∧
      (∀ x : ℂ, x ∈ (U : Set ℂ) → deriv Φ x ≠ 0) := by
  classical
  -- Read `e` at the level of `ℂ`, extending by `0` off `U`.
  let Φ : ℂ → ℂ := fun z => if hz : z ∈ (U : Set ℂ) then ((e ⟨z, hz⟩ : W) : ℂ) else 0
  have hΦ : ∀ z (hz : z ∈ (U : Set ℂ)), Φ z = ((e ⟨z, hz⟩ : W) : ℂ) := by
    intro z hz
    show (if hz' : z ∈ (U : Set ℂ) then ((e ⟨z, hz'⟩ : W) : ℂ) else 0) = _
    exact dite_eq_left hz
  -- Near `x ∈ U`, `Φ` agrees with the chart representation of `e` at `⟨x, hx⟩`.
  have hana : ∀ x ∈ (U : Set ℂ), AnalyticAt ℂ Φ x := by
    intro x hx
    have hchart := Work.Parabolic.analyticAt_chart_representation_infty
      (Φ := (⇑e : U → W)) e.contMDiff (⟨x, hx⟩ : U)
    have hcoord : (chartAt ℂ (⟨x, hx⟩ : U)) (⟨x, hx⟩ : U) = x := by
      rw [Submission.opens_chartAt_apply]
    rw [hcoord] at hchart
    refine hchart.congr ?_
    filter_upwards [U.isOpen.mem_nhds hx] with z hzU
    have hsymm : ((chartAt ℂ (⟨x, hx⟩ : U)).symm z : U) = ⟨z, hzU⟩ := by
      apply Subtype.ext
      exact Submission.opens_chartAt_symm_apply_cast U hzU
    rw [hsymm, hΦ z hzU, Submission.opens_chartAt_apply]
  refine ⟨Φ, hΦ, hana, ?_⟩
  -- `Φ` is injective on `U` (an open ball around a point of `U`), so its derivative cannot vanish.
  intro x hx
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp U.isOpen x hx
  refine Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn hr (hana x hx) ?_
  intro a ha b hb hab
  have haU : a ∈ (U : Set ℂ) := hrU ha
  have hbU : b ∈ (U : Set ℂ) := hrU hb
  rw [hΦ a haU, hΦ b hbU] at hab
  have h1 : (e ⟨a, haU⟩ : W) = e ⟨b, hbU⟩ := Subtype.coe_injective hab
  have h2 : (⟨a, haU⟩ : U) = ⟨b, hbU⟩ := e.toEquiv.injective h1
  exact (Subtype.mk.injEq a haU b hbU).mp h2

end Work.BasinSC.StepOneCrit
