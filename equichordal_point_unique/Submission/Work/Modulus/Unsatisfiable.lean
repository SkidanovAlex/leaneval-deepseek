import Mathlib
import Submission.GreenInterface
import Submission.Work.Modulus.Defs

/-!
# `Submission.HasGreenFunctionE` is unsatisfiable

The predicate `Submission.HasGreenFunctionE z₀ E` of `Submission/GreenInterface.lean` asks, as part
of its "decay at the ideal boundary" clause, for

`IsCompact {x : X | ε ≤ E x}`   for **every** `ε > 0`,

on a *total* function `E : X → ℝ`.  Together with the growth clause at the pole
(`∀ A, ∃ V ∈ 𝓝 z₀, ∀ x ∈ V, x ≠ z₀ → A < E x`) this is contradictory on a
`ChartedSpace ℂ X`: taking `ε = E z₀ + 1`,

* the growth clause gives `V ∈ 𝓝 z₀` with `V ∖ {z₀} ⊆ {ε ≤ E}`;
* `z₀` is not an isolated point of the charted space (`Work.Modulus.exists_ne_of_mem_nhds`), so
  `z₀ ∈ closure (V ∖ {z₀}) ⊆ closure {ε ≤ E}`;
* but `E z₀ < ε`, so `z₀ ∉ {ε ≤ E}`;
* hence `{ε ≤ E}` is not closed, and a compact subset of a Hausdorff space is closed: contradiction.

Consequently every statement whose hypothesis is `HasGreenFunctionE` is *vacuously* true, and the
mathematics of the modulus chapter has to be stated with the corrected (relative-compactness)
predicate `Work.UnitGreen.IsUnitGreenFunctionAt` — which is what
`Submission/Work/Modulus/Main.lean` does, the bridge being
`Work.Modulus.isUnitGreenFunctionAt_of_hasGreenFunctionE` (`Hypothesis.lean`).
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set

namespace Work.Modulus

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]

/-- **A charted space over `ℂ` has no isolated points.**  Every neighbourhood of `z₀` contains a
point other than `z₀`: the chart at `z₀` carries a neighbourhood of `z₀` onto a neighbourhood of
`(chartAt ℂ z₀) z₀` (`OpenPartialHomeomorph.image_mem_nhds`), and `ℂ` has no isolated points. -/
theorem exists_ne_of_mem_nhds {z₀ : X} {V : Set X} (hV : V ∈ nhds z₀) :
    ∃ x ∈ V, x ≠ z₀ := by
  set e : OpenPartialHomeomorph X ℂ := chartAt ℂ z₀ with he
  have hz : z₀ ∈ e.source := mem_chart_source ℂ z₀
  have himg : e '' (V ∩ e.source) ∈ 𝓝 (e z₀) :=
    e.image_mem_nhds hz (inter_mem hV (e.open_source.mem_nhds hz))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp himg
  set w : ℂ := e z₀ + ((ε / 2 : ℝ) : ℂ) with hw
  have hwmem : w ∈ Metric.ball (e z₀) ε := by
    rw [Metric.mem_ball, dist_eq_norm, hw]
    have h1 : e z₀ + ((ε / 2 : ℝ) : ℂ) - e z₀ = ((ε / 2 : ℝ) : ℂ) := by ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  obtain ⟨y, hy, hyeq⟩ := hball hwmem
  have hyne : y ≠ z₀ := by
    intro h
    have hw' : w = e z₀ := by rw [← hyeq, h]
    have h2 : ((ε / 2 : ℝ) : ℂ) = 0 := by
      have h3 : e z₀ + ((ε / 2 : ℝ) : ℂ) = e z₀ + 0 := by rw [add_zero, ← hw]; exact hw'
      exact add_left_cancel h3
    have h4 : ε / 2 = 0 := Complex.ofReal_injective h2
    linarith
  exact ⟨y, hy.1, hyne⟩

/-- **`Submission.HasGreenFunctionE` is unsatisfiable** on a charted space: its growth clause at
the pole and its compactness clause for the superlevel set `{E z₀ + 1 ≤ E}` contradict each other
(the superlevel set accumulates at `z₀` but does not contain it, so it is not closed, hence not
compact). -/
theorem not_hasGreenFunctionE {z₀ : X} {E : X → ℝ}
    (hE : Submission.HasGreenFunctionE z₀ E) : False := by
  obtain ⟨⟨-, -, hcomp⟩, -, hgrowth⟩ := hE
  set ε : ℝ := max (E z₀) 0 + 1 with hεdef
  have hεpos : (0 : ℝ) < ε := by rw [hεdef]; linarith [le_max_right (E z₀) 0]
  have hlt : E z₀ < ε := by rw [hεdef]; linarith [le_max_left (E z₀) 0]
  obtain ⟨V, hV, hVE⟩ := hgrowth ε
  have hcl : z₀ ∈ closure {x : X | ε ≤ E x} := by
    rw [mem_closure_iff]
    intro W hW hzW
    obtain ⟨x, hx, hxne⟩ := exists_ne_of_mem_nhds (z₀ := z₀) (inter_mem (hW.mem_nhds hzW) hV)
    exact ⟨x, hx.1, le_of_lt (hVE x hx.2 hxne)⟩
  have hnot : z₀ ∉ {x : X | ε ≤ E x} := by
    intro h
    exact absurd h (not_le.mpr hlt)
  exact hnot ((hcomp ε hεpos).isClosed.closure_subset hcl)

/-- The existential form: no point of a charted space carries a strong Green function. -/
theorem not_exists_hasGreenFunctionE (z₀ : X) :
    ¬ ∃ E : X → ℝ, Submission.HasGreenFunctionE z₀ E :=
  fun ⟨_, hE⟩ => not_hasGreenFunctionE hE

end Work.Modulus
