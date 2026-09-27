import Mathlib
import Submission.Work.Mostow.BaryBase

/-!
# Continuity of the barycentre functional (area T4)

`baryFun ν y = ∫ ξ, busemann ξ y ∂ν`.  If `ν` is a probability measure carried by the boundary
sphere `Sph n`, then the integrand `ξ ↦ busemann ξ y` is

* continuous in `y` for `ν`-almost every `ξ` (namely for `ξ ∈ Sph n`), and
* dominated on a neighbourhood of any `y₀` by the `ν`-integrable function
  `ξ ↦ if ξ ∈ Sph n then hdist 0 y₀ + 1 else 0`,

because `|busemann ξ y| ≤ hdist 0 y` for `ξ ∈ Sph n` and `y ↦ hdist 0 y` is continuous.

Consequently `baryFun ν` is continuous.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped Topology

noncomputable section

variable {n : ℕ}

/-- `y ↦ hdist 0 y` is continuous: in the chart it is the composition `arcosh ∘ tpart`,
and `tpart ≥ 1` everywhere. -/
theorem continuous_hdist_zero : Continuous (fun y : E n => hdist (0 : E n) y) := by
  have h : (fun y : E n => hdist (0 : E n) y) = fun y => Real.arcosh (tpart y) := by
    funext y
    simp [hdist, tpart_zero]
  rw [h]
  simpa [Function.comp_def] using continuousOn_univ.mp
    (Real.continuousOn_arcosh.comp continuous_tpart.continuousOn (fun y _ => one_le_tpart y))

/-- The `ν`-measure of the boundary sphere's complement is zero, i.e. `ν` is carried by `Sph n`. -/
theorem ae_mem_sph {ν : Measure (E n)} (hsupp : ν (Sph n)ᶜ = 0) : ∀ᵐ ξ ∂ν, ξ ∈ Sph n :=
  ae_iff.mpr hsupp

open Classical in
/-- `ξ ↦ c · 1_{Sph n}(ξ)` is integrable for every finite measure `ν`; here we only use
probability measures. -/
theorem integrable_ite_sph (ν : Measure (E n)) [IsFiniteMeasure ν] (c : ℝ) :
    Integrable (fun ξ : E n => if ξ ∈ Sph n then c else 0) ν := by
  classical
  have hms : MeasurableSet (Sph n) := by
    rw [Sph]; exact Metric.isClosed_sphere.measurableSet
  have heq : (fun ξ : E n => if ξ ∈ Sph n then c else 0)
      = (Sph n).indicator (fun _ : E n => c) := by
    funext ξ
    by_cases h : ξ ∈ Sph n <;> simp [h]
  rw [heq]
  exact (integrable_const c).indicator hms

theorem BaryContinuity (n : ℕ) (ν : MeasureTheory.Measure (Submission.Mostow.E n)) (hν : MeasureTheory.IsProbabilityMeasure ν) (hsupp : ν (Submission.Mostow.Sph n)ᶜ = 0) :
    Continuous (Submission.Mostow.baryFun ν) := by
  classical
  have haeSph : ∀ᵐ ξ ∂ν, ξ ∈ Sph n := ae_mem_sph hsupp
  rw [continuous_iff_continuousAt]
  intro y₀
  -- the local dominating function
  set bound : E n → ℝ := fun ξ => if ξ ∈ Sph n then hdist 0 y₀ + 1 else 0 with hbound_def
  -- measurability of the integrand in `ξ`
  have hmeas : ∀ᶠ y in 𝓝 y₀, AEStronglyMeasurable (fun ξ : E n => busemann ξ y) ν :=
    Filter.Eventually.of_forall fun y => (measurable_busemann y).aestronglyMeasurable
  -- a.e. continuity in `y`
  have hcont : ∀ᵐ ξ ∂ν, ContinuousAt (fun y : E n => busemann ξ y) y₀ := by
    filter_upwards [haeSph] with ξ hξ
    exact continuousAt_busemann ξ hξ y₀
  -- integrability of the dominating function
  have hInt : Integrable bound ν := by
    rw [hbound_def]
    exact integrable_ite_sph (n := n) ν (hdist 0 y₀ + 1)
  -- the domination, on a neighbourhood of `y₀`
  have hbnd : ∀ᶠ y in 𝓝 y₀, ∀ᵐ ξ ∂ν, ‖busemann ξ y‖ ≤ bound ξ := by
    have hopen : IsOpen {y : E n | hdist 0 y < hdist 0 y₀ + 1} :=
      isOpen_lt (continuous_hdist_zero (n := n)) continuous_const
    have hmem : y₀ ∈ {y : E n | hdist 0 y < hdist 0 y₀ + 1} := by
      show hdist 0 y₀ < hdist 0 y₀ + 1
      linarith
    filter_upwards [hopen.mem_nhds hmem] with y hy
    filter_upwards [haeSph] with ξ hξ
    have h1 : ‖busemann ξ y‖ ≤ hdist 0 y := by
      rw [Real.norm_eq_abs]; exact abs_busemann_le_hdist_zero ξ hξ y
    have h2 : bound ξ = hdist 0 y₀ + 1 := by rw [hbound_def]; simp [hξ]
    rw [h2]
    exact le_trans h1 (le_of_lt hy)
  have hfin := continuousAt_of_dominated (μ := ν)
    (F := fun (y : E n) (ξ : E n) => busemann ξ y) (x₀ := y₀) (bound := bound)
    hmeas hbnd hInt hcont
  show ContinuousAt (fun y : E n => ∫ ξ, busemann ξ y ∂ν) y₀
  exact hfin

end

end Work.Mostow
