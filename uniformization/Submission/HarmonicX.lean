import ChallengeDeps
import Submission.RiemannSurface
import Submission.Commons.Analysis.Complex.Harmonic.harmonicOnNhd_of_monotone_pointwise_limit_ball

/-!
# Harnack's convergence principle on a Riemann surface

An increasing sequence of harmonic functions on `X` whose pointwise limit exists is harmonic.
The proof reduces to the Euclidean statement on a chart disc around each point.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Submission

section Harnack

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **Harnack's convergence principle on `X`.** -/
theorem harmonicOnX_of_monotone_pointwise_limit {v : ℕ → X → ℝ} {w : X → ℝ}
    (hv : ∀ n : ℕ, HarmonicOnX (v n) univ)
    (hmono : ∀ n x, v n x ≤ v (n + 1) x)
    (hlim : ∀ x : X, Tendsto (fun n => v n x) atTop (nhds (w x))) :
    HarmonicOnX w univ := by
  intro x₀ _
  have hmem : (chartAt ℂ x₀) x₀ ∈ (chartAt ℂ x₀).target :=
    (chartAt ℂ x₀).map_source (mem_chart_source ℂ x₀)
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp ((chartAt ℂ x₀).open_target.mem_nhds hmem)
  refine (HarmonicOnXAt_iff_chart (mem_chart_source ℂ x₀)).mpr ?_
  have hv' : ∀ n : ℕ, InnerProductSpace.HarmonicOnNhd
      ((v n) ∘ (chartAt ℂ x₀).symm) (Metric.ball ((chartAt ℂ x₀) x₀) ρ) := by
    intro n z hz
    have h := (HarmonicOnXAt_iff_chart (X := X) (u := v n)
      (x := (chartAt ℂ x₀).symm z) (y := x₀)
      ((chartAt ℂ x₀).map_target (hρsub hz))).mp (hv n _ (mem_univ _))
    rwa [(chartAt ℂ x₀).right_inv (hρsub hz)] at h
  have hmono' : ∀ n : ℕ, ∀ z : ℂ, z ∈ Metric.ball ((chartAt ℂ x₀) x₀) ρ →
      ((v n) ∘ (chartAt ℂ x₀).symm) z ≤ ((v (n + 1)) ∘ (chartAt ℂ x₀).symm) z :=
    fun n z _ => hmono n _
  have hlim' : ∀ z : ℂ, z ∈ Metric.ball ((chartAt ℂ x₀) x₀) ρ →
      Tendsto (fun n : ℕ => ((v n) ∘ (chartAt ℂ x₀).symm) z) atTop
        (nhds ((w ∘ (chartAt ℂ x₀).symm) z)) :=
    fun z _ => hlim ((chartAt ℂ x₀).symm z)
  exact Commons.Analysis.Complex.Harmonic.harmonicOnNhd_of_monotone_pointwise_limit_ball
    hv' hmono' hlim' ((chartAt ℂ x₀) x₀) (Metric.mem_ball_self hρ)

/-- The pointwise supremum of an increasing sequence of harmonic functions on `X` is harmonic. -/
theorem harmonicOnX_of_monotone_iSup {v : ℕ → X → ℝ}
    (hv : ∀ n : ℕ, HarmonicOnX (v n) univ)
    (hmono : ∀ n x, v n x ≤ v (n + 1) x)
    (hbdd : ∀ x : X, BddAbove (Set.range (fun n => v n x))) :
    HarmonicOnX (fun x => ⨆ n, v n x) univ :=
  harmonicOnX_of_monotone_pointwise_limit hv hmono fun x =>
    tendsto_atTop_ciSup (monotone_nat_of_le_succ fun n => hmono n x) (hbdd x)

end Harnack

end Submission
