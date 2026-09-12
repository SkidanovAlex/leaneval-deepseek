import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Commons.Analysis.MeasureTheory.polar_integral_prod

set_option linter.unusedSectionVars false

noncomputable section
open Set Function MeasureTheory Metric
open scoped Classical ENNReal NNReal Pointwise

namespace Commons.Analysis.MeasureTheory

/-- For a nonnegative scalar `r` the cosine of `r • θ` scales linearly: `|⟨u, r•θ⟩| = r |⟨u,θ⟩|`. -/
lemma abs_inner_smul_nonneg {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u : V) (θ : V) (r : ℝ) (hr : 0 ≤ r) :
    |inner ℝ u (r • θ)| = r * |inner ℝ u θ| := by
  rw [inner_smul_right, abs_mul, abs_of_nonneg hr]

theorem integral_cosine_separable
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] [FiniteDimensional ℝ V] [Nontrivial V]
    (u : V) (g : Metric.sphere (0 : V) 1 → ℝ) (h : Set.Ioi (0 : ℝ) → ℝ) (f : V → ℝ)
    (hfspec : ∀ (r : Set.Ioi (0 : ℝ)) (θ : Metric.sphere (0 : V) 1),
        f (r.1 • (θ : V)) = h r * g θ) :
    (∫ x : V, |inner ℝ u x| * f x) =
      (∫ θ : Metric.sphere (0 : V) 1, |inner ℝ u (θ : V)| * g θ ∂MeasureTheory.volume.toSphere) *
      (∫ r : Set.Ioi (0 : ℝ), (r : ℝ) * h r
        ∂(MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ V - 1))) := by
  let σ : Measure (Metric.sphere (0 : V) 1) := MeasureTheory.volume.toSphere
  let ν : Measure (Set.Ioi (0 : ℝ)) := Measure.volumeIoiPow (Module.finrank ℝ V - 1)
  let F : V → ℝ := fun x => |inner ℝ u x| * f x
  have hpoint : ∀ p : Metric.sphere (0 : V) 1 × Set.Ioi (0 : ℝ),
      F (p.2.1 • (p.1 : V)) = (|inner ℝ u (p.1 : V)| * g p.1) * (p.2.1 * h p.2) := by
    intro p
    dsimp [F]
    rw [hfspec p.2 p.1]
    rw [abs_inner_smul_nonneg u (p.1 : V) p.2.1 (le_of_lt p.2.2)]
    ring
  calc
    (∫ x : V, |inner ℝ u x| * f x)
        = ∫ p : Metric.sphere (0 : V) 1 × Set.Ioi (0 : ℝ), F (p.2.1 • (p.1 : V)) ∂(σ.prod ν) := by
          simpa [σ, ν, F] using (polar_integral_prod (V := V) (F := F))
    _ = ∫ p : Metric.sphere (0 : V) 1 × Set.Ioi (0 : ℝ),
          (|inner ℝ u (p.1 : V)| * g p.1) * (p.2.1 * h p.2) ∂(σ.prod ν) := by
          refine integral_congr_ae ?_
          filter_upwards with p
          exact hpoint p
    _ = (∫ θ : Metric.sphere (0 : V) 1, |inner ℝ u (θ : V)| * g θ ∂σ) *
        (∫ r : Set.Ioi (0 : ℝ), (r : ℝ) * h r ∂ν) := by
          simpa using (integral_prod_mul (μ := σ) (ν := ν)
            (f := fun θ : Metric.sphere (0 : V) 1 => |inner ℝ u (θ : V)| * g θ)
            (g := fun r : Set.Ioi (0 : ℝ) => (r : ℝ) * h r))
    _ = (∫ θ : Metric.sphere (0 : V) 1, |inner ℝ u (θ : V)| * g θ ∂MeasureTheory.volume.toSphere) *
        (∫ r : Set.Ioi (0 : ℝ), (r : ℝ) * h r ∂(MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ V - 1))) := by
          simp [σ, ν]

end Commons.Analysis.MeasureTheory