import Submission.Lib.Unif2.UnifDeps
import Submission.Lib.Unif2.Extremal
import Submission.Lib.Unif2.Commons.Analysis.Complex.Montel.exists_subseq_tendstoLocallyUniformlyOn_manifold
import Submission.Lib.Unif2.ExtremalOnto


/-!
# Existence of the extremal function

The extremal problem on a complex one-manifold `X`:

`extremalFamily x₀ = {f : X → ℂ | f holomorphic, ‖f ·‖ ≤ 1, f x₀ = 0}`,

`extremalDerivative x₀ = sSup {‖f'(x₀)‖ : f ∈ extremalFamily x₀}`.

The supremum is finite (Schwarz bound, `Submission.extremalDerivative_le`) and it is **attained**:
a maximising sequence is normal (Montel's theorem on the manifold `X`,
`Commons.Analysis.Complex.Montel.exists_subseq_tendstoLocallyUniformlyOn_manifold`), and locally
uniform convergence implies convergence of the derivatives (Mathlib,
`TendstoLocallyUniformlyOn.deriv`), so the limit realises the supremum.

Combined with the Möbius amplification of `Submission/ExtremalOnto.lean` this shows that an
extremal function with non-zero derivative maps onto the unit disc.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Submission

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- Existence of a chart disc around any point with the closed ball inside the chart target. -/
theorem exists_chartDisc_radius (x₀ : X) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall ((chartAt ℂ x₀) x₀) ρ ⊆ (chartAt ℂ x₀).target := by
  obtain ⟨ρ₀, hρ₀, hρ₀sub⟩ := Metric.mem_nhds_iff.mp
    ((chartAt ℂ x₀).open_target.mem_nhds ((chartAt ℂ x₀).map_source (mem_chart_source ℂ x₀)))
  exact ⟨ρ₀ / 2, half_pos hρ₀,
    (Metric.closedBall_subset_ball (by linarith)).trans hρ₀sub⟩

/-- Holomorphy, transported to the chart at a fixed point. -/
theorem analyticOnNhd_chart_at {f : X → ℂ} (hf : HolomorphicOnX f univ) (x₀ : X) :
    AnalyticOnNhd ℂ (f ∘ (chartAt ℂ x₀).symm) (chartAt ℂ x₀).target := by
  intro w hw
  have hx : (chartAt ℂ x₀).symm w ∈ (chartAt ℂ x₀).source := (chartAt ℂ x₀).map_target hw
  have h1 : HolomorphicOnXAt f ((chartAt ℂ x₀).symm w) := hf _ (mem_univ _)
  have h2 := (HolomorphicOnXAt_iff_chart (f := f) (x := (chartAt ℂ x₀).symm w) (y := x₀) hx).mp h1
  rwa [(chartAt ℂ x₀).right_inv hw] at h2

/-- Montel's theorem on `X`, in the form used below. -/
theorem montel_on_X (x₀ : X) [SecondCountableTopology X]
    (f : ℕ → X → ℂ) (hf : ∀ n, HolomorphicOnX (f n) univ) (hb : ∀ n x, ‖f n x‖ ≤ 1) :
    ∃ (φ : ℕ → ℕ) (g : X → ℂ), StrictMono φ ∧
      TendstoLocallyUniformlyOn (fun n => f (φ n)) g Filter.atTop Set.univ ∧
      HolomorphicOnX g univ := by
  haveI : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace ℂ X
  obtain ⟨φ, g, hmono, hconv, hghol⟩ :=
    Commons.Analysis.Complex.Montel.exists_subseq_tendstoLocallyUniformlyOn_manifold
      (f := f) (fun n x => (hf n) x (mem_univ x)) hb
  exact ⟨φ, g, hmono, hconv, fun x _ => hghol x⟩

/-- **The extremal derivative is attained.** -/
theorem exists_extremal (x₀ : X) [ConnectedSpace X] [SecondCountableTopology X] :
    ∃ f ∈ extremalFamily x₀,
      ‖deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖ = extremalDerivative x₀ := by
  haveI : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace ℂ X
  obtain ⟨ρ, hρ, hsub⟩ := exists_chartDisc_radius (X := X) x₀
  have hbdd : BddAbove (extremalDerivativeSet x₀) := extremalDerivative_bddAbove hρ hsub
  have hne : (extremalDerivativeSet x₀).Nonempty := (extremalFamily_nonempty x₀).image _
  -- a maximising sequence
  have hseq : ∀ n : ℕ, ∃ f ∈ extremalFamily x₀,
      extremalDerivative x₀ - ((n : ℝ) + 1)⁻¹ <
        ‖deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖ := by
    intro n
    have hlt : extremalDerivative x₀ - ((n : ℝ) + 1)⁻¹ < sSup (extremalDerivativeSet x₀) := by
      rw [← extremalDerivative]
      have : 0 < ((n : ℝ) + 1)⁻¹ := by positivity
      linarith
    obtain ⟨y, ⟨f, hf, rfl⟩, hy⟩ := exists_lt_of_lt_csSup hne hlt
    exact ⟨f, hf, hy⟩
  choose f hf hfbound using hseq
  -- Montel: a locally uniformly convergent subsequence
  obtain ⟨φ, g, hφmono, hconv, hghol⟩ :=
    montel_on_X (X := X) x₀ f (fun n => (hf n).1) (fun n x => (hf n).2.1 x)
  -- the limit is in the extremal family
  have hgmem : g ∈ extremalFamily x₀ := by
    refine ⟨hghol, ?_, ?_⟩
    · intro x
      exact le_of_tendsto (hconv.tendsto_at (mem_univ x)).norm
        (Eventually.of_forall fun n => (hf (φ n)).2.1 x)
    · have hpt : Tendsto (fun n => f (φ n) x₀) atTop (𝓝 (g x₀)) :=
        hconv.tendsto_at (mem_univ x₀)
      have hzero : (fun n => f (φ n) x₀) = fun _ => (0 : ℂ) := by
        funext n; exact (hf (φ n)).2.2
      rw [hzero] at hpt
      exact tendsto_nhds_unique hpt tendsto_const_nhds
  -- convergence of the derivatives on the chart at `x₀`
  have hconv' : TendstoLocallyUniformlyOn (fun n => (f (φ n)) ∘ (chartAt ℂ x₀).symm)
      (g ∘ (chartAt ℂ x₀).symm) atTop (chartAt ℂ x₀).target :=
    hconv.comp (chartAt ℂ x₀).symm (mapsTo_univ _ _) (chartAt ℂ x₀).continuousOn_symm
  have hderivconv : TendstoLocallyUniformlyOn
      (deriv ∘ fun n => (f (φ n)) ∘ (chartAt ℂ x₀).symm)
      (deriv (g ∘ (chartAt ℂ x₀).symm)) atTop (chartAt ℂ x₀).target := by
    refine hconv'.deriv ?_ (chartAt ℂ x₀).open_target
    filter_upwards with n
    intro w hw
    exact ((analyticOnNhd_chart_at (hf (φ n)).1 x₀) w hw).differentiableWithinAt
  have hpt := hderivconv.tendsto_at ((chartAt ℂ x₀).map_source (mem_chart_source ℂ x₀))
  have hnorm : Tendsto (fun n => ‖deriv ((f (φ n)) ∘ (chartAt ℂ x₀).symm)
      ((chartAt ℂ x₀) x₀)‖) atTop
      (𝓝 ‖deriv (g ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖) := hpt.norm
  -- squeeze with the maximising sequence
  have hupper : ∀ n : ℕ, ‖deriv ((f (φ n)) ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖
      ≤ extremalDerivative x₀ := fun n =>
    le_csSup hbdd ⟨f (φ n), hf (φ n), rfl⟩
  have hlower : Tendsto (fun n : ℕ => extremalDerivative x₀ - ((φ n : ℝ) + 1)⁻¹) atTop
      (𝓝 (extremalDerivative x₀)) := by
    have hφR : Tendsto (fun n : ℕ => ((φ n : ℝ))) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hφmono.tendsto_atTop
    have h0 : Tendsto (fun n : ℕ => ((φ n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 hφR)
    simpa using tendsto_const_nhds.sub h0
  have hlim : ‖deriv (g ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖ = extremalDerivative x₀ :=
    tendsto_nhds_unique hnorm
      (tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower tendsto_const_nhds
        (Eventually.of_forall fun n => le_of_lt (hfbound (φ n)))
        (Eventually.of_forall hupper))
  exact ⟨g, hgmem, hlim⟩

/-- **The extremal function maps onto the unit disc** (whenever the extremal derivative is
positive, i.e. in the hyperbolic case). -/
theorem exists_extremal_surjective (x₀ : X) [ConnectedSpace X] [SecondCountableTopology X]
    [Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)]
    (hpos : 0 < extremalDerivative x₀) :
    ∃ f ∈ extremalFamily x₀, ∀ a : ℂ, ‖a‖ < 1 → ∃ x : X, f x = a := by
  obtain ⟨f, hf, hmax⟩ := exists_extremal (X := X) x₀
  refine ⟨f, hf, extremalFamily_surjective_of_max hf ?_ ?_⟩
  · intro g hg
    rw [hmax]
    exact le_csSup (by
      obtain ⟨ρ, hρ, hsub⟩ := exists_chartDisc_radius (X := X) x₀
      exact extremalDerivative_bddAbove hρ hsub) ⟨g, hg, rfl⟩
  · rw [hmax]; exact hpos

end Submission
