import Submission.IndexScale

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory
open Submission.Geodesic
open Submission.Rauch
open Submission.IntrinsicVariation
open Submission.IndexIntrinsic
open Submission.IndexIntrinsic2

/-!
# The second variation of the energy over a chart cover, with a *local* integrability hypothesis

`Submission.SecondVarGlobal.energy_second_deriv_cover` assembles the per-piece second variations of
the energy into the one over `[0,L]`, but its interval-integrability hypothesis
`∀ (σ : ℝ) (k), IntervalIntegrable (fun t => F σ t) volume (c k) (c (k+1))` is demanded for **all**
real `σ`.  In the intended application (Roadmap §101.6 item 3) the integrand is
`F σ t = (curveSpeed (fun s => GExp (γ s) (σ • V s)) t) ^ 2` with `V` a field whose *phase*
`(chartCoord, flowScale • (σ • u))` leaves the flow domain for large `σ`, so the smoothness — and
hence the integrability — of the family is only available for `σ` in a neighbourhood of `0`.

This module provides **`energy_second_deriv_cover_eventually`**: the same conclusion from the weaker
hypothesis `∀ᶠ σ in 𝓝 0, ∀ k < N, IntervalIntegrable (fun t => F σ t) volume (c k) (c (k+1))`.
The only change to the proof is that the telescoping identity
`∫_0^L F σ = Σ_k ∫_{c k}^{c (k+1)} F σ` is now an `EventuallyEq` near `0` instead of an equality.
-/

namespace Submission.EnergyCover

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **The second variation of the energy over a chart cover** (local-in-`σ` integrability). -/
theorem energy_second_deriv_cover_eventually
    {γ : ℝ → M} {V Z : (t : ℝ) → TangentSpace I (γ t)} {a b : ℝ}
    {N : ℕ} {c : ℕ → ℝ} {F : ℝ → ℝ → ℝ}
    (hc0 : c 0 = a) (hcN : c N = b)
    (hint : ∀ᶠ σ in 𝓝 (0 : ℝ), ∀ k : ℕ, k < N →
      IntervalIntegrable (fun t : ℝ => F σ t) volume (c k) (c (k + 1)))
    (hintZ : ∀ k : ℕ, k < N → IntervalIntegrable (fun t : ℝ => idxAlong (cov := cov) γ V Z t)
      volume (c k) (c (k + 1)))
    (hk : ∀ k : ℕ, k < N →
      (∀ᶠ σ in 𝓝 (0 : ℝ),
        DifferentiableAt ℝ (fun σ : ℝ => ∫ t in c k..c (k + 1), F σ t) σ) ∧
      HasDerivAt (deriv (fun σ : ℝ => ∫ t in c k..c (k + 1), F σ t))
        (2 * ∫ t in c k..c (k + 1), idxAlong (cov := cov) γ V Z t) 0) :
    HasDerivAt (deriv (fun σ : ℝ => ∫ t in a..b, F σ t))
      (2 * ∫ t in a..b, idxAlong (cov := cov) γ V Z t) 0 ∧
    DifferentiableAt ℝ (fun σ : ℝ => ∫ t in a..b, F σ t) 0 := by
  classical
  -- the telescoping identity, eventually near `0`
  have hsum : (fun σ : ℝ => ∫ t in a..b, F σ t)
      =ᶠ[𝓝 (0 : ℝ)] fun σ : ℝ => ∑ k ∈ Finset.range N, ∫ t in c k..c (k + 1), F σ t := by
    filter_upwards [hint] with σ hσ
    have h := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
      (f := fun t : ℝ => F σ t) (a := c) (n := N) (fun k hk' => hσ k hk')
    rw [hc0, hcN] at h
    exact h.symm
  have hdiff : ∀ᶠ σ in 𝓝 (0 : ℝ), ∀ k ∈ Finset.range N,
      DifferentiableAt ℝ (fun σ : ℝ => ∫ t in c k..c (k + 1), F σ t) σ := by
    rw [Finset.eventually_all]
    intro k hk'
    exact (hk k (Finset.mem_range.mp hk')).1
  have hderiv : deriv (fun σ : ℝ => ∑ k ∈ Finset.range N, ∫ t in c k..c (k + 1), F σ t)
      =ᶠ[𝓝 (0 : ℝ)] (fun σ : ℝ => ∑ k ∈ Finset.range N,
        deriv (fun σ : ℝ => ∫ t in c k..c (k + 1), F σ t) σ) := by
    filter_upwards [hdiff] with σ hσ
    exact deriv_fun_sum hσ
  have hsecond : HasDerivAt (fun σ : ℝ => ∑ k ∈ Finset.range N,
      deriv (fun σ : ℝ => ∫ t in c k..c (k + 1), F σ t) σ)
      (∑ k ∈ Finset.range N, 2 * ∫ t in c k..c (k + 1), idxAlong (cov := cov) γ V Z t) 0 :=
    HasDerivAt.fun_sum (fun k hk' => (hk k (Finset.mem_range.mp hk')).2)
  have hsecond' : HasDerivAt (deriv (fun σ : ℝ => ∑ k ∈ Finset.range N,
      ∫ t in c k..c (k + 1), F σ t))
      (∑ k ∈ Finset.range N, 2 * ∫ t in c k..c (k + 1), idxAlong (cov := cov) γ V Z t) 0 :=
    hsecond.congr_of_eventuallyEq hderiv
  have hdiff0 : DifferentiableAt ℝ (fun σ : ℝ => ∑ k ∈ Finset.range N,
      ∫ t in c k..c (k + 1), F σ t) 0 :=
    DifferentiableAt.fun_sum (fun k hk' => (hk k (Finset.mem_range.mp hk')).1.self_of_nhds)
  have hZsum : (∑ k ∈ Finset.range N, ∫ t in c k..c (k + 1), idxAlong (cov := cov) γ V Z t)
      = ∫ t in a..b, idxAlong (cov := cov) γ V Z t := by
    have h := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
      (f := fun t : ℝ => idxAlong (cov := cov) γ V Z t) (a := c) (n := N) hintZ
    rwa [hc0, hcN] at h
  refine ⟨?_, ?_⟩
  · have h2 := hsecond'
    rw [← Finset.mul_sum, hZsum] at h2
    exact h2.congr_of_eventuallyEq (hsum.deriv)
  · exact hdiff0.congr_of_eventuallyEq hsum


/-- **The second variation of the energy over a chart cover** (local-in-`σ` integrability), with
the *eventual differentiability* of the total energy kept: this is what the shortening argument of
Klingenberg's estimate needs in order to apply the mean value theorem. -/
theorem energy_second_deriv_cover_eventually' 
    {γ : ℝ → M} {V Z : (t : ℝ) → TangentSpace I (γ t)} {a b : ℝ}
    {N : ℕ} {c : ℕ → ℝ} {F : ℝ → ℝ → ℝ}
    (hc0 : c 0 = a) (hcN : c N = b)
    (hint : ∀ᶠ σ in 𝓝 (0 : ℝ), ∀ k : ℕ, k < N →
      IntervalIntegrable (fun t : ℝ => F σ t) volume (c k) (c (k + 1)))
    (hintZ : ∀ k : ℕ, k < N → IntervalIntegrable (fun t : ℝ => idxAlong (cov := cov) γ V Z t)
      volume (c k) (c (k + 1)))
    (hk : ∀ k : ℕ, k < N →
      (∀ᶠ σ in 𝓝 (0 : ℝ),
        DifferentiableAt ℝ (fun σ : ℝ => ∫ t in c k..c (k + 1), F σ t) σ) ∧
      HasDerivAt (deriv (fun σ : ℝ => ∫ t in c k..c (k + 1), F σ t))
        (2 * ∫ t in c k..c (k + 1), idxAlong (cov := cov) γ V Z t) 0) :
    HasDerivAt (deriv (fun σ : ℝ => ∫ t in a..b, F σ t))
      (2 * ∫ t in a..b, idxAlong (cov := cov) γ V Z t) 0 ∧
    DifferentiableAt ℝ (fun σ : ℝ => ∫ t in a..b, F σ t) 0 ∧
    (∀ᶠ σ in 𝓝 (0 : ℝ), DifferentiableAt ℝ (fun σ : ℝ => ∫ t in a..b, F σ t) σ) := by
  classical
  have hsum : (fun σ : ℝ => ∫ t in a..b, F σ t)
      =ᶠ[𝓝 (0 : ℝ)] fun σ : ℝ => ∑ k ∈ Finset.range N, ∫ t in c k..c (k + 1), F σ t := by
    filter_upwards [hint] with σ hσ
    have h := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
      (f := fun t : ℝ => F σ t) (a := c) (n := N) (fun k hk' => hσ k hk')
    rw [hc0, hcN] at h
    exact h.symm
  have hdiff : ∀ᶠ σ in 𝓝 (0 : ℝ), ∀ k ∈ Finset.range N,
      DifferentiableAt ℝ (fun σ : ℝ => ∫ t in c k..c (k + 1), F σ t) σ := by
    rw [Finset.eventually_all]
    intro k hk'
    exact (hk k (Finset.mem_range.mp hk')).1
  have hderiv : deriv (fun σ : ℝ => ∑ k ∈ Finset.range N, ∫ t in c k..c (k + 1), F σ t)
      =ᶠ[𝓝 (0 : ℝ)] (fun σ : ℝ => ∑ k ∈ Finset.range N,
        deriv (fun σ : ℝ => ∫ t in c k..c (k + 1), F σ t) σ) := by
    filter_upwards [hdiff] with σ hσ
    exact deriv_fun_sum hσ
  have hsecond : HasDerivAt (fun σ : ℝ => ∑ k ∈ Finset.range N,
      deriv (fun σ : ℝ => ∫ t in c k..c (k + 1), F σ t) σ)
      (∑ k ∈ Finset.range N, 2 * ∫ t in c k..c (k + 1), idxAlong (cov := cov) γ V Z t) 0 :=
    HasDerivAt.fun_sum (fun k hk' => (hk k (Finset.mem_range.mp hk')).2)
  have hsecond' : HasDerivAt (deriv (fun σ : ℝ => ∑ k ∈ Finset.range N,
      ∫ t in c k..c (k + 1), F σ t))
      (∑ k ∈ Finset.range N, 2 * ∫ t in c k..c (k + 1), idxAlong (cov := cov) γ V Z t) 0 :=
    hsecond.congr_of_eventuallyEq hderiv
  have hdiff0 : DifferentiableAt ℝ (fun σ : ℝ => ∑ k ∈ Finset.range N,
      ∫ t in c k..c (k + 1), F σ t) 0 :=
    DifferentiableAt.fun_sum (fun k hk' => (hk k (Finset.mem_range.mp hk')).1.self_of_nhds)
  have hZsum : (∑ k ∈ Finset.range N, ∫ t in c k..c (k + 1), idxAlong (cov := cov) γ V Z t)
      = ∫ t in a..b, idxAlong (cov := cov) γ V Z t := by
    have h := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
      (f := fun t : ℝ => idxAlong (cov := cov) γ V Z t) (a := c) (n := N) hintZ
    rwa [hc0, hcN] at h
  -- the eventual differentiability of the total energy
  have hsumDiff : ∀ᶠ σ in 𝓝 (0 : ℝ), DifferentiableAt ℝ
      (fun σ : ℝ => ∑ k ∈ Finset.range N, ∫ t in c k..c (k + 1), F σ t) σ := by
    filter_upwards [hdiff] with σ hσ
    exact DifferentiableAt.fun_sum hσ
  have htotalDiff : ∀ᶠ σ in 𝓝 (0 : ℝ), DifferentiableAt ℝ (fun σ : ℝ => ∫ t in a..b, F σ t) σ := by
    obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp hsum
    obtain ⟨ε', hε'pos, hε'sub⟩ := Metric.mem_nhds_iff.mp hsumDiff
    set η : ℝ := min ε ε' / 2 with hηdef
    have hηpos : 0 < η := by rw [hηdef]; positivity
    have hηε : η < ε := by rw [hηdef]; have := min_le_left ε ε'; linarith
    have hηε' : η < ε' := by rw [hηdef]; have := min_le_right ε ε'; linarith
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hηpos] with σ hσ
    have hσdist : dist σ 0 < η := hσ
    have hσabs : |σ| < η := by rw [Real.dist_eq, sub_zero] at hσdist; exact hσdist
    have hdiffσ : DifferentiableAt ℝ
        (fun σ' : ℝ => ∑ k ∈ Finset.range N, ∫ t in c k..c (k + 1), F σ' t) σ :=
      hε'sub (by rw [Metric.mem_ball, Real.dist_eq, sub_zero]; linarith)
    have heq : (fun σ' : ℝ => ∫ t in a..b, F σ' t) =ᶠ[𝓝 σ]
        fun σ' : ℝ => ∑ k ∈ Finset.range N, ∫ t in c k..c (k + 1), F σ' t := by
      filter_upwards [Metric.isOpen_ball.mem_nhds (show σ ∈ Metric.ball (0 : ℝ) ε by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero]; linarith)] with σ' hσ'
      exact hεsub hσ'
    exact hdiffσ.congr_of_eventuallyEq heq
  refine ⟨?_, ?_, htotalDiff⟩
  · have h2 := hsecond'
    rw [← Finset.mul_sum, hZsum] at h2
    exact h2.congr_of_eventuallyEq (hsum.deriv)
  · exact hdiff0.congr_of_eventuallyEq hsum
end

end Submission.EnergyCover
