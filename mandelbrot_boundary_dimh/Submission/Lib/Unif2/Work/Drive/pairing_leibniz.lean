import Mathlib
import Submission.Lib.Unif2.Work.Drive.energyGreenRung

/-!
# The Leibniz rule for the Dirichlet pairing

The two-sided comparison of the localised test functions in the reciprocity argument splits the
pairing of `f` against `W' * g` into the pairing of `f` against `g` with the merged weight `W * W'`
plus the *correction* pairing of `f` against `W'` with the weight `W * g`:

  `pairTerm x ρ σ W f (W' * g) = pairTerm x ρ σ (W * W') f g + pairTerm x ρ σ (W * g) f W'`.

The pointwise input is the Leibniz rule for `gradient` applied to the clamped pullback of the product
(which is the product of the clamped pullbacks — `clampedPullback_mul`), together with the fact that
all the clamps are honest on the ball of radius `σ` and the whole integrand vanishes outside it.
No support hypothesis on `W'` is needed: on `ball σ` (which is inside `ball ρ`) the clamped pullbacks
at `σ` and at `ρ` agree, and off `ball σ` the weight `clampedPullback x σ W` kills everything.
-/

open MeasureTheory Set Filter
open scoped Manifold Topology Gradient

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Drive

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]

-- The two lemmas below are *local, private* copies of results that live in
-- `Submission/Work/Drive/energyGreenRung.lean`, whose namespace is currently being reorganised by
-- another agent.  Keeping private copies here makes this file immune to that churn.

/-- **Local copy of the Leibniz rule for the gradient of a product.** -/
private lemma gradient_mul_real_local {f g : ℂ → ℝ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    gradient (fun w => f w * g w) z = f z • gradient g z + g z • gradient f z := by
  show (InnerProductSpace.toDual ℝ ℂ).symm (fderiv ℝ (f * g) z) = _
  rw [fderiv_mul hf hg, map_add, map_smul, map_smul]
  rfl

private lemma clampedPullback_mul_local (x₀ : X) (ρ : ℝ) (u v : X → ℝ) :
    clampedPullback x₀ ρ (u * v) = clampedPullback x₀ ρ u * clampedPullback x₀ ρ v := by
  funext z
  by_cases hz : z ∈ Metric.ball ((chartAt ℂ x₀) x₀) ρ
  · simp only [Pi.mul_apply, clampedPullback, Set.indicator_of_mem hz]
  · simp only [Pi.mul_apply, clampedPullback, Set.indicator_of_notMem hz, zero_mul]

/-- **The Leibniz rule for the pairing term.** -/
theorem pairTerm_leibniz {x : X} {ρ σ : ℝ} {W W' f g : X → ℝ}
    (hσρ : σ < ρ)
    (htgt : Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target)
    (hfg : PairIntegrable x ρ σ W f (W' * g))
    (h1 : PairIntegrable x ρ σ (W * W') f g)
    (h2 : PairIntegrable x ρ σ (W * g) f W')
    (hf : ∀ᵐ z ∂(volume : Measure ℂ), DifferentiableAt ℝ (clampedPullback x ρ f) z)
    (hg : ∀ᵐ z ∂(volume : Measure ℂ), DifferentiableAt ℝ (clampedPullback x ρ g) z)
    (hW' : ∀ᵐ z ∂(volume : Measure ℂ), DifferentiableAt ℝ (clampedPullback x ρ W') z) :
    pairTerm x ρ σ W f (W' * g)
      = pairTerm x ρ σ (W * W') f g + pairTerm x ρ σ (W * g) f W' := by
  rw [pairTerm, pairTerm, pairTerm, ← integral_add h1 h2]
  refine integral_congr_ae ?_
  filter_upwards [hf, hg, hW'] with z hfz hgz hW'z
  by_cases hz : z ∈ Metric.ball ((chartAt ℂ x) x) σ
  · have hzρ : z ∈ Metric.ball ((chartAt ℂ x) x) ρ := Metric.ball_subset_ball hσρ.le hz
    have hρσ : clampedPullback x ρ g z = clampedPullback x σ g z := by
      rw [clampedPullback_apply_of_mem (u := g) hzρ, clampedPullback_apply_of_mem (u := g) hz]
    have hρσ' : clampedPullback x ρ W' z = clampedPullback x σ W' z := by
      rw [clampedPullback_apply_of_mem (u := W') hzρ, clampedPullback_apply_of_mem (u := W') hz]
    have hww : clampedPullback x σ W z * clampedPullback x σ W' z
        = clampedPullback x σ (W * W') z := by
      rw [clampedPullback_mul_local]; rfl
    have hwg : clampedPullback x σ W z * clampedPullback x σ g z
        = clampedPullback x σ (W * g) z := by
      rw [clampedPullback_mul_local]; rfl
    -- the Leibniz rule for the clamped pullback of the product
    have hgrad : gradient (clampedPullback x ρ (W' * g)) z
        = clampedPullback x ρ W' z • gradient (clampedPullback x ρ g) z
          + clampedPullback x ρ g z • gradient (clampedPullback x ρ W') z := by
      rw [clampedPullback_mul_local]
      exact gradient_mul_real_local hW'z hgz
    rw [hgrad, inner_add_right, mul_add, inner_smul_right, inner_smul_right, hρσ', hρσ,
      ← mul_assoc, ← mul_assoc, hww, hwg]

  · have hW0 : clampedPullback x σ W z = 0 := clampedPullback_eq_zero_of_notMem_ball hz
    have h1' : clampedPullback x σ (W * W') z = 0 := clampedPullback_eq_zero_of_notMem_ball hz
    have h2' : clampedPullback x σ (W * g) z = 0 := clampedPullback_eq_zero_of_notMem_ball hz
    rw [hW0, h1', h2']
    ring

/-- **The Leibniz rule for the pairing.** -/
theorem pairing_leibniz {ι : Type*} [Fintype ι] {y : ι → X} {ρ σ : ι → ℝ} {ψ : ι → X → ℝ}
    {W W' f g : X → ℝ}
    (hσρ : ∀ i, σ i < ρ i) (htgt : ∀ i, Metric.ball ((chartAt ℂ (y i)) (y i)) (ρ i)
      ⊆ (chartAt ℂ (y i)).target)
    (hfg : ∀ i, PairIntegrable (y i) (ρ i) (σ i) (ψ i * W) f (W' * g))
    (h1 : ∀ i, PairIntegrable (y i) (ρ i) (σ i) (ψ i * W * W') f g)
    (h2 : ∀ i, PairIntegrable (y i) (ρ i) (σ i) (ψ i * W * g) f W')
    (hf : ∀ i, ∀ᵐ z ∂(volume : Measure ℂ), DifferentiableAt ℝ (clampedPullback (y i) (ρ i) f) z)
    (hg : ∀ i, ∀ᵐ z ∂(volume : Measure ℂ), DifferentiableAt ℝ (clampedPullback (y i) (ρ i) g) z)
    (hW' : ∀ i, ∀ᵐ z ∂(volume : Measure ℂ), DifferentiableAt ℝ (clampedPullback (y i) (ρ i) W') z) :
    pairing y ρ σ (fun i => ψ i * W) f (W' * g)
      = pairing y ρ σ (fun i => ψ i * (W * W')) f g
        + pairing y ρ σ (fun i => ψ i * (W * g)) f W' := by
  rw [pairing, pairing, pairing, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := pairTerm_leibniz (x := y i) (ρ := ρ i) (σ := σ i) (W := ψ i * W) (W' := W')
    (f := f) (g := g) (hσρ i) (htgt i) (hfg i)
    (h1 i) (h2 i)
    (hf i) (hg i) (hW' i)
  rw [h]
  simp only [mul_assoc]

end Work.Drive
