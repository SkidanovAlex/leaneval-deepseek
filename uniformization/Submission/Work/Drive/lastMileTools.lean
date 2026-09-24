import Mathlib
import Submission.Work.Drive.energyGreenRung
import Submission.Work.Drive.greenEnergyGlue

/-!
# Tools of the "last mile" of the energy route to the symmetry of the Green function

* `Work.Drive.gradient_comp_of_differentiableAt` — the chain rule `∇(Φ ∘ u) = (deriv Φ ∘ u) • ∇u`.

* `Work.Drive.pairTerm_comp_right` — the **chain rule for the pairing term**: composing the last
  function with `Φ : ℝ → ℝ`, `Φ 0 = 0`, multiplies the weight by `deriv Φ ∘ g`.  This turns the pole
  identity applied to `Φ ∘ f` into an identity for the weighted energy `∑ᵢ ∫ ψᵢ·(deriv Φ ∘ f)·⟪∇f,∇f⟫`,
  which is the form in which the level identity and the collar estimates are used.

* `Work.Drive.pairTerm_abs_le` — **Cauchy–Schwarz for the pairing term**: for a nonnegative weight,
  `|pairTerm x ρ σ W f g| ≤ (pairTerm x ρ σ W f f + pairTerm x ρ σ W g g)/2`.  This makes the
  *integrability of the mixed pairing* — the obstruction recorded in the earlier sessions of this
  project — a consequence of the level identities instead of an extra hypothesis.
-/

open MeasureTheory Set Filter
open scoped Manifold Topology Gradient

noncomputable section

set_option linter.unusedSectionVars false

namespace Work.Drive

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]

/-! ## 1. The chain rule for `gradient` -/

/-- **Chain rule for `gradient`**: `∇(Φ ∘ u) = (deriv Φ ∘ u) • ∇u`. -/
theorem gradient_comp_of_differentiableAt {Φ : ℝ → ℝ} {u : ℂ → ℝ} {z : ℂ}
    (hΦ : DifferentiableAt ℝ Φ (u z)) (hu : DifferentiableAt ℝ u z) :
    gradient (fun w => Φ (u w)) z = deriv Φ (u z) • gradient u z := by
  have hfd : fderiv ℝ (fun w => Φ (u w)) z = (fderiv ℝ Φ (u z)).comp (fderiv ℝ u z) := by
    change fderiv ℝ (Φ ∘ u) z = _
    exact fderiv_comp z hΦ hu
  refine ext_inner_right ℝ fun v => ?_
  rw [inner_gradient_left, hfd, ContinuousLinearMap.comp_apply]
  have h1 : (fderiv ℝ Φ (u z)) ((fderiv ℝ u z) v) = deriv Φ (u z) * ((fderiv ℝ u z) v) := by
    have h2 : fderiv ℝ Φ (u z) = ContinuousLinearMap.toSpanSingleton ℝ (deriv Φ (u z)) := by
      refine ContinuousLinearMap.ext_ring ?_
      rw [ContinuousLinearMap.toSpanSingleton_apply, one_smul, fderiv_apply_one_eq_deriv]
    rw [h2, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm]
  rw [h1]
  simp only [real_inner_smul_left, inner_gradient_left]

/-! ## 2. The chain rule for the pairing term -/

/-- The clamped pullback commutes with composition by `Φ` when `Φ 0 = 0`. -/
theorem clampedPullback_comp {x : X} {ρ : ℝ} {g : X → ℝ} {Φ : ℝ → ℝ} (hΦ : Φ 0 = 0) :
    clampedPullback x ρ (fun y => Φ (g y)) = fun z => Φ (clampedPullback x ρ g z) := by
  funext z
  by_cases hz : z ∈ Metric.ball ((chartAt ℂ x) x) ρ
  · simp only [clampedPullback, Set.indicator_of_mem hz]
  · simp only [clampedPullback, Set.indicator_of_notMem hz, hΦ]

/-- **Chain rule for the pairing term.** -/
theorem pairTerm_comp_right {x : X} {ρ σ : ℝ} (hσρ : σ < ρ) {W f g : X → ℝ} {Φ : ℝ → ℝ}
    (hΦ0 : Φ 0 = 0) (hΦd : Differentiable ℝ Φ)
    (hdiff : ∀ᵐ z ∂(volume : Measure ℂ), DifferentiableAt ℝ (clampedPullback x ρ g) z) :
    pairTerm x ρ σ W f (fun y => Φ (g y))
      = pairTerm x ρ σ (fun y => W y * deriv Φ (g y)) f g := by
  rw [pairTerm, pairTerm]
  refine integral_congr_ae ?_
  filter_upwards [hdiff] with z hz
  have hchain : gradient (fun w => Φ (clampedPullback x ρ g w)) z
      = deriv Φ (clampedPullback x ρ g z) • gradient (clampedPullback x ρ g) z :=
    gradient_comp_of_differentiableAt hΦd.differentiableAt hz
  have hcomp : clampedPullback x ρ (fun y => Φ (g y))
      = fun w => Φ (clampedPullback x ρ g w) := clampedPullback_comp (x := x) (ρ := ρ) hΦ0
  rw [hcomp, hchain, inner_smul_right]
  by_cases hzσ : z ∈ Metric.ball ((chartAt ℂ x) x) σ
  · have hzρ : z ∈ Metric.ball ((chartAt ℂ x) x) ρ := Metric.ball_subset_ball hσρ.le hzσ
    rw [clampedPullback_apply_of_mem hzσ, clampedPullback_apply_of_mem hzσ,
      clampedPullback_apply_of_mem hzρ]
    ring
  · rw [clampedPullback_eq_zero_of_notMem_ball (u := W) hzσ,
      clampedPullback_eq_zero_of_notMem_ball (u := fun y => W y * deriv Φ (g y)) hzσ]
    ring

/-! ## 3. Cauchy–Schwarz for the pairing term -/

/-- The clamped pullback of a nonnegative function is nonnegative. -/
theorem clampedPullback_nonneg {x : X} {ρ : ℝ} {W : X → ℝ} (hW : ∀ y, 0 ≤ W y) (z : ℂ) :
    0 ≤ clampedPullback x ρ W z := by
  by_cases hz : z ∈ Metric.ball ((chartAt ℂ x) x) ρ
  · rw [clampedPullback_apply_of_mem hz]; exact hW _
  · rw [clampedPullback_eq_zero_of_notMem_ball hz]

/-- **Cauchy–Schwarz for the pairing term.** -/
theorem pairTerm_abs_le {x : X} {ρ σ : ℝ} {W f g : X → ℝ} (hW : ∀ y, 0 ≤ W y)
    (hfg : PairIntegrable x ρ σ W f g) (hff : PairIntegrable x ρ σ W f f)
    (hgg : PairIntegrable x ρ σ W g g)
    (hf : ∀ᵐ z ∂(volume : Measure ℂ), DifferentiableAt ℝ (clampedPullback x ρ f) z)
    (hg : ∀ᵐ z ∂(volume : Measure ℂ), DifferentiableAt ℝ (clampedPullback x ρ g) z) :
    |pairTerm x ρ σ W f g| ≤ (pairTerm x ρ σ W f f + pairTerm x ρ σ W g g) / 2 := by
  set F : ℂ → ℝ := fun z => clampedPullback x σ W z *
    inner ℝ (gradient (clampedPullback x ρ f) z) (gradient (clampedPullback x ρ g) z) with hF
  set A : ℂ → ℝ := fun z => clampedPullback x σ W z *
    inner ℝ (gradient (clampedPullback x ρ f) z) (gradient (clampedPullback x ρ f) z) with hA
  set B : ℂ → ℝ := fun z => clampedPullback x σ W z *
    inner ℝ (gradient (clampedPullback x ρ g) z) (gradient (clampedPullback x ρ g) z) with hB
  have hFint : Integrable F := hfg
  have hAint : Integrable A := hff
  have hBint : Integrable B := hgg
  have hpt : ∀ᵐ z ∂(volume : Measure ℂ), |F z| ≤ (A z + B z) / 2 := by
    filter_upwards [hf, hg] with z hzf hzg
    have hWz : 0 ≤ clampedPullback x σ W z := clampedPullback_nonneg hW z
    have h1 : |inner ℝ (gradient (clampedPullback x ρ f) z) (gradient (clampedPullback x ρ g) z)|
        ≤ (inner ℝ (gradient (clampedPullback x ρ f) z) (gradient (clampedPullback x ρ f) z)
          + inner ℝ (gradient (clampedPullback x ρ g) z) (gradient (clampedPullback x ρ g) z)) / 2 := by
      have h2 : ‖inner ℝ (gradient (clampedPullback x ρ f) z)
          (gradient (clampedPullback x ρ g) z)‖
          ≤ ‖gradient (clampedPullback x ρ f) z‖ * ‖gradient (clampedPullback x ρ g) z‖ :=
        norm_inner_le_norm _ _
      rw [Real.norm_eq_abs] at h2
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
      nlinarith [sq_nonneg (‖gradient (clampedPullback x ρ f) z‖ - ‖gradient (clampedPullback x ρ g) z‖),
        norm_nonneg (gradient (clampedPullback x ρ f) z), norm_nonneg (gradient (clampedPullback x ρ g) z)]
    simp only [hF, hA, hB]
    rw [abs_mul, abs_of_nonneg hWz]
    calc clampedPullback x σ W z * |inner ℝ (gradient (clampedPullback x ρ f) z)
          (gradient (clampedPullback x ρ g) z)|
        ≤ clampedPullback x σ W z *
          ((inner ℝ (gradient (clampedPullback x ρ f) z) (gradient (clampedPullback x ρ f) z)
            + inner ℝ (gradient (clampedPullback x ρ g) z) (gradient (clampedPullback x ρ g) z)) / 2) :=
          mul_le_mul_of_nonneg_left h1 hWz
      _ = (clampedPullback x σ W z * inner ℝ (gradient (clampedPullback x ρ f) z)
            (gradient (clampedPullback x ρ f) z)
          + clampedPullback x σ W z * inner ℝ (gradient (clampedPullback x ρ g) z)
            (gradient (clampedPullback x ρ g) z)) / 2 := by ring
  have hBint' : Integrable (fun z => (A z + B z) / 2) := (hAint.add hBint).div_const 2
  have key : |∫ z, F z| ≤ ∫ z, (A z + B z) / 2 :=
    le_trans (abs_integral_le_integral_abs (f := F)) (integral_mono_ae hFint.abs hBint' hpt)
  have hpairA : pairTerm x ρ σ W f f = ∫ z, A z := rfl
  have hpairB : pairTerm x ρ σ W g g = ∫ z, B z := rfl
  have hsum : (pairTerm x ρ σ W f f + pairTerm x ρ σ W g g) = ∫ z, (A z + B z) := by
    rw [hpairA, hpairB, ← integral_add hAint hBint]
  have hpair : pairTerm x ρ σ W f g = ∫ z, F z := rfl
  rw [hpair, hsum, ← integral_div]
  exact key

end Work.Drive
