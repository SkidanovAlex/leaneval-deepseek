import Mathlib
import Submission.Work.Drive.sweepFamOf

/-!
# The averaged chord is the `n`-pairing of the blurred slice difference

`Work.Drive.avgChordOf` is the box average of the `n`-component of the chord of length `g` of a loop
family `Γ`, while `Work.Drive.sweepFamOf` is the double bump-blur of `Γ`.  This module proves that
the two are related by the Jacobi identity of the Bochner integral and the linearity of the inner
product:

`avgChordOf Γ δ₁ δ₂ s n t g = ⟪n, sweepFamOf Γ δ₁ δ₂ s (t+g) - sweepFamOf Γ δ₁ δ₂ s t⟫`.

No smoothness of `Γ` (and no positivity of `δ₁, δ₂`) is needed: only the joint continuity used to
justify the integrability hypotheses of the interval-integral algebra.
-/

noncomputable section
namespace Work.Drive

open MeasureTheory
open scoped intervalIntegral

/-- The convolution kernel `Work.Drive.sweepBump` is continuous (a local copy so that this module
does not have to import the `C^∞`-layer that already proves it). -/
lemma sweepBump_continuous_avgChordOf : Continuous sweepBump := by
  unfold sweepBump
  exact (Real.smoothTransition.continuous.comp (continuous_const.add continuous_id)).mul
    (Real.smoothTransition.continuous.comp (continuous_const.sub continuous_id))

/-- Passing `inner n` through an interval integral of the form `∫ u, φ u • f u` over `[-1,1]`. -/
lemma avgChordOf_inner_intervalIntegral_smul {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {φ : ℝ → ℝ} (hφ : Continuous φ)
    {f : ℝ → E} (hf : Continuous f) (n : E) :
    inner ℝ n (∫ u in (-1 : ℝ)..1, φ u • f u)
      = ∫ u in (-1 : ℝ)..1, φ u * inner ℝ n (f u) := by
  have hint : MeasureTheory.Integrable (fun u : ℝ => φ u • f u)
      (MeasureTheory.volume.restrict (Set.Ioc (-1 : ℝ) 1)) :=
    ((hφ.smul hf).intervalIntegrable (-1) 1).1.integrable
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  rw [← integral_inner (f := fun u : ℝ => φ u • f u) hint n]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
  exact inner_smul_right n (f u) (φ u)

open LeanEval.KnotTheory.Quadrisecant in
theorem avgChordOf_eq_inner_sweepFamOf
    (Γ : ℝ → ℝ → Space) (hΓ : Continuous (fun p : ℝ × ℝ => Γ p.1 p.2))
    (δ₁ δ₂ s : ℝ) (n : Space) (t g : ℝ) :
    Work.Drive.avgChordOf Γ δ₁ δ₂ s n t g
      = inner ℝ n (Work.Drive.sweepFamOf Γ δ₁ δ₂ s (t + g)
          - Work.Drive.sweepFamOf Γ δ₁ δ₂ s t) := by
  have hb : Continuous sweepBump := sweepBump_continuous_avgChordOf
  -- the two knot evaluations, at fixed sweep parameter `v`, are continuous in the loop variable
  have hknot1 : ∀ v : ℝ, Continuous (fun u : ℝ => Γ (s - δ₂ * v) (t + g - δ₁ * u)) := fun v =>
    hΓ.comp (by fun_prop : Continuous fun u : ℝ => (s - δ₂ * v, t + g - δ₁ * u))
  have hknot2 : ∀ v : ℝ, Continuous (fun u : ℝ => Γ (s - δ₂ * v) (t - δ₁ * u)) := fun v =>
    hΓ.comp (by fun_prop : Continuous fun u : ℝ => (s - δ₂ * v, t - δ₁ * u))
  -- the inner integrals are continuous in `v`
  have hP : Continuous (fun v : ℝ =>
      ∫ u in (-1 : ℝ)..1, sweepBump u • Γ (s - δ₂ * v) (t + g - δ₁ * u)) := by
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) (f := fun v u => sweepBump u • Γ (s - δ₂ * v) (t + g - δ₁ * u)) ?_ (-1) 1
    show Continuous (fun p : ℝ × ℝ => sweepBump p.2 • Γ (s - δ₂ * p.1) (t + g - δ₁ * p.2))
    exact (hb.comp continuous_snd).smul
      (hΓ.comp (by fun_prop : Continuous fun p : ℝ × ℝ => (s - δ₂ * p.1, t + g - δ₁ * p.2)))
  have hQ : Continuous (fun v : ℝ =>
      ∫ u in (-1 : ℝ)..1, sweepBump u • Γ (s - δ₂ * v) (t - δ₁ * u)) := by
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) (f := fun v u => sweepBump u • Γ (s - δ₂ * v) (t - δ₁ * u)) ?_ (-1) 1
    show Continuous (fun p : ℝ × ℝ => sweepBump p.2 • Γ (s - δ₂ * p.1) (t - δ₁ * p.2))
    exact (hb.comp continuous_snd).smul
      (hΓ.comp (by fun_prop : Continuous fun p : ℝ × ℝ => (s - δ₂ * p.1, t - δ₁ * p.2)))
  -- the integrability of the outer integrands
  have hA : IntervalIntegrable (fun v : ℝ => sweepBump v •
      (∫ u in (-1 : ℝ)..1, sweepBump u • Γ (s - δ₂ * v) (t + g - δ₁ * u))) volume (-1) 1 :=
    (hb.smul hP).intervalIntegrable (-1) 1
  have hB : IntervalIntegrable (fun v : ℝ => sweepBump v •
      (∫ u in (-1 : ℝ)..1, sweepBump u • Γ (s - δ₂ * v) (t - δ₁ * u))) volume (-1) 1 :=
    (hb.smul hQ).intervalIntegrable (-1) 1
  -- the integrability of the inner integrands, at fixed `v`
  have hC : ∀ v : ℝ, IntervalIntegrable
      (fun u : ℝ => sweepBump u • Γ (s - δ₂ * v) (t + g - δ₁ * u)) volume (-1) 1 :=
    fun v => (hb.smul (hknot1 v)).intervalIntegrable (-1) 1
  have hD : ∀ v : ℝ, IntervalIntegrable
      (fun u : ℝ => sweepBump u • Γ (s - δ₂ * v) (t - δ₁ * u)) volume (-1) 1 :=
    fun v => (hb.smul (hknot2 v)).intervalIntegrable (-1) 1
  -- Step 1: the difference of the two blurred slices is the double integral of the differences
  have hsub : sweepFamOf Γ δ₁ δ₂ s (t + g) - sweepFamOf Γ δ₁ δ₂ s t
      = ∫ v in (-1 : ℝ)..1, sweepBump v •
          (∫ u in (-1 : ℝ)..1, sweepBump u •
            (Γ (s - δ₂ * v) (t + g - δ₁ * u) - Γ (s - δ₂ * v) (t - δ₁ * u))) := by
    simp only [sweepFamOf]
    rw [← intervalIntegral.integral_sub hA hB]
    refine intervalIntegral.integral_congr (fun v _ => ?_)
    rw [← smul_sub]
    have hp : (∫ u in (-1 : ℝ)..1, sweepBump u • Γ (s - δ₂ * v) (t + g - δ₁ * u))
        - (∫ u in (-1 : ℝ)..1, sweepBump u • Γ (s - δ₂ * v) (t - δ₁ * u))
        = ∫ u in (-1 : ℝ)..1, sweepBump u •
            (Γ (s - δ₂ * v) (t + g - δ₁ * u) - Γ (s - δ₂ * v) (t - δ₁ * u)) := by
      rw [← intervalIntegral.integral_sub (hC v) (hD v)]
      refine intervalIntegral.integral_congr (fun u _ => ?_)
      simp only [smul_sub]
    rw [hp]
  -- Step 2: passing `inner n` through the outer integral
  have hout : inner ℝ n (∫ v in (-1 : ℝ)..1, sweepBump v •
        (∫ u in (-1 : ℝ)..1, sweepBump u •
          (Γ (s - δ₂ * v) (t + g - δ₁ * u) - Γ (s - δ₂ * v) (t - δ₁ * u))))
      = ∫ v in (-1 : ℝ)..1, sweepBump v * inner ℝ n
          (∫ u in (-1 : ℝ)..1, sweepBump u •
            (Γ (s - δ₂ * v) (t + g - δ₁ * u) - Γ (s - δ₂ * v) (t - δ₁ * u))) := by
    refine avgChordOf_inner_intervalIntegral_smul hb ?_ n
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume)
      (f := fun v u => sweepBump u •
        (Γ (s - δ₂ * v) (t + g - δ₁ * u) - Γ (s - δ₂ * v) (t - δ₁ * u))) ?_ (-1) 1
    show Continuous (fun p : ℝ × ℝ => sweepBump p.2 •
      (Γ (s - δ₂ * p.1) (t + g - δ₁ * p.2) - Γ (s - δ₂ * p.1) (t - δ₁ * p.2)))
    exact (hb.comp continuous_snd).smul
      ((hΓ.comp (by fun_prop : Continuous fun p : ℝ × ℝ => (s - δ₂ * p.1, t + g - δ₁ * p.2))).sub
        (hΓ.comp (by fun_prop : Continuous fun p : ℝ × ℝ => (s - δ₂ * p.1, t - δ₁ * p.2))))
  -- Step 3: passing `inner n` through the inner integral, pointwise in `v`
  have hin : ∀ v : ℝ, inner ℝ n
        (∫ u in (-1 : ℝ)..1, sweepBump u •
          (Γ (s - δ₂ * v) (t + g - δ₁ * u) - Γ (s - δ₂ * v) (t - δ₁ * u)))
      = ∫ u in (-1 : ℝ)..1, sweepBump u * inner ℝ n
          (Γ (s - δ₂ * v) (t + g - δ₁ * u) - Γ (s - δ₂ * v) (t - δ₁ * u)) := by
    intro v
    refine avgChordOf_inner_intervalIntegral_smul hb ?_ n
    exact (hknot1 v).sub (hknot2 v)
  calc avgChordOf Γ δ₁ δ₂ s n t g
      = ∫ v in (-1 : ℝ)..1, sweepBump v *
          (∫ u in (-1 : ℝ)..1, sweepBump u * inner ℝ n
            (Γ (s - δ₂ * v) (t + g - δ₁ * u) - Γ (s - δ₂ * v) (t - δ₁ * u))) := rfl
    _ = inner ℝ n (sweepFamOf Γ δ₁ δ₂ s (t + g) - sweepFamOf Γ δ₁ δ₂ s t) := by
        rw [hsub, hout]
        refine intervalIntegral.integral_congr (fun v _ => ?_)
        rw [hin v]

end Work.Drive
