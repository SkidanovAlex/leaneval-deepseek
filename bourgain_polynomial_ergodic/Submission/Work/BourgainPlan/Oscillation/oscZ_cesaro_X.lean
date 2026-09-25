import Mathlib
import Submission.Work.BourgainPlan.Oscillation.lacunary_defs
import Submission.Work.BourgainPlan.Oscillation.lacScale_error_tsum_le
import Submission.Work.BourgainPlan.Oscillation.Lacunary.oscZ_reflect
import Submission.Work.BourgainPlan.Oscillation.Lacunary.opF_cesaro_backward
import Submission.Work.BourgainPlan.Oscillation.Lacunary.cesaro_mult_oscZ_assembled
import Submission.Work.BourgainPlan.Oscillation.Lacunary.cesaro_family_oscZ_eq
import Submission.Work.BourgainPlan.Maximal.poly_dyadic_of_model
import Submission.Work.BourgainPlan.Maximal.shift_fourier_coeff_conj

namespace Work.BourgainPlan.Oscillation

open Finset MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- **The Weyl operator of `Polynomial.X` is the forward Cesàro average.**
`polyWeylOp X g s N x = N⁻¹ ∑_{n<N} g (x + n)`. -/
theorem polyWeylOp_X_eq (g : ℤ → ℂ) (s : Finset ℤ)
    (hs : ∀ n, n ∉ s → g n = 0) (N : ℕ) (x : ℤ) :
    polyWeylOp Polynomial.X g s N x
      = ((N : ℝ)⁻¹ : ℂ) * ∑ n ∈ Finset.range N, g (x + (n : ℤ)) := by
  have hmain := Work.BourgainPlan.Maximal.shift_fourier_coeff_conj
    Polynomial.X g s hs N x
  simp only [Polynomial.eval_X] at hmain
  unfold polyWeylOp
  refine Eq.trans ?_ hmain
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  simp only [Work.BourgainPlan.Maximal.conj_polyWeylKernel, Polynomial.eval_X]
  push_cast
  ring

theorem oscZ_cesaro_X (ρ : ℝ) (hρ : 1 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : ℕ) (k : ℕ → ℕ), StrictMono k →
      ∀ (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
        Work.BourgainPlan.Oscillation.oscZ (fun i x =>
            Work.BourgainPlan.Oscillation.polyWeylOp Polynomial.X g s
              (Work.BourgainPlan.Oscillation.lacScale ρ i) x) J k
          ≤ ENNReal.ofReal (C^2) * ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
  -- the analytic core: the block oscillation of the Cesaro multiplier family
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Work.BourgainPlan.Oscillation.Lacunary.cesaro_mult_oscZ_assembled ρ hρ
  refine ⟨C₀, hC₀pos, fun J k hk g s hs => ?_⟩
  classical
  set F : ℤ → ℂ := fun y => g (-y) with hF
  set s' : Finset ℤ := s.image (fun z : ℤ => -z) with hs'
  have hs'p : ∀ n, n ∉ s' → F n = 0 := by
    intro n hn
    by_contra hne
    have hmem : -n ∈ s := by
      by_contra hc
      exact hne (hs (-n) hc)
    exact hn (by rw [hs']; exact Finset.mem_image.mpr ⟨-n, hmem, by simp⟩)
  -- the same family, as an `opF`-integral
  set G : ℕ → ℤ → ℂ := fun i x => ∫ θ in (0 : ℝ)..1,
      (((Work.BourgainPlan.Oscillation.lacScale ρ i : ℂ))⁻¹ *
        ∑ n ∈ Finset.range (Work.BourgainPlan.Oscillation.lacScale ρ i),
          Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) * (θ : ℂ))))
        * (∑ j ∈ s', F j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ))))
        * Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ))) with hG
  -- Fourier inversion: `G` is the backward Cesaro average of `F`
  have hGback : G = fun i x => ((Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ)⁻¹ : ℂ) *
      ∑ n ∈ Finset.range (Work.BourgainPlan.Oscillation.lacScale ρ i), F (x - (n : ℤ)) := by
    funext i x
    simp only [hG]
    simpa only [mul_assoc] using Work.BourgainPlan.Oscillation.Lacunary.opF_cesaro_backward _
      (Work.BourgainPlan.Oscillation.one_le_lacScale ρ hρ.le i) F s' hs'p x
  -- the core is stated with the closed form `(e(Nθ)-1)/(e(θ)-1)` of the Cesaro multiplier;
  -- `G` uses the geometric-sum form.  The two agree a.e. on `(0,1)`, so the bounds coincide.
  have hcore : Work.BourgainPlan.Oscillation.oscZ G J k
      ≤ ENNReal.ofReal (C₀ ^ 2) *
          ∫⁻ x : ℤ, ‖F x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count := by
    rw [hG]
    -- the closed form and the geometric-sum form agree a.e. on `(0,1)`, so the core
    -- `cesaro_mult_oscZ` (closed form) transfers to `G` (geometric-sum form).
    refine le_trans (le_of_eq ?_) (hC₀ J k hk F s' hs'p)
    simpa only [mul_assoc] using
      (Work.BourgainPlan.Oscillation.Lacunary.cesaro_family_oscZ_eq ρ hρ J k F s' hs'p).symm
  -- the backward Cesaro family of `F` is the reflection of the forward family of `g`
  have hbackF : (fun i x => ((Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ)⁻¹ : ℂ) *
        ∑ n ∈ Finset.range (Work.BourgainPlan.Oscillation.lacScale ρ i), F (x - (n : ℤ)))
      = (fun i x => ((Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ)⁻¹ : ℂ) *
        ∑ n ∈ Finset.range (Work.BourgainPlan.Oscillation.lacScale ρ i), g ((-x) + (n : ℤ))) := by
    funext i x
    congr 1
    refine Finset.sum_congr rfl (fun n _ => ?_)
    simp only [hF]
    congr 1
    ring
  have hfwd : (fun i x => ((Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ)⁻¹ : ℂ) *
        ∑ n ∈ Finset.range (Work.BourgainPlan.Oscillation.lacScale ρ i), g ((-x) + (n : ℤ)))
      = (fun i y => Work.BourgainPlan.Oscillation.polyWeylOp Polynomial.X g s
          (Work.BourgainPlan.Oscillation.lacScale ρ i) (-y)) := by
    funext i y
    rw [polyWeylOp_X_eq g s hs]
  -- reflection invariance of `oscZ`
  have hrefl : Work.BourgainPlan.Oscillation.oscZ
        (fun i y => Work.BourgainPlan.Oscillation.polyWeylOp Polynomial.X g s
          (Work.BourgainPlan.Oscillation.lacScale ρ i) (-y)) J k
      = Work.BourgainPlan.Oscillation.oscZ (fun i y =>
          Work.BourgainPlan.Oscillation.polyWeylOp Polynomial.X g s
            (Work.BourgainPlan.Oscillation.lacScale ρ i) y) J k := by
    have h := Work.BourgainPlan.Oscillation.Lacunary.oscZ_reflect
      (fun i y => Work.BourgainPlan.Oscillation.polyWeylOp Polynomial.X g s
        (Work.BourgainPlan.Oscillation.lacScale ρ i) y) J k
    simpa using h
  -- the `ℓ²` mass of the reflected function
  have hmass : (∫⁻ x : ℤ, ‖F x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count)
      = ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count := by
    rw [hF]
    exact Work.BourgainPlan.Oscillation.Lacunary.lintegral_count_neg
      (fun x : ℤ => ‖g x‖ₑ ^ (2 : ℝ))
  calc Work.BourgainPlan.Oscillation.oscZ (fun i x =>
          Work.BourgainPlan.Oscillation.polyWeylOp Polynomial.X g s
            (Work.BourgainPlan.Oscillation.lacScale ρ i) x) J k
      = Work.BourgainPlan.Oscillation.oscZ
          (fun i y => Work.BourgainPlan.Oscillation.polyWeylOp Polynomial.X g s
            (Work.BourgainPlan.Oscillation.lacScale ρ i) (-y)) J k := hrefl.symm
    _ = Work.BourgainPlan.Oscillation.oscZ
          (fun i x => ((Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ)⁻¹ : ℂ) *
            ∑ n ∈ Finset.range (Work.BourgainPlan.Oscillation.lacScale ρ i),
              g ((-x) + (n : ℤ))) J k := by rw [← hfwd]
    _ = Work.BourgainPlan.Oscillation.oscZ
          (fun i x => ((Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ)⁻¹ : ℂ) *
            ∑ n ∈ Finset.range (Work.BourgainPlan.Oscillation.lacScale ρ i),
              F (x - (n : ℤ))) J k := by rw [← hbackF]
    _ = Work.BourgainPlan.Oscillation.oscZ G J k := by rw [hGback]
    _ ≤ ENNReal.ofReal (C₀ ^ 2) *
          ∫⁻ x : ℤ, ‖F x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count := hcore
    _ = ENNReal.ofReal (C₀ ^ 2) *
          ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count := by rw [hmass]

end

end Work.BourgainPlan.Oscillation
