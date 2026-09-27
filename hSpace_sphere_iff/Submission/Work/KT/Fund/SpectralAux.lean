import Mathlib

/-!
# `Work.KT.Fund.SpectralAux` — the circle-integral calculus of the spectral splitting

This file contains (i) the elementary calculus of circle integrals used in the proof of the
spectral splitting `Work.KT.Fund.spectral_split`, and (ii) the definitions of the elements that
occur in that proof, in the abstract setting of a complex Banach algebra `A`:

* `Res b z = (z • 1 - b)⁻¹` — the resolvent of `b`;
* `CircA b ρ = ∮_{|z|=ρ} Res b z` and `CircB b ρ = ∮_{|z|=1} Res b z` — the two circle integrals;
* `Proj b ρ = (2πi)⁻¹ • CircA b ρ` — the "inside" spectral projection;
* `ProjB b ρ`, `Out b ρ` — its avatar on the unit circle, and the "outside inverse"
  `Out b ρ = -(2πi)⁻¹ ∮_{|z|=ρ} z⁻¹ • Res b z`.

The main theorems about these elements (proved in the files `spectral_*`) are

* `b * Out = 1 - Proj` and `Out * b = 1 - Proj`,
* `b * Proj = Proj * b`,
* `Proj = ProjB` (deformation invariance of the contour integral),
* `CircA * CircB = (2πi) • CircA` (the two-circle computation, via Fubini for circle integrals),
* `Proj * Proj = Proj`,
* `IsUnit (z • 1 + t • (Proj * b))` for `‖z‖ = 1`, `t ∈ [0,1]`,
* `IsUnit ((1 - Proj) * b + Proj)`.

The standing hypothesis is that the resolvent exists on the annulus `ρ ≤ ‖z‖ ≤ 1`.
-/

namespace Work.KT.Fund

open Matrix MeasureTheory intervalIntegral
open scoped Topology Interval

noncomputable section

section Aux

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- Pulling a constant element of `A` out of a circle integral (on the left). -/
theorem circleIntegral_const_mul (a : A) (f : ℂ → A) (c : ℂ) (R : ℝ)
    (hf : CircleIntegrable f c R) :
    (∮ z in C(c, R), a * f z) = a * ∮ z in C(c, R), f z := by
  have h1 : (fun θ : ℝ => deriv (circleMap c R) θ • (a * f (circleMap c R θ)))
      = fun θ : ℝ => a * (deriv (circleMap c R) θ • f (circleMap c R θ)) := by
    funext θ
    rw [mul_smul_comm]
  have h2 : Integrable (fun θ : ℝ => deriv (circleMap c R) θ • f (circleMap c R θ))
      (volume.restrict (Set.Ioc 0 (2 * Real.pi))) :=
    hf.out.1
  have h3 : (∫ θ in (0:ℝ)..(2 * Real.pi), a * (deriv (circleMap c R) θ • f (circleMap c R θ)))
      = a * ∫ θ in (0:ℝ)..(2 * Real.pi), deriv (circleMap c R) θ • f (circleMap c R θ) := by
    rw [intervalIntegral.integral_of_le Real.two_pi_pos.le,
      intervalIntegral.integral_of_le Real.two_pi_pos.le]
    exact integral_const_mul_of_integrable h2
  rw [circleIntegral, circleIntegral, h1]
  exact h3

/-- Pulling a constant element of `A` out of a circle integral (on the right). -/
theorem circleIntegral_mul_const (a : A) (f : ℂ → A) (c : ℂ) (R : ℝ)
    (hf : CircleIntegrable f c R) :
    (∮ z in C(c, R), f z * a) = (∮ z in C(c, R), f z) * a := by
  have h1 : (fun θ : ℝ => deriv (circleMap c R) θ • (f (circleMap c R θ) * a))
      = fun θ : ℝ => (deriv (circleMap c R) θ • f (circleMap c R θ)) * a := by
    funext θ
    rw [smul_mul_assoc]
  have h2 : Integrable (fun θ : ℝ => deriv (circleMap c R) θ • f (circleMap c R θ))
      (volume.restrict (Set.Ioc 0 (2 * Real.pi))) :=
    hf.out.1
  have h3 : (∫ θ in (0:ℝ)..(2 * Real.pi), (deriv (circleMap c R) θ • f (circleMap c R θ)) * a)
      = (∫ θ in (0:ℝ)..(2 * Real.pi), deriv (circleMap c R) θ • f (circleMap c R θ)) * a := by
    rw [intervalIntegral.integral_of_le Real.two_pi_pos.le,
      intervalIntegral.integral_of_le Real.two_pi_pos.le]
    exact integral_mul_const_of_integrable h2
  rw [circleIntegral, circleIntegral, h1]
  exact h3

/-- Fubini for iterated circle integrals. -/
theorem circleIntegral_swap (F : ℂ → ℂ → A) {ρ σ : ℝ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hF : ContinuousOn (Function.uncurry F) (Metric.sphere (0:ℂ) ρ ×ˢ Metric.sphere (0:ℂ) σ)) :
    (∮ w in C(0, ρ), ∮ w' in C(0, σ), F w w') = ∮ w' in C(0, σ), ∮ w in C(0, ρ), F w w' := by
  set G : ℝ → ℝ → A := fun θ ψ =>
    (deriv (circleMap 0 ρ) θ) • ((deriv (circleMap 0 σ) ψ) • (F (circleMap 0 ρ θ) (circleMap 0 σ ψ)))
    with hG
  have hd1 : ContinuousOn (fun p : ℝ × ℝ => deriv (circleMap 0 ρ) p.1)
      (Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 (2 * Real.pi)) := by
    rw [show (fun p : ℝ × ℝ => deriv (circleMap 0 ρ) p.1)
        = fun p : ℝ × ℝ => circleMap 0 ρ p.1 * Complex.I from
      funext fun p => deriv_circleMap 0 ρ p.1]
    exact (((continuous_circleMap 0 ρ).comp continuous_fst).mul continuous_const).continuousOn
  have hd2 : ContinuousOn (fun p : ℝ × ℝ => deriv (circleMap 0 σ) p.2)
      (Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 (2 * Real.pi)) := by
    rw [show (fun p : ℝ × ℝ => deriv (circleMap 0 σ) p.2)
        = fun p : ℝ × ℝ => circleMap 0 σ p.2 * Complex.I from
      funext fun p => deriv_circleMap 0 σ p.2]
    exact (((continuous_circleMap 0 σ).comp continuous_snd).mul continuous_const).continuousOn
  have hGcont : ContinuousOn (Function.uncurry G) (Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 (2 * Real.pi)) := by
    rw [hG]
    have hmaps : Set.MapsTo (fun p : ℝ × ℝ => (circleMap 0 ρ p.1, circleMap 0 σ p.2))
        (Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 (2 * Real.pi))
        (Metric.sphere (0:ℂ) ρ ×ˢ Metric.sphere (0:ℂ) σ) := by
      rintro ⟨θ, ψ⟩ ⟨hθ, hψ⟩
      exact ⟨circleMap_mem_sphere 0 hρ θ, circleMap_mem_sphere 0 hσ ψ⟩
    have hcomp := hF.comp (by fun_prop) hmaps
    exact ContinuousOn.smul hd1 (ContinuousOn.smul hd2 hcomp)
  have hint : IntegrableOn (Function.uncurry G)
      (Ι (0:ℝ) (2 * Real.pi) ×ˢ Ι (0:ℝ) (2 * Real.pi)) volume := by
    have hset : (Ι (0:ℝ) (2 * Real.pi)) = Set.Ioc 0 (2 * Real.pi) := by
      simp [Set.uIoc, Real.two_pi_pos.le]
    have h1 : IntegrableOn (Function.uncurry G)
        (Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 (2 * Real.pi)) volume :=
      hGcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    rw [hset]
    exact h1.mono_set (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)
  have hswap := MeasureTheory.intervalIntegral_intervalIntegral_swap hint
  have hL : (∮ w in C(0, ρ), ∮ w' in C(0, σ), F w w')
      = ∫ θ in (0:ℝ)..(2 * Real.pi), ∫ ψ in (0:ℝ)..(2 * Real.pi), G θ ψ := by
    simp only [circleIntegral]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    rw [← intervalIntegral.integral_smul]
  have hR : (∮ w' in C(0, σ), ∮ w in C(0, ρ), F w w')
      = ∫ ψ in (0:ℝ)..(2 * Real.pi), ∫ θ in (0:ℝ)..(2 * Real.pi), G θ ψ := by
    simp only [circleIntegral]
    refine intervalIntegral.integral_congr fun ψ _ => ?_
    rw [← intervalIntegral.integral_smul]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    rw [hG, smul_comm]
  rw [hL, hR, hswap]

/-- Deformation invariance of the resolvent circle integral. -/
theorem circleIntegral_resolvent_eq (b : A) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (h : ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ R → IsUnit (z • 1 - b)) :
    (∮ z in C(0, R), Ring.inverse (z • 1 - b)) = ∮ z in C(0, r), Ring.inverse (z • 1 - b) ∧
    (∮ z in C(0, R), z⁻¹ • Ring.inverse (z • 1 - b)) =
      ∮ z in C(0, r), z⁻¹ • Ring.inverse (z • 1 - b) := by
  have hle_closedBall : ∀ z : ℂ, z ∈ Metric.closedBall (0:ℂ) R → ‖z‖ ≤ R :=
    fun z hz => by simpa [Metric.mem_closedBall, dist_zero_right] using hz
  have hge_not_ball : ∀ z : ℂ, z ∉ Metric.ball (0:ℂ) r → r ≤ ‖z‖ := by
    intro z hz
    by_contra hcon
    exact hz (by simpa [Metric.mem_ball, dist_zero_right] using not_le.mp hcon)
  have hge_not_closedBall : ∀ z : ℂ, z ∉ Metric.closedBall (0:ℂ) r → r ≤ ‖z‖ := by
    intro z hz
    by_contra hcon
    exact hz (by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_of_lt (not_le.mp hcon))
  have hle_ball : ∀ z : ℂ, z ∈ Metric.ball (0:ℂ) R → ‖z‖ ≤ R :=
    fun z hz => by
      have : ‖z‖ < R := by simpa [Metric.mem_ball, dist_zero_right] using hz
      exact le_of_lt this
  have hann : ∀ z ∈ (Metric.closedBall (0:ℂ) R \ Metric.ball (0:ℂ) r), IsUnit (z • 1 - b) :=
    fun z hz => h z (hge_not_ball z hz.2) (hle_closedBall z hz.1)
  have hunits : ContinuousOn Ring.inverse {x : A | IsUnit x} := by
    intro x hx
    simpa only [IsUnit.unit_spec hx] using (NormedRing.inverse_continuousAt hx.unit).continuousWithinAt
  have hlin : Continuous fun z : ℂ => z • (1 : A) - b :=
    (continuous_id.smul continuous_const).sub continuous_const
  have hres : ContinuousOn (fun z : ℂ => Ring.inverse (z • 1 - b))
      (Metric.closedBall (0:ℂ) R \ Metric.ball (0:ℂ) r) := by
    have := hunits.comp hlin.continuousOn (fun z hz => hann z hz)
    simpa [Function.comp_def] using this
  have hdiff : ∀ z ∈ (Metric.ball (0:ℂ) R \ Metric.closedBall (0:ℂ) r),
      DifferentiableAt ℂ (fun z : ℂ => Ring.inverse (z • 1 - b)) z := by
    intro z hz
    have hzr : r ≤ ‖z‖ := hge_not_closedBall z hz.2
    have hzR : ‖z‖ ≤ R := hle_ball z hz.1
    have hg : DifferentiableAt ℂ (fun y : ℂ => y • (1 : A) - b) z :=
      (((differentiableAt_id : DifferentiableAt ℂ (fun y : ℂ => y) z)).smul_const (1 : A)).sub_const b
    exact hg.inverse (h z hzr hzR)
  constructor
  · exact Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hrR
      Set.countable_empty hres (fun z hz => hdiff z hz.1)
  · have := Complex.circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable
      (c := 0) hr hrR (s := (∅ : Set ℂ)) Set.countable_empty hres (fun z hz => hdiff z hz.1)
    simpa using this

/-- The resolvent of `b`, as a function of the spectral parameter. -/
def Res (b : A) (z : ℂ) : A := Ring.inverse (z • 1 - b)

/-- The circle integral of the resolvent over `|z| = ρ`. -/
def CircA (b : A) (ρ : ℝ) : A := ∮ z in C(0, ρ), Res b z

/-- The circle integral of the resolvent over the unit circle. -/
def CircB (b : A) (ρ : ℝ) : A := ∮ z in C(0, 1), Res b z

/-- The "inside" spectral projection `(2πi)⁻¹ ∮_{|z|=ρ} (z - b)⁻¹ dz`. -/
def Proj (b : A) (ρ : ℝ) : A := (2 * Real.pi * Complex.I)⁻¹ • CircA b ρ

/-- The same projection computed on the unit circle. -/
def ProjB (b : A) (ρ : ℝ) : A := (2 * Real.pi * Complex.I)⁻¹ • CircB b ρ

/-- The "outside inverse" `-(2πi)⁻¹ ∮_{|z|=ρ} z⁻¹ (z - b)⁻¹ dz`. -/
def Out (b : A) (ρ : ℝ) : A := -((2 * Real.pi * Complex.I)⁻¹ • (∮ z in C(0, ρ), z⁻¹ • Res b z))

end Aux

end

end Work.KT.Fund
