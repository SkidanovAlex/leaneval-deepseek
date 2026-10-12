import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.ScatKernelChosen
import Submission.Work.SmallBoxA0.one_d_potential_crux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false

noncomputable section

namespace Work.SmallBoxA0

open MeasureTheory Metric
open scoped Topology

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

noncomputable def coulombProfile (G : ℝ³ → ℝ) : ℝ → ℝ :=
  fun r => ∫ s in Set.Ioi (0 : ℝ),
    (s ^ 2 * Submission.BoseGases.radialProfile G s) / max r s

lemma radial_coulomb_nonneg {G : EuclideanSpace ℝ (Fin 3) → ℝ} (hrad : BoseGases.IsRadial G) (hG : MeasureTheory.Integrable G) {R : ℝ} (hsupp : tsupport G ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) : 0 ≤ ∫ x : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3), G x * G y * (‖x - y‖ : ℝ)⁻¹ := by
  rcases le_or_gt R 0 with hRle | hRpos
  · have hball : Metric.ball (0 : ℝ³) R = ∅ := ball_eq_empty.mpr hRle
    have hzero : ∀ x : ℝ³, G x = 0 := by
      intro x
      by_contra hx
      have hx' : x ∈ tsupport G := subset_tsupport _ (Function.mem_support.mpr hx)
      rw [hball] at hsupp
      exact hsupp hx'
    simp [hzero]
  · set p : ℝ → ℝ := Submission.BoseGases.radialProfile G with hp_def
    have hGx : ∀ x : ℝ³, G x = p ‖x‖ := fun x => Submission.BoseGases.radial_eq_profile hrad x
    have hgsupp : ∀ y : ℝ³, R ≤ ‖y‖ → G y = 0 := by
      intro y hy
      by_contra h0
      have hy' : y ∈ tsupport G := subset_tsupport _ (Function.mem_support.mpr h0)
      have hlt : ‖y‖ < R := by
        have := hsupp hy'
        simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using this
      linarith
    have hp0 : ∀ r : ℝ, R ≤ r → p r = 0 := by
      intro r hr
      have h1 : p r = G (r • Submission.BoseGases.radU0) := rfl
      rw [h1]
      apply hgsupp
      rw [Submission.BoseGases.norm_smul_radU0, abs_of_nonneg (le_trans (le_of_lt hRpos) hr)]
      exact hr
    have hp : IntegrableOn (fun r : ℝ => r ^ 2 * p r) (Set.Ioo (0 : ℝ) R) := by
      have hball : IntegrableOn (fun x : ℝ³ => p ‖x‖) (Metric.ball (0 : ℝ³) R) := by
        have heq : (fun x : ℝ³ => p ‖x‖) = fun x => G x := funext fun x => (hGx x).symm
        rw [heq]
        exact hG.integrableOn
      exact (Submission.BoseGases.integrable_radial_ball_r3 (f := p) R).mp hball
    set Φ : ℝ → ℝ := coulombProfile G with hΦ_def
    have hpoint : (fun x : ℝ³ => ∫ y : ℝ³, G x * G y * (‖x - y‖ : ℝ)⁻¹)
        =ᵐ[volume] (fun x : ℝ³ => 4 * Real.pi * (p ‖x‖ * Φ ‖x‖)) := by
      have hne : ∀ᵐ x : ℝ³ ∂volume, x ≠ 0 := by
        rw [MeasureTheory.ae_iff]
        simp
      filter_upwards [hne] with x hx
      have hsplit := Submission.BoseGases.newton_potential_shell_integral (g := G) (R := R)
        hRpos hrad hgsupp hG x hx
      have hpull : (∫ y : ℝ³, G x * G y * (‖x - y‖ : ℝ)⁻¹)
          = G x * (∫ y : ℝ³, G y * (‖x - y‖ : ℝ)⁻¹) := by
        rw [← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
      rw [hpull, hsplit]
      simp only [hΦ_def, coulombProfile, hp_def, hGx x]
      ring
    have hI3 : (∫ x : ℝ³, ∫ y : ℝ³, G x * G y * (‖x - y‖ : ℝ)⁻¹)
        = ∫ x : ℝ³, 4 * Real.pi * (p ‖x‖ * Φ ‖x‖) := integral_congr_ae hpoint
    have hI4 : (∫ x : ℝ³, 4 * Real.pi * (p ‖x‖ * Φ ‖x‖))
        = 4 * Real.pi * ∫ x : ℝ³, (p ‖x‖ * Φ ‖x‖) := integral_const_mul _ _
    have hI5 : (∫ x : ℝ³, (p ‖x‖ * Φ ‖x‖))
        = 4 * Real.pi * ∫ r in Set.Ioi (0 : ℝ), r ^ 2 * (p r * Φ r) :=
      Submission.BoseGases.integral_fun_norm_r3 (g := fun r => p r * Φ r)
    have hI1 : (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * (p r * Φ r))
        = ∫ r in Set.Ioi (0 : ℝ), r ^ 2 * p r * Φ r := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r _
      ring
    have hI2 : (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * p r * Φ r)
        = ∫ r in Set.Ioi (0 : ℝ), r ^ 2 * p r *
            (∫ s in Set.Ioi (0 : ℝ), (s ^ 2 * p s) / max r s) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r _
      simp only [hΦ_def, coulombProfile, hp_def]
    rw [hI3, hI4, hI5, hI1, hI2]
    rw [show 4 * Real.pi * (4 * Real.pi * ∫ r in Set.Ioi (0 : ℝ), r ^ 2 * p r *
          (∫ s in Set.Ioi (0 : ℝ), (s ^ 2 * p s) / max r s))
        = 16 * Real.pi ^ 2 * (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * p r *
          (∫ s in Set.Ioi (0 : ℝ), (s ^ 2 * p s) / max r s)) from by ring]
    by_cases hInt : IntegrableOn (fun r : ℝ => r ^ 2 * p r *
        (∫ s in Set.Ioi (0 : ℝ), (s ^ 2 * p s) / max r s)) (Set.Ioi (0 : ℝ))
    · have h := one_d_potential_crux hRpos p hp hp0 hInt
      exact mul_nonneg (by positivity) h
    · have hzero : (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * p r *
          (∫ s in Set.Ioi (0 : ℝ), (s ^ 2 * p s) / max r s)) = 0 :=
        MeasureTheory.integral_undef hInt
      rw [hzero]
      ring_nf
      positivity

end Work.SmallBoxA0
