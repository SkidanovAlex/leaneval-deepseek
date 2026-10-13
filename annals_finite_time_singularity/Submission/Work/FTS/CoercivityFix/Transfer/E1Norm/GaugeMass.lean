/-
# `E1Norm/GaugeMass` — the angular mass of the gauge profile `Γ(θ)·(sin²2θ + α)`

The product separation lemma `E1Norm.angRad_HkSq_le` bounds the mixed `D_θ`-slots of a product
`a(θ)·r(z)` by `B1²·M`, where `M` bounds the angular mass
`∫_θ G(θ)²·sin(2θ)^{-γ} dθ` of the gauge profile `G` in terms of which the angular iterates of
`a` are estimated.  For the transfer defect `E1 α f = (D_θΓ)·radA α f` the natural gauge is

  `G(θ) = Γ(θ)·(sin²(2θ) + α)`,

because `D_θ^i (D_θΓ) = (2α/3)·Aang_i(cos²θ)·Γ` with `|Aang_i| ≤ 10⁷(α + sin²2θ)`
(`Construction.H4N_GammaTerm_Lop_bound`).

This file proves that the angular mass of that gauge is **bounded by an `α`-independent
constant** (here `1000`): the extra factor `sin²(2θ)` in the gauge kills the singularity of
`sin(2θ)^{-γ}` at the endpoints, leaving `∫ s^{2α/3-γ}` as the only singular piece, whose
`1/α`-blow-up is compensated by the `α²` in the gauge's square.  Concretely, on `0 < θ < π/2`

  `Γ(θ)²(sin²2θ + α)²·s^{-γ} ≤ 2·s^{4+2α/3-γ} + 2α²·s^{2α/3-γ}`,

the first term is bounded by `1` and the second integrates to at most `3000α/17`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.AngGam
import Submission.Work.FTS.Nonlinear.RadialProd.radial_prod
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E1Norm

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-- The gauge integrand is continuous on the open interval (every factor is: `Γ²` is a real
power of the positive function `sin θ cos²θ`, `(sin²2θ + α)²` is a polynomial, and
`sin(2θ)^{-γ}` is a real power of the positive `sin(2θ)`). -/
private theorem continuousOn_gauge_integrand (α : ℝ) :
    ContinuousOn (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2 * ((Real.sin (2 * θ)) ^ 2 + α) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) (Set.Ioo (0 : ℝ) (π / 2)) := by
  have hbase : ContinuousOn (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) (Set.Ioo (0 : ℝ) (π / 2)) :=
    (Real.continuous_sin.mul (Real.continuous_cos.pow 2)).continuousOn
  have hΓ : ContinuousOn (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3))
      (Set.Ioo (0 : ℝ) (π / 2)) :=
    hbase.rpow_const (fun θ hθ => Or.inl (by
      have h1 : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
      have h2 : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
      positivity))
  have hΓ2 : ContinuousOn (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2) (Set.Ioo (0 : ℝ) (π / 2)) := by
    refine (hΓ.mul hΓ).congr (fun θ _ => ?_)
    simp only [Pi.mul_apply]
    rw [show Work.Spaces.Gam α θ = (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3) from rfl, pow_two]
  have hpoly : ContinuousOn (fun θ : ℝ => ((Real.sin (2 * θ)) ^ 2 + α) ^ 2)
      (Set.Ioo (0 : ℝ) (π / 2)) :=
    (by fun_prop : Continuous fun θ : ℝ => ((Real.sin (2 * θ)) ^ 2 + α) ^ 2).continuousOn
  have hsm : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      (Set.Ioo (0 : ℝ) (π / 2)) := by
    have hsin2 : Continuous fun θ : ℝ => Real.sin (2 * θ) :=
      Real.continuous_sin.comp (by fun_prop)
    refine hsin2.continuousOn.rpow_const (fun θ hθ => Or.inl ?_)
    have h1 : (0 : ℝ) < 2 * θ := by linarith [hθ.1]
    have h2 : 2 * θ < Real.pi := by linarith [hθ.2, Real.pi_pos]
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 h2)
  exact (hΓ2.mul hpoly).mul hsm

/-- The pointwise domination of the gauge integrand by the two explicit profile pieces. -/
theorem gauge_pt (α θ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (Work.Spaces.Gam α θ) ^ 2 * ((Real.sin (2 * θ)) ^ 2 + α) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ 2 * (Real.sin (2 * θ)) ^ (4 + 2 * α / 3 - Work.Spaces.gam α)
        + 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hsnn : (0 : ℝ) ≤ Real.sin (2 * θ) := le_of_lt hs
  have hGam : (Work.Spaces.Gam α θ) ^ 2 ≤ (Real.sin (2 * θ)) ^ (2 * α / 3) := by
    rw [Work.FTS.CoercivityFix.Transfer.E1Parts.Gam_sq_eq α θ hθ]
    refine Real.rpow_le_rpow ?_ (Work.FTS.CoercivityFix.Transfer.E1Parts.sin_cos_sq_le_sin_two θ hθ)
      (by linarith)
    have h1 : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have h2 : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    positivity
  have hpoly : ((Real.sin (2 * θ)) ^ 2 + α) ^ 2
      ≤ 2 * (Real.sin (2 * θ)) ^ 4 + 2 * α ^ 2 := by
    nlinarith [sq_nonneg ((Real.sin (2 * θ)) ^ 2 - α)]
  have hprod : (Work.Spaces.Gam α θ) ^ 2 * ((Real.sin (2 * θ)) ^ 2 + α) ^ 2
      ≤ (Real.sin (2 * θ)) ^ (2 * α / 3) * (2 * (Real.sin (2 * θ)) ^ 4 + 2 * α ^ 2) :=
    mul_le_mul hGam hpoly (sq_nonneg _) (Real.rpow_nonneg hsnn _)
  have hsmnn : (0 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hsnn _
  have h1 : (Work.Spaces.Gam α θ) ^ 2 * ((Real.sin (2 * θ)) ^ 2 + α) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ (Real.sin (2 * θ)) ^ (2 * α / 3)
        * (2 * (Real.sin (2 * θ)) ^ 4 + 2 * α ^ 2) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    mul_le_mul_of_nonneg_right hprod hsmnn
  have hA : (Real.sin (2 * θ)) ^ (2 * α / 3) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      = (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) := by
    rw [← Real.rpow_add hs]; ring_nf
  have h4 : (Real.sin (2 * θ)) ^ 4 = (Real.sin (2 * θ)) ^ (4 : ℝ) :=
    (Real.rpow_natCast _ 4).symm
  have hB : (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) * (Real.sin (2 * θ)) ^ (4 : ℝ)
      = (Real.sin (2 * θ)) ^ (4 + 2 * α / 3 - Work.Spaces.gam α) := by
    rw [← Real.rpow_add hs]; ring_nf
  refine le_trans h1 (le_of_eq ?_)
  calc (Real.sin (2 * θ)) ^ (2 * α / 3) * (2 * (Real.sin (2 * θ)) ^ 4 + 2 * α ^ 2)
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      = 2 * ((Real.sin (2 * θ)) ^ (2 * α / 3) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Real.sin (2 * θ)) ^ 4)
        + 2 * α ^ 2 * ((Real.sin (2 * θ)) ^ (2 * α / 3)
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
    _ = 2 * ((Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) * (Real.sin (2 * θ)) ^ 4)
        + 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) := by rw [hA]
    _ = 2 * ((Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) * (Real.sin (2 * θ)) ^ (4 : ℝ))
        + 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) := by rw [h4]
    _ = 2 * (Real.sin (2 * θ)) ^ (4 + 2 * α / 3 - Work.Spaces.gam α)
        + 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) := by rw [hB]

/-- **The angular mass of the gauge profile is bounded by an `α`-independent constant.**  For
`0 < α ≤ 1` the integrand `Γ(θ)²(sin²2θ + α)²·sin(2θ)^{-γ}` is integrable on `Iθ` and its
integral is at most `1000`. -/
theorem gauge_mass (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2
        * ((Real.sin (2 * θ)) ^ 2 + α) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ) ^ 2 * ((Real.sin (2 * θ)) ^ 2 + α) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) ≤ 1000 := by
  have hIoo : Set.Ioo (0 : ℝ) (π / 2) =ᵐ[volume] Work.Spaces.Iθ := by
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) from rfl]
    exact MeasureTheory.Ioo_ae_eq_Icc
  have hsin : ∀ θ ∈ Work.Spaces.Iθ, (0 : ℝ) ≤ Real.sin (2 * θ) :=
    fun θ hθ => Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
  -- ## integrability of the two profile pieces
  have hp1 : -1 < 2 * α / 3 - Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hp2 : 2 * α / 3 - Work.Spaces.gam α ≤ 0 := by rw [Work.Spaces.gam]; linarith
  obtain ⟨hsm_int, hsm_bd⟩ := Work.Spaces.sin_two_rpow (2 * α / 3 - Work.Spaces.gam α) hp1 hp2
  have hq0 : (0 : ℝ) ≤ 4 + 2 * α / 3 - Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hq_cont : Continuous fun θ : ℝ => (Real.sin (2 * θ)) ^ (4 + 2 * α / 3 - Work.Spaces.gam α) :=
    (Real.continuous_rpow_const hq0).comp
      (Real.continuous_sin.comp (by fun_prop))
  have hq_int : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (4 + 2 * α / 3 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono'
      (MeasureTheory.integrableOn_const (μ := volume) (s := Work.Spaces.Iθ) (C := (1 : ℝ)) ?_)
      hq_cont.aestronglyMeasurable ?_
    · rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      have hs0 : (0 : ℝ) ≤ Real.sin (2 * θ) :=
        Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hs0 _)]
      exact Real.rpow_le_one hs0 (Real.sin_le_one _) hq0
  have hDint : MeasureTheory.IntegrableOn (fun θ : ℝ =>
      2 * (Real.sin (2 * θ)) ^ (4 + 2 * α / 3 - Work.Spaces.gam α)
        + 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)) Work.Spaces.Iθ :=
    (hq_int.const_mul 2).add (hsm_int.const_mul (2 * α ^ 2))
  -- ## the bound on the integral of the profile
  have hone := Work.Spaces.sin_two_rpow 0 (by norm_num) (le_refl 0)
  have hq_bd : (∫ θ in Work.Spaces.Iθ,
      (Real.sin (2 * θ)) ^ (4 + 2 * α / 3 - Work.Spaces.gam α)) ≤ 100 := by
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => Real.rpow_nonneg (hsin θ hθ) _))
      hone.1
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => by
        have h1 : (Real.sin (2 * θ)) ^ (4 + 2 * α / 3 - Work.Spaces.gam α) ≤ 1 :=
          Real.rpow_le_one (hsin θ hθ) (Real.sin_le_one _) hq0
        simpa using h1))
    have hone' : (∫ θ in Set.Icc (0 : ℝ) (π / 2), (Real.sin (2 * θ)) ^ (0 : ℝ)) ≤ 100 := by
      have h := hone.2
      have h100 : (100 : ℝ) / (0 + 1) = 100 := by norm_num
      rw [h100] at h
      simpa only [Work.Spaces.Iθ] using h
    exact le_trans hmono hone'
  have hsm_bd' : (∫ θ in Work.Spaces.Iθ,
      (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)) ≤ 3000 / (17 * α) := by
    have h17 : 2 * α / 3 - Work.Spaces.gam α + 1 = 17 * α / 30 := by
      rw [Work.Spaces.gam]; ring
    refine le_trans hsm_bd ?_
    rw [h17]
    exact le_of_eq (by field_simp; ring)
  have hDbd : (∫ θ in Work.Spaces.Iθ,
      2 * (Real.sin (2 * θ)) ^ (4 + 2 * α / 3 - Work.Spaces.gam α)
        + 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)) ≤ 1000 := by
    rw [MeasureTheory.integral_add (hq_int.const_mul 2) (hsm_int.const_mul (2 * α ^ 2)),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    have h3a : 2 * (∫ θ in Work.Spaces.Iθ,
        (Real.sin (2 * θ)) ^ (4 + 2 * α / 3 - Work.Spaces.gam α)) ≤ 2 * 100 :=
      mul_le_mul_of_nonneg_left hq_bd (by norm_num)
    have h3b : 2 * α ^ 2 * (∫ θ in Work.Spaces.Iθ,
        (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)) ≤ 2 * α ^ 2 * (3000 / (17 * α)) :=
      mul_le_mul_of_nonneg_left hsm_bd' (by positivity)
    have h2 : 2 * α ^ 2 * (3000 / (17 * α)) ≤ 400 := by
      rw [show 2 * α ^ 2 * (3000 / (17 * α)) = 6000 * α / 17 by field_simp; ring]
      nlinarith [hα1]
    linarith [h3a, h3b, h2]
  -- ## the a.e. pointwise bound and the measurability
  have hpt : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.Gam α θ) ^ 2 * ((Real.sin (2 * θ)) ^ 2 + α) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        ≤ 2 * (Real.sin (2 * θ)) ^ (4 + 2 * α / 3 - Work.Spaces.gam α)
          + 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) := by
    have h1 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2))),
        (Work.Spaces.Gam α θ) ^ 2 * ((Real.sin (2 * θ)) ^ 2 + α) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          ≤ 2 * (Real.sin (2 * θ)) ^ (4 + 2 * α / 3 - Work.Spaces.gam α)
            + 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) :=
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
        (fun θ hθ => gauge_pt α θ hα hα1 hθ)
    rwa [MeasureTheory.Measure.restrict_congr_set hIoo] at h1
  have haesm : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2
      * ((Real.sin (2 * θ)) ^ 2 + α) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h1 : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2
        * ((Real.sin (2 * θ)) ^ 2 + α) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) :=
      (continuousOn_gauge_integrand α).aestronglyMeasurable measurableSet_Ioo
    rwa [MeasureTheory.Measure.restrict_congr_set hIoo] at h1
  have hpt_norm : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖(Work.Spaces.Gam α θ) ^ 2 * ((Real.sin (2 * θ)) ^ 2 + α) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))‖
        ≤ 2 * (Real.sin (2 * θ)) ^ (4 + 2 * α / 3 - Work.Spaces.gam α)
          + 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) := by
    filter_upwards [hpt, MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ h1 h2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Real.rpow_nonneg (hsin θ h2) _))]
    exact h1
  refine ⟨MeasureTheory.Integrable.mono' hDint haesm hpt_norm, ?_⟩
  refine le_trans (MeasureTheory.integral_mono_of_nonneg
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
      mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (Real.rpow_nonneg (hsin θ hθ) _)))
    hDint hpt) hDbd

end Work.FTS.CoercivityFix.Transfer.E1Norm
