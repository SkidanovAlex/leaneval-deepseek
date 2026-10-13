import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.thetaHardyRight

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.SixRoute

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option maxHeartbeats 2000000

/-! ## The main theorem -/

theorem thetaHardyA : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ f : ℝ → ℝ,
    ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)) →
    MeasureTheory.IntegrableOn (fun θ => (Real.sin (2 * θ) * deriv f θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ →
      (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 - α / 10)))
        ≤ C / α ^ 2 * (∫ θ in Work.Spaces.Iθ,
              (Real.sin (2 * θ) * deriv f θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          + C / α * (f (Real.pi / 4)) ^ 2 := by
  refine ⟨40000, by norm_num, fun α hα f hsm hint => ?_⟩
  obtain ⟨hα0, hα1⟩ := hα
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hqpos : (0 : ℝ) < Real.pi / 4 := by linarith
  have hqlt : Real.pi / 4 < Real.pi / 2 := by linarith
  have hhalf : (0 : ℝ) < Real.pi / 2 := by linarith
  have hβ0 : (0 : ℝ) < α / 10 := by linarith
  have hβ1 : α / 10 ≤ 1 := by linarith
  -- the pointwise identification of the two weight pairs
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      (Real.sin (2 * θ) * deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        = (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - α / 10) := by
    intro θ hθ
    have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
    rcases lt_or_eq_of_le hs with hslt | hseq
    · have hγ : Work.Spaces.gam α = 1 + α / 10 := rfl
      have hexp2 : (2 : ℝ) + (-(Work.Spaces.gam α)) = 1 - α / 10 := by rw [hγ]; ring
      have hpow : (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          = (Real.sin (2 * θ)) ^ (1 - α / 10) := by
        rw [← Real.rpow_two, ← Real.rpow_add hslt, hexp2]
      calc (Real.sin (2 * θ) * deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          = (deriv f θ) ^ 2
              * ((Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
            ring
        _ = (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - α / 10) := by rw [hpow]
    · have hgt : α / 10 < 1 := by linarith
      have h2 : -(Work.Spaces.gam α) ≠ 0 := by
        have hγ : Work.Spaces.gam α = 1 + α / 10 := rfl
        intro h; rw [hγ] at h; linarith
      have h3 : 1 - α / 10 ≠ 0 := by intro h; linarith
      have hs0 : Real.sin (2 * θ) = 0 := hseq.symm
      rw [hs0]
      simp only [mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), Real.zero_rpow h2,
        Real.zero_rpow h3, mul_zero]
  -- integrability of the RHS integrand over the two halves
  have hintIoc : IntegrableOn (fun θ => (Real.sin (2 * θ) * deriv f θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) (Set.Ioc (0 : ℝ) (Real.pi / 2)) :=
    hint.mono_set Set.Ioc_subset_Icc_self
  have hPhi : IntegrableOn (fun θ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - α / 10))
      (Set.Ioc (0 : ℝ) (Real.pi / 2)) :=
    hintIoc.congr_fun (fun θ hθ => hpt θ ⟨le_of_lt hθ.1, hθ.2⟩) measurableSet_Ioc
  have hPhiL : IntegrableOn (fun θ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - α / 10))
      (Set.Ioc (0 : ℝ) (Real.pi / 4)) :=
    hPhi.mono_set (fun x hx => ⟨hx.1, le_trans hx.2 (le_of_lt hqlt)⟩)
  have hPhiR : IntegrableOn (fun θ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - α / 10))
      (Set.Ioc (Real.pi / 4) (Real.pi / 2)) :=
    hPhi.mono_set (fun x hx => ⟨lt_trans hqpos hx.1, hx.2⟩)
  -- the two half estimates
  have hL := hardy_half_left_open (β := α / 10) hβ0 hβ1 hsm hPhiL
  have hR := hardy_half_right_open (β := α / 10) hβ0 hβ1 hsm hPhiR
  -- interval integrability of the left-hand integrand on each half
  have hFintL : IntervalIntegrable
      (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (α / 10 - 1)) volume 0 (Real.pi / 4) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hqpos.le).mpr hL.1
  have hFintR : IntervalIntegrable
      (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (α / 10 - 1)) volume (Real.pi / 4) (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hqlt.le).mpr hR.1
  -- the left-hand side, split at `π/4`
  have hexp : ∀ θ, (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 - α / 10))
      = (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (α / 10 - 1) := by
    intro θ; congr 1; ring
  have hLHS : (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 - α / 10)))
      = (∫ θ in Set.Ioc (0 : ℝ) (Real.pi / 4), (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (α / 10 - 1))
        + (∫ θ in Set.Ioc (Real.pi / 4) (Real.pi / 2),
            (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (α / 10 - 1)) := by
    have hcongr : (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 - α / 10)))
        = ∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (α / 10 - 1) :=
      setIntegral_congr_fun measurableSet_Icc (fun θ _ => hexp θ)
    rw [hcongr,
      show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl,
      MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le hhalf.le,
      ← intervalIntegral.integral_add_adjacent_intervals hFintL hFintR,
      intervalIntegral.integral_of_le hqpos.le, intervalIntegral.integral_of_le hqlt.le]
  -- the right-hand side, split at `π/4`
  have hRHS : (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ) * deriv f θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      = (∫ θ in Set.Ioc (0 : ℝ) (Real.pi / 4),
            (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - α / 10))
        + (∫ θ in Set.Ioc (Real.pi / 4) (Real.pi / 2),
            (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - α / 10)) := by
    have hcongr : (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ) * deriv f θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        = ∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - α / 10) :=
      setIntegral_congr_fun measurableSet_Icc (fun θ hθ => hpt θ hθ)
    rw [hcongr,
      show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl,
      MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le hhalf.le,
      ← intervalIntegral.integral_add_adjacent_intervals
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le hqpos.le).mpr hPhiL)
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le hqlt.le).mpr hPhiR),
      intervalIntegral.integral_of_le hqpos.le, intervalIntegral.integral_of_le hqlt.le]
  -- final arithmetic
  have hfq0 : (0 : ℝ) ≤ (f (Real.pi / 4)) ^ 2 := sq_nonneg _
  have hcoef1 : 4 / (α / 10) ^ 2 * (Real.pi / 4) ^ 2 ≤ 40000 / α ^ 2 := by
    have h1 : (Real.pi / 4) ^ 2 ≤ 4 := by nlinarith [Real.pi_le_four, Real.pi_pos]
    have : 4 / (α / 10) ^ 2 * (Real.pi / 4) ^ 2 ≤ 4 / (α / 10) ^ 2 * 4 :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h2 : 4 / (α / 10) ^ 2 * 4 = 1600 / α ^ 2 := by field_simp; ring
    rw [h2] at this
    exact le_trans this (by
      have : (0:ℝ) < α ^ 2 := by positivity
      rw [div_le_div_iff_of_pos_right this]; norm_num)
  have hcoef2 : Real.pi / (2 * (α / 10)) + Real.pi / (2 * (α / 10)) ≤ 40000 / α := by
    have h1 : Real.pi / (2 * (α / 10)) + Real.pi / (2 * (α / 10)) = 10 * Real.pi / α := by
      field_simp
      ring
    rw [h1, div_le_div_iff_of_pos_right hα0]
    nlinarith [Real.pi_pos, Real.pi_le_four]
  calc (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 - α / 10)))
      = (∫ θ in Set.Ioc (0 : ℝ) (Real.pi / 4), (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (α / 10 - 1))
        + (∫ θ in Set.Ioc (Real.pi / 4) (Real.pi / 2),
            (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (α / 10 - 1)) := hLHS
    _ ≤ 4 / (α / 10) ^ 2 * (Real.pi / 4) ^ 2
            * (∫ θ in Set.Ioc (0 : ℝ) (Real.pi / 4),
                (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - α / 10))
          + Real.pi / (2 * (α / 10)) * (f (Real.pi / 4)) ^ 2
        + (4 / (α / 10) ^ 2 * (Real.pi / 4) ^ 2
            * (∫ θ in Set.Ioc (Real.pi / 4) (Real.pi / 2),
                (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - α / 10))
          + Real.pi / (2 * (α / 10)) * (f (Real.pi / 4)) ^ 2) :=
        add_le_add hL.2 hR.2
    _ = 4 / (α / 10) ^ 2 * (Real.pi / 4) ^ 2
          * ((∫ θ in Set.Ioc (0 : ℝ) (Real.pi / 4),
                (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - α / 10))
            + (∫ θ in Set.Ioc (Real.pi / 4) (Real.pi / 2),
                (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - α / 10)))
        + (Real.pi / (2 * (α / 10)) + Real.pi / (2 * (α / 10))) * (f (Real.pi / 4)) ^ 2 := by
        ring
    _ = 4 / (α / 10) ^ 2 * (Real.pi / 4) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ) * deriv f θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        + (Real.pi / (2 * (α / 10)) + Real.pi / (2 * (α / 10))) * (f (Real.pi / 4)) ^ 2 := by
        rw [← hRHS]
    _ ≤ 40000 / α ^ 2 * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ) * deriv f θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          + 40000 / α * (f (Real.pi / 4)) ^ 2 := by
        have hnn : (0:ℝ) ≤ ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ) * deriv f θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
          refine MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => ?_)
          have hs := sin_two_nonneg_of_mem_Iθ hθ
          have hγ : 0 < Work.Spaces.gam α := by
            have : Work.Spaces.gam α = 1 + α / 10 := rfl
            rw [this]; linarith
          positivity
        have hb := mul_le_mul_of_nonneg_right hcoef2 hfq0
        have ha := mul_le_mul_of_nonneg_right hcoef1 hnn
        linarith [ha, hb]

end

end Work.FTS.StrongPersist.N6Trans.SixRoute
