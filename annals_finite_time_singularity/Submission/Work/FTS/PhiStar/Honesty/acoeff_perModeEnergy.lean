import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Honesty.radGreen_modeEnergy_of_o
import Submission.Work.FTS.PhiStar.Honesty.integrableOn_acoeff_sq_w_sq_meas
import Submission.Work.FTS.PhiStar.Honesty.aemeasurable_cmode_clamp
import Submission.Work.FTS.PhiStar.Honesty.cmode_sq_le_slice
import Submission.Work.FTS.PhiStar.Honesty.integrableOn_sliceMass_div_z4_of_HkMem
import Submission.Work.FTS.PhiStar.Honesty.integrableOn_sliceMass_Ioi_one_of_HkMem
import Submission.Work.FTS.PhiStar.Honesty.integrableOn_sq_sEta_of_HkMem
import Submission.Work.FTS.PhiStar.Honesty.eNorm_mul_cmode_sq_le_sliceMass
import Submission.Work.EllipticEst.ModalSolution.cmode_bessel

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set Filter

/-! ## The per-mode energy inequality in weighted `L²` form

The target is the *normalised* form of the sharp per-mode weighted energy bound
`radGreen_modeEnergy_of_o`:

  `μ_m² ∫_0^∞ (radGreen α m c)² w² ≤ ∫_0^∞ c² w²`,   `μ_m = λ_m − 3α² − 3α(5+α)/2`,

at `c = cmode m F` (clamped outside `(0,∞)`, which is all that `radGreen` sees).  Taking square
roots and using `√(eNorm m) ≥ 1` on the right-hand side turns that into

  `μ_m · √(∫_z (acoeff α m F)² w²) ≤ √(∫_z (√(eNorm m) · cmode m F)² w²)`,

which is exactly the requested statement.  All the analytic hypotheses of
`radGreen_modeEnergy_of_o` (`AEMeasurable c`, `∫_0^1 c²/t⁴ < ∞`, `∫_1^∞ c² < ∞`, the `o(t^{3/2})`
rate) are supplied from `SmoothOpen F` / `HkMem α 0 F` by the imported `Honesty` bricks. -/

/-! ### Two elementary auxiliary lemmas -/

/-- For `z > 0` the value `radGreen α m c z` depends only on the values of `c` on the open
half-line `(0,∞)`: both integrals in `radGreen` are taken over subsets of `(0,∞)`. -/
private lemma radGreen_congr_Ioi {α : ℝ} {m : ℕ} {c₁ c₂ : ℝ → ℝ}
    (h : ∀ t : ℝ, 0 < t → c₁ t = c₂ t) {z : ℝ} (hz : 0 < z) :
    Work.FTS.PhiStar.Radial.radGreen α m c₁ z
      = Work.FTS.PhiStar.Radial.radGreen α m c₂ z := by
  have h1 : (∫ t in (0 : ℝ)..z, c₁ t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      = ∫ t in (0 : ℝ)..z, c₂ t * t ^ ((2 * (m : ℝ) + 5) / α - 1) := by
    rw [intervalIntegral.integral_of_le hz.le, intervalIntegral.integral_of_le hz.le]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      (fun t ht => by rw [h t ht.1])
  have h2 : (∫ t in Set.Ioi z, c₁ t * t ^ (-(2 * (m : ℝ) / α) - 1))
      = ∫ t in Set.Ioi z, c₂ t * t ^ (-(2 * (m : ℝ) / α) - 1) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun t ht => by rw [h t (lt_trans hz ht)])
  rw [Work.FTS.PhiStar.Radial.radGreen, Work.FTS.PhiStar.Radial.radGreen, h1, h2]

/-- The arithmetic transfer: `μ² A ≤ B`, `μ > 0`, `B ≥ 0`, `1 ≤ e` give `μ √A ≤ √(e·B)`. -/
private lemma sqrt_mu_bound {μ A B e : ℝ} (hμ : 0 < μ) (hB : 0 ≤ B) (he : 1 ≤ e)
    (h : μ ^ 2 * A ≤ B) : μ * Real.sqrt A ≤ Real.sqrt (e * B) := by
  have h1 : μ * Real.sqrt A ≤ Real.sqrt B := by
    have h2 := Real.sqrt_le_sqrt h
    rwa [Real.sqrt_mul (sq_nonneg μ), Real.sqrt_sq hμ.le] at h2
  have h3 : Real.sqrt B ≤ Real.sqrt (e * B) := Real.sqrt_le_sqrt (by nlinarith)
  exact le_trans h1 h3

theorem acoeff_perModeEnergy {α : ℝ} {F : ℝ → ℝ → ℝ} (m : ℕ)
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF : Work.Spaces.HkMem α 0 F)
    (heNorm : 1 ≤ Work.EllipticEst.ModalSolution.eNorm m)
    (hvy : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t ≤ δ →
      |Work.FTS.PhiStar.Series.cmode m F t| ≤ ε * t ^ ((3 : ℝ) / 2)) :
    (Work.FTS.PhiStar.Radial.lamR m - 3 * α ^ 2 - 3 * α * (5 + α) / 2)
        * Real.sqrt (∫ z in Work.Spaces.Iz,
            (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ Real.sqrt (∫ z in Work.Spaces.Iz,
          (Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)
            * Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
  classical
  -- the clamped mode coefficient: `radGreen` (and every weighted integral of it) only sees
  -- `cmode m F` on `(0,∞)`
  set cl : ℝ → ℝ := fun z => if 0 < z then Work.FTS.PhiStar.Series.cmode m F z else 0 with hcl
  have hcl_eq : ∀ t : ℝ, 0 < t → cl t = Work.FTS.PhiStar.Series.cmode m F t := by
    intro t ht; simp [hcl, ht]
  have hENpos : 0 < Work.EllipticEst.ModalSolution.eNorm m :=
    Work.EllipticEst.ModalSolution.eNorm_pos m
  have hc : AEMeasurable cl (μ := volume) := by
    rw [hcl]
    exact aemeasurable_cmode_clamp (α := α) m hsm
  -- the slice mass uniformly dominates the squared (clamped) mode coefficient
  have hbnd : ∀ z : ℝ, 0 < z → (cl z) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        / Work.EllipticEst.ModalSolution.eNorm m := by
    intro z hz
    have h := eNorm_mul_cmode_sq_le_sliceMass (m := m) (F := F) (z := z)
      (integrableOn_sq_sEta_of_HkMem hF hz)
    have h' : (Work.FTS.PhiStar.Series.cmode m F z) ^ 2
        * Work.EllipticEst.ModalSolution.eNorm m
        ≤ ∫ θ in Work.Spaces.Iθ,
            (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      rw [mul_comm]; exact h
    rw [hcl_eq z hz]
    exact (le_div_iff₀ hENpos).mpr h'
  -- near `0`: `∫_0^1 c²/t⁴ < ∞`
  have hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (cl t) ^ 2 / t ^ 4) (Set.Ioo 0 1) := by
    have hdom : MeasureTheory.IntegrableOn
        (fun t : ℝ => (Work.EllipticEst.ModalSolution.eNorm m)⁻¹
          * ((∫ θ in Work.Spaces.Iθ,
              (F t θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) / t ^ 4))
        (Set.Ioo 0 1) :=
      MeasureTheory.Integrable.const_mul (integrableOn_sliceMass_div_z4_of_HkMem hF) _
    refine MeasureTheory.Integrable.mono' (MeasureTheory.IntegrableOn.integrable hdom) ?_ ?_
    · exact (AEMeasurable.div
        ((hc.mono_measure MeasureTheory.Measure.restrict_le_self).pow_const 2)
        ((measurable_id.pow_const 4).aemeasurable)).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      have ht0 : 0 < t := ht.1
      have hb := hbnd t ht0
      rw [Real.norm_of_nonneg (by positivity)]
      calc (cl t) ^ 2 / t ^ 4
          ≤ ((∫ θ in Work.Spaces.Iθ,
                (F t θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
              / Work.EllipticEst.ModalSolution.eNorm m) / t ^ 4 :=
            div_le_div_of_nonneg_right hb (by positivity)
        _ = (Work.EllipticEst.ModalSolution.eNorm m)⁻¹
              * ((∫ θ in Work.Spaces.Iθ,
                  (F t θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) / t ^ 4) := by
            ring_nf
  -- far `∞`: `∫_1^∞ c² < ∞`
  have hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (cl t) ^ 2) (Set.Ioi 1) := by
    have hdom : MeasureTheory.IntegrableOn
        (fun t : ℝ => (Work.EllipticEst.ModalSolution.eNorm m)⁻¹
          * (∫ θ in Work.Spaces.Iθ,
              (F t θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
        (Set.Ioi 1) :=
      MeasureTheory.Integrable.const_mul (integrableOn_sliceMass_Ioi_one_of_HkMem hF) _
    refine MeasureTheory.Integrable.mono' (MeasureTheory.IntegrableOn.integrable hdom) ?_ ?_
    · exact ((hc.mono_measure MeasureTheory.Measure.restrict_le_self).pow_const 2
        ).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := lt_trans one_pos ht
      have hb := hbnd t ht0
      rw [Real.norm_of_nonneg (by positivity)]
      calc (cl t) ^ 2
          ≤ ((∫ θ in Work.Spaces.Iθ,
                (F t θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
              / Work.EllipticEst.ModalSolution.eNorm m) := hb
        _ = (Work.EllipticEst.ModalSolution.eNorm m)⁻¹
              * (∫ θ in Work.Spaces.Iθ,
                  (F t θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
            rw [div_eq_inv_mul]
  -- the vanishing rate at `0` transfers to the clamped coefficient
  have hvy' : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t ≤ δ →
      |cl t| ≤ ε * t ^ ((3 : ℝ) / 2) := by
    intro ε hε
    obtain ⟨δ, hδ, h⟩ := hvy ε hε
    exact ⟨δ, hδ, fun t ht htδ => by rw [hcl_eq t ht]; exact h t ht htδ⟩
  -- the sharp per-mode weighted energy bound for the clamped source
  have hmain : (Work.FTS.PhiStar.Radial.lamR m - 3 * α ^ 2 - 3 * α * (5 + α) / 2) ^ 2
        * (∫ z in Set.Ioi 0,
            (Work.FTS.PhiStar.Radial.radGreen α m cl z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ ∫ z in Set.Ioi 0, (cl z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
    radGreen_modeEnergy_of_o hα hα4 hm hc hnear hfar hvy'
  -- convert the `Iz`-integral of the solution into the `(0,∞)`-integral of `radGreen α m cl`
  have hAeq : (∫ z in Work.Spaces.Iz,
        (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2 * (Work.Spaces.w z) ^ 2)
      = ∫ z in Set.Ioi 0,
        (Work.FTS.PhiStar.Radial.radGreen α m cl z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    rw [Work.Spaces.Iz, MeasureTheory.integral_Ici_eq_integral_Ioi]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
    have hrg : Work.FTS.PhiStar.Series.acoeff α m F z
        = Work.FTS.PhiStar.Radial.radGreen α m cl z := by
      rw [show Work.FTS.PhiStar.Series.acoeff α m F z
          = Work.FTS.PhiStar.Radial.radGreen α m
              (fun t : ℝ => Work.FTS.PhiStar.Series.cmode m F t) z from rfl]
      exact (radGreen_congr_Ioi (fun t ht => hcl_eq t ht) hz).symm
    rw [hrg]
  -- the right-hand side: `(√(eNorm m) · cmode m F)² = eNorm m · (cl)²` on `(0,∞)`
  have hRHS : (∫ z in Work.Spaces.Iz,
        (Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)
          * Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (Work.Spaces.w z) ^ 2)
      = Work.EllipticEst.ModalSolution.eNorm m
        * (∫ z in Set.Ioi 0, (cl z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    rw [Work.Spaces.Iz, MeasureTheory.integral_Ici_eq_integral_Ioi]
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    have hsq : (Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)
        * Work.FTS.PhiStar.Series.cmode m F z) ^ 2
        = Work.EllipticEst.ModalSolution.eNorm m
          * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (le_of_lt hENpos)]
    rw [hsq, ← hcl_eq z hz]; ring
  have hBnn : 0 ≤ ∫ z in Set.Ioi 0, (cl z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
    MeasureTheory.integral_nonneg (fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hμ : 0 < Work.FTS.PhiStar.Radial.lamR m - 3 * α ^ 2 - 3 * α * (5 + α) / 2 := by
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    rw [Work.FTS.PhiStar.Radial.lamR]
    nlinarith [sq_nonneg α, hα.le, hα4, hm1]
  rw [hAeq, hRHS]
  exact sqrt_mu_bound hμ hBnn heNorm hmain

end Work.FTS.PhiStar.Honesty
