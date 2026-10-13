/-
Support lemmas for `Work.FTS.Apriori.Profile.linf_H2_quad`.

These are elementary one-dimensional bounds on the angular weights
`sin(2σ)^{γ-2}` and `sin(2σ)^{-η}` that the assembly of `linf_H2_quad` needs.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Linf_H2
import Submission.Work.Spaces.HardyZ
import Submission.Work.FTS.LocData.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.FTS.H2.LinfQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Apriori.Profile

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Work.Spaces

/-- `sin (2θ) ≥ 0` on the angular interval. -/
theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- The angular weight `sin(2σ)^{γ-2}` is integrable on `Iθ` (for `0 < α ≤ 1`). -/
theorem integrableOn_sin_gam_sub_two {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    IntegrableOn (fun σ : ℝ => (Real.sin (2 * σ)) ^ (gam α - 2)) Iθ := by
  have hγ1 : 1 < gam α := one_lt_gam hα
  have hγ2 : gam α ≤ 2 := by rw [gam]; linarith
  exact (sin_two_rpow (gam α - 2) (by linarith) (by linarith)).1

/-- The angular cost integral, taken from the left end. -/
theorem theta_cost_le_up {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {a : ℝ} (ha : a ∈ Iθ) :
    (∫ σ in Set.Ioc a (Real.pi / 2), (Real.sin (2 * σ)) ^ (gam α - 2))
      ≤ 100 / (gam α - 1) := by
  have hγ1 : 1 < gam α := one_lt_gam hα
  have hγ2 : gam α ≤ 2 := by rw [gam]; linarith
  have hp1 : -1 < gam α - 2 := by linarith
  have hp0 : gam α - 2 ≤ 0 := by linarith
  obtain ⟨hint, hbnd⟩ := sin_two_rpow (gam α - 2) hp1 hp0
  have hbnd' : (∫ σ in Iθ, (Real.sin (2 * σ)) ^ (gam α - 2)) ≤ 100 / (gam α - 1) := by
    have h : gam α - 2 + 1 = gam α - 1 := by ring
    simpa [h] using hbnd
  refine le_trans (MeasureTheory.setIntegral_mono_set hint ?_ ?_) hbnd'
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with σ hσ
    exact Real.rpow_nonneg (sin_two_nonneg_Iθ hσ) _
  · filter_upwards with σ hσ
    exact ⟨le_of_lt (lt_of_le_of_lt ha.1 hσ.1), hσ.2⟩

/-- The angular cost integral, taken from the right end. -/
theorem theta_cost_le_down {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {a : ℝ} (ha : a ∈ Iθ) :
    (∫ σ in Set.Ioc 0 a, (Real.sin (2 * σ)) ^ (gam α - 2)) ≤ 100 / (gam α - 1) := by
  have hγ1 : 1 < gam α := one_lt_gam hα
  have hγ2 : gam α ≤ 2 := by rw [gam]; linarith
  have hp1 : -1 < gam α - 2 := by linarith
  have hp0 : gam α - 2 ≤ 0 := by linarith
  obtain ⟨hint, hbnd⟩ := sin_two_rpow (gam α - 2) hp1 hp0
  have hbnd' : (∫ σ in Iθ, (Real.sin (2 * σ)) ^ (gam α - 2)) ≤ 100 / (gam α - 1) := by
    have h : gam α - 2 + 1 = gam α - 1 := by ring
    simpa [h] using hbnd
  refine le_trans (MeasureTheory.setIntegral_mono_set hint ?_ ?_) hbnd'
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with σ hσ
    exact Real.rpow_nonneg (sin_two_nonneg_Iθ hσ) _
  · filter_upwards with σ hσ
    exact ⟨le_of_lt hσ.1, le_trans hσ.2 ha.2⟩

/-- `sin(2σ)^{-η} ≥ 1` on `(0,π/2)`. -/
theorem one_le_sin_rpow_neg_eta {σ : ℝ} (h0 : 0 < σ) (h1 : σ < Real.pi / 2) :
    1 ≤ (Real.sin (2 * σ)) ^ (-(eta)) := by
  have hs : 0 < Real.sin (2 * σ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [h1, Real.pi_pos])
  have hs1 : Real.sin (2 * σ) ≤ 1 := Real.sin_le_one _
  have hpow : (Real.sin (2 * σ)) ^ eta ≤ 1 := Real.rpow_le_one hs.le hs1 eta_pos.le
  have hpos : 0 < (Real.sin (2 * σ)) ^ eta := Real.rpow_pos_of_pos hs eta
  rw [Real.rpow_neg hs.le eta]
  exact (one_le_inv₀ hpos).mpr hpow

/-- The angular mass integral from the right end is at least `1/4`
(valid for `θ₀ ≤ 3π/8`). -/
theorem theta_mass_up {θ₀ : ℝ} (h0 : 0 ≤ θ₀) (h : θ₀ ≤ 3 * Real.pi / 8) :
    1 / 4 ≤ (∫ σ in Set.Ioc θ₀ (Real.pi / 2), (Real.sin (2 * σ)) ^ (-(eta))) := by
  have hp1 : -1 < -(eta) := by have := eta_lt_one; linarith
  have hp0 : -(eta) ≤ 0 := by have := eta_pos; linarith
  have hint : IntegrableOn (fun σ : ℝ => (Real.sin (2 * σ)) ^ (-(eta))) Iθ :=
    (sin_two_rpow (-(eta)) hp1 hp0).1
  have hbig : IntegrableOn (fun σ : ℝ => (Real.sin (2 * σ)) ^ (-(eta)))
      (Set.Ioc θ₀ (Real.pi / 2)) :=
    hint.mono_set (fun σ hσ => ⟨le_of_lt (lt_of_le_of_lt h0 hσ.1), hσ.2⟩)
  have hsmall : IntegrableOn (fun σ : ℝ => (Real.sin (2 * σ)) ^ (-(eta)))
      (Set.Ioo (3 * Real.pi / 8) (Real.pi / 2)) :=
    hint.mono_set (fun σ hσ => ⟨le_of_lt (by linarith [Real.pi_pos, hσ.1] : (0:ℝ) < σ),
      le_of_lt hσ.2⟩)
  have hmono : (∫ σ in Set.Ioo (3 * Real.pi / 8) (Real.pi / 2),
        (Real.sin (2 * σ)) ^ (-(eta)))
      ≤ (∫ σ in Set.Ioc θ₀ (Real.pi / 2), (Real.sin (2 * σ)) ^ (-(eta))) := by
    refine MeasureTheory.setIntegral_mono_set hbig ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with σ hσ
      exact Real.rpow_nonneg (sin_two_nonneg_Iθ ⟨le_of_lt (lt_of_le_of_lt h0 hσ.1), hσ.2⟩) _
    · filter_upwards with σ hσ
      exact ⟨lt_of_le_of_lt h hσ.1, hσ.2.le⟩
  refine le_trans ?_ hmono
  have hpt : ∀ σ ∈ Set.Ioo (3 * Real.pi / 8) (Real.pi / 2),
      (1:ℝ) ≤ (Real.sin (2 * σ)) ^ (-(eta)) := by
    intro σ hσ
    exact one_le_sin_rpow_neg_eta (by linarith [Real.pi_pos, hσ.1]) hσ.2
  have hconst : (∫ σ in Set.Ioo (3 * Real.pi / 8) (Real.pi / 2), (1:ℝ)) = Real.pi / 8 := by
    have hsub : Real.pi / 2 - 3 * Real.pi / 8 = Real.pi / 8 := by ring
    rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one, MeasureTheory.Measure.real,
      Real.volume_Ioo, hsub,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : (0:ℝ) ≤ Real.pi / 8)]
  have hle1 : (∫ σ in Set.Ioo (3 * Real.pi / 8) (Real.pi / 2), (1:ℝ))
      ≤ (∫ σ in Set.Ioo (3 * Real.pi / 8) (Real.pi / 2), (Real.sin (2 * σ)) ^ (-(eta))) :=
    MeasureTheory.setIntegral_mono_of_nonneg (fun _ _ => zero_le_one) (fun σ hσ => hpt σ hσ) hsmall
  have hquarter : (1:ℝ) / 4 ≤ Real.pi / 8 := by linarith [Real.pi_gt_three]
  exact le_trans hquarter (le_trans (le_of_eq hconst.symm) hle1)

/-- The angular mass integral from the left end is at least `1/4`
(valid for `3π/8 ≤ θ₀ ≤ π/2`). -/
theorem theta_mass_down {θ₀ : ℝ} (h2 : θ₀ ≤ Real.pi / 2) (h : 3 * Real.pi / 8 ≤ θ₀) :
    1 / 4 ≤ (∫ σ in Set.Ioc 0 θ₀, (Real.sin (2 * σ)) ^ (-(eta))) := by
  have hp1 : -1 < -(eta) := by have := eta_lt_one; linarith
  have hp0 : -(eta) ≤ 0 := by have := eta_pos; linarith
  have hint : IntegrableOn (fun σ : ℝ => (Real.sin (2 * σ)) ^ (-(eta))) Iθ :=
    (sin_two_rpow (-(eta)) hp1 hp0).1
  have hbig : IntegrableOn (fun σ : ℝ => (Real.sin (2 * σ)) ^ (-(eta))) (Set.Ioc 0 θ₀) :=
    hint.mono_set (fun σ hσ => ⟨le_of_lt hσ.1, le_trans hσ.2 h2⟩)
  have hsmall : IntegrableOn (fun σ : ℝ => (Real.sin (2 * σ)) ^ (-(eta)))
      (Set.Ioo (Real.pi / 4) (3 * Real.pi / 8)) :=
    hint.mono_set (fun σ hσ => ⟨le_of_lt (by linarith [Real.pi_pos, hσ.1] : (0:ℝ) < σ),
      le_of_lt (by linarith [Real.pi_pos, hσ.2] : σ < Real.pi / 2)⟩)
  have hmono : (∫ σ in Set.Ioo (Real.pi / 4) (3 * Real.pi / 8), (Real.sin (2 * σ)) ^ (-(eta)))
      ≤ (∫ σ in Set.Ioc 0 θ₀, (Real.sin (2 * σ)) ^ (-(eta))) := by
    refine MeasureTheory.setIntegral_mono_set hbig ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with σ hσ
      exact Real.rpow_nonneg (sin_two_nonneg_Iθ ⟨le_of_lt hσ.1, le_trans hσ.2 h2⟩) _
    · filter_upwards with σ hσ
      exact ⟨by linarith [Real.pi_pos, hσ.1], le_trans hσ.2.le h⟩
  refine le_trans ?_ hmono
  have hpt : ∀ σ ∈ Set.Ioo (Real.pi / 4) (3 * Real.pi / 8),
      (1:ℝ) ≤ (Real.sin (2 * σ)) ^ (-(eta)) := by
    intro σ hσ
    exact one_le_sin_rpow_neg_eta (by linarith [Real.pi_pos, hσ.1])
      (by linarith [Real.pi_pos, hσ.2])
  have hconst : (∫ σ in Set.Ioo (Real.pi / 4) (3 * Real.pi / 8), (1:ℝ)) = Real.pi / 8 := by
    have hsub : 3 * Real.pi / 8 - Real.pi / 4 = Real.pi / 8 := by ring
    rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one, MeasureTheory.Measure.real,
      Real.volume_Ioo, hsub,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : (0:ℝ) ≤ Real.pi / 8)]
  have hle1 : (∫ σ in Set.Ioo (Real.pi / 4) (3 * Real.pi / 8), (1:ℝ))
      ≤ (∫ σ in Set.Ioo (Real.pi / 4) (3 * Real.pi / 8), (Real.sin (2 * σ)) ^ (-(eta))) :=
    MeasureTheory.setIntegral_mono_of_nonneg (fun _ _ => zero_le_one) (fun σ hσ => hpt σ hσ) hsmall
  have hquarter : (1:ℝ) / 4 ≤ Real.pi / 8 := by linarith [Real.pi_gt_three]
  exact le_trans hquarter (le_trans (le_of_eq hconst.symm) hle1)

end Work.FTS.Apriori.Profile
