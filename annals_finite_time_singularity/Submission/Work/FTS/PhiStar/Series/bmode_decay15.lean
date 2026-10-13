import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Have
import Submission.Work.FTS.PhiStar.Series.BmodeCoeff
import Submission.Work.FTS.PhiStar.Series.BmCut
import Submission.Work.FTS.PhiStar.Series.BmCutComm
import Submission.Work.FTS.PhiStar.Series.exists_eFam_bounds
import Submission.Work.FTS.PhiStar.Series.exists_layer_small
import Submission.Work.FTS.PhiStar.Series.bmcut_chi_tendsto

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series

local notation "Iθ" => Work.Spaces.Iθ
local notation "Idm" => Work.FTS.EllipticEst.Lzero1
local notation "eF" => Work.FTS.PhiStar.Gegenbauer.eFam
local notation "GB" => Work.FTS.VocabO.GamBar
local notation "λm" => Work.FTS.PhiStar.Gegenbauer.lam

theorem bmode_decay15 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (ψ : ℝ → ℝ), 0 < α → α ≤ 1 / 5 →
    Work.FTS.PhiStar.AngModel α ψ → ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.cmode m (fun _ θ => ψ θ) 0|
        ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) := by
  obtain ⟨χ, K₁, K₂, hK₁, hK₂, hχc, hχbnd, hχ1, hχ0, hχd, hχdd, hχsupp⟩ := exists_bmcut_supp
  refine ⟨100, by norm_num, fun α ψ hα hα5 hang m hm => ?_⟩
  have hα1 : α ≤ 1 := by linarith
  obtain ⟨Ae, Be, hAe₀, hBe₀, hAe, hAe2, hBe⟩ := exists_eFam_bounds m
  have hsmallψ := exists_layer_small ψ hang.cont hang.bdry0 hang.bdry1
  have hAe' : ∀ θ ∈ Iθ, |eF m θ * Real.cos θ| ≤ Ae := by
    intro θ hθ
    have h1 := hAe2 θ hθ
    have hsin0 : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    have hc2 : Real.cos θ ^ 2 ≤ 1 := by
      nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sin θ)]
    have h2 : Real.sin θ * Real.cos θ ^ 2 ≤ 1 := by
      nlinarith [Real.sin_le_one θ, hsin0, sq_nonneg (Real.cos θ)]
    calc |eF m θ * Real.cos θ| ≤ Ae * Real.sin θ * Real.cos θ ^ 2 := h1
      _ = Ae * (Real.sin θ * Real.cos θ ^ 2) := by ring
      _ ≤ Ae * 1 := mul_le_mul_of_nonneg_left h2 (le_of_lt hAe₀)
      _ = Ae := mul_one _
  have hlimA := bmcut_chi_tendsto χ Ae hAe₀ m ψ hang.cont
    (fun δ hδ => (hχc δ hδ).continuous) hχ0 hχ1
    (fun δ hδ θ => (hχbnd δ hδ θ).1) (fun δ hδ θ => (hχbnd δ hδ θ).2) hAe'
  have hlimC := bmcut_chi_tendsto χ Ae hAe₀ m (fun θ => GB α θ)
    (continuousOn_GamBar α hα hα1) (fun δ hδ => (hχc δ hδ).continuous) hχ0 hχ1
    (fun δ hδ θ => (hχbnd δ hδ θ).1) (fun δ hδ θ => (hχbnd δ hδ θ).2) hAe'
  have hlimB := bmcut_commutator_tendsto χ K₁ K₂ Ae Be hK₁ hK₂ hAe₀ hBe₀ hχd hχdd hχsupp m
    hAe hAe2 hBe ψ hsmallψ
  have hkey := coeff_eq χ hχc hχ1 hχ0 α hα hα1 hang m hlimA hlimC hlimB
  have hN := Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts m
  have hNge := eFam_norm_ge m hm
  have hsqrtc : ContinuousOn (fun θ => Real.sqrt (Real.cos θ)) Iθ :=
    (Real.continuous_sqrt.comp Real.continuous_cos).continuousOn
  have hGc : ContinuousOn (fun θ => GB α θ) Iθ := continuousOn_GamBar α hα hα1
  have hEc : ContinuousOn (fun θ => eF m θ) Iθ := (contDiff_eF m).continuous.continuousOn
  have hcs := sq_integral_mul_le (fun θ => GB α θ * Real.sqrt (Real.cos θ))
    (fun θ => eF m θ * Real.sqrt (Real.cos θ))
    (integrableOn_Iθ_of_continuous ((hGc.mul hsqrtc).pow 2))
    (integrableOn_Iθ_of_continuous ((hGc.mul hsqrtc).mul (hEc.mul hsqrtc)))
    (integrableOn_Iθ_of_continuous ((hEc.mul hsqrtc).pow 2))
  have hI1 : (∫ θ in Iθ, (GB α θ * Real.sqrt (Real.cos θ)) * (eF m θ * Real.sqrt (Real.cos θ)))
      = ∫ θ in Iθ, GB α θ * eF m θ * Real.cos θ := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Iθ (fun θ hθ => ?_)
    have hc := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have hs : Real.sqrt (Real.cos θ) * Real.sqrt (Real.cos θ) = Real.cos θ := by
      rw [← sq, Real.sq_sqrt hc]
    calc (GB α θ * Real.sqrt (Real.cos θ)) * (eF m θ * Real.sqrt (Real.cos θ))
        = GB α θ * eF m θ * (Real.sqrt (Real.cos θ) * Real.sqrt (Real.cos θ)) := by ring
      _ = GB α θ * eF m θ * Real.cos θ := by rw [hs]
  have hI2 : (∫ θ in Iθ, (eF m θ * Real.sqrt (Real.cos θ)) ^ 2)
      = ∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Iθ (fun θ hθ => ?_)
    have hc := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    rw [mul_pow, Real.sq_sqrt hc]
  have hI3 : (∫ θ in Iθ, (GB α θ * Real.sqrt (Real.cos θ)) ^ 2)
      = ∫ θ in Iθ, GB α θ ^ 2 * Real.cos θ := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Iθ (fun θ hθ => ?_)
    have hc := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    rw [mul_pow, Real.sq_sqrt hc]
  rw [hI1, hI2, hI3] at hcs
  have hG2 : (∫ θ in Iθ, GB α θ ^ 2 * Real.cos θ) ≤ (45 / 4) ^ 2 := by
    have hb : ∀ θ ∈ Iθ, GB α θ ^ 2 * Real.cos θ ≤ (45 / 4) ^ 2 * Real.cos θ := by
      intro θ hθ
      have h1 : |GB α θ| ≤ 45 / 4 := GamBar_abs_le α hα hα1 hθ
      have h2 : 0 ≤ Real.cos θ :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
      have h3 : GB α θ ^ 2 ≤ (45 / 4) ^ 2 := by
        nlinarith [abs_le.mp h1]
      exact mul_le_mul_of_nonneg_right h3 h2
    have hP : IntegrableOn (fun θ => GB α θ ^ 2 * Real.cos θ) Iθ :=
      integrableOn_Iθ_of_continuous ((hGc.pow 2).mul Real.continuous_cos.continuousOn)
    have hQ : IntegrableOn (fun θ => (45 / 4) ^ 2 * Real.cos θ) Iθ :=
      integrableOn_Iθ_of_continuous (continuousOn_const.mul Real.continuous_cos.continuousOn)
    have hmono := MeasureTheory.setIntegral_mono_on hP hQ measurableSet_Iθ hb
    calc (∫ θ in Iθ, GB α θ ^ 2 * Real.cos θ) ≤ ∫ θ in Iθ, (45 / 4) ^ 2 * Real.cos θ := hmono
      _ = (45 / 4) ^ 2 * (∫ θ in Iθ, Real.cos θ) := by rw [integral_const_mul]
      _ = (45 / 4) ^ 2 := by rw [int_cos_Iθ, mul_one]
  have hcs' : (∫ θ in Iθ, GB α θ * eF m θ * Real.cos θ) ^ 2
      ≤ (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ) * (45 / 4) ^ 2 := by
    have hNp : 0 < ∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ := by
      have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
      linarith [hNge, hm1]
    calc (∫ θ in Iθ, GB α θ * eF m θ * Real.cos θ) ^ 2
        ≤ (∫ θ in Iθ, GB α θ ^ 2 * Real.cos θ) * (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ) := hcs
      _ ≤ (45 / 4) ^ 2 * (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ) :=
          mul_le_mul_of_nonneg_right hG2 (le_of_lt hNp)
      _ = (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ) * (45 / 4) ^ 2 := by ring
  have hKle : |∫ θ in Iθ, GB α θ * eF m θ * Real.cos θ|
      ≤ (45 / 4) * Real.sqrt (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ) := by
    have hNpos : 0 < ∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ := by
      have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
      linarith [hNge, hm1]
    have h1 : (∫ θ in Iθ, GB α θ * eF m θ * Real.cos θ) ^ 2
        ≤ ((45 / 4) * Real.sqrt (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (le_of_lt hNpos)]
      nlinarith [hcs']
    have h2 := sq_le_sq.mp h1
    exact h2.trans_eq (abs_of_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hNpos : 0 < ∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ := by linarith [hNge, hm1]
  have hlam : 0 < λm m := by
    rw [Work.FTS.PhiStar.Gegenbauer.lam]
    nlinarith [hm1]
  have hstep3 : (45 / 4) * Real.sqrt (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ)
      * Real.sqrt (2 * (m : ℝ) + 1) ≤ 100 * (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ) := by
    have h2m : 2 * (m : ℝ) + 1 ≤ 2 * (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ) := by linarith [hNge]
    have hs2 : ((45 / 4) * Real.sqrt (2 * (m : ℝ) + 1)) ^ 2
        ≤ (100 * Real.sqrt (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2 * (m:ℝ) + 1),
        Real.sq_sqrt (le_of_lt hNpos)]
      nlinarith [h2m]
    have hle : (45 / 4) * Real.sqrt (2 * (m : ℝ) + 1)
        ≤ 100 * Real.sqrt (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ) := by
      have h := sq_le_sq.mp hs2
      rwa [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at h
    calc (45 / 4) * Real.sqrt (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ) * Real.sqrt (2 * (m : ℝ) + 1)
        = Real.sqrt (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ)
          * ((45 / 4) * Real.sqrt (2 * (m : ℝ) + 1)) := by ring
      _ ≤ Real.sqrt (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ)
          * (100 * Real.sqrt (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ)) := by
          refine mul_le_mul_of_nonneg_left hle (Real.sqrt_nonneg _)
      _ = 100 * (Real.sqrt (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ)
          * Real.sqrt (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ)) := by ring
      _ = 100 * (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ) := by
          rw [← sq, Real.sq_sqrt (le_of_lt hNpos)]
  have hK : |∫ θ in Iθ, GB α θ * eF m θ * Real.cos θ|
      = λm m * |∫ θ in Iθ, ψ θ * eF m θ * Real.cos θ| := by
    rw [← hkey, abs_mul, abs_of_pos hlam]
  have hstep4 : |∫ θ in Iθ, ψ θ * eF m θ * Real.cos θ| * λm m * Real.sqrt (2 * (m : ℝ) + 1)
      ≤ 100 * (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ) := by
    have h1 : |∫ θ in Iθ, ψ θ * eF m θ * Real.cos θ| * λm m
        = |∫ θ in Iθ, GB α θ * eF m θ * Real.cos θ| := by
      rw [hK]; ring
    rw [h1]
    calc |∫ θ in Iθ, GB α θ * eF m θ * Real.cos θ| * Real.sqrt (2 * (m : ℝ) + 1)
        ≤ ((45 / 4) * Real.sqrt (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ))
          * Real.sqrt (2 * (m : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right hKle (Real.sqrt_nonneg _)
      _ = (45 / 4) * Real.sqrt (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ)
          * Real.sqrt (2 * (m : ℝ) + 1) := by ring
      _ ≤ 100 * (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ) := hstep3
  have hfinal : |∫ θ in Iθ, ψ θ * eF m θ * Real.cos θ|
        / (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ)
      ≤ 100 / (λm m * Real.sqrt (2 * (m : ℝ) + 1)) := by
    have hpos : (0:ℝ) < λm m * Real.sqrt (2 * (m : ℝ) + 1) :=
      mul_pos hlam (Real.sqrt_pos.mpr (by positivity : (0:ℝ) < 2 * (m : ℝ) + 1))
    have hposN : (0:ℝ) < λm m * Real.sqrt (2 * (m : ℝ) + 1)
        * (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ) := mul_pos hpos hNpos
    rw [div_le_iff₀ hNpos]
    rw [show 100 / (λm m * Real.sqrt (2 * (m : ℝ) + 1))
          * (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ)
        = 100 * (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ) / (λm m * Real.sqrt (2 * (m : ℝ) + 1))
        from by ring]
    rw [le_div_iff₀ hpos]
    have hassoc : |∫ θ in Iθ, ψ θ * eF m θ * Real.cos θ| * (λm m * Real.sqrt (2 * (m : ℝ) + 1))
        = |∫ θ in Iθ, ψ θ * eF m θ * Real.cos θ| * λm m * Real.sqrt (2 * (m : ℝ) + 1) := by
      ring
    rw [hassoc]
    exact hstep4
  have hnum : (∫ θ in (0 : ℝ)..(Real.pi / 2), ψ θ * eF m θ * Real.cos θ)
      = ∫ θ in Iθ, ψ θ * eF m θ * Real.cos θ := iota_eq _
  have hden : (∫ θ in (0 : ℝ)..(Real.pi / 2), eF m θ ^ 2 * Real.cos θ)
      = ∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ := iota_eq _
  show |Work.FTS.PhiStar.Series.cmode m (fun _ θ => ψ θ) 0|
      ≤ 100 / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
  rw [show Work.FTS.PhiStar.Series.cmode m (fun _ θ => ψ θ) 0
      = (∫ θ in (0 : ℝ)..(Real.pi / 2), ψ θ * eF m θ * Real.cos θ)
        / (∫ θ in (0 : ℝ)..(Real.pi / 2), eF m θ ^ 2 * Real.cos θ) from rfl, hnum, hden,
    abs_div, abs_of_pos hNpos]
  exact hfinal

end Work.FTS.PhiStar.Series
