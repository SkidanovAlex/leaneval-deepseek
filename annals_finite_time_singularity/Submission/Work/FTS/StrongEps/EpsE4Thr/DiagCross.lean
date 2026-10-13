import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.AffineSpace.Slope
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.EpsE4Thr.DiagAux
import Submission.Work.FTS.StrongEps.EpsE4Thr.DiagSlices

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

namespace Work.FTS.StrongEps.EpsE4Thr

set_option linter.unusedVariables false

/-- **The crossed pairing is a.e. measurable as a function of `σ`.** -/
theorem diag_Rmeas {ρ : ℝ → ℝ → ℝ} {u udot : ℝ → Work.FTS.Galerkin.Fn} {τ T : ℝ}
    (D : DiagData ρ u udot τ T) :
    AEMeasurable (fun σ : ℝ => ∫ p : ℝ × ℝ, udot σ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2 ∂diaM)
      volume := by
  have hWprod : AEStronglyMeasurable (fun q : ℝ × (ℝ × ℝ) => ρ q.2.1 q.2.2)
      (MeasureTheory.volume.prod diaM) := D.wmeas.aestronglyMeasurable.comp_snd
  have hRprod : AEStronglyMeasurable
      (fun q : ℝ × (ℝ × ℝ) => udot q.1 q.2.1 q.2.2 * u τ q.2.1 q.2.2 * ρ q.2.1 q.2.2)
      (MeasureTheory.volume.prod diaM) :=
    (D.aesmd.mul ((D.umeas τ D.hτ).aestronglyMeasurable.comp_snd)).mul hWprod
  exact hRprod.integral_prod_right'.aemeasurable

/-- **Continuity of the crossed pairing at `τ`.** -/
theorem diag_Rcont {ρ : ℝ → ℝ → ℝ} {u udot : ℝ → Work.FTS.Galerkin.Fn} {τ T : ℝ}
    (D : DiagData ρ u udot τ T) :
    Filter.Tendsto (fun σ : ℝ => ∫ p : ℝ × ℝ, udot σ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2 ∂diaM)
      (nhds τ) (nhds (diagQval ρ u udot τ)) := by
  set Ct : ℝ := ∫ p : ℝ × ℝ, u τ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2 ∂diaM with hCt
  have hCt0 : 0 ≤ Ct :=
    integral_nonneg_of_ae (D.ρnn.mono (fun p hp => mul_nonneg (mul_self_nonneg _) hp))
  have hdiff_int : ∀ σ ∈ Set.Ioo (0 : ℝ) T, MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (udot σ p.1 p.2 - udot τ p.1 p.2)
        * (udot σ p.1 p.2 - udot τ p.1 p.2) * ρ p.1 p.2) diaM := by
    intro σ hσ
    exact integrable_sub_sq D.ρnn D.wmeas (D.diagd σ ⟨le_of_lt hσ.1, le_of_lt hσ.2⟩)
      (D.diagd τ D.hτIcc) (D.dmeas σ hσ) (D.dmeas τ D.hτ)
  have hcross_int : ∀ σ ∈ Set.Ioo (0 : ℝ) T, MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (udot σ p.1 p.2 - udot τ p.1 p.2) * u τ p.1 p.2 * ρ p.1 p.2) diaM := by
    intro σ hσ
    exact integrable_amgm_mul D.ρnn D.wmeas
      (G := fun p : ℝ × ℝ => udot σ p.1 p.2 - udot τ p.1 p.2)
      (H := fun p : ℝ × ℝ => u τ p.1 p.2)
      (hdiff_int σ hσ) (D.diag τ D.hτIcc)
      ((D.dmeas σ hσ).sub (D.dmeas τ D.hτ)) (D.umeas τ D.hτ)
  have huτ_int : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => udot τ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2) diaM :=
    integrable_amgm_mul D.ρnn D.wmeas (G := fun p : ℝ × ℝ => udot τ p.1 p.2)
      (H := fun p : ℝ × ℝ => u τ p.1 p.2) (D.diagd τ D.hτIcc) (D.diag τ D.hτIcc)
      (D.dmeas τ D.hτ) (D.umeas τ D.hτ)
  have huσ_int : ∀ σ ∈ Set.Ioo (0 : ℝ) T, MeasureTheory.Integrable
      (fun p : ℝ × ℝ => udot σ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2) diaM := by
    intro σ hσ
    exact integrable_amgm_mul D.ρnn D.wmeas (G := fun p : ℝ × ℝ => udot σ p.1 p.2)
      (H := fun p : ℝ × ℝ => u τ p.1 p.2)
      (D.diagd σ ⟨le_of_lt hσ.1, le_of_lt hσ.2⟩) (D.diag τ D.hτIcc)
      (D.dmeas σ hσ) (D.umeas τ D.hτ)
  have hcs : ∀ᶠ σ in nhds τ,
      (∫ p : ℝ × ℝ, udot σ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2 ∂diaM
        - ∫ p : ℝ × ℝ, udot τ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2 ∂diaM) ^ 2
      ≤ Ct * (∫ p : ℝ × ℝ, (udot σ p.1 p.2 - udot τ p.1 p.2)
          * (udot σ p.1 p.2 - udot τ p.1 p.2) * ρ p.1 p.2 ∂diaM) := by
    filter_upwards [Ioo_mem_nhds D.hτ1 D.hτ2] with σ hσ
    have h1 : (∫ p : ℝ × ℝ, udot σ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2 ∂diaM)
        - (∫ p : ℝ × ℝ, udot τ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2 ∂diaM)
        = ∫ p : ℝ × ℝ, (udot σ p.1 p.2 - udot τ p.1 p.2) * u τ p.1 p.2 * ρ p.1 p.2 ∂diaM := by
      rw [← integral_sub (huσ_int σ hσ) huτ_int]
      exact integral_congr_ae (Eventually.of_forall fun p => by ring)
    rw [h1]
    have hCS := cs_diag_mup (wt := ρ)
      (G := fun p : ℝ × ℝ => udot σ p.1 p.2 - udot τ p.1 p.2)
      (H := fun p : ℝ × ℝ => u τ p.1 p.2) D.ρnn (hdiff_int σ hσ) (D.diag τ D.hτIcc)
      (hcross_int σ hσ)
    calc (∫ p : ℝ × ℝ, (udot σ p.1 p.2 - udot τ p.1 p.2) * u τ p.1 p.2 * ρ p.1 p.2 ∂diaM) ^ 2
        ≤ (∫ p : ℝ × ℝ, (udot σ p.1 p.2 - udot τ p.1 p.2)
              * (udot σ p.1 p.2 - udot τ p.1 p.2) * ρ p.1 p.2 ∂diaM)
          * (∫ p : ℝ × ℝ, u τ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2 ∂diaM) := hCS
      _ = Ct * (∫ p : ℝ × ℝ, (udot σ p.1 p.2 - udot τ p.1 p.2)
              * (udot σ p.1 p.2 - udot τ p.1 p.2) * ρ p.1 p.2 ∂diaM) := by
          rw [hCt]; ring
  have hGsq : Filter.Tendsto (fun σ : ℝ => ∫ p : ℝ × ℝ,
      (udot σ p.1 p.2 - udot τ p.1 p.2) * (udot σ p.1 p.2 - udot τ p.1 p.2) * ρ p.1 p.2 ∂diaM)
      (nhds τ) (nhds 0) := by
    have hcongr : (fun σ : ℝ => ∫ p : ℝ × ℝ,
        (udot σ p.1 p.2 - udot τ p.1 p.2) * (udot σ p.1 p.2 - udot τ p.1 p.2) * ρ p.1 p.2 ∂diaM)
        = fun σ : ℝ => ∫ p : ℝ × ℝ,
            (udot σ p.1 p.2 - udot τ p.1 p.2) ^ 2 * ρ p.1 p.2 ∂diaM := by
      funext σ
      exact integral_congr_ae (Eventually.of_forall (fun p => by simp only [pow_two]))
    rw [hcongr]
    exact D.contU
  have hlim : Filter.Tendsto (fun σ : ℝ =>
      ∫ p : ℝ × ℝ, udot σ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2 ∂diaM
      - ∫ p : ℝ × ℝ, udot τ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2 ∂diaM) (nhds τ) (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (g := fun σ : ℝ => Real.sqrt (Ct * (∫ p : ℝ × ℝ,
      (udot σ p.1 p.2 - udot τ p.1 p.2) * (udot σ p.1 p.2 - udot τ p.1 p.2) * ρ p.1 p.2 ∂diaM)))
      (Eventually.of_forall fun σ => norm_nonneg _) ?_ ?_
    · filter_upwards [hcs] with σ hσ
      rw [Real.norm_eq_abs]
      have h2 : |∫ p : ℝ × ℝ, udot σ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2 ∂diaM
            - ∫ p : ℝ × ℝ, udot τ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2 ∂diaM|
          ≤ Real.sqrt (Ct * (∫ p : ℝ × ℝ, (udot σ p.1 p.2 - udot τ p.1 p.2)
              * (udot σ p.1 p.2 - udot τ p.1 p.2) * ρ p.1 p.2 ∂diaM)) := by
        have h3 := Real.sqrt_le_sqrt hσ
        rw [Real.sqrt_sq_eq_abs] at h3
        exact h3
      exact h2
    · have h1 : Filter.Tendsto (fun σ : ℝ => Ct * (∫ p : ℝ × ℝ,
          (udot σ p.1 p.2 - udot τ p.1 p.2) * (udot σ p.1 p.2 - udot τ p.1 p.2) * ρ p.1 p.2 ∂diaM))
          (nhds τ) (nhds (Ct * 0)) := hGsq.const_mul Ct
      simpa using h1.sqrt
  have hfun : (fun σ : ℝ => (∫ p : ℝ × ℝ, udot σ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2 ∂diaM
        - ∫ p : ℝ × ℝ, udot τ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2 ∂diaM)
        + ∫ p : ℝ × ℝ, udot τ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2 ∂diaM)
      =ᶠ[nhds τ] fun σ : ℝ => ∫ p : ℝ × ℝ, udot σ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2 ∂diaM :=
    Eventually.of_forall fun σ => by ring
  have hval : (0 : ℝ) + (∫ p : ℝ × ℝ, udot τ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2 ∂diaM)
      = diagQval ρ u udot τ := by rw [zero_add]; rfl
  have hthis := hlim.add_const (∫ p : ℝ × ℝ, udot τ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2 ∂diaM)
  rw [hval] at hthis
  exact Tendsto.congr' hfun hthis

/-- **The square remainder tends to `0`.** -/
theorem diag_Arem0 {ρ : ℝ → ℝ → ℝ} {u udot : ℝ → Work.FTS.Galerkin.Fn} {τ T : ℝ}
    (D : DiagData ρ u udot τ T)
    (hSlices : ∀ᵐ p ∂diaM, ρ p.1 p.2 = 0 ∨
      (((∀ s ∈ Set.Ioo (τ - D.δ) (τ + D.δ),
          IntervalIntegrable (fun σ : ℝ => udot σ p.1 p.2) volume τ s) ∧
        (∀ s ∈ Set.Ioo (τ - D.δ) (τ + D.δ),
          IntervalIntegrable (fun σ : ℝ => udot σ p.1 p.2 * udot σ p.1 p.2) volume τ s)) ∧
        (∀ s ∈ Set.Ioo (τ - D.δ) (τ + D.δ),
          u s p.1 p.2 - u τ p.1 p.2 = ∫ σ in τ..s, udot σ p.1 p.2))) :
    Filter.Tendsto (diagArem ρ u τ) (nhdsWithin τ {τ}ᶜ) (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (g := fun s : ℝ => D.K * |s - τ|)
    (Eventually.of_forall fun s => norm_nonneg _) ?_ ?_
  · filter_upwards [nhdsWithin_le_nhds D.δ_mem, self_mem_nhdsWithin] with s hs hsne
    have hX0 : 0 ≤ ∫ p : ℝ × ℝ,
        (u s p.1 p.2 - u τ p.1 p.2) * (u s p.1 p.2 - u τ p.1 p.2) * ρ p.1 p.2 ∂diaM :=
      integral_nonneg_of_ae (D.ρnn.mono (fun p hp => mul_nonneg (mul_self_nonneg _) hp))
    have hne : s - τ ≠ 0 := sub_ne_zero.mpr hsne
    rw [diagArem, Real.norm_eq_abs, abs_mul, abs_inv]
    calc |s - τ|⁻¹ * |∫ p : ℝ × ℝ,
            (u s p.1 p.2 - u τ p.1 p.2) * (u s p.1 p.2 - u τ p.1 p.2) * ρ p.1 p.2 ∂diaM|
        ≤ |s - τ|⁻¹ * (|s - τ| * (D.K * |s - τ|)) := by
          refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (abs_nonneg _))
          rw [abs_of_nonneg hX0]
          exact diag_sq_est D hSlices s hs
      _ = D.K * |s - τ| := by
          rw [inv_mul_cancel_left₀ (abs_ne_zero.mpr hne)]
  · have hsub : Filter.Tendsto (fun s : ℝ => s - τ) (nhdsWithin τ {τ}ᶜ) (nhds 0) := by
      have h1 : Filter.Tendsto (fun s : ℝ => s - τ) (nhds τ) (nhds (τ - τ)) :=
        (Filter.tendsto_id (x := nhds τ)).sub_const τ
      simpa using tendsto_nhdsWithin_of_tendsto_nhds h1
    have habs : Filter.Tendsto (fun s : ℝ => |s - τ|) (nhdsWithin τ {τ}ᶜ) (nhds 0) := by
      simpa [Real.norm_eq_abs] using hsub.norm
    simpa using habs.const_mul D.K

/-- **The crossed remainder equals the average of the crossed pairing.** -/
theorem diag_Blim {ρ : ℝ → ℝ → ℝ} {u udot : ℝ → Work.FTS.Galerkin.Fn} {τ T : ℝ}
    (D : DiagData ρ u udot τ T)
    (hSlices : ∀ᵐ p ∂diaM, ρ p.1 p.2 = 0 ∨
      (((∀ s ∈ Set.Ioo (τ - D.δ) (τ + D.δ),
          IntervalIntegrable (fun σ : ℝ => udot σ p.1 p.2) volume τ s) ∧
        (∀ s ∈ Set.Ioo (τ - D.δ) (τ + D.δ),
          IntervalIntegrable (fun σ : ℝ => udot σ p.1 p.2 * udot σ p.1 p.2) volume τ s)) ∧
        (∀ s ∈ Set.Ioo (τ - D.δ) (τ + D.δ),
          u s p.1 p.2 - u τ p.1 p.2 = ∫ σ in τ..s, udot σ p.1 p.2))) :
    Filter.Tendsto (diagBrem ρ u τ) (nhdsWithin τ {τ}ᶜ) (nhds (diagQval ρ u udot τ)) := by
  have hBident : diagBrem ρ u τ =ᶠ[nhdsWithin τ {τ}ᶜ] fun s : ℝ => (s - τ)⁻¹ * ∫ σ in τ..s,
      (∫ p : ℝ × ℝ, udot σ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2 ∂diaM) := by
    filter_upwards [nhdsWithin_le_nhds D.δ_mem, self_mem_nhdsWithin] with s hs hsne
    set Ct : ℝ := ∫ p : ℝ × ℝ, u τ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2 ∂diaM with hCt
    haveI : IsFiniteMeasure (MeasureTheory.volume.restrict (Set.uIoc τ s)) :=
      ⟨by rw [Measure.restrict_apply_univ, Real.volume_uIoc]; exact ENNReal.ofReal_lt_top⟩
    have hs1 : (0 : ℝ) < s := (D.Ioo_mem hs).1
    have hs2 : s < T := (D.Ioo_mem hs).2
    have hm : τ - D.δ < min τ s := lt_min (by linarith [D.δ_pos]) hs.1
    have hM : max τ s < τ + D.δ := max_lt (by linarith [D.δ_pos]) hs.2
    have hIccmm : Set.Icc (min τ s) (max τ s) ⊆ Set.Icc (0 : ℝ) T := by
      intro x hx
      rw [Set.mem_Icc] at hx
      exact ⟨by linarith [hm, hx.1, D.δ_pos'], by linarith [hM, hx.2, D.δ_T]⟩
    -- the a.e. Newton-Leibniz substitution
    have hAe : (fun p : ℝ × ℝ => u τ p.1 p.2 * (u s p.1 p.2 - u τ p.1 p.2) * ρ p.1 p.2)
        =ᵐ[diaM] fun p : ℝ × ℝ => u τ p.1 p.2 * (∫ σ in τ..s, udot σ p.1 p.2) * ρ p.1 p.2 := by
      filter_upwards [hSlices] with p hS
      rcases hS with h0 | ⟨⟨hIV, hIsq⟩, hNL⟩
      · rw [h0]; ring
      · rw [hNL s hs]
    -- Fubini
    have hjoint : AEStronglyMeasurable
        (fun z : ℝ × (ℝ × ℝ) => udot z.1 z.2.1 z.2.2 * u τ z.2.1 z.2.2 * ρ z.2.1 z.2.2)
        ((MeasureTheory.volume.restrict (Set.uIoc τ s)).prod diaM) :=
      (((D.aesmd.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)).mul
          ((D.umeas τ D.hτ).aestronglyMeasurable.comp_snd)).mul
        ((D.wmeas.aestronglyMeasurable.comp_snd).mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)))
    have huncurry : MeasureTheory.Integrable
        (Function.uncurry (fun σ (p : ℝ × ℝ) => udot σ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2))
        ((MeasureTheory.volume.restrict (Set.uIoc τ s)).prod diaM) := by
      refine (integrable_prod_iff hjoint).mpr ⟨?_, ?_⟩
      · filter_upwards [ae_restrict_mem (measurableSet_uIoc (a := τ) (b := s))] with σ hσ
        have hσ' : σ ∈ Set.Ioc (min τ s) (max τ s) := hσ
        rw [Set.mem_Ioc] at hσ'
        have hσIoo : σ ∈ Set.Ioo (0 : ℝ) T :=
          ⟨by linarith [hm, hσ'.1, D.δ_pos'], by linarith [hM, hσ'.2, D.δ_T]⟩
        exact integrable_amgm_mul D.ρnn D.wmeas
          (G := fun p : ℝ × ℝ => udot σ p.1 p.2) (H := fun p : ℝ × ℝ => u τ p.1 p.2)
          (D.diagd σ (hIccmm ⟨le_of_lt hσ'.1, hσ'.2⟩)) (D.diag τ D.hτIcc)
          (D.dmeas σ hσIoo) (D.umeas τ D.hτ)
      · have hnm : AEStronglyMeasurable (fun σ : ℝ => ∫ p : ℝ × ℝ,
            ‖udot σ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2‖ ∂diaM)
            (MeasureTheory.volume.restrict (Set.uIoc τ s)) :=
          hjoint.norm.integral_prod_right'
        refine (integrable_const ((Ct + D.K) / 2)).mono' hnm ?_
        filter_upwards [ae_restrict_mem (measurableSet_uIoc (a := τ) (b := s))] with σ hσ
        have hσ' : σ ∈ Set.Ioc (min τ s) (max τ s) := hσ
        rw [Set.mem_Ioc] at hσ'
        have hσIcc : σ ∈ Set.Icc (0 : ℝ) T := hIccmm ⟨le_of_lt hσ'.1, hσ'.2⟩
        have hpoint : (fun p : ℝ × ℝ => ‖udot σ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2‖)
            ≤ᵐ[diaM] fun p : ℝ × ℝ =>
              ((udot σ p.1 p.2 * udot σ p.1 p.2 + u τ p.1 p.2 * u τ p.1 p.2) / 2) * ρ p.1 p.2 := by
          filter_upwards [D.ρnn] with p hp
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hp]
          calc |udot σ p.1 p.2| * |u τ p.1 p.2| * ρ p.1 p.2
              = |udot σ p.1 p.2 * u τ p.1 p.2| * ρ p.1 p.2 := by rw [abs_mul]
            _ ≤ ((udot σ p.1 p.2 * udot σ p.1 p.2 + u τ p.1 p.2 * u τ p.1 p.2) / 2)
                  * ρ p.1 p.2 :=
                mul_le_mul_of_nonneg_right (abs_mul_le_half_sq _ _) hp
        have hdomint : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
            ((udot σ p.1 p.2 * udot σ p.1 p.2 + u τ p.1 p.2 * u τ p.1 p.2) / 2)
              * ρ p.1 p.2) diaM := by
          rw [show (fun p : ℝ × ℝ =>
                ((udot σ p.1 p.2 * udot σ p.1 p.2 + u τ p.1 p.2 * u τ p.1 p.2) / 2) * ρ p.1 p.2)
              = fun p : ℝ × ℝ => ((udot σ p.1 p.2 * udot σ p.1 p.2 * ρ p.1 p.2)
                  + (u τ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2)) / 2 from by funext p; ring]
          exact ((D.diagd σ hσIcc).add (D.diag τ D.hτIcc)).div_const 2
        calc ‖∫ p : ℝ × ℝ, ‖udot σ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2‖ ∂diaM‖
            = ∫ p : ℝ × ℝ, ‖udot σ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2‖ ∂diaM := by
              rw [Real.norm_eq_abs, abs_of_nonneg
                (integral_nonneg_of_ae (Eventually.of_forall fun p => norm_nonneg _))]
          _ ≤ ∫ p : ℝ × ℝ,
                ((udot σ p.1 p.2 * udot σ p.1 p.2 + u τ p.1 p.2 * u τ p.1 p.2) / 2)
                  * ρ p.1 p.2 ∂diaM :=
              integral_mono_of_nonneg (Eventually.of_forall fun p => norm_nonneg _) hdomint hpoint
          _ = (∫ p : ℝ × ℝ, udot σ p.1 p.2 * udot σ p.1 p.2 * ρ p.1 p.2 ∂diaM
                + ∫ p : ℝ × ℝ, u τ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2 ∂diaM) / 2 := by
              rw [show (fun p : ℝ × ℝ =>
                    ((udot σ p.1 p.2 * udot σ p.1 p.2 + u τ p.1 p.2 * u τ p.1 p.2) / 2) * ρ p.1 p.2)
                  = fun p : ℝ × ℝ => ((udot σ p.1 p.2 * udot σ p.1 p.2 * ρ p.1 p.2)
                      + (u τ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2)) / 2 from by funext p; ring]
              rw [integral_div, integral_add (D.diagd σ hσIcc) (D.diag τ D.hτIcc)]
          _ ≤ (Ct + D.K) / 2 := by
              have h1 := D.bdd σ hσIcc
              rw [hCt] at *
              linarith
    have hFub : (∫ p : ℝ × ℝ, u τ p.1 p.2 * (∫ σ in τ..s, udot σ p.1 p.2) * ρ p.1 p.2 ∂diaM)
        = ∫ σ in τ..s, (∫ p : ℝ × ℝ, udot σ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2 ∂diaM) := by
      have h2 := intervalIntegral_integral_swap (μ := diaM)
        (f := fun σ (p : ℝ × ℝ) => udot σ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2) huncurry
      have hcongr : (∫ p : ℝ × ℝ, u τ p.1 p.2 * (∫ σ in τ..s, udot σ p.1 p.2)
            * ρ p.1 p.2 ∂diaM)
          = ∫ p : ℝ × ℝ, (∫ σ in τ..s, udot σ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2) ∂diaM := by
        refine integral_congr_ae (Eventually.of_forall fun p => ?_)
        change u τ p.1 p.2 * (∫ σ in τ..s, udot σ p.1 p.2) * ρ p.1 p.2
          = ∫ σ in τ..s, udot σ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2
        rw [show (fun σ : ℝ => udot σ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2)
            = fun σ : ℝ => (u τ p.1 p.2 * ρ p.1 p.2) * udot σ p.1 p.2 from by funext σ; ring]
        rw [intervalIntegral.integral_const_mul]
        ring
      exact hcongr.trans h2.symm
    rw [diagBrem, integral_congr_ae hAe, hFub]
  have h2 : Filter.Tendsto (fun s : ℝ => (s - τ)⁻¹ * ∫ σ in τ..s,
      (∫ p : ℝ × ℝ, udot σ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2 ∂diaM))
      (nhdsWithin τ {τ}ᶜ)
      (nhds (∫ p : ℝ × ℝ, udot τ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2 ∂diaM)) :=
    tendsto_slope_interval_integral (diag_Rcont D) (diag_Rmeas D)
  have h3 : (∫ p : ℝ × ℝ, udot τ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2 ∂diaM)
      = diagQval ρ u udot τ := rfl
  rw [h3] at h2
  exact Tendsto.congr' hBident.symm h2


/-- **The difference quotient splits into the two remainders.** -/
theorem diag_DQ {ρ : ℝ → ℝ → ℝ} {u udot : ℝ → Work.FTS.Galerkin.Fn} {τ T : ℝ}
    (D : DiagData ρ u udot τ T) :
    slope (diagPfun ρ u) τ =ᶠ[nhdsWithin τ {τ}ᶜ]
      fun s => diagArem ρ u τ s + 2 * diagBrem ρ u τ s := by
  filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds D.hτ1 D.hτ2), self_mem_nhdsWithin] with s hs hsne
  have hIs : s ∈ Set.Icc (0 : ℝ) T := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
  have hsplit : diagPfun ρ u s - diagPfun ρ u τ = ∫ p : ℝ × ℝ, (u s p.1 p.2 * u s p.1 p.2 * ρ p.1 p.2
      - u τ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2) ∂diaM := by
    have h1 : diagPfun ρ u s = ∫ p : ℝ × ℝ, u s p.1 p.2 * u s p.1 p.2 * ρ p.1 p.2 ∂diaM := rfl
    have h2 : diagPfun ρ u τ = ∫ p : ℝ × ℝ, u τ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2 ∂diaM := rfl
    rw [h1, h2]
    exact (integral_sub (D.diag s hIs) (D.diag τ D.hτIcc)).symm
  have hsplit2 : (∫ p : ℝ × ℝ, (u s p.1 p.2 * u s p.1 p.2 * ρ p.1 p.2
      - u τ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2) ∂diaM)
      = ∫ p : ℝ × ℝ, ((u s p.1 p.2 - u τ p.1 p.2) * (u s p.1 p.2 - u τ p.1 p.2)
          * ρ p.1 p.2
          + 2 * (u τ p.1 p.2 * (u s p.1 p.2 - u τ p.1 p.2) * ρ p.1 p.2)) ∂diaM :=
    integral_congr_ae (Eventually.of_forall fun p => by ring)
  have hint1 : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (u s p.1 p.2 - u τ p.1 p.2) * (u s p.1 p.2 - u τ p.1 p.2) * ρ p.1 p.2) diaM :=
    integrable_sub_sq D.ρnn D.wmeas (G := fun p : ℝ × ℝ => u s p.1 p.2)
      (H := fun p : ℝ × ℝ => u τ p.1 p.2) (D.diag s hIs) (D.diag τ D.hτIcc)
      (D.umeas s hs) (D.umeas τ D.hτ)
  have hint2 : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      2 * (u τ p.1 p.2 * (u s p.1 p.2 - u τ p.1 p.2) * ρ p.1 p.2)) diaM :=
    (integrable_amgm_mul D.ρnn D.wmeas (G := fun p : ℝ × ℝ => u τ p.1 p.2)
      (H := fun p : ℝ × ℝ => u s p.1 p.2 - u τ p.1 p.2)
      (D.diag τ D.hτIcc)
      (integrable_sub_sq D.ρnn D.wmeas (D.diag s hIs) (D.diag τ D.hτIcc)
        (D.umeas s hs) (D.umeas τ D.hτ))
      (D.umeas τ D.hτ) ((D.umeas s hs).sub (D.umeas τ D.hτ))).const_mul 2
  have hsplit3 : (∫ p : ℝ × ℝ, ((u s p.1 p.2 - u τ p.1 p.2) * (u s p.1 p.2 - u τ p.1 p.2)
          * ρ p.1 p.2
          + 2 * (u τ p.1 p.2 * (u s p.1 p.2 - u τ p.1 p.2) * ρ p.1 p.2)) ∂diaM)
      = (∫ p : ℝ × ℝ, (u s p.1 p.2 - u τ p.1 p.2) * (u s p.1 p.2 - u τ p.1 p.2)
          * ρ p.1 p.2 ∂diaM)
        + 2 * (∫ p : ℝ × ℝ, u τ p.1 p.2 * (u s p.1 p.2 - u τ p.1 p.2) * ρ p.1 p.2 ∂diaM) := by
    rw [integral_add hint1 hint2, integral_const_mul]
  rw [slope_def_field, hsplit, hsplit2, hsplit3, diagArem, diagBrem]
  ring

end Work.FTS.StrongEps.EpsE4Thr
