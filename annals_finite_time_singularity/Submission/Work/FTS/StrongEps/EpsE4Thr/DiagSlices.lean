import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.EpsE4Thr.DiagAux

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

/-- **The a.e. Newton-Leibniz identity on the window and the slice integrabilities.** -/
theorem diag_ae_slices {ρ : ℝ → ℝ → ℝ} {u udot : ℝ → Work.FTS.Galerkin.Fn} {τ T : ℝ}
    (D : DiagData ρ u udot τ T) :
    ∀ᵐ p ∂diaM, ρ p.1 p.2 = 0 ∨
      (((∀ s ∈ Set.Ioo (τ - D.δ) (τ + D.δ),
          IntervalIntegrable (fun σ : ℝ => udot σ p.1 p.2) volume τ s) ∧
        (∀ s ∈ Set.Ioo (τ - D.δ) (τ + D.δ),
          IntervalIntegrable (fun σ : ℝ => udot σ p.1 p.2 * udot σ p.1 p.2) volume τ s)) ∧
        (∀ s ∈ Set.Ioo (τ - D.δ) (τ + D.δ),
          u s p.1 p.2 - u τ p.1 p.2 = ∫ σ in τ..s, udot σ p.1 p.2)) := by
  have hslice_meas : ∀ᵐ p ∂diaM, AEStronglyMeasurable (fun σ : ℝ => udot σ p.1 p.2) volume :=
    D.aesmd.prodMk_right
  have hfin_ae : ∀ᵐ p ∂diaM, ρ p.1 p.2 = 0 ∨
      (∫⁻ σ in Set.Ioc (τ - D.δ) (τ + D.δ), ENNReal.ofReal ((udot σ p.1 p.2) ^ 2)) < ⊤ :=
    ae_slice_lintegral_lt_top (V := udot) (ρ := ρ) (T := T) (a := τ - D.δ) (b := τ + D.δ)
      (K := D.K) D.δ_ab D.Ioc_mem D.aesmd.aemeasurable D.ρmeas D.ρnn D.diagd_sq D.bdd_sq
  filter_upwards [hslice_meas, hfin_ae, D.deriv] with p hsm hfp hd
  rcases hfp with h0 | hfp
  · exact Or.inl h0
  · have hsq : MeasureTheory.Integrable
        (fun σ : ℝ => udot σ p.1 p.2 * udot σ p.1 p.2)
        (MeasureTheory.volume.restrict (Set.Ioc (τ - D.δ) (τ + D.δ))) := by
      refine ⟨(hsm.mul hsm).mono_measure Measure.restrict_le_self, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      have h1 : ∀ σ : ℝ, ‖udot σ p.1 p.2 * udot σ p.1 p.2‖ₑ
          = ENNReal.ofReal ((udot σ p.1 p.2) ^ 2) := by
        intro σ
        rw [Real.enorm_eq_ofReal (mul_self_nonneg _), pow_two]
      rw [lintegral_congr h1]
      exact hfp
    have hV : MeasureTheory.Integrable (fun σ : ℝ => udot σ p.1 p.2)
        (MeasureTheory.volume.restrict (Set.Ioc (τ - D.δ) (τ + D.δ))) := by
      haveI : IsFiniteMeasure (MeasureTheory.volume.restrict (Set.Ioc (τ - D.δ) (τ + D.δ))) :=
        ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩
      have hdom : MeasureTheory.Integrable
          (fun σ : ℝ => (udot σ p.1 p.2 * udot σ p.1 p.2 + 1) / 2)
          (MeasureTheory.volume.restrict (Set.Ioc (τ - D.δ) (τ + D.δ))) :=
        (hsq.add (integrable_const (1 : ℝ))).div_const 2
      refine hdom.mono' (hsm.mono_measure Measure.restrict_le_self) ?_
      filter_upwards with σ
      have h2 : |udot σ p.1 p.2| ≤ (udot σ p.1 p.2 * udot σ p.1 p.2 + 1) / 2 := by
        nlinarith [sq_nonneg (|udot σ p.1 p.2| - 1), sq_abs (udot σ p.1 p.2)]
      rwa [Real.norm_eq_abs]
    have hVbase : IntervalIntegrable (fun σ : ℝ => udot σ p.1 p.2) volume (τ - D.δ) (τ + D.δ) := by
      rw [intervalIntegrable_iff]
      rw [Set.uIoc_of_le D.δ_ab]
      exact hV
    have hsqbase : IntervalIntegrable (fun σ : ℝ => udot σ p.1 p.2 * udot σ p.1 p.2) volume
        (τ - D.δ) (τ + D.δ) := by
      rw [intervalIntegrable_iff]
      rw [Set.uIoc_of_le D.δ_ab]
      exact hsq
    have hsub : ∀ s ∈ Set.Ioo (τ - D.δ) (τ + D.δ),
        Set.uIcc τ s ⊆ Set.uIcc (τ - D.δ) (τ + D.δ) := by
      intro s hs
      rw [Set.uIcc_of_le D.δ_ab, Set.uIcc]
      intro x hx
      rw [Set.mem_Icc] at hx
      have hm : τ - D.δ < min τ s := lt_min (by linarith [D.δ_pos]) hs.1
      have hM : max τ s < τ + D.δ := max_lt (by linarith [D.δ_pos]) hs.2
      exact ⟨by linarith [hm, hx.1], by linarith [hM, hx.2]⟩
    refine Or.inr ⟨⟨?_, ?_⟩, ?_⟩
    · intro s hs
      exact hVbase.mono_set (hsub s hs)
    · intro s hs
      exact hsqbase.mono_set (hsub s hs)
    · intro s hs
      have hInt : IntervalIntegrable (fun σ : ℝ => udot σ p.1 p.2) volume τ s :=
        hVbase.mono_set (hsub s hs)
      have hder : ∀ x ∈ Set.uIcc τ s,
          HasDerivAt (fun t : ℝ => u t p.1 p.2) (udot x p.1 p.2) x := by
        intro x hx
        have hx' : x ∈ Set.Icc (min τ s) (max τ s) := hx
        rw [Set.mem_Icc] at hx'
        have hm : τ - D.δ < min τ s := lt_min (by linarith [D.δ_pos]) hs.1
        have hM : max τ s < τ + D.δ := max_lt (by linarith [D.δ_pos]) hs.2
        exact hd x ⟨by linarith [hm, hx'.1, D.δ_pos'], by linarith [hM, hx'.2, D.δ_T]⟩
      exact (intervalIntegral.integral_eq_sub_of_hasDerivAt hder hInt).symm


/-- **The quadratic estimate on the window**: the square remainder is `O(|s - τ|²)`. -/
theorem diag_sq_est {ρ : ℝ → ℝ → ℝ} {u udot : ℝ → Work.FTS.Galerkin.Fn} {τ T : ℝ}
    (D : DiagData ρ u udot τ T)
    (hSlices : ∀ᵐ p ∂diaM, ρ p.1 p.2 = 0 ∨
      (((∀ s ∈ Set.Ioo (τ - D.δ) (τ + D.δ),
          IntervalIntegrable (fun σ : ℝ => udot σ p.1 p.2) volume τ s) ∧
        (∀ s ∈ Set.Ioo (τ - D.δ) (τ + D.δ),
          IntervalIntegrable (fun σ : ℝ => udot σ p.1 p.2 * udot σ p.1 p.2) volume τ s)) ∧
        (∀ s ∈ Set.Ioo (τ - D.δ) (τ + D.δ),
          u s p.1 p.2 - u τ p.1 p.2 = ∫ σ in τ..s, udot σ p.1 p.2))) :
    ∀ s ∈ Set.Ioo (τ - D.δ) (τ + D.δ),
      ∫ p : ℝ × ℝ,
          (u s p.1 p.2 - u τ p.1 p.2) * (u s p.1 p.2 - u τ p.1 p.2) * ρ p.1 p.2 ∂diaM
        ≤ |s - τ| * (D.K * |s - τ|) := by
  have hWprod : AEStronglyMeasurable (fun q : ℝ × (ℝ × ℝ) => ρ q.2.1 q.2.2)
      (MeasureTheory.volume.prod diaM) := D.wmeas.aestronglyMeasurable.comp_snd

  intro s hs
  have hs1 : (0 : ℝ) < s := (D.Ioo_mem hs).1
  have hs2 : s < T := (D.Ioo_mem hs).2
  have hm : τ - D.δ < min τ s := lt_min (by linarith [D.δ_pos]) hs.1
  have hM : max τ s < τ + D.δ := max_lt (by linarith [D.δ_pos]) hs.2
  have hIocmem : Set.uIoc τ s ⊆ Set.Icc (0 : ℝ) T := by
    intro x hx
    have hx' : x ∈ Set.Ioc (min τ s) (max τ s) := hx
    rw [Set.mem_Ioc] at hx'
    exact ⟨by linarith [hm, hx'.1, D.δ_pos'], by linarith [hM, hx'.2, D.δ_T]⟩
  have hIccmm : Set.Icc (min τ s) (max τ s) ⊆ Set.Icc (0 : ℝ) T := by
    intro x hx
    rw [Set.mem_Icc] at hx
    exact ⟨by linarith [hm, hx.1, D.δ_pos'], by linarith [hM, hx.2, D.δ_T]⟩
  -- integrability of the uncurried squared family
  haveI : IsFiniteMeasure (MeasureTheory.volume.restrict (Set.uIoc τ s)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_uIoc]; exact ENNReal.ofReal_lt_top⟩
  have huncurry : MeasureTheory.Integrable
      (Function.uncurry (fun σ (p : ℝ × ℝ) => udot σ p.1 p.2 * udot σ p.1 p.2 * ρ p.1 p.2))
      ((MeasureTheory.volume.restrict (Set.uIoc τ s)).prod diaM) := by
    refine (integrable_prod_iff ?_).mpr ⟨?_, ?_⟩
    · exact ((D.aesmd.mul D.aesmd).mul hWprod).mono_measure
        (Measure.prod_mono Measure.restrict_le_self le_rfl)
    · filter_upwards [ae_restrict_mem (measurableSet_uIoc (a := τ) (b := s))] with σ hσ
      have hσ' : σ ∈ Set.Ioc (min τ s) (max τ s) := hσ
      rw [Set.mem_Ioc] at hσ'
      exact D.diagd σ (hIccmm ⟨le_of_lt hσ'.1, hσ'.2⟩)
    · have hmeasn : AEStronglyMeasurable (fun σ : ℝ => ∫ p : ℝ × ℝ,
          ‖udot σ p.1 p.2 * udot σ p.1 p.2 * ρ p.1 p.2‖ ∂diaM)
          (MeasureTheory.volume.restrict (Set.uIoc τ s)) :=
        ((D.aesmd.mul D.aesmd).mul hWprod).norm.integral_prod_right'.mono_measure
          Measure.restrict_le_self
      refine (integrable_const D.K).mono' hmeasn ?_
      filter_upwards [ae_restrict_mem (measurableSet_uIoc (a := τ) (b := s))] with σ hσ
      have hσ' : σ ∈ Set.Ioc (min τ s) (max τ s) := hσ
      rw [Set.mem_Ioc] at hσ'
      have hσIcc : σ ∈ Set.Icc (0 : ℝ) T := hIccmm ⟨le_of_lt hσ'.1, hσ'.2⟩
      have h1 : (∫ y : ℝ × ℝ, ‖Function.uncurry (fun σ (p : ℝ × ℝ) =>
            udot σ p.1 p.2 * udot σ p.1 p.2 * ρ p.1 p.2) (σ, y)‖ ∂diaM)
          = ∫ y : ℝ × ℝ, udot σ y.1 y.2 * udot σ y.1 y.2 * ρ y.1 y.2 ∂diaM := by
        change (∫ y : ℝ × ℝ, ‖udot σ y.1 y.2 * udot σ y.1 y.2 * ρ y.1 y.2‖ ∂diaM)
          = ∫ y : ℝ × ℝ, udot σ y.1 y.2 * udot σ y.1 y.2 * ρ y.1 y.2 ∂diaM
        refine integral_congr_ae ?_
        filter_upwards [D.ρnn] with y hy
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_self_nonneg _) hy)]
      have h2 : 0 ≤ ∫ y : ℝ × ℝ, udot σ y.1 y.2 * udot σ y.1 y.2 * ρ y.1 y.2 ∂diaM :=
        integral_nonneg_of_ae (D.ρnn.mono (fun p hp => mul_nonneg (mul_self_nonneg _) hp))
      rw [Real.norm_eq_abs, h1, abs_of_nonneg h2]
      exact D.bdd σ hσIcc
  have hmarg : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => ∫ σ, udot σ p.1 p.2 * udot σ p.1 p.2 * ρ p.1 p.2
        ∂(MeasureTheory.volume.restrict (Set.uIoc τ s))) diaM :=
    huncurry.integral_prod_right
  have hfub : (∫ p : ℝ × ℝ, (∫ σ, udot σ p.1 p.2 * udot σ p.1 p.2 * ρ p.1 p.2
          ∂(MeasureTheory.volume.restrict (Set.uIoc τ s))) ∂diaM)
      = ∫ σ, (∫ p : ℝ × ℝ, udot σ p.1 p.2 * udot σ p.1 p.2 * ρ p.1 p.2 ∂diaM)
          ∂(MeasureTheory.volume.restrict (Set.uIoc τ s)) := by
    exact MeasureTheory.integral_integral_swap huncurry.swap
  haveI : IsFiniteMeasure (MeasureTheory.volume.restrict (Set.uIoc τ s)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_uIoc]; exact ENNReal.ofReal_lt_top⟩
  have hbound : (∫ σ, (∫ p : ℝ × ℝ, udot σ p.1 p.2 * udot σ p.1 p.2 * ρ p.1 p.2 ∂diaM)
          ∂(MeasureTheory.volume.restrict (Set.uIoc τ s))) ≤ D.K * |s - τ| := by
    have hnn : (fun _ : ℝ => (0 : ℝ)) ≤ᵐ[MeasureTheory.volume.restrict (Set.uIoc τ s)]
        (fun σ => ∫ p : ℝ × ℝ, udot σ p.1 p.2 * udot σ p.1 p.2 * ρ p.1 p.2 ∂diaM) := by
      filter_upwards with σ
      exact integral_nonneg_of_ae (D.ρnn.mono (fun p hp => mul_nonneg (mul_self_nonneg _) hp))
    calc (∫ σ, (∫ p : ℝ × ℝ, udot σ p.1 p.2 * udot σ p.1 p.2 * ρ p.1 p.2 ∂diaM)
            ∂(MeasureTheory.volume.restrict (Set.uIoc τ s)))
        ≤ ∫ σ, D.K ∂(MeasureTheory.volume.restrict (Set.uIoc τ s)) := by
          refine integral_mono_of_nonneg hnn (integrable_const D.K) ?_
          filter_upwards [ae_restrict_mem (measurableSet_uIoc (a := τ) (b := s))] with σ hσ
          exact D.bdd σ (hIocmem hσ)
      _ = D.K * |s - τ| := by
          rw [integral_const]
          simp only [Measure.real, Measure.restrict_apply_univ, Real.volume_uIoc,
            ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul]
          ring
  have hpt : ∀ᵐ p ∂diaM,
      (u s p.1 p.2 - u τ p.1 p.2) * (u s p.1 p.2 - u τ p.1 p.2) * ρ p.1 p.2
        ≤ |s - τ| * (∫ σ, udot σ p.1 p.2 * udot σ p.1 p.2 * ρ p.1 p.2
            ∂(MeasureTheory.volume.restrict (Set.uIoc τ s))) := by
    filter_upwards [hSlices, D.ρnn] with p hS hp
    rcases hS with h0 | ⟨⟨hIV, hIsq⟩, hNL⟩
    · have hzero : (∫ σ in Set.uIoc τ s, udot σ p.1 p.2 * udot σ p.1 p.2 * ρ p.1 p.2) = 0 := by
        rw [show (fun σ : ℝ => udot σ p.1 p.2 * udot σ p.1 p.2 * ρ p.1 p.2)
            = fun _ : ℝ => (0 : ℝ) from by funext σ; rw [h0]; ring]
        simp
      rw [hzero, h0]
      simp
    · have hNLp := hNL s hs
      have hVmem : MeasureTheory.Integrable (fun σ : ℝ => udot σ p.1 p.2)
          (MeasureTheory.volume.restrict (Set.uIoc τ s)) := intervalIntegrable_iff.mp (hIV s hs)
      have hsqmem : MeasureTheory.Integrable (fun σ : ℝ => udot σ p.1 p.2 * udot σ p.1 p.2)
          (MeasureTheory.volume.restrict (Set.uIoc τ s)) := intervalIntegrable_iff.mp (hIsq s hs)
      have hf1 : MeasureTheory.Integrable (fun x : ℝ => udot x p.1 p.2 * udot x p.1 p.2 * (1 : ℝ))
          (MeasureTheory.volume.restrict (Set.uIoc τ s)) := by
        refine hsqmem.congr ?_
        filter_upwards with x
        ring
      have hg1 : MeasureTheory.Integrable (fun x : ℝ => (1 : ℝ) * 1 * 1)
          (MeasureTheory.volume.restrict (Set.uIoc τ s)) := by
        refine (integrable_const (1 : ℝ)).congr ?_
        filter_upwards with x
        ring
      have hfg1 : MeasureTheory.Integrable (fun x : ℝ => udot x p.1 p.2 * 1 * 1)
          (MeasureTheory.volume.restrict (Set.uIoc τ s)) := by
        refine hVmem.congr ?_
        filter_upwards with x
        ring
      have hcs0 := cs_diag (μ := MeasureTheory.volume.restrict (Set.uIoc τ s))
        (ρ := fun _ : ℝ => (1 : ℝ)) (f := fun x : ℝ => udot x p.1 p.2)
        (g := fun _ : ℝ => (1 : ℝ)) (Eventually.of_forall fun _ => zero_le_one)
        hf1 hg1 hfg1
      have hconst : (∫ σ : ℝ, (1 : ℝ) * 1 * 1 ∂(MeasureTheory.volume.restrict (Set.uIoc τ s)))
          = |s - τ| := by
        rw [show (fun _ : ℝ => (1 : ℝ) * 1 * 1) = fun _ : ℝ => (1 : ℝ) from by funext; ring]
        rw [integral_const]
        simp only [Measure.real, Measure.restrict_apply_univ, Real.volume_uIoc,
          ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul]
        ring
      have hleft : (∫ σ : ℝ, udot σ p.1 p.2 * 1 * 1
          ∂(MeasureTheory.volume.restrict (Set.uIoc τ s)))
          = ∫ σ : ℝ, udot σ p.1 p.2 ∂(MeasureTheory.volume.restrict (Set.uIoc τ s)) :=
        integral_congr_ae (Eventually.of_forall fun σ => by ring)
      have hright : (∫ σ : ℝ, udot σ p.1 p.2 * udot σ p.1 p.2 * 1
          ∂(MeasureTheory.volume.restrict (Set.uIoc τ s)))
          = ∫ σ : ℝ, udot σ p.1 p.2 * udot σ p.1 p.2
              ∂(MeasureTheory.volume.restrict (Set.uIoc τ s)) :=
        integral_congr_ae (Eventually.of_forall fun σ => by ring)
      rw [hleft, hright, hconst] at hcs0
      have hcsσ : (∫ σ : ℝ, udot σ p.1 p.2 ∂(MeasureTheory.volume.restrict (Set.uIoc τ s))) ^ 2
          ≤ |s - τ| * (∫ σ : ℝ, udot σ p.1 p.2 * udot σ p.1 p.2
              ∂(MeasureTheory.volume.restrict (Set.uIoc τ s))) := by
        linarith [hcs0]
      have hinterval : (∫ σ in τ..s, udot σ p.1 p.2) ^ 2
          = (∫ σ : ℝ, udot σ p.1 p.2 ∂(MeasureTheory.volume.restrict (Set.uIoc τ s))) ^ 2 := by
        rcases le_total τ s with hle | hle
        · rw [intervalIntegral.integral_of_le hle, Set.uIoc_of_le hle]
        · rw [intervalIntegral.integral_of_ge hle, Set.uIoc_of_ge hle, neg_sq]
      have hstepX : (∫ σ : ℝ, udot σ p.1 p.2 * udot σ p.1 p.2
            ∂(MeasureTheory.volume.restrict (Set.uIoc τ s))) * ρ p.1 p.2
          = ∫ σ, udot σ p.1 p.2 * udot σ p.1 p.2 * ρ p.1 p.2
            ∂(MeasureTheory.volume.restrict (Set.uIoc τ s)) := by
        rw [← integral_mul_const (r := ρ p.1 p.2)
          (f := fun σ : ℝ => udot σ p.1 p.2 * udot σ p.1 p.2)]
      have hstep : (|s - τ| * (∫ σ : ℝ, udot σ p.1 p.2 * udot σ p.1 p.2
            ∂(MeasureTheory.volume.restrict (Set.uIoc τ s)))) * ρ p.1 p.2
          = |s - τ| * (∫ σ, udot σ p.1 p.2 * udot σ p.1 p.2 * ρ p.1 p.2
            ∂(MeasureTheory.volume.restrict (Set.uIoc τ s))) := by
        rw [mul_assoc, hstepX]
      calc (u s p.1 p.2 - u τ p.1 p.2) * (u s p.1 p.2 - u τ p.1 p.2) * ρ p.1 p.2
          = (∫ σ in τ..s, udot σ p.1 p.2) * (∫ σ in τ..s, udot σ p.1 p.2) * ρ p.1 p.2 := by
            rw [hNLp]
        _ = (∫ σ : ℝ, udot σ p.1 p.2 ∂(MeasureTheory.volume.restrict (Set.uIoc τ s))) ^ 2
              * ρ p.1 p.2 := by
            rw [show (∫ σ in τ..s, udot σ p.1 p.2) * (∫ σ in τ..s, udot σ p.1 p.2)
                = (∫ σ in τ..s, udot σ p.1 p.2) ^ 2 from by ring, hinterval]
        _ ≤ (|s - τ| * (∫ σ : ℝ, udot σ p.1 p.2 * udot σ p.1 p.2
              ∂(MeasureTheory.volume.restrict (Set.uIoc τ s)))) * ρ p.1 p.2 :=
            mul_le_mul_of_nonneg_right hcsσ hp
        _ = |s - τ| * (∫ σ, udot σ p.1 p.2 * udot σ p.1 p.2 * ρ p.1 p.2
              ∂(MeasureTheory.volume.restrict (Set.uIoc τ s))) := hstep
  have hint_lhs : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (u s p.1 p.2 - u τ p.1 p.2) * (u s p.1 p.2 - u τ p.1 p.2) * ρ p.1 p.2) diaM :=
    integrable_sub_sq D.ρnn D.wmeas (G := fun p : ℝ × ℝ => u s p.1 p.2)
      (H := fun p : ℝ × ℝ => u τ p.1 p.2)
      (D.diag s ⟨le_of_lt hs1, le_of_lt hs2⟩) (D.diag τ D.hτIcc)
      (D.umeas s (D.Ioo_mem hs)) (D.umeas τ D.hτ)
  calc ∫ p : ℝ × ℝ,
          (u s p.1 p.2 - u τ p.1 p.2) * (u s p.1 p.2 - u τ p.1 p.2) * ρ p.1 p.2 ∂diaM
      ≤ ∫ p : ℝ × ℝ, |s - τ| * (∫ σ, udot σ p.1 p.2 * udot σ p.1 p.2 * ρ p.1 p.2
              ∂(MeasureTheory.volume.restrict (Set.uIoc τ s))) ∂diaM :=
        integral_mono_ae hint_lhs (hmarg.const_mul |s - τ|) hpt
    _ = |s - τ| * (∫ p : ℝ × ℝ, (∫ σ, udot σ p.1 p.2 * udot σ p.1 p.2 * ρ p.1 p.2
              ∂(MeasureTheory.volume.restrict (Set.uIoc τ s))) ∂diaM) := by
        rw [integral_const_mul]
    _ = |s - τ| * (∫ σ, (∫ p : ℝ × ℝ,
            udot σ p.1 p.2 * udot σ p.1 p.2 * ρ p.1 p.2 ∂diaM)
              ∂(MeasureTheory.volume.restrict (Set.uIoc τ s))) := by rw [hfub]
    _ ≤ |s - τ| * (D.K * |s - τ|) := mul_le_mul_of_nonneg_left hbound (abs_nonneg _)


end Work.FTS.StrongEps.EpsE4Thr
