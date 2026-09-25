import Mathlib
import Submission.Work.NN.Core.TelTwoDF.analyticOn_integral_of_bounded_support
import Submission.Work.NN.Core.TelTwoDF.analyticOn_integral_disc_tsupport
import Submission.Work.NN.Core.TelTwoDF.dbarTransform_eq_ball
import Submission.Work.NN.Core.TelTwoDF.sharpCut_dbar_props
import Submission.Work.NN.Core.TelTwoDF.analyticOn_update_comp
import Submission.Work.NN.Core.sharpCut
import Submission.Work.NN.Ratio.Cut
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Cauchy.openSolDefs

namespace Work.NN.Core.TelTwoDF

open MeasureTheory Set Metric

theorem analyticOn_dbarTransform_dbarC_sharpCut_mul {n : ℕ} (s : Fin n) {a b r : ℝ}
    (ha : 0 < a) (hab : a < b) (hbr : b ≤ r / 2)
    {Q ρ' : Fin n → ℝ} (hQ : ∀ k, 0 < Q k) (hbQ : b < Q s) (hρ'a : ρ' s < a)
    (hρ'Q : ∀ k, k ≠ s → ρ' k < Q k)
    {D : (Fin n → ℂ) → ℂ} (hD : AnalyticOn ℝ D (Work.CR.Flat.polydisc 0 Q)) (hDc : Continuous D) :
    AnalyticOn ℝ (fun z : Fin n → ℂ => Work.CR.Flat.Cauchy.dbarTransform r s
        (fun y => Work.CR.Flat.dbarC (Work.NN.Core.sharpCut a b) (y s) * D y) z)
      (Work.CR.Flat.polydisc 0 ρ') := by
  classical
  have ha0 : (0 : ℝ) ≤ a := ha.le
  set kbar : ℂ → ℂ := Work.CR.Flat.dbarC (Work.NN.Core.sharpCut a b) with hkbareq
  have hkbar_cont : Continuous kbar := by
    rw [hkbareq]; exact (contDiff_dbarC_sharpCut a b).continuous
  have hkbar_cs : HasCompactSupport kbar := by
    rw [hkbareq, dbarC_sharpCut_eq]
    exact Work.NN.Ratio.hasCompactSupport_dbarC_rCut ha0 hab
  have hkbar_in : ∀ ζ : ℂ, ‖ζ‖ ≤ a → kbar ζ = 0 := by
    intro ζ hζ
    rw [hkbareq, dbarC_sharpCut_eq]
    exact Work.NN.Ratio.dbarC_rCut_eq_zero_of_norm_le ha0 hab hζ
  have hkbar_out : ∀ ζ : ℂ, b ≤ ‖ζ‖ → kbar ζ = 0 := by
    intro ζ hζ
    rw [hkbareq, dbarC_sharpCut_eq]
    exact Work.NN.Ratio.dbarC_rCut_eq_zero_of_le_norm ha0 hab hζ
  -- geometry
  set c : ℝ := (a + ρ' s) / 2 with hcdef
  set c' : ℝ := (b + Q s) / 2 with hc'def
  have hρ's_lt_c : ρ' s < c := by rw [hcdef]; linarith
  have hc_lt_a : c < a := by rw [hcdef]; linarith
  have hb_lt_c' : b < c' := by rw [hc'def]; linarith
  have hc'_lt_Qs : c' < Q s := by rw [hc'def]; linarith
  set U : Set ℂ := {ζ : ℂ | c < ‖ζ‖ ∧ ‖ζ‖ < c'} with hUdef
  have hU_open : IsOpen U := by
    have hEq : U = {ζ : ℂ | c < ‖ζ‖} ∩ {ζ : ℂ | ‖ζ‖ < c'} := by
      ext ζ; simp [hUdef, and_comm]
    rw [hEq]
    exact (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  have hts_sub : tsupport kbar ⊆ U := by
    have hS_closed : IsClosed {ζ : ℂ | a ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ b} := by
      have hEq : {ζ : ℂ | a ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ b} = {ζ : ℂ | a ≤ ‖ζ‖} ∩ {ζ : ℂ | ‖ζ‖ ≤ b} := by
        ext ζ; simp
      rw [hEq]
      exact (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
    have hsupp : Function.support kbar ⊆ {ζ : ℂ | a ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ b} := by
      intro ζ hζ
      exact ⟨le_of_lt (not_le.mp (fun h => hζ (hkbar_in ζ h))),
             le_of_lt (not_le.mp (fun h => hζ (hkbar_out ζ h)))⟩
    have hSU : {ζ : ℂ | a ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ b} ⊆ U := by
      intro ζ hζ
      simp only [hUdef, Set.mem_ofPred_eq] at hζ ⊢
      exact ⟨by linarith [hζ.1, hc_lt_a], by linarith [hζ.2, hb_lt_c']⟩
    exact (closure_minimal hsupp hS_closed).trans hSU
  -- analyticity of the integrand
  have hρ'leQ : ∀ k, ρ' k ≤ Q k := by
    intro k
    by_cases hk : k = s
    · subst hk; linarith [hρ'a, hab, hbQ]
    · exact le_of_lt (hρ'Q k hk)
  have hbase : AnalyticOn ℝ (fun p : (Fin n → ℂ) × ℂ => D (Function.update p.1 s p.2))
      (Work.CR.Flat.polydisc 0 ρ' ×ˢ U) := by
    refine (analyticOn_update_comp s (hQ s) hD).mono ?_
    intro p hp
    refine ⟨Work.CR.Flat.polydisc_mono hρ'leQ hp.1, ?_⟩
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    exact lt_trans hp.2.2 hc'_lt_Qs
  have hsub : AnalyticOn ℝ (fun p : (Fin n → ℂ) × ℂ => p.2 - p.1 s)
      (Work.CR.Flat.polydisc 0 ρ' ×ˢ U) := by
    refine AnalyticOn.congr (ContinuousLinearMap.analyticOn
      ((ContinuousLinearMap.snd ℝ (Fin n → ℂ) ℂ) -
        ((ContinuousLinearMap.proj (R := ℝ) s).comp
          (ContinuousLinearMap.fst ℝ (Fin n → ℂ) ℂ))) _) ?_
    intro p _
    simp
  have hinv : AnalyticOn ℝ (fun p : (Fin n → ℂ) × ℂ => (p.2 - p.1 s)⁻¹)
      (Work.CR.Flat.polydisc 0 ρ' ×ˢ U) := by
    refine hsub.inv (fun p hp => ?_)
    intro hzero
    have hpeq : p.2 = p.1 s := sub_eq_zero.mp hzero
    have h1 : ‖p.1 s‖ < ρ' s := by simpa using hp.1 s
    have h2 : c < ‖p.2‖ := hp.2.1
    rw [hpeq] at h2
    linarith [hρ's_lt_c]
  have hF_an : AnalyticOn ℝ
      (fun p : (Fin n → ℂ) × ℂ => D (Function.update p.1 s p.2) * (p.2 - p.1 s)⁻¹)
      (Work.CR.Flat.polydisc 0 ρ' ×ˢ U) := hbase.mul hinv
  have hAnInt : AnalyticOn ℝ
      (fun z : Fin n → ℂ => ∫ w, kbar w * (D (Function.update z s w) * (w - z s)⁻¹))
      (Work.CR.Flat.polydisc 0 ρ') :=
    analyticOn_integral_disc_tsupport hkbar_cont hkbar_cs hU_open hts_sub
      (Work.CR.Flat.isOpen_polydisc 0 ρ') hF_an
  -- the pointwise identity
  have hg_cont : Continuous (fun y : Fin n → ℂ => kbar (y s) * D y) :=
    (hkbar_cont.comp (continuous_apply s)).mul hDc
  refine ((analyticOn_const (v := -((Real.pi : ℂ))⁻¹)).mul hAnInt).congr ?_
  intro z hz
  change Work.CR.Flat.Cauchy.dbarTransform r s (fun y => kbar (y s) * D y) z
      = -((Real.pi : ℂ))⁻¹ * ∫ w, kbar w * (D (Function.update z s w) * (w - z s)⁻¹)
  rw [dbarTransform_eq_ball s hg_cont z]
  have hIntEq : (∫ ζ in Metric.ball (z s) r,
        (fun y : Fin n → ℂ => kbar (y s) * D y) (Function.update z s ζ) / (ζ - z s))
      = (∫ w, kbar w * (D (Function.update z s w) * (w - z s)⁻¹)) := by
    have hstep1 : (∫ ζ in Metric.ball (z s) r,
          (fun y : Fin n → ℂ => kbar (y s) * D y) (Function.update z s ζ) / (ζ - z s))
        = ∫ ζ in Metric.ball (z s) r, kbar ζ * (D (Function.update z s ζ) * (ζ - z s)⁻¹) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_ball (fun ζ _ => ?_)
      simp only [Function.update_self]
      ring
    rw [hstep1]
    refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_)
    intro ζ hζ
    have hz0 : kbar ζ = 0 := by
      by_contra hne
      have hζb : ‖ζ‖ < b := not_le.mp (fun hb => hne (hkbar_out ζ hb))
      have hmem : ζ ∈ Metric.ball (z s) r := by
        rw [Metric.mem_ball, dist_eq_norm]
        have hzsz : ‖z s‖ < ρ' s := by simpa using hz s
        have h1 : ‖ζ - z s‖ ≤ ‖ζ‖ + ‖z s‖ := norm_sub_le ζ (z s)
        have hbr2 : 2 * b ≤ r := by linarith [hbr]
        nlinarith [h1, hζb, hzsz, hρ'a, hab, hbr2]
      exact hζ hmem
    rw [hz0, zero_mul]
  rw [hIntEq]

end Work.NN.Core.TelTwoDF
