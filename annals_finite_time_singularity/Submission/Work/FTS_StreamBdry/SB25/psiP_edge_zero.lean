import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB25.Defs
import Submission.Work.FTS_StreamBdry.SB1.Engine
import Submission.Work.FTS_StreamBdry.SB1.psiP_ode
import Submission.Work.FTS_StreamBdry.SB3.psiP_c2
import Submission.Work.FTS_StreamBdry.SB3.psiP_DzLe
import Submission.Work.FTS_StreamBdry.SB3.psiP_D3_le
import Submission.Work.FTS_StreamBdry.SB3.pth_DzIter_le
import Submission.Work.FTS_StreamBdry.SB3.law_psiP
import Submission.Work.FTS_StreamBdry.SB25.lip_edge_trace
import Submission.Work.FTS_StreamBdry.SB25.axis_tan_bound
import Submission.Work.FTS_StreamBdry.SB25.axis_d2_bound
import Submission.Work.FTS_StreamBdry.SB25.pze_aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-! Helper lemmas (`pze_*`): `Submission/Work/FTS_StreamBdry/SB25/pze_aux.lean`. -/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB25

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK)
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false


theorem psiP_edge_zero {αG M L Mf : ℝ} (hαG : 0 < αG) {F Ψ : ℝ → ℝ → ℝ} :
    Work.FTS_StreamBdry.SB25.PsiPEdgeZero αG M L Mf F Ψ := by
  intro hsol h3 hslot hF hK' z0 hz0
  dsimp only
  set P : ℝ → ℝ → ℝ := Work.FTS.StreamBdryIface.psiP αG Ψ with hP
  obtain ⟨K', hK'b⟩ := hK'
  have hQd := Work.FTS_StreamBdry.SB1.isOpen_Qd
  have hQdd : ((1 : ℝ), Real.pi / 4) ∈ Work.Construction.Qd :=
    Work.FTS_StreamBdry.SB1.Qd_nonempty
  have hθmem : (Real.pi / 4 : ℝ) ∈ Work.Spaces.Iθ :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hMnn : 0 ≤ M := le_trans (abs_nonneg _) (SlotBd.Uprime_le hslot hQdd)
  have hMfnn : 0 ≤ Mf := le_trans (abs_nonneg _) (SrcOK.F_le hF (z := 1) (by norm_num) hθmem)
  have hP2 : ContDiffOn ℝ 2 (Function.uncurry P) Work.Construction.Qd := by
    have h := Work.FTS_StreamBdry.SB3.psiP_c2 (αG := αG) (M := M) (Ψ := Ψ) hαG h3 hslot
    simpa only [← hP] using h
  have hDzLeP : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → ∀ j, j ≤ 2 →
      |Work.Spaces.DzIter j P z θ| ≤ M * Work.Construction.s2 θ := by
    intro z θ hmem j hj
    have h := Work.FTS_StreamBdry.SB3.psiP_DzLe (αG := αG) (M := M) (Ψ := Ψ)
      hαG h3 hslot z θ hmem j hj
    rw [← hP] at h
    exact h
  have hVopeq : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.Vop P z θ = Work.Construction.Vop Ψ z θ := by
    intro z θ hmem
    have h := Work.FTS_StreamBdry.SB3.Vop_psiP_eq (αG := αG) (M := M) (Ψ := Ψ) hαG h3 hslot
      z θ hmem
    rw [← hP] at h
    exact h
  have hlaw : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.pth (Work.Construction.Vop P) z θ
        = -(αG ^ 2 * Work.Spaces.DzIter 2 P z θ + 5 * αG * Work.Spaces.Dz P z θ
            + 6 * P z θ) - F z θ := by
    intro z θ hmem
    have h := Work.FTS_StreamBdry.SB3.law_psiP (αG := αG) (M := M) (F := F) (Ψ := Ψ)
      hαG hsol h3 hslot z θ hmem
    rw [← hP] at h
    exact h
  have hpzsplit : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.pz (Work.Spaces.pth P) z θ
        = Work.Spaces.pz (Work.Construction.Vop Ψ) z θ
          + Real.tan θ * Work.Spaces.pz P z θ := by
    intro z θ hmem
    have h := Work.FTS_StreamBdry.SB3.pz_pth_psiP_eq (αG := αG) (M := M) (Ψ := Ψ)
      hαG h3 hslot hmem
    rw [← hP] at h
    exact h
  have h1 : Filter.Tendsto (Function.uncurry P) (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 0) := by
    refine pze_tendsto_zero_of_eventually_le (u := fun θ => M * Work.Construction.s2 θ) ?_ ?_ ?_
    · simp only [Work.Construction.s2]
      fun_prop
    · simp
    · refine pze_eventually_of_mem_Qd (fun z θ hmem => ?_)
      have h := hDzLeP z θ hmem 0 (by norm_num)
      simpa only [Work.Spaces.DzIter_zero, Function.uncurry] using h
  have h2 : Filter.Tendsto (Function.uncurry (Work.Spaces.pz P))
      (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 0) := by
    refine pze_tendsto_zero_of_eventually_le (u := fun θ => (2 * M / z0) * Work.Construction.s2 θ)
      ?_ ?_ ?_
    · simp only [Work.Construction.s2]
      fun_prop
    · simp
    · filter_upwards [self_mem_nhdsWithin, pze_eventually_fst_gt hz0] with p hp hpz
      show |Work.Spaces.pz P p.1 p.2| ≤ (2 * M / z0) * Work.Construction.s2 p.2
      have hz1 : 0 < p.1 := pze_pos_fst hp
      have hb : |Work.Spaces.DzIter 1 P p.1 p.2| ≤ M * Work.Construction.s2 p.2 :=
        hDzLeP p.1 p.2 hp 1 (by norm_num)
      have hMz : 0 ≤ M * Work.Construction.s2 p.2 := mul_nonneg hMnn (pze_s2_nonneg hp)
      have hpzeq : Work.Spaces.pz P p.1 p.2 = Work.Spaces.DzIter 1 P p.1 p.2 / p.1 := by
        rw [show Work.Spaces.DzIter 1 P p.1 p.2 = p.1 * Work.Spaces.pz P p.1 p.2 from rfl,
          mul_div_cancel_left₀ _ (ne_of_gt hz1)]
      rw [hpzeq, abs_div, abs_of_pos hz1]
      calc |Work.Spaces.DzIter 1 P p.1 p.2| / p.1
          ≤ (M * Work.Construction.s2 p.2) / p.1 := div_le_div_of_nonneg_right hb hz1.le
        _ = (M * Work.Construction.s2 p.2) * (1 / p.1) := by ring
        _ ≤ (M * Work.Construction.s2 p.2) * (1 / (z0 / 2)) :=
            mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (by linarith) hpz.le) hMz
        _ = (2 * M / z0) * Work.Construction.s2 p.2 := by
            field_simp
            try ring
  have h3c : Filter.Tendsto (Function.uncurry (Work.Spaces.pz (Work.Spaces.pz P)))
      (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 0) := by
    refine pze_tendsto_zero_of_eventually_le (u := fun θ => (8 * M / z0 ^ 2) * Work.Construction.s2 θ)
      ?_ ?_ ?_
    · simp only [Work.Construction.s2]
      fun_prop
    · simp
    · filter_upwards [self_mem_nhdsWithin, pze_eventually_fst_gt hz0] with p hp hpz
      show |Work.Spaces.pz (Work.Spaces.pz P) p.1 p.2|
        ≤ (8 * M / z0 ^ 2) * Work.Construction.s2 p.2
      have hz1 : 0 < p.1 := pze_pos_fst hp
      have hz2 : 0 < p.1 ^ 2 := pow_pos hz1 2
      have hb1 : |Work.Spaces.DzIter 1 P p.1 p.2| ≤ M * Work.Construction.s2 p.2 :=
        hDzLeP p.1 p.2 hp 1 (by norm_num)
      have hb2 : |Work.Spaces.DzIter 2 P p.1 p.2| ≤ M * Work.Construction.s2 p.2 :=
        hDzLeP p.1 p.2 hp 2 (by norm_num)
      have hMz : 0 ≤ M * Work.Construction.s2 p.2 := mul_nonneg hMnn (pze_s2_nonneg hp)
      have hnum : |Work.Spaces.DzIter 2 P p.1 p.2 - Work.Spaces.DzIter 1 P p.1 p.2|
          ≤ 2 * (M * Work.Construction.s2 p.2) := by
        have h := abs_sub_le (Work.Spaces.DzIter 2 P p.1 p.2) 0
          (Work.Spaces.DzIter 1 P p.1 p.2)
        simp only [sub_zero, zero_sub, abs_neg] at h
        linarith
      have h2Mz : 0 ≤ 2 * (M * Work.Construction.s2 p.2) := by linarith
      rw [pze_pz_pz_eq hP2 hp, abs_div, abs_of_pos hz2]
      calc |Work.Spaces.DzIter 2 P p.1 p.2 - Work.Spaces.DzIter 1 P p.1 p.2| / p.1 ^ 2
          ≤ (2 * (M * Work.Construction.s2 p.2)) / p.1 ^ 2 :=
            div_le_div_of_nonneg_right hnum hz2.le
        _ = (2 * (M * Work.Construction.s2 p.2)) * (1 / p.1 ^ 2) := by ring
        _ ≤ (2 * (M * Work.Construction.s2 p.2)) * (1 / (z0 / 2) ^ 2) :=
            mul_le_mul_of_nonneg_left
              (one_div_le_one_div_of_le (by positivity) (by nlinarith [hpz])) h2Mz
        _ = (8 * M / z0 ^ 2) * Work.Construction.s2 p.2 := by
            field_simp
            try ring
  have hA : Filter.Tendsto (fun p : ℝ × ℝ => -(αG ^ 2 * Work.Spaces.DzIter 2 P p.1 p.2
      + 5 * αG * Work.Spaces.Dz P p.1 p.2 + 6 * P p.1 p.2))
      (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 0) := by
    refine pze_tendsto_zero_of_eventually_le
      (u := fun θ => ((αG ^ 2 + 5 * αG + 6) * M) * Work.Construction.s2 θ) ?_ ?_ ?_
    · simp only [Work.Construction.s2]
      fun_prop
    · simp
    · refine pze_eventually_of_mem_Qd (fun z θ hmem => ?_)
      have h0 : |P z θ| ≤ M * Work.Construction.s2 θ := by
        have h := hDzLeP z θ hmem 0 (by norm_num)
        simpa only [Work.Spaces.DzIter_zero] using h
      have h1 := hDzLeP z θ hmem 1 (by norm_num)
      have h2 := hDzLeP z θ hmem 2 (by norm_num)
      rw [abs_neg]
      have e1 : |αG ^ 2 * Work.Spaces.DzIter 2 P z θ| ≤ αG ^ 2 * (M * Work.Construction.s2 θ) := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ αG ^ 2)]
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
      have e2 : |5 * αG * Work.Spaces.Dz P z θ| ≤ 5 * αG * (M * Work.Construction.s2 θ) := by
        rw [show (5:ℝ) * αG * Work.Spaces.Dz P z θ
            = ((5:ℝ) * αG) * Work.Spaces.Dz P z θ from by ring,
          abs_mul, abs_of_nonneg (by nlinarith [hαG])]
        exact mul_le_mul_of_nonneg_left h1 (by nlinarith [hαG])
      have e3 : |6 * P z θ| ≤ 6 * (M * Work.Construction.s2 θ) := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 6)]
        exact mul_le_mul_of_nonneg_left h0 (by norm_num)
      have e4 : |αG ^ 2 * Work.Spaces.DzIter 2 P z θ + 5 * αG * Work.Spaces.Dz P z θ
          + 6 * P z θ| ≤ |αG ^ 2 * Work.Spaces.DzIter 2 P z θ|
            + |5 * αG * Work.Spaces.Dz P z θ| + |6 * P z θ| := by
        have h := abs_add_le (αG ^ 2 * Work.Spaces.DzIter 2 P z θ
          + 5 * αG * Work.Spaces.Dz P z θ) (6 * P z θ)
        have h' := abs_add_le (αG ^ 2 * Work.Spaces.DzIter 2 P z θ)
          (5 * αG * Work.Spaces.Dz P z θ)
        linarith
      have hsum : αG ^ 2 * (M * Work.Construction.s2 θ) + 5 * αG * (M * Work.Construction.s2 θ)
          + 6 * (M * Work.Construction.s2 θ)
          = ((αG ^ 2 + 5 * αG + 6) * M) * Work.Construction.s2 θ := by ring
      linarith [e1, e2, e3, e4, hsum]
  have hFlim : Filter.Tendsto (fun p : ℝ × ℝ => F p.1 p.2)
      (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 0) := by
    have hmem : (z0, 0) ∈ Ioi 0 ×ˢ Work.Spaces.Iθ :=
      ⟨hz0, ⟨le_refl 0, by linarith [Real.pi_pos]⟩⟩
    have hsub : Work.Construction.Qd ⊆ Ioi 0 ×ˢ Work.Spaces.Iθ := by
      intro p hp
      exact ⟨(mem_Qd.mp hp).1, ⟨le_of_lt (mem_Qd.mp hp).2.1, le_of_lt (mem_Qd.mp hp).2.2⟩⟩
    have h1 : Filter.Tendsto (Function.uncurry F) (𝓝[Ioi 0 ×ˢ Work.Spaces.Iθ] (z0, 0))
        (𝓝 (Function.uncurry F (z0, 0))) := hF.1.continuousWithinAt hmem
    have h2 := h1.mono_left (nhdsWithin_mono (z0, 0) hsub)
    have h2' : Filter.Tendsto (Function.uncurry F) (𝓝[Work.Construction.Qd] (z0, 0))
        (𝓝 (Function.uncurry F (z0, 0))) := h2
    have hval : Function.uncurry F (z0, 0) = 0 := (hF.2.2.2.1 z0 hz0).1
    rw [hval] at h2'
    exact h2'
  have hC : Filter.Tendsto (fun p : ℝ × ℝ =>
      (1 / Real.cos p.2 ^ 2 + Real.tan p.2 ^ 2) * P p.1 p.2)
      (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 0) := by
    refine pze_tendsto_zero_of_eventually_le (u := fun θ => (3 * M) * Work.Construction.s2 θ)
      ?_ ?_ ?_
    · simp only [Work.Construction.s2]
      fun_prop
    · simp
    · filter_upwards [self_mem_nhdsWithin,
        pze_eventually_snd_lt (z0 := z0) (by norm_num : (0:ℝ) < 1 / 2)] with p hp hplt
      show |(1 / Real.cos p.2 ^ 2 + Real.tan p.2 ^ 2) * P p.1 p.2|
        ≤ (3 * M) * Work.Construction.s2 p.2
      have hb : |P p.1 p.2| ≤ M * Work.Construction.s2 p.2 := by
        have h := hDzLeP p.1 p.2 hp 0 (by norm_num)
        simpa only [Work.Spaces.DzIter_zero] using h
      have hc : |1 / Real.cos p.2 ^ 2 + Real.tan p.2 ^ 2| ≤ 3 :=
        pze_one_div_cos_sq_add_tan_sq_abs_le_three (le_of_lt (pze_pos_snd hp)) hplt.le
      rw [abs_mul]
      have hcl := mul_le_mul hc hb (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 3)
      calc |1 / Real.cos p.2 ^ 2 + Real.tan p.2 ^ 2| * |P p.1 p.2|
          ≤ 3 * (M * Work.Construction.s2 p.2) := hcl
        _ = (3 * M) * Work.Construction.s2 p.2 := by ring
  have hD : Filter.Tendsto (fun p : ℝ × ℝ => Real.tan p.2 * Work.Construction.Vop P p.1 p.2)
      (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 0) := by
    refine pze_tendsto_zero_of_eventually_le (u := fun θ => (2 * M) * θ) ?_ ?_ ?_
    · fun_prop
    · simp
    · filter_upwards [self_mem_nhdsWithin,
        pze_eventually_snd_lt (z0 := z0) (by norm_num : (0:ℝ) < 1 / 2)] with p hp hplt
      show |Real.tan p.2 * Work.Construction.Vop P p.1 p.2| ≤ (2 * M) * p.2
      have hVb : |Work.Construction.Vop P p.1 p.2| ≤ M := by
        rw [hVopeq p.1 p.2 hp]
        exact SlotBd.V_le hslot hp (j := 0) (by norm_num)
      have htan : |Real.tan p.2| ≤ 2 * p.2 :=
        pze_tan_abs_le_two_mul (le_of_lt (pze_pos_snd hp)) hplt.le
      rw [abs_mul]
      have hml := mul_le_mul htan hVb (abs_nonneg _) (by linarith [pze_pos_snd hp] : (0:ℝ) ≤ 2 * p.2)
      calc |Real.tan p.2| * |Work.Construction.Vop P p.1 p.2| ≤ (2 * p.2) * M := hml
        _ = (2 * M) * p.2 := by ring
  have h4c : Filter.Tendsto (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth P)))
      (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 0) := by
    have hsum : Filter.Tendsto (fun p : ℝ × ℝ =>
        -(αG ^ 2 * Work.Spaces.DzIter 2 P p.1 p.2 + 5 * αG * Work.Spaces.Dz P p.1 p.2
            + 6 * P p.1 p.2) - F p.1 p.2
        + (1 / Real.cos p.2 ^ 2 + Real.tan p.2 ^ 2) * P p.1 p.2
        + Real.tan p.2 * Work.Construction.Vop P p.1 p.2)
        (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 0) := by
      have h := ((hA.sub hFlim).add hC).add hD
      simpa using h
    refine hsum.congr' ?_
    refine pze_eventually_of_mem_Qd (fun z θ hmem => ?_)
    show -(αG ^ 2 * Work.Spaces.DzIter 2 P z θ + 5 * αG * Work.Spaces.Dz P z θ
        + 6 * P z θ) - F z θ
      + (1 / Real.cos θ ^ 2 + Real.tan θ ^ 2) * P z θ
      + Real.tan θ * Work.Construction.Vop P z θ = Work.Spaces.pth (Work.Spaces.pth P) z θ
    have h1 := pze_pth_pth_eq hP2 hmem
    have h2 := hlaw z θ hmem
    rw [h1, h2]
    try ring
  have hVcont : ContinuousOn (Function.uncurry (Work.Construction.Vop Ψ))
      (Ioi 0 ×ˢ Ioo (0 : ℝ) (π / 2)) :=
    (pze_contDiffOn_uncurry_Vop_Qd h3).continuousOn
  have hVdiff : ∀ z θ, 0 < z → θ ∈ Ioo (0 : ℝ) (π / 2) →
      DifferentiableAt ℝ (fun θ' => Work.Construction.Vop Ψ z θ') θ := by
    intro z θ hz hθ
    have hmem : (z, θ) ∈ Work.Construction.Qd := ⟨hz, hθ⟩
    exact Work.Spaces.differentiableAt_curry_right
      (((pze_contDiffOn_uncurry_Vop_Qd h3).differentiableOn (by norm_num)).differentiableAt
        (hQd.mem_nhds hmem))
  have hVbnd : ∀ z θ, 0 < z → θ ∈ Ioo (0 : ℝ) (π / 2) →
      |Work.Spaces.pth (Work.Construction.Vop Ψ) z θ| ≤ (αG ^ 2 + 5 * αG + 6) * M + Mf := by
    intro z θ hz hθ
    have hmem : (z, θ) ∈ Work.Construction.Qd := ⟨hz, hθ⟩
    have hlaw' := hlaw z θ hmem
    have h0 : |P z θ| ≤ M * Work.Construction.s2 θ := by
      have h := hDzLeP z θ hmem 0 (by norm_num)
      simpa only [Work.Spaces.DzIter_zero] using h
    have h1 := hDzLeP z θ hmem 1 (by norm_num)
    have h2 := hDzLeP z θ hmem 2 (by norm_num)
    have hFb : |F z θ| ≤ Mf := SrcOK.F_le hF hz (pze_theta_Iθ hmem)
    have hVe : Work.Spaces.pth (Work.Construction.Vop P) z θ
        = Work.Spaces.pth (Work.Construction.Vop Ψ) z θ :=
      pze_pth_congr_of_isOpen hQd (fun p hp => hVopeq p.1 p.2 hp) hmem
    rw [← hVe, hlaw']
    have e1 : |αG ^ 2 * Work.Spaces.DzIter 2 P z θ| ≤ αG ^ 2 * (M * Work.Construction.s2 θ) := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ αG ^ 2)]
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    have e2 : |5 * αG * Work.Spaces.Dz P z θ| ≤ 5 * αG * (M * Work.Construction.s2 θ) := by
      rw [show (5:ℝ) * αG * Work.Spaces.Dz P z θ
          = ((5:ℝ) * αG) * Work.Spaces.Dz P z θ from by ring,
        abs_mul, abs_of_nonneg (by nlinarith [hαG])]
      exact mul_le_mul_of_nonneg_left h1 (by nlinarith [hαG])
    have e3 : |6 * P z θ| ≤ 6 * (M * Work.Construction.s2 θ) := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 6)]
      exact mul_le_mul_of_nonneg_left h0 (by norm_num)
    have hs2le : Work.Construction.s2 θ ≤ 1 := by
      rw [Work.Construction.s2_eq]
      exact Real.sin_le_one _
    have hsum : αG ^ 2 * (M * Work.Construction.s2 θ) + 5 * αG * (M * Work.Construction.s2 θ)
        + 6 * (M * Work.Construction.s2 θ) ≤ (αG ^ 2 + 5 * αG + 6) * M := by
      have hfac : αG ^ 2 * (M * Work.Construction.s2 θ)
            + 5 * αG * (M * Work.Construction.s2 θ)
            + 6 * (M * Work.Construction.s2 θ)
          = ((αG ^ 2 + 5 * αG + 6) * M) * Work.Construction.s2 θ := by ring
      rw [hfac]
      have hnonneg : (0:ℝ) ≤ (αG ^ 2 + 5 * αG + 6) * M := by
        have : (0:ℝ) ≤ αG ^ 2 + 5 * αG + 6 := by nlinarith [sq_nonneg αG, hαG]
        exact mul_nonneg this hMnn
      calc ((αG ^ 2 + 5 * αG + 6) * M) * Work.Construction.s2 θ
          ≤ ((αG ^ 2 + 5 * αG + 6) * M) * 1 :=
            mul_le_mul_of_nonneg_left hs2le hnonneg
        _ = (αG ^ 2 + 5 * αG + 6) * M := by ring
    have htp : |αG ^ 2 * Work.Spaces.DzIter 2 P z θ + 5 * αG * Work.Spaces.Dz P z θ
        + 6 * P z θ| ≤ |αG ^ 2 * Work.Spaces.DzIter 2 P z θ|
          + |5 * αG * Work.Spaces.Dz P z θ| + |6 * P z θ| := by
      have h := abs_add_le (αG ^ 2 * Work.Spaces.DzIter 2 P z θ + 5 * αG * Work.Spaces.Dz P z θ)
        (6 * P z θ)
      have h' := abs_add_le (αG ^ 2 * Work.Spaces.DzIter 2 P z θ)
        (5 * αG * Work.Spaces.Dz P z θ)
      linarith
    have hfin : |-(αG ^ 2 * Work.Spaces.DzIter 2 P z θ + 5 * αG * Work.Spaces.Dz P z θ
        + 6 * P z θ) - F z θ| ≤ (αG ^ 2 + 5 * αG + 6) * M + Mf := by
      have hAb : |αG ^ 2 * Work.Spaces.DzIter 2 P z θ + 5 * αG * Work.Spaces.Dz P z θ
          + 6 * P z θ| ≤ (αG ^ 2 + 5 * αG + 6) * M := by linarith [htp, e1, e2, e3, hsum]
      have h := abs_sub_le (-(αG ^ 2 * Work.Spaces.DzIter 2 P z θ
        + 5 * αG * Work.Spaces.Dz P z θ + 6 * P z θ)) 0 (F z θ)
      simp only [sub_zero, zero_sub, abs_neg] at h
      linarith [h, hAb, hFb]
    exact hfin
  obtain ⟨fa, fb, hfac, hfbc, hfbd⟩ :=
    Work.FTS_StreamBdry.SB25.lip_edge_trace (Work.Construction.Vop Ψ) 0 (π / 2)
      ((αG ^ 2 + 5 * αG + 6) * M + Mf) (by linarith [Real.pi_pos]) hVcont hVdiff hVbnd
  have hlimV : Filter.Tendsto (Function.uncurry (Work.Construction.Vop Ψ))
      (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 (fa z0)) := by
    refine pze_tendsto_of_eventually_le_add hz0 (c := fun p : ℝ × ℝ => fa p.1)
      (u := fun θ => ((αG ^ 2 + 5 * αG + 6) * M + Mf) * θ) ?_ ?_ ?_ ?_
    · have h : ContinuousOn (fun p : ℝ × ℝ => fa p.1) (Ioi 0 ×ˢ (Set.univ : Set ℝ)) :=
        hfac.comp continuousOn_fst (fun p hp => hp.1)
      simpa using h
    · fun_prop
    · simp
    · refine pze_eventually_of_mem_Qd (fun z θ hmem => ?_)
      have h := (hfbd z θ (pze_pos_fst hmem) (pze_theta_mem hmem)).1
      simpa using h
  have htanP : Filter.Tendsto (fun p : ℝ × ℝ => Real.tan p.2 * P p.1 p.2)
      (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 0) := by
    refine pze_tendsto_zero_of_eventually_le (u := fun θ => (2 * M) * θ) (by fun_prop) (by simp) ?_
    refine pze_eventually_of_mem_Qd (fun z θ hmem => ?_)
    have hb : |P z θ| ≤ M * Work.Construction.s2 θ := by
      have h := hDzLeP z θ hmem 0 (by norm_num)
      simpa only [Work.Spaces.DzIter_zero] using h
    have hcos : Real.cos θ ≠ 0 := ne_of_gt (cos_pos_of_Qd hmem)
    have hsin0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc
      ⟨le_of_lt (Qd_theta_mem hmem).1, by linarith [(Qd_theta_mem hmem).2, Real.pi_pos]⟩
    have hsinle : Real.sin θ ≤ 1 := Real.sin_le_one θ
    have hsinle2 : Real.sin θ ≤ θ := Real.sin_le (le_of_lt (Qd_theta_mem hmem).1)
    have hsq : Real.sin θ ^ 2 ≤ θ := by
      have hmul : Real.sin θ * Real.sin θ ≤ θ * 1 :=
        mul_le_mul hsinle2 hsinle hsin0 (le_of_lt (Qd_theta_mem hmem).1)
      simpa [pow_two] using hmul
    have htanpos : 0 < Real.tan θ :=
      Real.tan_pos_of_pos_of_lt_pi_div_two (Qd_theta_mem hmem).1 (Qd_theta_mem hmem).2
    rw [show |Real.tan θ * P z θ| = Real.tan θ * |P z θ| from by
      rw [abs_mul, abs_of_pos htanpos]]
    calc Real.tan θ * |P z θ| ≤ Real.tan θ * (M * Work.Construction.s2 θ) :=
          mul_le_mul_of_nonneg_left hb htanpos.le
      _ = 2 * M * Real.sin θ ^ 2 := by
          rw [show Real.tan θ * (M * Work.Construction.s2 θ)
              = M * (Real.tan θ * Work.Construction.s2 θ) from by ring, tan_mul_s2 hcos]
          ring
      _ ≤ 2 * M * θ := by nlinarith [hsq, hMnn]
  have h5 : ∃ l, Filter.Tendsto (Function.uncurry (Work.Spaces.pth P))
      (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 l) := by
    refine ⟨fa z0, ?_⟩
    have hsum : Filter.Tendsto
        (fun p : ℝ × ℝ => Work.Construction.Vop Ψ p.1 p.2 + Real.tan p.2 * P p.1 p.2)
        (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 (fa z0)) := by
      simpa [Function.uncurry] using hlimV.add htanP
    refine hsum.congr' ?_
    refine pze_eventually_of_mem_Qd (fun z θ hmem => ?_)
    show Work.Construction.Vop Ψ z θ + Real.tan θ * P z θ
      = Function.uncurry (Work.Spaces.pth P) (z, θ)
    rw [Function.uncurry]
    show Work.Construction.Vop Ψ z θ + Real.tan θ * P z θ = Work.Spaces.pth P z θ
    rw [← hVopeq z θ hmem, Work.Construction.Vop]
    ring
  have hWcont : ContinuousOn (Function.uncurry (Work.Spaces.Dz (Work.Construction.Vop Ψ)))
      (Ioi 0 ×ˢ Ioo (0 : ℝ) (π / 2)) := by
    have hpz1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz (Work.Construction.Vop Ψ)))
        Work.Construction.Qd := pze_contDiffOn_uncurry_pz_Qd (pze_contDiffOn_uncurry_Vop_Qd h3)
    refine ((continuousOn_fst.mul hpz1.continuousOn).congr (fun p _ => ?_))
    simp only [Function.uncurry, Work.Spaces.Dz, Pi.mul_apply]
  have hWdiff : ∀ z θ, 0 < z → θ ∈ Ioo (0 : ℝ) (π / 2) →
      DifferentiableAt ℝ (fun θ' => Work.Spaces.Dz (Work.Construction.Vop Ψ) z θ') θ := by
    intro z θ hz hθ
    have hmem : (z, θ) ∈ Work.Construction.Qd := ⟨hz, hθ⟩
    have hpz1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz (Work.Construction.Vop Ψ)))
        Work.Construction.Qd := pze_contDiffOn_uncurry_pz_Qd (pze_contDiffOn_uncurry_Vop_Qd h3)
    have hd : DifferentiableAt ℝ (fun θ' => Work.Spaces.pz (Work.Construction.Vop Ψ) z θ') θ :=
      Work.Spaces.differentiableAt_curry_right
        ((hpz1.differentiableOn (by norm_num)).differentiableAt (hQd.mem_nhds hmem))
    exact hd.const_mul z
  have hWbnd : ∀ z θ, 0 < z → θ ∈ Ioo (0 : ℝ) (π / 2) →
      |Work.Spaces.pth (Work.Spaces.Dz (Work.Construction.Vop Ψ)) z θ| ≤ K' := by
    intro z θ hz hθ
    have hmem : (z, θ) ∈ Work.Construction.Qd := ⟨hz, hθ⟩
    have heq : ∀ p ∈ Work.Construction.Qd,
        Work.Spaces.Dz (Work.Construction.Vop Ψ) p.1 p.2
          = Work.Spaces.Dz (Work.Construction.Vop P) p.1 p.2 := by
      intro p hp
      rw [Work.Spaces.Dz, Work.Spaces.Dz, pze_pz_congr_of_isOpen hQd (fun q hq => hVopeq q.1 q.2 hq) hp]
    rw [pze_pth_congr_of_isOpen hQd heq hmem]
    exact hK'b z θ hmem
  obtain ⟨ga, gb, hgac, hgbc, hgbd⟩ :=
    Work.FTS_StreamBdry.SB25.lip_edge_trace (Work.Spaces.Dz (Work.Construction.Vop Ψ)) 0 (π / 2)
      K' (by linarith [Real.pi_pos]) hWcont hWdiff hWbnd
  have hK'nn : 0 ≤ K' := le_trans (abs_nonneg _) (hK'b 1 (Real.pi / 4) hQdd)
  have hpzV : Filter.Tendsto (Function.uncurry (Work.Spaces.pz (Work.Construction.Vop Ψ)))
      (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 (ga z0 / z0)) := by
    refine pze_tendsto_of_eventually_le_add hz0 (c := fun p : ℝ × ℝ => ga p.1 / p.1)
      (u := fun θ => (2 * K' / z0) * θ) ?_ ?_ ?_ ?_
    · have hnum : ContinuousOn (fun p : ℝ × ℝ => ga p.1) (Ioi 0 ×ˢ (Set.univ : Set ℝ)) :=
        hgac.comp continuousOn_fst (fun p hp => hp.1)
      refine (hnum.div continuousOn_fst (fun p hp => ne_of_gt hp.1)).congr (fun p _ => rfl)
    · fun_prop
    · simp
    · filter_upwards [self_mem_nhdsWithin, pze_eventually_fst_gt hz0] with p hp hpz
      show |Work.Spaces.pz (Work.Construction.Vop Ψ) p.1 p.2 - ga p.1 / p.1|
        ≤ (2 * K' / z0) * p.2
      have hz1 : 0 < p.1 := pze_pos_fst hp
      have hb := (hgbd p.1 p.2 hz1 (pze_theta_mem hp)).1
      have hpzeq : Work.Spaces.pz (Work.Construction.Vop Ψ) p.1 p.2
          = Work.Spaces.Dz (Work.Construction.Vop Ψ) p.1 p.2 / p.1 := by
        rw [show Work.Spaces.Dz (Work.Construction.Vop Ψ) p.1 p.2
            = p.1 * Work.Spaces.pz (Work.Construction.Vop Ψ) p.1 p.2 from rfl,
          mul_div_cancel_left₀ _ (ne_of_gt hz1)]
      rw [hpzeq]
      have hgoal : |Work.Spaces.Dz (Work.Construction.Vop Ψ) p.1 p.2 / p.1 - ga p.1 / p.1|
          = |Work.Spaces.Dz (Work.Construction.Vop Ψ) p.1 p.2 - ga p.1| / p.1 := by
        rw [← sub_div, abs_div, abs_of_pos hz1]
      rw [hgoal]
      have hK'p : 0 ≤ K' * p.2 := mul_nonneg hK'nn (le_of_lt (pze_pos_snd hp))
      calc |Work.Spaces.Dz (Work.Construction.Vop Ψ) p.1 p.2 - ga p.1| / p.1
          ≤ (K' * (p.2 - 0)) / p.1 := div_le_div_of_nonneg_right hb hz1.le
        _ = (K' * p.2) * (1 / p.1) := by ring
        _ ≤ (K' * p.2) * (1 / (z0 / 2)) :=
            mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (by linarith) hpz.le) hK'p
        _ = (2 * K' / z0) * p.2 := by
            field_simp
            try ring
  have htanpz : Filter.Tendsto (fun p : ℝ × ℝ => Real.tan p.2 * Work.Spaces.pz P p.1 p.2)
      (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 0) := by
    refine pze_tendsto_zero_of_eventually_le (u := fun θ => (4 * M / z0) * θ) (by fun_prop) (by simp) ?_
    filter_upwards [self_mem_nhdsWithin, pze_eventually_fst_gt hz0] with p hp hpz
    show |Real.tan p.2 * Work.Spaces.pz P p.1 p.2| ≤ (4 * M / z0) * p.2
    have hz1 : 0 < p.1 := pze_pos_fst hp
    have hb : |Work.Spaces.DzIter 1 P p.1 p.2| ≤ M * Work.Construction.s2 p.2 :=
      hDzLeP p.1 p.2 hp 1 (by norm_num)
    have hMz : 0 ≤ M * Work.Construction.s2 p.2 := mul_nonneg hMnn (pze_s2_nonneg hp)
    have hpzeq : Work.Spaces.pz P p.1 p.2 = Work.Spaces.DzIter 1 P p.1 p.2 / p.1 := by
      rw [show Work.Spaces.DzIter 1 P p.1 p.2 = p.1 * Work.Spaces.pz P p.1 p.2 from rfl,
        mul_div_cancel_left₀ _ (ne_of_gt hz1)]
    have hpzb : |Work.Spaces.pz P p.1 p.2| ≤ (2 * M / z0) * Work.Construction.s2 p.2 := by
      rw [hpzeq, abs_div, abs_of_pos hz1]
      calc |Work.Spaces.DzIter 1 P p.1 p.2| / p.1
          ≤ (M * Work.Construction.s2 p.2) / p.1 := div_le_div_of_nonneg_right hb hz1.le
        _ = (M * Work.Construction.s2 p.2) * (1 / p.1) := by ring
        _ ≤ (M * Work.Construction.s2 p.2) * (1 / (z0 / 2)) :=
            mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (by linarith) hpz.le) hMz
        _ = (2 * M / z0) * Work.Construction.s2 p.2 := by
            field_simp
            try ring
    have hcos : Real.cos p.2 ≠ 0 := ne_of_gt (pze_cos_pos hp)
    have htanpos : 0 < Real.tan p.2 :=
      Real.tan_pos_of_pos_of_lt_pi_div_two (pze_pos_snd hp) (pze_snd_lt hp)
    have hsin0 : 0 ≤ Real.sin p.2 := Real.sin_nonneg_of_mem_Icc
      ⟨le_of_lt (pze_pos_snd hp), by linarith [pze_snd_lt hp, Real.pi_pos]⟩
    have hsinle : Real.sin p.2 ≤ 1 := Real.sin_le_one p.2
    have hsinle2 : Real.sin p.2 ≤ p.2 := Real.sin_le (le_of_lt (pze_pos_snd hp))
    have hsq : Real.sin p.2 ^ 2 ≤ p.2 := by
      have hmul : Real.sin p.2 * Real.sin p.2 ≤ p.2 * 1 :=
        mul_le_mul hsinle2 hsinle hsin0 (le_of_lt (pze_pos_snd hp))
      simpa [pow_two] using hmul
    rw [show |Real.tan p.2 * Work.Spaces.pz P p.1 p.2|
        = Real.tan p.2 * |Work.Spaces.pz P p.1 p.2| from by
      rw [abs_mul, abs_of_pos htanpos]]
    calc Real.tan p.2 * |Work.Spaces.pz P p.1 p.2|
        ≤ Real.tan p.2 * ((2 * M / z0) * Work.Construction.s2 p.2) :=
          mul_le_mul_of_nonneg_left hpzb htanpos.le
      _ = (2 * M / z0) * (Real.tan p.2 * Work.Construction.s2 p.2) := by ring
      _ = (2 * M / z0) * (2 * Real.sin p.2 ^ 2) := by rw [tan_mul_s2 hcos]
      _ ≤ (4 * M / z0) * p.2 := by
          have hM2 : (0:ℝ) ≤ 2 * M / z0 := div_nonneg (by linarith [hMnn]) hz0.le
          have hstep : (2 * M / z0) * (2 * Real.sin p.2 ^ 2) ≤ (2 * M / z0) * (2 * p.2) :=
            mul_le_mul_of_nonneg_left (by linarith [hsq]) hM2
          have heq : (4 * M / z0) * p.2 = (2 * M / z0) * (2 * p.2) := by ring
          rw [heq]
          exact hstep
  have h6 : ∃ l, Filter.Tendsto (Function.uncurry (Work.Spaces.pz (Work.Spaces.pth P)))
        (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 l) ∧
      Filter.Tendsto (Function.uncurry (Work.Spaces.pth (Work.Spaces.pz P)))
        (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 l) := by
    have hmain : Filter.Tendsto (fun p : ℝ × ℝ => Work.Spaces.pz (Work.Spaces.pth P) p.1 p.2)
        (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 (ga z0 / z0)) := by
      have hsum : Filter.Tendsto
          (fun p : ℝ × ℝ => Work.Spaces.pz (Work.Construction.Vop Ψ) p.1 p.2
            + Real.tan p.2 * Work.Spaces.pz P p.1 p.2)
          (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 (ga z0 / z0)) := by
        simpa [Function.uncurry] using hpzV.add htanpz
      refine hsum.congr' ?_
      refine pze_eventually_of_mem_Qd (fun z θ hmem => ?_)
      show Work.Spaces.pz (Work.Construction.Vop Ψ) z θ + Real.tan θ * Work.Spaces.pz P z θ
        = Work.Spaces.pz (Work.Spaces.pth P) z θ
      exact (hpzsplit z θ hmem).symm
    refine ⟨ga z0 / z0, hmain, ?_⟩
    refine Filter.Tendsto.congr' ?_ hmain
    refine pze_eventually_of_mem_Qd (fun z θ hmem => ?_)
    exact Work.Spaces.pz_pth_comm (hP2.contDiffAt (hQd.mem_nhds hmem))
  exact ⟨h1, h2, h3c, h4c, h5, h6⟩

end Work.FTS_StreamBdry.SB25
