import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB6.UprimeAux.OdeBound2
import Submission.Work.FTS_StreamBdry.SB6.UprimeAux.OdeFacts
import Submission.Work.FTS_StreamBdry.SB6.clauses3
import Submission.Work.FTS_StreamBdry.SBpsiP.DzJ_crux
import Submission.Work.FTS_StreamBdry.SBpsiP.SelfUprime
import Submission.Work.FTS_StreamBdry.sb5_barrier_proved
import Submission.Work.Spaces.pz_mixed_mul_le_4
-- ===== merged: Submission.Work.FTS_StreamBdry.SB25.psiP_edge_zero =====
section

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
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB25Aux3.trace_DzVop_psiP =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25Aux3.trace_DzVop_psiP`

The function `f := D_z V(psiP αG Ψ)` on the open quadrant has a continuous edge trace at
`θ = π/2`, approached at the linear rate given by the pointwise bound `K'` on its `θ`-derivative
`∂_θ D_z V(psiP αG Ψ)`.

This is leaf SB2 of the `SB3/SB2/SB5` route (`NOTES_SB3_route.md` §4): the `θ`-edge trace of
`D_z V(psiP)`.  The proof is the general `SB25.lip_edge_trace` (leaf B2) applied to `f`, so all
that is needed is the regularity of `f` on the open quadrant — which comes from the `C³` hypothesis
on `Ψ`:

* `SB25Aux3.psiP_c3` : `psiP αG Ψ` is `C³` on `Qd`;
* `SB25.pze_contDiffOn_uncurry_Vop_Qd` : hence `V(psiP)` is `C²` there;
* `SB25.pze_contDiffOn_uncurry_pz_Qd` : hence `∂_z V(psiP)` is `C¹`, and `D_z V(psiP) = z∂_zV(psiP)`
  is `C¹`, so its `θ`-slices are differentiable and `f` is continuous;

and then `SB25.lip_edge_trace` produces the trace at `b = π/2` with rate `|K'|` (the bound on
`|∂_θ f|` is upgraded from `K'` to `|K'|`).
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_StreamBdry.SB25Aux3

set_option autoImplicit false

theorem trace_DzVop_psiP {αG M K' : ℝ} (hαG : 0 < αG) {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : Work.FTS.StreamBdryIface.SlotBd αG Ψ M)
    (hK' : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.pth (Work.Spaces.DzIter 1
        (Work.Construction.Vop (Work.FTS.StreamBdryIface.psiP αG Ψ))) z θ| ≤ K') :
    ∃ DVb : ℝ → ℝ, ContinuousOn DVb (Set.Ioi 0) ∧
      ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
        |Work.Spaces.DzIter 1 (Work.Construction.Vop (Work.FTS.StreamBdryIface.psiP αG Ψ)) z θ - DVb z|
          ≤ |K'| * (Real.pi / 2 - θ) := by
  -- The regularity of the `U`-slot `P := psiP αG Ψ` on the open quadrant.
  have hQd : IsOpen Work.Construction.Qd := Work.FTS_StreamBdry.SB1.isOpen_Qd
  have hP3 : ContDiffOn ℝ 3
      (Function.uncurry (Work.FTS.StreamBdryIface.psiP αG Ψ)) Work.Construction.Qd :=
    psiP_c3 hαG h3 hslot
  have hV2 : ContDiffOn ℝ 2
      (Function.uncurry (Work.Construction.Vop (Work.FTS.StreamBdryIface.psiP αG Ψ)))
      Work.Construction.Qd :=
    Work.FTS_StreamBdry.SB25.pze_contDiffOn_uncurry_Vop_Qd hP3
  have hpz1 : ContDiffOn ℝ 1
      (Function.uncurry
        (Work.Spaces.pz (Work.Construction.Vop (Work.FTS.StreamBdryIface.psiP αG Ψ))))
      Work.Construction.Qd :=
    Work.FTS_StreamBdry.SB25.pze_contDiffOn_uncurry_pz_Qd hV2
  -- `D_z V(P) = z · ∂_z V(P)` is therefore `C¹` on the quadrant.
  have hf1 : ContDiffOn ℝ 1
      (Function.uncurry
        (Work.Spaces.DzIter 1 (Work.Construction.Vop (Work.FTS.StreamBdryIface.psiP αG Ψ))))
      Work.Construction.Qd := by
    have hfun : Function.uncurry
          (Work.Spaces.DzIter 1 (Work.Construction.Vop (Work.FTS.StreamBdryIface.psiP αG Ψ)))
        = fun p : ℝ × ℝ =>
            p.1 * Function.uncurry
              (Work.Spaces.pz (Work.Construction.Vop (Work.FTS.StreamBdryIface.psiP αG Ψ))) p := by
      funext p
      rcases p with ⟨z, θ⟩
      rfl
    rw [hfun]
    exact contDiff_fst.contDiffOn.mul hpz1
  -- Leaf B2: the edge trace at `b = π/2` with rate `|K'|`.
  obtain ⟨fa, fb, hfa_cont, hfb_cont, hrate⟩ :=
    Work.FTS_StreamBdry.SB25.lip_edge_trace
      (Work.Spaces.DzIter 1 (Work.Construction.Vop (Work.FTS.StreamBdryIface.psiP αG Ψ)))
      0 (Real.pi / 2) |K'| (by positivity) hf1.continuousOn
      (fun z θ hz hθ =>
        Work.Spaces.differentiableAt_curry_right
          ((hf1.differentiableOn (by norm_num)).differentiableAt
            (hQd.mem_nhds (show (z, θ) ∈ Work.Construction.Qd from ⟨hz, hθ⟩))))
      (fun z θ hz hθ =>
        le_trans (hK' z θ (show (z, θ) ∈ Work.Construction.Qd from ⟨hz, hθ⟩))
          (le_abs_self K'))
  exact ⟨fb, hfb_cont, fun z θ h =>
    (hrate z θ (Work.FTS_StreamBdry.mem_Qd.mp h).1 (Work.FTS_StreamBdry.mem_Qd.mp h).2).2⟩

end Work.FTS_StreamBdry.SB25Aux3
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB25Aux3.trace_Vop_psiP =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25Aux3.trace_Vop_psiP`

The `θ = π/2` edge trace of the `V`-slot of the `U`-slot part `P := psiP αG Ψ` of a stream
function, with the linear rate `((αG² + 5αG + 6)·M + Mf)·(π/2 - θ)`.

On the open quadrant the elliptic law in `D`-form (`SB3.law_psiP`) reads

  `∂_θ V(P) = -(αG² D_z²P + 5αG D_zP + 6P) - F`,

and `SB3.psiP_DzLe` bounds `|D_z^j P| ≤ M·sin 2θ` (`j ≤ 2`), while `SrcOK` bounds `|F| ≤ Mf`.
Hence `|∂_θ V(P)| ≤ (αG²+5αG+6)·M + Mf` on the quadrant (using `sin 2θ ≤ 1` and `M ≥ 0`, the
latter forced by `SlotBd`), i.e. the slices of `V(P)` are uniformly Lipschitz in `θ`.  The leaf
`SB25.lip_edge_trace` converts a uniform `θ`-Lipschitz bound into a continuous edge trace at
`θ = π/2` approached at the linear rate, which is exactly the statement.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB25Aux3

open Work.FTS.StreamBdryIface (psiP SlotBd SrcOK)

set_option autoImplicit false

theorem trace_Vop_psiP {αG M L Mf : ℝ} (hαG : 0 < αG) {F Ψ : ℝ → ℝ → ℝ}
    (hsol : Work.FTS.StrongGlobal.IsBslSolPos αG F Ψ)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : Work.FTS.StreamBdryIface.SlotBd αG Ψ M)
    (hsrc : Work.FTS.StreamBdryIface.SrcOK F L Mf) :
    ∃ Vb : ℝ → ℝ, ContinuousOn Vb (Set.Ioi 0) ∧
      ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
        |Work.Construction.Vop (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ - Vb z|
          ≤ ((αG ^ 2 + 5 * αG + 6) * M + Mf) * (Real.pi / 2 - θ) := by
  -- `sin 2θ ≤ 1` and the boundary datum `M ≥ 0` forced by `SlotBd`
  have hM0 : 0 ≤ M := by
    have h := Work.FTS_StreamBdry.SlotBd.Dz_le hslot (z := 1) (θ := Real.pi / 4)
      Work.FTS_StreamBdry.SB1.Qd_nonempty (j := 0) (by norm_num)
    exact le_trans (abs_nonneg _) h
  have hcoef : 0 ≤ αG ^ 2 + 5 * αG + 6 := by nlinarith [sq_nonneg αG, hαG]
  -- the pointwise bound on the `θ`-derivative, i.e. the Lipschitz constant of the slices
  have hmain : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.pth (Work.Construction.Vop (psiP αG Ψ)) z θ|
        ≤ (αG ^ 2 + 5 * αG + 6) * M + Mf := by
    intro z θ hmem
    have hθm := Work.FTS_StreamBdry.Qd_theta_mem hmem
    have hzpos := Work.FTS_StreamBdry.Qd_pos hmem
    have hs2pos := Work.FTS_StreamBdry.s2_pos_of_Qd hmem
    have hs2le : Work.Construction.s2 θ ≤ 1 := by
      rw [Work.Construction.s2_eq]; exact Real.sin_le_one _
    have hs2M : M * Work.Construction.s2 θ ≤ M := by
      simpa using mul_le_mul_of_nonneg_left hs2le hM0
    -- the elliptic law in `D`-form for `psiP`
    have hlaw := Work.FTS_StreamBdry.SB3.law_psiP hαG hsol h3 hslot z θ hmem
    -- `|D_z^j psiP| ≤ M sin 2θ` for `j ≤ 2`
    have hDz := Work.FTS_StreamBdry.SB3.psiP_DzLe hαG h3 hslot
    have hD2 : |Work.Spaces.DzIter 2 (psiP αG Ψ) z θ| ≤ M * Work.Construction.s2 θ :=
      hDz z θ hmem 2 (by norm_num)
    have hD1 : |Work.Spaces.Dz (psiP αG Ψ) z θ| ≤ M * Work.Construction.s2 θ :=
      hDz z θ hmem 1 (by norm_num)
    have hD0 : |psiP αG Ψ z θ| ≤ M * Work.Construction.s2 θ :=
      hDz z θ hmem 0 (by norm_num)
    -- the source bound
    have hF : |F z θ| ≤ Mf :=
      Work.FTS_StreamBdry.SrcOK.F_le hsrc hzpos (Work.FTS_StreamBdry.Qd_theta_Iθ hmem)
    -- the three weighted summands
    have hA : |αG ^ 2 * Work.Spaces.DzIter 2 (psiP αG Ψ) z θ|
        ≤ αG ^ 2 * (M * Work.Construction.s2 θ) := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg αG)]
      exact mul_le_mul_of_nonneg_left hD2 (sq_nonneg αG)
    have hB : |5 * αG * Work.Spaces.Dz (psiP αG Ψ) z θ|
        ≤ 5 * αG * (M * Work.Construction.s2 θ) := by
      have h5 : (0 : ℝ) ≤ 5 * αG := by linarith
      rw [abs_mul, abs_of_nonneg h5]
      exact mul_le_mul_of_nonneg_left hD1 h5
    have hC : |6 * psiP αG Ψ z θ| ≤ 6 * (M * Work.Construction.s2 θ) := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
      exact mul_le_mul_of_nonneg_left hD0 (by norm_num)
    have htri : |αG ^ 2 * Work.Spaces.DzIter 2 (psiP αG Ψ) z θ
          + 5 * αG * Work.Spaces.Dz (psiP αG Ψ) z θ + 6 * psiP αG Ψ z θ|
        ≤ |αG ^ 2 * Work.Spaces.DzIter 2 (psiP αG Ψ) z θ|
          + |5 * αG * Work.Spaces.Dz (psiP αG Ψ) z θ| + |6 * psiP αG Ψ z θ| := by
      have h₁ := abs_add_le (αG ^ 2 * Work.Spaces.DzIter 2 (psiP αG Ψ) z θ
        + 5 * αG * Work.Spaces.Dz (psiP αG Ψ) z θ) (6 * psiP αG Ψ z θ)
      have h₂ := abs_add_le (αG ^ 2 * Work.Spaces.DzIter 2 (psiP αG Ψ) z θ)
        (5 * αG * Work.Spaces.Dz (psiP αG Ψ) z θ)
      linarith [abs_nonneg (αG ^ 2 * Work.Spaces.DzIter 2 (psiP αG Ψ) z θ),
        abs_nonneg (5 * αG * Work.Spaces.Dz (psiP αG Ψ) z θ),
        abs_nonneg (6 * psiP αG Ψ z θ)]
    have hsum : αG ^ 2 * (M * Work.Construction.s2 θ)
          + 5 * αG * (M * Work.Construction.s2 θ) + 6 * (M * Work.Construction.s2 θ)
        = (αG ^ 2 + 5 * αG + 6) * (M * Work.Construction.s2 θ) := by ring
    rw [hlaw]
    have hneg : -(αG ^ 2 * Work.Spaces.DzIter 2 (psiP αG Ψ) z θ
          + 5 * αG * Work.Spaces.Dz (psiP αG Ψ) z θ + 6 * psiP αG Ψ z θ) - F z θ
        = -(αG ^ 2 * Work.Spaces.DzIter 2 (psiP αG Ψ) z θ
          + 5 * αG * Work.Spaces.Dz (psiP αG Ψ) z θ + 6 * psiP αG Ψ z θ + F z θ) := by
      ring
    rw [hneg, abs_neg]
    have hsplit := abs_add_le (αG ^ 2 * Work.Spaces.DzIter 2 (psiP αG Ψ) z θ
      + 5 * αG * Work.Spaces.Dz (psiP αG Ψ) z θ + 6 * psiP αG Ψ z θ) (F z θ)
    have hfin : (αG ^ 2 + 5 * αG + 6) * (M * Work.Construction.s2 θ) + Mf
        ≤ (αG ^ 2 + 5 * αG + 6) * M + Mf := by
      have := mul_le_mul_of_nonneg_left hs2M hcoef
      linarith
    linarith
  -- smoothness of `Vop (psiP αG Ψ)` on the open quadrant
  have hVopΨ : ContDiffOn ℝ 2 (Function.uncurry (Work.Construction.Vop Ψ))
      Work.Construction.Qd :=
    Work.FTS_StreamBdry.SB25.pze_contDiffOn_uncurry_Vop_Qd (Ψ := Ψ) h3
  have hVopP : ContDiffOn ℝ 2
      (Function.uncurry (Work.Construction.Vop (psiP αG Ψ))) Work.Construction.Qd :=
    hVopΨ.congr (fun p hp => by
      obtain ⟨z, θ⟩ := p
      exact Work.FTS_StreamBdry.SB3.Vop_psiP_eq (αG := αG) (M := M) (Ψ := Ψ)
        hαG h3 hslot z θ hp)
  have hcont : ContinuousOn (Function.uncurry (Work.Construction.Vop (psiP αG Ψ)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hVopP.continuousOn
  have hdiff : ∀ z θ, 0 < z → θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      DifferentiableAt ℝ (fun θ' => Work.Construction.Vop (psiP αG Ψ) z θ') θ := by
    intro z θ hz hθ
    have hmem : (z, θ) ∈ Work.Construction.Qd := ⟨hz, hθ.1, hθ.2⟩
    exact Work.Spaces.differentiableAt_curry_right
      ((hVopP.differentiableOn (by norm_num)).differentiableAt
        (Work.FTS_StreamBdry.SB1.isOpen_Qd.mem_nhds hmem))
  -- the edge trace at `θ = π/2`
  obtain ⟨fa, fb, _hfa, hfb, hrt⟩ :=
    Work.FTS_StreamBdry.SB25.lip_edge_trace (Work.Construction.Vop (psiP αG Ψ)) 0 (Real.pi / 2)
      ((αG ^ 2 + 5 * αG + 6) * M + Mf) (by linarith [Real.pi_pos]) hcont hdiff
      (fun z θ hz hθ => hmain z θ ⟨hz, hθ.1, hθ.2⟩)
  exact ⟨fb, hfb, fun z θ hmem =>
    (hrt z θ (Work.FTS_StreamBdry.Qd_pos hmem) (Work.FTS_StreamBdry.Qd_theta_mem hmem)).2⟩

end Work.FTS_StreamBdry.SB25Aux3
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB25Aux4.Part1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25Aux4.psiP_edge_axis_zero123`

The three vanishing limits of `psiP αG Ψ` at `(z₀, π/2)`: `P`, `∂_zP`, `∂_z²P` all tend to `0`,
uniformly in `z` near `z₀ > 0`.

`|D_z^j P| ≤ M sin 2θ` (`psiP_DzLe`, `j ≤ 2`) with `sin 2θ ≤ 2(π/2 - θ)` gives the first two
directly; for `∂_z²P` one uses `D_z² = z∂_z + z²∂_z²` (`DzIter_two_eq`) and `z ≥ z₀/2`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB25Aux4

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK gaugeMode psiP)

set_option autoImplicit false

theorem psiP_edge_axis_zero123 {αG M : ℝ} (hαG : 0 < αG) {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M) :
    ∀ z0 : ℝ, 0 < z0 →
      Tendsto (Function.uncurry (psiP αG Ψ)) (𝓝[Work.Construction.Qd] (z0, Real.pi / 2))
          (𝓝 0) ∧
        Tendsto (Function.uncurry (Work.Spaces.pz (psiP αG Ψ)))
            (𝓝[Work.Construction.Qd] (z0, Real.pi / 2)) (𝓝 0) ∧
          Tendsto (Function.uncurry (Work.Spaces.pz (Work.Spaces.pz (psiP αG Ψ))))
            (𝓝[Work.Construction.Qd] (z0, Real.pi / 2)) (𝓝 0) := by
  have hMnn : 0 ≤ M := by
    have h1 := Work.FTS_StreamBdry.SlotBd.Dz_le hslot (z := 1) (θ := Real.pi / 4)
      Work.FTS_StreamBdry.SB1.Qd_nonempty (j := 0) (by norm_num)
    exact le_trans (abs_nonneg _) h1
  have hDz := Work.FTS_StreamBdry.SB3.psiP_DzLe (αG := αG) (M := M) hαG h3 hslot
  have hP2 : ContDiffOn ℝ 2 (Function.uncurry (psiP αG Ψ)) Work.Construction.Qd :=
    Work.FTS_StreamBdry.SB3.psiP_c2 (αG := αG) (M := M) hαG h3 hslot
  intro z0 hz0
  refine ⟨?_, ?_, ?_⟩
  · -- `P → 0`
    refine tendsto_nhdsWithin_of_abs_le (L := 0)
      (g := fun p : ℝ × ℝ => 2 * M * (Real.pi / 2 - p.2)) ?_ ?_
    · simpa using tendsto_const_mul_sub_snd_zero (2 * M) z0
    · refine eventually_nhdsWithin_Qd (fun z θ hmem => ?_)
      have h1 : |Work.Spaces.DzIter 0 (psiP αG Ψ) z θ| ≤ M * Work.Construction.s2 θ :=
        hDz z θ hmem 0 (by norm_num)
      rw [Work.Spaces.DzIter_zero] at h1
      have h2 := s2_le_two_sub (Work.FTS_StreamBdry.Qd_theta_mem hmem)
      have h4 : M * Work.Construction.s2 θ ≤ 2 * M * (Real.pi / 2 - θ) := by
        have h5 := mul_le_mul_of_nonneg_left h2 hMnn
        have h6 : M * (2 * (Real.pi / 2 - θ)) = 2 * M * (Real.pi / 2 - θ) := by ring
        linarith [h5, h6]
      have hgoal : |psiP αG Ψ z θ| ≤ 2 * M * (Real.pi / 2 - θ) := by linarith [h1, h4]
      simpa [Function.uncurry, sub_zero] using hgoal
  · -- `∂_zP → 0`
    refine tendsto_nhdsWithin_of_abs_le (L := 0)
      (g := fun p : ℝ × ℝ => (4 * M / z0) * (Real.pi / 2 - p.2)) ?_ ?_
    · simpa using tendsto_const_mul_sub_snd_zero (4 * M / z0) z0
    · refine eventually_nhdsWithin_iff.mpr ?_
      have hz_ev : ∀ᶠ p : ℝ × ℝ in 𝓝 (z0, Real.pi / 2), z0 / 2 < p.1 :=
        (tendsto_fst' (a := z0) (b := Real.pi / 2)).eventually
          ((isOpen_Ioi (a := z0 / 2)).mem_nhds (by linarith : z0 / 2 < z0))
      filter_upwards [hz_ev] with p hpz hmem
      obtain ⟨z, θ⟩ := p
      have hzpos : 0 < z := Work.FTS_StreamBdry.Qd_pos hmem
      have hs2nn : 0 ≤ Work.Construction.s2 θ :=
        Work.FTS_StreamBdry.s2_nonneg_of_Iθ (Work.FTS_StreamBdry.Qd_theta_Iθ hmem)
      have h1 : |z * Work.Spaces.pz (psiP αG Ψ) z θ| ≤ M * Work.Construction.s2 θ := by
        have h0 := hDz z θ hmem 1 (by norm_num)
        rwa [show Work.Spaces.DzIter 1 (psiP αG Ψ) z θ
          = z * Work.Spaces.pz (psiP αG Ψ) z θ from rfl] at h0
      rw [abs_mul, abs_of_pos hzpos] at h1
      have hpz : |Work.Spaces.pz (psiP αG Ψ) z θ| ≤ M * Work.Construction.s2 θ / z := by
        rw [le_div_iff₀ hzpos]
        calc |Work.Spaces.pz (psiP αG Ψ) z θ| * z
            = z * |Work.Spaces.pz (psiP αG Ψ) z θ| := by ring
          _ ≤ M * Work.Construction.s2 θ := h1
      have hMpos : 0 ≤ M * Work.Construction.s2 θ := mul_nonneg hMnn hs2nn
      have h4 : M * Work.Construction.s2 θ / z ≤ M * Work.Construction.s2 θ / (z0 / 2) :=
        div_le_div_of_nonneg_left hMpos (by linarith) (by linarith)
      have h5 : M * Work.Construction.s2 θ / (z0 / 2)
          = 2 * (M * Work.Construction.s2 θ) / z0 := by field_simp
      have h6 : 2 * (M * Work.Construction.s2 θ) / z0
          ≤ 2 * (M * (2 * (Real.pi / 2 - θ))) / z0 := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hz0)
        nlinarith [mul_le_mul_of_nonneg_left
          (s2_le_two_sub (Work.FTS_StreamBdry.Qd_theta_mem hmem)) hMnn]
      have h7 : 2 * (M * (2 * (Real.pi / 2 - θ))) / z0
          = (4 * M / z0) * (Real.pi / 2 - θ) := by ring
      have hgoal : |Work.Spaces.pz (psiP αG Ψ) z θ| ≤ (4 * M / z0) * (Real.pi / 2 - θ) := by
        linarith [hpz, h4, h5 ▸ h4, h6, h7]
      simpa [Function.uncurry, sub_zero] using hgoal
  · -- `∂_z²P → 0`
    refine tendsto_nhdsWithin_of_abs_le (L := 0)
      (g := fun p : ℝ × ℝ => (16 * M / z0 ^ 2) * (Real.pi / 2 - p.2)) ?_ ?_
    · simpa using tendsto_const_mul_sub_snd_zero (16 * M / z0 ^ 2) z0
    · refine eventually_nhdsWithin_iff.mpr ?_
      have hz_ev : ∀ᶠ p : ℝ × ℝ in 𝓝 (z0, Real.pi / 2), z0 / 2 < p.1 :=
        (tendsto_fst' (a := z0) (b := Real.pi / 2)).eventually
          ((isOpen_Ioi (a := z0 / 2)).mem_nhds (by linarith : z0 / 2 < z0))
      filter_upwards [hz_ev] with p hpz hmem
      obtain ⟨z, θ⟩ := p
      have hzpos : 0 < z := Work.FTS_StreamBdry.Qd_pos hmem
      have hθmem := Work.FTS_StreamBdry.Qd_theta_mem hmem
      have hI2 := hDz z θ hmem 2 (by norm_num)
      have hI1 := hDz z θ hmem 1 (by norm_num)
      have hI1' : |z * Work.Spaces.pz (psiP αG Ψ) z θ| ≤ M * Work.Construction.s2 θ := by
        rwa [show Work.Spaces.DzIter 1 (psiP αG Ψ) z θ
          = z * Work.Spaces.pz (psiP αG Ψ) z θ from rfl] at hI1
      have hsplit := DzIter_two_eq (P := psiP αG Ψ) hP2 hmem
      have hkey : z ^ 2 * |Work.Spaces.pz (Work.Spaces.pz (psiP αG Ψ)) z θ|
          ≤ 2 * (M * Work.Construction.s2 θ) := by
        rw [← abs_of_nonneg (sq_nonneg z), ← abs_mul]
        have heq : z ^ 2 * Work.Spaces.pz (Work.Spaces.pz (psiP αG Ψ)) z θ
            = Work.Spaces.DzIter 2 (psiP αG Ψ) z θ
              - z * Work.Spaces.pz (psiP αG Ψ) z θ := by linarith [hsplit]
        rw [heq]
        calc |Work.Spaces.DzIter 2 (psiP αG Ψ) z θ - z * Work.Spaces.pz (psiP αG Ψ) z θ|
            ≤ |Work.Spaces.DzIter 2 (psiP αG Ψ) z θ|
              + |z * Work.Spaces.pz (psiP αG Ψ) z θ| := abs_sub _ _
          _ ≤ M * Work.Construction.s2 θ + M * Work.Construction.s2 θ := by linarith [hI2, hI1']
          _ = 2 * (M * Work.Construction.s2 θ) := by ring
      have hpzz : |Work.Spaces.pz (Work.Spaces.pz (psiP αG Ψ)) z θ|
          ≤ 2 * (M * Work.Construction.s2 θ) / z ^ 2 := by
        rw [le_div_iff₀ (pow_pos hzpos 2)]
        calc |Work.Spaces.pz (Work.Spaces.pz (psiP αG Ψ)) z θ| * z ^ 2
            = z ^ 2 * |Work.Spaces.pz (Work.Spaces.pz (psiP αG Ψ)) z θ| := by ring
          _ ≤ 2 * (M * Work.Construction.s2 θ) := hkey
      have hMpos : 0 ≤ 2 * (M * Work.Construction.s2 θ) :=
        mul_nonneg (by norm_num) (mul_nonneg hMnn
          (Work.FTS_StreamBdry.s2_nonneg_of_Iθ (Work.FTS_StreamBdry.Qd_theta_Iθ hmem)))
      have h4 : 2 * (M * Work.Construction.s2 θ) / z ^ 2
          ≤ 2 * (M * Work.Construction.s2 θ) / (z0 / 2) ^ 2 :=
        div_le_div_of_nonneg_left hMpos (pow_pos (by linarith) 2) (by nlinarith)
      have h5 : 2 * (M * Work.Construction.s2 θ) / (z0 / 2) ^ 2
          = 8 * (M * Work.Construction.s2 θ) / z0 ^ 2 := by field_simp; ring
      have h6 : 8 * (M * Work.Construction.s2 θ) / z0 ^ 2
          ≤ 8 * (M * (2 * (Real.pi / 2 - θ))) / z0 ^ 2 := by
        apply div_le_div_of_nonneg_right _ (le_of_lt (pow_pos hz0 2))
        nlinarith [mul_le_mul_of_nonneg_left (s2_le_two_sub hθmem) hMnn]
      have h7 : 8 * (M * (2 * (Real.pi / 2 - θ))) / z0 ^ 2
          = (16 * M / z0 ^ 2) * (Real.pi / 2 - θ) := by ring
      have hgoal : |Work.Spaces.pz (Work.Spaces.pz (psiP αG Ψ)) z θ|
          ≤ (16 * M / z0 ^ 2) * (Real.pi / 2 - θ) := by
        linarith [hpzz, h4, h5 ▸ h4, h6, h7]
      simpa [Function.uncurry, sub_zero] using hgoal

end Work.FTS_StreamBdry.SB25Aux4
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB25Aux4.Part3 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25Aux4.psiP_edge_axis_pth`

The limit of `∂_θP` at `(z₀, π/2)`: it is `Vb z₀ / 2`.

`∂_θP = V(P) + tan θ·P`; the edge trace `Vb` of `V(P)` gives `V(P) → Vb z` at rate `K_V`, and
`SB25.axis_tan_bound` per `z`-slice turns that rate into `tan θ·P → -Vb z/2` (also at rate `K_V`),
so `∂_θP → Vb z₀/2`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB25Aux4

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK gaugeMode psiP)

set_option autoImplicit false

theorem psiP_edge_axis_pth {αG M Mf : ℝ} (hαG : 0 < αG) {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M)
    (Vb : ℝ → ℝ) (hVbc : ContinuousOn Vb (Set.Ioi 0))
    (hVb : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Construction.Vop (psiP αG Ψ) z θ - Vb z|
        ≤ ((αG ^ 2 + 5 * αG + 6) * M + Mf) * (Real.pi / 2 - θ)) :
    ∀ z0 : ℝ, 0 < z0 →
      ∃ l, Tendsto (Function.uncurry (Work.Spaces.pth (psiP αG Ψ)))
        (𝓝[Work.Construction.Qd] (z0, Real.pi / 2)) (𝓝 l) := by
  have hMnn : 0 ≤ M := by
    have h1 := Work.FTS_StreamBdry.SlotBd.Dz_le hslot (z := 1) (θ := Real.pi / 4)
      Work.FTS_StreamBdry.SB1.Qd_nonempty (j := 0) (by norm_num)
    exact le_trans (abs_nonneg _) h1
  have hDz := Work.FTS_StreamBdry.SB3.psiP_DzLe (αG := αG) (M := M) hαG h3 hslot
  have hP2 : ContDiffOn ℝ 2 (Function.uncurry (psiP αG Ψ)) Work.Construction.Qd :=
    Work.FTS_StreamBdry.SB3.psiP_c2 (αG := αG) (M := M) hαG h3 hslot
  have hQd : IsOpen Work.Construction.Qd := Work.FTS_StreamBdry.SB1.isOpen_Qd
  intro z0 hz0
  have hVbc_at : ContinuousAt Vb z0 := hVbc.continuousAt (isOpen_Ioi.mem_nhds hz0)
  set CV := |Vb z0| + 1 with hCV
  have hCVnn : 0 ≤ CV := by rw [hCV]; positivity
  have hCV_ev : ∀ᶠ p : ℝ × ℝ in 𝓝 (z0, Real.pi / 2), |Vb p.1| ≤ CV := by
    have h1 : ∀ᶠ p : ℝ × ℝ in 𝓝 (z0, Real.pi / 2), dist (Vb p.1) (Vb z0) < 1 :=
      hVbc_at.tendsto.comp (tendsto_fst' (a := z0) (b := Real.pi / 2))
        |>.eventually (Metric.ball_mem_nhds _ one_pos)
    filter_upwards [h1] with p hp
    rw [Real.dist_eq] at hp
    have h2 : |Vb p.1| ≤ |Vb p.1 - Vb z0| + |Vb z0| := by
      calc |Vb p.1| = |(Vb p.1 - Vb z0) + Vb z0| := by ring_nf
        _ ≤ |Vb p.1 - Vb z0| + |Vb z0| := abs_add_le _ _
    rw [hCV]; linarith
  refine ⟨Vb z0 / 2, ?_⟩
  refine tendsto_nhdsWithin_of_abs_le (L := Vb z0 / 2)
    (g := fun p : ℝ × ℝ => |Vb p.1 - Vb z0| / 2
      + (((αG ^ 2 + 5 * αG + 6) * M + Mf) + CV * (Real.pi / 2)
          + 3 * ((αG ^ 2 + 5 * αG + 6) * M + Mf)) * (Real.pi / 2 - p.2)) ?_ ?_
  · have h1 : Tendsto (fun p : ℝ × ℝ => |Vb p.1 - Vb z0| / 2)
        (𝓝 (z0, Real.pi / 2)) (𝓝 0) := by
      simpa using (tendsto_abs_sub_const hVbc_at).div_const 2
    have h2 := tendsto_const_mul_sub_snd_zero
      (((αG ^ 2 + 5 * αG + 6) * M + Mf) + CV * (Real.pi / 2)
        + 3 * ((αG ^ 2 + 5 * αG + 6) * M + Mf)) z0
    simpa using h1.add h2
  · refine eventually_nhdsWithin_iff.mpr ?_
    filter_upwards [hCV_ev] with p hpV hmem
    obtain ⟨z, θ⟩ := p
    have hpV' : |Vb z| ≤ CV := hpV
    have hθ := Work.FTS_StreamBdry.Qd_theta_mem hmem
    have hzpos : 0 < z := Work.FTS_StreamBdry.Qd_pos hmem
    have hb3 := Work.FTS_StreamBdry.SB25.axis_tan_bound (fun θ' => psiP αG Ψ z θ')
      (Vb z) ((αG ^ 2 + 5 * αG + 6) * M + Mf) M
    simp only [Work.FTS_StreamBdry.SB25.AxisTanBound] at hb3
    have hdiff : ∀ θ' ∈ Ioo (0 : ℝ) (Real.pi / 2),
        DifferentiableAt ℝ (fun θ'' => psiP αG Ψ z θ'') θ' := by
      intro θ' hθ'
      have hmem' : (z, θ') ∈ Work.Construction.Qd :=
        Work.FTS_StreamBdry.mem_Qd.mpr ⟨hzpos, hθ'.1, hθ'.2⟩
      exact Work.Spaces.differentiableAt_curry_right
        ((hP2.differentiableOn (by norm_num)).differentiableAt (hQd.mem_nhds hmem'))
    have hbd : ∀ θ' ∈ Ioo (0 : ℝ) (Real.pi / 2),
        |(fun θ'' => psiP αG Ψ z θ'') θ'| ≤ M := by
      intro θ' hθ'
      have hmem' : (z, θ') ∈ Work.Construction.Qd :=
        Work.FTS_StreamBdry.mem_Qd.mpr ⟨hzpos, hθ'.1, hθ'.2⟩
      have h0 := hDz z θ' hmem' 0 (by norm_num)
      rw [Work.Spaces.DzIter_zero] at h0
      have hs1 : Work.Construction.s2 θ' ≤ 1 := by
        rw [Work.Construction.s2_eq]; exact Real.sin_le_one _
      exact le_trans h0 (by simpa using mul_le_of_le_one_right hMnn hs1)
    have hcl : ∀ θ' ∈ Ioo (0 : ℝ) (Real.pi / 2),
        |deriv (fun θ'' => psiP αG Ψ z θ'') θ' - Real.tan θ' * psiP αG Ψ z θ' - Vb z|
          ≤ ((αG ^ 2 + 5 * αG + 6) * M + Mf) * (Real.pi / 2 - θ') := by
      intro θ' hθ'
      have hmem' : (z, θ') ∈ Work.Construction.Qd :=
        Work.FTS_StreamBdry.mem_Qd.mpr ⟨hzpos, hθ'.1, hθ'.2⟩
      show |Work.Construction.Vop (psiP αG Ψ) z θ' - Vb z| ≤ _
      exact hVb z θ' hmem'
    have hres := hb3 hdiff hbd hcl θ hθ
    have hVbd2 : |Work.Construction.Vop (psiP αG Ψ) z θ - Vb z|
        ≤ ((αG ^ 2 + 5 * αG + 6) * M + Mf) * (Real.pi / 2 - θ) := hVb z θ hmem
    have hsq : (Real.pi / 2 - θ) ^ 2 ≤ (Real.pi / 2) * (Real.pi / 2 - θ) := by
      have hp0 : 0 ≤ Real.pi / 2 - θ := by linarith [hθ.2]
      have hp1 : Real.pi / 2 - θ ≤ Real.pi / 2 := by linarith [hθ.1]
      nlinarith
    have hmid : |Real.tan θ * psiP αG Ψ z θ + Vb z / 2|
        ≤ CV * (Real.pi / 2) * (Real.pi / 2 - θ)
          + 3 * ((αG ^ 2 + 5 * αG + 6) * M + Mf) * (Real.pi / 2 - θ) := by
      have hp0 : 0 ≤ Real.pi / 2 - θ := by linarith [hθ.2]
      have h1 : |Vb z| * (Real.pi / 2 - θ) ^ 2 ≤ CV * ((Real.pi / 2) * (Real.pi / 2 - θ)) := by
        nlinarith [hsq, hpV', hp0, hCVnn]
      linarith [hres, h1]
    have hident : Work.Spaces.pth (psiP αG Ψ) z θ - Vb z0 / 2
        = (Work.Construction.Vop (psiP αG Ψ) z θ - Vb z)
          + (Real.tan θ * psiP αG Ψ z θ + Vb z / 2) + (Vb z - Vb z0) / 2 := by
      rw [Work.Construction.Vop]; ring
    have hgoal : |Work.Spaces.pth (psiP αG Ψ) z θ - Vb z0 / 2|
        ≤ |Vb z - Vb z0| / 2
          + (((αG ^ 2 + 5 * αG + 6) * M + Mf) + CV * (Real.pi / 2)
              + 3 * ((αG ^ 2 + 5 * αG + 6) * M + Mf)) * (Real.pi / 2 - θ) := by
      rw [hident]
      calc |(Work.Construction.Vop (psiP αG Ψ) z θ - Vb z)
              + (Real.tan θ * psiP αG Ψ z θ + Vb z / 2) + (Vb z - Vb z0) / 2|
          ≤ |Work.Construction.Vop (psiP αG Ψ) z θ - Vb z|
            + |Real.tan θ * psiP αG Ψ z θ + Vb z / 2| + |(Vb z - Vb z0) / 2| := by
            linarith [abs_add_three (Work.Construction.Vop (psiP αG Ψ) z θ - Vb z)
              (Real.tan θ * psiP αG Ψ z θ + Vb z / 2) ((Vb z - Vb z0) / 2)]
        _ ≤ |Vb z - Vb z0| / 2
              + (((αG ^ 2 + 5 * αG + 6) * M + Mf) + CV * (Real.pi / 2)
                  + 3 * ((αG ^ 2 + 5 * αG + 6) * M + Mf)) * (Real.pi / 2 - θ) := by
            rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
            nlinarith [hVbd2, hmid]
    simpa [Function.uncurry] using hgoal

end Work.FTS_StreamBdry.SB25Aux4
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB5.PthIter2Reproved =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB3.pthIter2_le` — the second `θ`-derivative of the `U`-slot part

`|∂_θ² (D_z^j (psiP αG Ψ))| ≤ K` on the open quadrant, for `j ≤ 1`, under `IsBslSolPos`,
`C³`-regularity of `Ψ`, the slot bounds `SlotBd` and the source facts `SrcOK`.

The route.  Write `P = psiP αG Ψ` and `u = P/s2`.  The `D_z`-bounds `|D_z^jP| ≤ K s2` (`j ≤ 3`)
give `|D_z^j u| ≤ K` (the division identities `P2Aux.div_identities`), and the elliptic law
`bslOp αG P = F` (`P2Aux.bslOp_psiP`, from the SB1′ gauge decomposition) turns into the singular
second-order ODE `u'' + c u' = -F/s2 - (αG²D_z²u + 5αG D_zu)` with
`c = 4cos2θ/sin2θ - tanθ` (`P2Aux.bslOp_div_s2_hasDerivAt`), whose weighted first-order bound is
`P2Aux.fam_ode_deriv_bound`.  The explicit formula
`∂_θ²P = -4 s2 u + 2 sin²θ u' - F - s2(αG²D_z²u + 5αG D_zu)` (`P2Aux.pthIter2_eq`) then bounds
`∂_θ²P` by `4M + 2K + Mf + (αG²M + 5αG M)`.  The `j = 1` case repeats the same argument for
`Q = D_zP`, `F ↦ D_zF` (`P2Aux.bslOp_Dz_comm`, `P2Aux.div_identities`).
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB3

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK psiP gaugeMode)
open Work.FTS_StreamBdry.SB3.P2Aux




end Work.FTS_StreamBdry.SB3
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB6.UprimeAux.OdeBound3 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB6.UprimeAux.OdeBound3` — the final bound for the singular `θ`-ODE

Combining the two endpoint representations with the elementary integral bounds and the lower
bounds on `wfun` gives a bound on `|u'|` on `(0, π/2)` which is uniform in the parameter `z`.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB6.UprimeAux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-- The constant of the left half. -/
def Kleft (A C : ℝ) : ℝ := Real.pi ^ 2 / Real.sqrt 2 * (A / 4 + C * Real.pi / 12)

/-- The constant of the right half. -/
def Kright (A C : ℝ) : ℝ := Real.pi ^ 3 / 4 * (A / 6 + C * Real.pi / 8)

lemma Kleft_nonneg {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) : 0 ≤ Kleft A C := by
  rw [Kleft]
  have : 0 ≤ A / 4 + C * Real.pi / 12 := by positivity
  positivity



lemma Kleft_arith {A C θ w : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hθ : 0 < θ)
    (hθle : θ ≤ Real.pi / 4) (hw : Real.sqrt 2 * θ ^ 2 / Real.pi ^ 2 ≤ w) :
    (A * (θ ^ 2 / 4) + C * (θ ^ 3 / 3)) / w ≤ Kleft A C := by
  have hwpos : 0 < w := lt_of_lt_of_le (by positivity) hw
  rw [div_le_iff₀ hwpos, Kleft]
  have hAB : A / 4 + C * θ / 3 ≤ A / 4 + C * Real.pi / 12 := by
    have h : θ / 3 ≤ Real.pi / 12 := by linarith [hθle, Real.pi_pos]
    nlinarith [hC, h]
  have hABnn : 0 ≤ A / 4 + C * Real.pi / 12 := by positivity
  have hcoef : 0 ≤ Real.pi ^ 2 / Real.sqrt 2 := by positivity
  have hrat : θ ^ 2 ≤ (Real.pi ^ 2 / Real.sqrt 2) * (Real.sqrt 2 * θ ^ 2 / Real.pi ^ 2) := by
    have h2 : (Real.pi ^ 2 / Real.sqrt 2) * (Real.sqrt 2 * θ ^ 2 / Real.pi ^ 2) = θ ^ 2 := by
      field_simp
      try ring
    linarith [h2]
  have hstep1 : θ ^ 2 * (A / 4 + C * Real.pi / 12)
      ≤ (Real.pi ^ 2 / Real.sqrt 2 * (A / 4 + C * Real.pi / 12))
        * (Real.sqrt 2 * θ ^ 2 / Real.pi ^ 2) := by
    have h := mul_le_mul_of_nonneg_left hrat hABnn
    calc θ ^ 2 * (A / 4 + C * Real.pi / 12)
        = (A / 4 + C * Real.pi / 12) * θ ^ 2 := by ring
      _ ≤ (A / 4 + C * Real.pi / 12)
            * ((Real.pi ^ 2 / Real.sqrt 2) * (Real.sqrt 2 * θ ^ 2 / Real.pi ^ 2)) := h
      _ = (Real.pi ^ 2 / Real.sqrt 2 * (A / 4 + C * Real.pi / 12))
            * (Real.sqrt 2 * θ ^ 2 / Real.pi ^ 2) := by ring
  calc A * (θ ^ 2 / 4) + C * (θ ^ 3 / 3)
      = θ ^ 2 * (A / 4 + C * θ / 3) := by ring
    _ ≤ θ ^ 2 * (A / 4 + C * Real.pi / 12) := mul_le_mul_of_nonneg_left hAB (sq_nonneg θ)
    _ ≤ (Real.pi ^ 2 / Real.sqrt 2 * (A / 4 + C * Real.pi / 12))
          * (Real.sqrt 2 * θ ^ 2 / Real.pi ^ 2) := hstep1
    _ ≤ (Real.pi ^ 2 / Real.sqrt 2 * (A / 4 + C * Real.pi / 12)) * w :=
        mul_le_mul_of_nonneg_left hw (mul_nonneg hcoef hABnn)

lemma Kright_arith {A C θ w : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hδ : 0 < Real.pi / 2 - θ)
    (hδle : Real.pi / 2 - θ ≤ Real.pi / 2)
    (hw : 4 * (Real.pi / 2 - θ) ^ 3 / Real.pi ^ 3 ≤ w) :
    (A * ((Real.pi / 2 - θ) ^ 3 / 6) + C * ((Real.pi / 2 - θ) ^ 4 / 4)) / w
      ≤ Kright A C := by
  set δ := Real.pi / 2 - θ with hδdef
  have hδpos : 0 < δ := hδdef ▸ hδ
  have hwpos : 0 < w := lt_of_lt_of_le (by positivity) hw
  rw [div_le_iff₀ hwpos, Kright]
  have hAB : A / 6 + C * δ / 4 ≤ A / 6 + C * Real.pi / 8 := by
    have h : δ / 4 ≤ Real.pi / 8 := by rw [hδdef]; linarith [hδle]
    nlinarith [hC, h]
  have hABnn : 0 ≤ A / 6 + C * Real.pi / 8 := by positivity
  have hcoef : 0 ≤ Real.pi ^ 3 / 4 := by positivity
  have hrat : δ ^ 3 ≤ (Real.pi ^ 3 / 4) * (4 * δ ^ 3 / Real.pi ^ 3) := by
    have h2 : (Real.pi ^ 3 / 4) * (4 * δ ^ 3 / Real.pi ^ 3) = δ ^ 3 := by
      field_simp
      try ring
    linarith [h2]
  have hstep1 : δ ^ 3 * (A / 6 + C * Real.pi / 8)
      ≤ (Real.pi ^ 3 / 4 * (A / 6 + C * Real.pi / 8)) * (4 * δ ^ 3 / Real.pi ^ 3) := by
    have h := mul_le_mul_of_nonneg_left hrat hABnn
    calc δ ^ 3 * (A / 6 + C * Real.pi / 8)
        = (A / 6 + C * Real.pi / 8) * δ ^ 3 := by ring
      _ ≤ (A / 6 + C * Real.pi / 8)
            * ((Real.pi ^ 3 / 4) * (4 * δ ^ 3 / Real.pi ^ 3)) := h
      _ = (Real.pi ^ 3 / 4 * (A / 6 + C * Real.pi / 8)) * (4 * δ ^ 3 / Real.pi ^ 3) := by ring
  calc A * (δ ^ 3 / 6) + C * (δ ^ 4 / 4)
      = δ ^ 3 * (A / 6 + C * δ / 4) := by ring
    _ ≤ δ ^ 3 * (A / 6 + C * Real.pi / 8) :=
        mul_le_mul_of_nonneg_left hAB (by positivity)
    _ ≤ (Real.pi ^ 3 / 4 * (A / 6 + C * Real.pi / 8)) * (4 * δ ^ 3 / Real.pi ^ 3) := hstep1
    _ ≤ (Real.pi ^ 3 / 4 * (A / 6 + C * Real.pi / 8)) * w :=
        mul_le_mul_of_nonneg_left hw (mul_nonneg hcoef hABnn)

/-- **The `z`-fixed bound**: the singular ODE forces `|u'| ≤ max Kleft Kright` on `(0, π/2)`. -/
lemma ode_z {u H : ℝ → ℝ → ℝ} {z A C C₁ : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁)
    (hode : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (u1fun u z)
        (H z θ - (4 * Real.cos (2 * θ) / Real.sin (2 * θ) - Real.tan θ) * u1fun u z θ) θ)
    (hH : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |H z θ| ≤ A / Real.sin (2 * θ) + C)
    (hcrude : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Real.sin (2 * θ) * u1fun u z θ| ≤ C₁) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |u1fun u z θ| ≤ max (Kleft A C) (Kright A C) := by
  intro θ hθ
  have hwpos : 0 < wfun θ := Wpos hθ
  have hG : |wfun θ * u1fun u z θ| = wfun θ * |u1fun u z θ| := by
    rw [abs_mul, abs_of_pos hwpos]
  have hcont1 : Continuous (fun t : ℝ => wfun t / Real.sin (2 * t)) := by
    have h : (fun t : ℝ => wfun t / Real.sin (2 * t))
        = fun t => Real.sin t * Real.cos t ^ 2 / 2 := by
      funext t; exact wfun_div_s2_eq t
    rw [h]; fun_prop
  have hcont2 : Continuous wfun := by
    have h : wfun = fun t : ℝ => Real.sin t ^ 2 * Real.cos t ^ 3 := rfl
    rw [h]; fun_prop
  have hsplit : ∀ a b : ℝ, ∫ t in a..b, gwt A C t
      = A * (∫ t in a..b, wfun t / Real.sin (2 * t)) + C * (∫ t in a..b, wfun t) := by
    intro a b
    have h1 : (fun t => gwt A C t)
        = fun t => A * (wfun t / Real.sin (2 * t)) + C * wfun t := by
      funext t; rw [gwt_def]
    rw [h1, intervalIntegral.integral_add]
    · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    · exact (hcont1.const_mul A).intervalIntegrable a b
    · exact (hcont2.const_mul C).intervalIntegrable a b
  rcases le_total θ (Real.pi / 4) with hle | hle
  · have hrep := left_rep (u := u) (H := H) (z := z) hA hC hC₁ hode hH hcrude ⟨hθ.1, hle⟩
    have hb1 : ∫ t in (0 : ℝ)..θ, wfun t ≤ θ ^ 3 / 3 := Wint1 ⟨hθ.1.le, hθ.2.le⟩
    have hb2 : ∫ t in (0 : ℝ)..θ, wfun t / Real.sin (2 * t) ≤ θ ^ 2 / 4 :=
      Wint2 ⟨hθ.1.le, hθ.2.le⟩
    have hnum : ∫ t in (0 : ℝ)..θ, gwt A C t ≤ A * (θ ^ 2 / 4) + C * (θ ^ 3 / 3) := by
      rw [hsplit]
      have h2 := mul_le_mul_of_nonneg_left hb2 hA
      have h3 := mul_le_mul_of_nonneg_left hb1 hC
      linarith
    have hfin : |u1fun u z θ| ≤ (A * (θ ^ 2 / 4) + C * (θ ^ 3 / 3)) / wfun θ := by
      rw [le_div_iff₀ hwpos]
      calc |u1fun u z θ| * wfun θ = |wfun θ * u1fun u z θ| := by
            rw [abs_mul, abs_of_pos hwpos, mul_comm]
        _ ≤ ∫ t in (0 : ℝ)..θ, gwt A C t := hrep
        _ ≤ A * (θ ^ 2 / 4) + C * (θ ^ 3 / 3) := hnum
    exact le_trans hfin (le_trans (Kleft_arith hA hC hθ.1 hle (Wge_left ⟨hθ.1, hle⟩))
      (le_max_left _ _))
  · have hrep := right_rep (u := u) (H := H) (z := z) hA hC hC₁ hode hH hcrude ⟨hle, hθ.2⟩
    have hb3 : ∫ t in θ..(Real.pi / 2), wfun t ≤ (Real.pi / 2 - θ) ^ 4 / 4 := Wint3 hθ
    have hb4 : ∫ t in θ..(Real.pi / 2), wfun t / Real.sin (2 * t)
        ≤ (Real.pi / 2 - θ) ^ 3 / 6 := Wint4 hθ
    have hnum : ∫ t in θ..(Real.pi / 2), gwt A C t
        ≤ A * ((Real.pi / 2 - θ) ^ 3 / 6) + C * ((Real.pi / 2 - θ) ^ 4 / 4) := by
      rw [hsplit]
      have h2 := mul_le_mul_of_nonneg_left hb4 hA
      have h3 := mul_le_mul_of_nonneg_left hb3 hC
      linarith
    have hfin : |u1fun u z θ| ≤ (A * ((Real.pi / 2 - θ) ^ 3 / 6)
        + C * ((Real.pi / 2 - θ) ^ 4 / 4)) / wfun θ := by
      rw [le_div_iff₀ hwpos]
      calc |u1fun u z θ| * wfun θ = |wfun θ * u1fun u z θ| := by
            rw [abs_mul, abs_of_pos hwpos, mul_comm]
        _ ≤ ∫ t in θ..(Real.pi / 2), gwt A C t := hrep
        _ ≤ A * ((Real.pi / 2 - θ) ^ 3 / 6) + C * ((Real.pi / 2 - θ) ^ 4 / 4) := hnum
    exact le_trans hfin (le_trans
      (Kright_arith hA hC (by linarith [hθ.2]) (by linarith [hθ.1, Real.pi_pos])
        (Wge_right ⟨hle, hθ.2⟩))
      (le_max_right _ _))

set_option maxHeartbeats 2000000 in
/-- **The singular `θ`-ODE bound, uniformly in `z`.** -/
theorem ode_deriv_bound_fam {u H : ℝ → ℝ → ℝ} {A C C₁ : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁)
    (hode : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      HasDerivAt (deriv (fun θ' => u z θ'))
        (H z θ - (4 * Real.cos (2 * θ) / Real.sin (2 * θ) - Real.tan θ)
          * deriv (fun θ' => u z θ') θ) θ)
    (hH : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |H z θ| ≤ A / Real.sin (2 * θ) + C)
    (hcrude : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Real.sin (2 * θ) * deriv (fun θ' => u z θ') θ| ≤ C₁) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |deriv (fun θ' => u z θ') θ| ≤ K := by
  refine ⟨max (max (Kleft A C) (Kright A C)) 1, ?_, ?_⟩
  · exact le_max_of_le_left (le_max_of_le_left (Kleft_nonneg hA hC))
  · intro z θ hmem
    obtain ⟨hz, hθ1, hθ2⟩ := Work.FTS_StreamBdry.mem_Qd.mp hmem
    have h := ode_z (u := u) (H := H) (z := z) hA hC hC₁
      (fun θ hθ => hode z θ ⟨hz, hθ.1, hθ.2⟩)
      (fun θ hθ => hH z θ ⟨hz, hθ.1, hθ.2⟩)
      (fun θ hθ => hcrude z θ ⟨hz, hθ.1, hθ.2⟩)
      θ ⟨hθ1, hθ2⟩
    exact le_trans h (le_max_of_le_left le_rfl)

end Work.FTS_StreamBdry.SB6.UprimeAux
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB6.psiP_bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB6.psiP_bounds` — pointwise decay and `θ`-bounds for `psiP`

* `psiP_tendsto_atTop`: `psiP z θ → 0` as `z → ∞` (gauge decomposition + decay of `Ψ`);
* `psiP_pthIter2_le`: `|∂_θ² psiP| ≤ K` from the identity `pthIter2_eq` and a bound on
  `∂_θ(psiP/sin 2θ)`;
* `psiP_unif_decay`: the uniform-in-`θ` smallness `|psiP z θ| ≤ ε·sin 2θ` for `z ≥ R` (leaf E5).
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB6

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK psiP oddPerS)

set_option autoImplicit false

/-- The pointwise decay of the `U`-slot part at `z → ∞`, from the gauge decomposition
`Ψ = psiP + κ·gaugeMode` and the decay of `Ψ`. -/
theorem psiP_tendsto_atTop {αG M : ℝ} (hαG : 0 < αG) {F Ψ : ℝ → ℝ → ℝ}
    (hsol : Work.FTS.StrongGlobal.IsBslSolPos αG F Ψ)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Filter.Tendsto (fun z => psiP αG Ψ z θ) Filter.atTop (nhds 0) := by
  obtain ⟨κ, hκ⟩ := Work.FTS_StreamBdry.sb1_gauge_proved (αG := αG) (M := M) hαG h3 hslot
  intro θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hcos : Real.cos θ ≠ 0 := ne_of_gt (Work.FTS_StreamBdry.cos_pos_of_Ioo hθ)
  -- `Ψ (·, θ) → 0`
  have h1 : Filter.Tendsto (fun z => Ψ z θ) Filter.atTop (nhds 0) := hsol.2.2.2 θ hθI
  -- `gaugeMode αG (·, θ) → 0`
  have h2 : Filter.Tendsto (fun z => Work.FTS.StreamBdryIface.gaugeMode αG z θ)
      Filter.atTop (nhds 0) := by
    have hexp : 0 < 3 / αG := by positivity
    have hz0 : Filter.Tendsto (fun z : ℝ => z ^ (-(3 / αG))) Filter.atTop (nhds 0) :=
      tendsto_rpow_neg_atTop hexp
    have h4 := hz0.div_const (Real.cos θ)
    simpa only [Work.FTS.StreamBdryIface.gaugeMode, zero_div] using h4
  have h5 : Filter.Tendsto (fun z => Ψ z θ - κ * Work.FTS.StreamBdryIface.gaugeMode αG z θ)
      Filter.atTop (nhds (0 - κ * 0)) := h1.sub (h2.const_mul κ)
  simp only [mul_zero, sub_zero] at h5
  refine h5.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with z hz
  have hmem : (z, θ) ∈ Work.Construction.Qd :=
    Work.FTS_StreamBdry.mem_Qd.mpr ⟨by linarith, hθ.1, hθ.2⟩
  rw [hκ z θ hmem]
  ring

/-- **The second `θ`-derivative of `psiP` is bounded**, given a uniform bound `Ku` on
`∂_θ(psiP/sin 2θ)` (which is what the ground-state ODE `Lgs u = F/s2` provides).

The identity is `pthIter2_eq`: for `u = psiP/sin 2θ`,
`∂_θ² psiP = -4 sin 2θ·u + 2 sin²θ·u' - F - sin 2θ·(α²D_z²u + 5α D_zu)`; the fields `u`, `D_zu`,
`D_z²u` are bounded by `M` on the quadrant (`psiP_DzLe` + the division identities) and `|F| ≤ Mf`
(`SrcOK`). -/
theorem psiP_pthIter2_le {αG M L Mf Ku : ℝ} (hαG : 0 < αG) {F Ψ : ℝ → ℝ → ℝ}
    (hsol : Work.FTS.StrongGlobal.IsBslSolPos αG F Ψ)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : Work.FTS.StreamBdryIface.SlotBd αG Ψ M)
    (hF : Work.FTS.StreamBdryIface.SrcOK F L Mf)
    (hu : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |deriv (fun θ' => psiP αG Ψ z θ' / Work.Construction.s2 θ') θ| ≤ Ku) :
    ∃ K : ℝ, 0 < K ∧ ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.pthIter 2 (psiP αG Ψ) z θ| ≤ K := by
  have hM : 0 ≤ M := M_nonneg hslot
  have hMf : 0 ≤ Mf := by
    have hθ : (Real.pi / 4 : ℝ) ∈ Work.Spaces.Iθ :=
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    exact le_trans (abs_nonneg _) (Work.FTS_StreamBdry.SrcOK.F_le hF (z := 1) (by norm_num) hθ)
  have hP3 : ContDiffOn ℝ 3 (Function.uncurry (psiP αG Ψ)) Work.Construction.Qd :=
    Work.FTS_StreamBdry.SB3.P2Aux.psiP_c3 hαG h3 hslot
  have hP2 : ContDiffOn ℝ 2 (Function.uncurry (psiP αG Ψ)) Work.Construction.Qd :=
    Work.FTS_StreamBdry.SB3.psiP_c2 hαG h3 hslot
  have hQd : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo
  have hCt : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      ContDiffAt ℝ 2 (Function.uncurry (psiP αG Ψ)) (z, θ) :=
    fun z θ h => hP2.contDiffAt (hQd.mem_nhds h)
  have hlaw : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Elliptic.bslOp αG (psiP αG Ψ) z θ = F z θ :=
    Work.FTS_StreamBdry.SB3.P2Aux.bslOp_psiP hαG hsol h3 hslot
  have hdiv := Work.FTS_StreamBdry.SB3.P2Aux.div_identities (P := psiP αG Ψ) hP3
  have hDz : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → ∀ j ≤ 2,
      |Work.Spaces.DzIter j (psiP αG Ψ) z θ| ≤ M * Work.Construction.s2 θ :=
    fun z θ h j hj => Work.FTS_StreamBdry.SB3.psiP_DzLe hαG h3 hslot z θ h j hj
  have hsp1 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → Work.Construction.s2 θ ≤ 1 := by
    intro z θ _
    rw [Work.Construction.s2_eq]
    exact Real.sin_le_one _
  -- the `D_z`-bounds for `u = psiP/s2`
  have hu0 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |psiP αG Ψ z θ / Work.Construction.s2 θ| ≤ M := by
    intro z θ h
    have hsp : 0 < Work.Construction.s2 θ := Work.FTS_StreamBdry.s2_pos_of_Qd h
    rw [abs_div, abs_of_pos hsp, div_le_iff₀ hsp]
    exact hDz z θ h 0 (by norm_num)
  have hdiv1 := fun (z θ : ℝ) (h : (z, θ) ∈ Work.Construction.Qd) =>
    hdiv.1 z θ h 1 (by norm_num)
  have hdiv2 := fun (z θ : ℝ) (h : (z, θ) ∈ Work.Construction.Qd) =>
    hdiv.1 z θ h 2 (by norm_num)
  have hu1 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.Dz (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ| ≤ M := by
    intro z θ h
    have hsp : 0 < Work.Construction.s2 θ := Work.FTS_StreamBdry.s2_pos_of_Qd h
    have heq : Work.Spaces.Dz (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ
        = Work.Spaces.DzIter 1 (psiP αG Ψ) z θ / Work.Construction.s2 θ := by
      simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using hdiv1 z θ h
    rw [heq, abs_div, abs_of_pos hsp, div_le_iff₀ hsp]
    exact hDz z θ h 1 (by norm_num)
  have hu2 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.DzIter 2 (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ| ≤ M := by
    intro z θ h
    have hsp : 0 < Work.Construction.s2 θ := Work.FTS_StreamBdry.s2_pos_of_Qd h
    rw [hdiv2 z θ h, abs_div, abs_of_pos hsp, div_le_iff₀ hsp]
    exact hDz z θ h 2 (by norm_num)
  have hKun : 0 ≤ Ku := by
    have h1 : ((1 : ℝ), Real.pi / 4) ∈ Work.Construction.Qd :=
      Work.FTS_StreamBdry.mem_Qd.mpr
        ⟨by norm_num, by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    exact le_trans (abs_nonneg _) (hu 1 (Real.pi / 4) h1)
  have hKpos : (0 : ℝ) < 4 * M + 2 * Ku + Mf + (αG ^ 2 + 5 * |αG|) * M + 1 := by
    have hc : 0 ≤ (αG ^ 2 + 5 * |αG|) * M := by positivity
    linarith
  refine ⟨_, hKpos, ?_⟩
  intro z θ hmem
  have hsp : 0 < Work.Construction.s2 θ := Work.FTS_StreamBdry.s2_pos_of_Qd hmem
  have hs2nn : 0 ≤ Work.Construction.s2 θ := le_of_lt hsp
  have hs2le : Work.Construction.s2 θ ≤ 1 := hsp1 z θ hmem
  rw [Work.FTS_StreamBdry.SB3.P2Aux.pthIter2_eq hCt hlaw z θ hmem]
  have h1 : |-4 * Work.Construction.s2 θ * (psiP αG Ψ z θ / Work.Construction.s2 θ)|
      ≤ 4 * M := by
    have habs : |(-4 : ℝ)| = 4 := by norm_num
    rw [abs_mul, abs_mul, habs, abs_of_nonneg hs2nn]
    calc 4 * Work.Construction.s2 θ * |psiP αG Ψ z θ / Work.Construction.s2 θ|
        ≤ 4 * 1 * M := by
          refine mul_le_mul (by linarith) (hu0 z θ hmem) (abs_nonneg _) (by norm_num)
      _ = 4 * M := by ring
  have h2 : |2 * Real.sin θ ^ 2
      * deriv (fun θ' => psiP αG Ψ z θ' / Work.Construction.s2 θ') θ| ≤ 2 * Ku := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.sin θ ^ 2)]
    have hs : Real.sin θ ^ 2 ≤ 1 := by
      nlinarith [Real.sin_le_one θ, Real.neg_one_le_sin θ, sq_nonneg (Real.sin θ)]
    calc 2 * Real.sin θ ^ 2 * |deriv (fun θ' => psiP αG Ψ z θ'
          / Work.Construction.s2 θ') θ|
        ≤ 2 * 1 * Ku :=
          mul_le_mul (by linarith) (hu z θ hmem) (abs_nonneg _) (by norm_num)
      _ = 2 * Ku := by ring
  have h3' : |F z θ| ≤ Mf :=
    Work.FTS_StreamBdry.SrcOK.F_le hF (Work.FTS_StreamBdry.Qd_pos hmem)
      (Work.FTS_StreamBdry.Qd_theta_Iθ hmem)
  have h4 : |Work.Construction.s2 θ
      * (αG ^ 2 * Work.Spaces.DzIter 2 (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ
        + 5 * αG * Work.Spaces.Dz
          (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ)|
      ≤ (αG ^ 2 + 5 * |αG|) * M := by
    have hb1 : |αG ^ 2 * Work.Spaces.DzIter 2
          (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ|
        ≤ αG ^ 2 * M := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ αG ^ 2)]
      exact mul_le_mul_of_nonneg_left (hu2 z θ hmem) (by positivity)
    have hb2 : |5 * αG * Work.Spaces.Dz
          (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ| ≤ 5 * |αG| * M := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 5)]
      exact mul_le_mul_of_nonneg_left (hu1 z θ hmem) (by positivity)
    have hb : |αG ^ 2 * Work.Spaces.DzIter 2
            (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ
          + 5 * αG * Work.Spaces.Dz
            (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ|
        ≤ (αG ^ 2 + 5 * |αG|) * M :=
      (abs_add_le _ _).trans (by linarith [hb1, hb2])
    rw [abs_mul, abs_of_nonneg hs2nn]
    calc Work.Construction.s2 θ * |αG ^ 2 * Work.Spaces.DzIter 2
          (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ
        + 5 * αG * Work.Spaces.Dz
          (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ|
        ≤ 1 * ((αG ^ 2 + 5 * |αG|) * M) :=
          mul_le_mul hs2le hb (abs_nonneg _) (by positivity)
      _ = (αG ^ 2 + 5 * |αG|) * M := by ring
  have htot := abs_four_sub_le h1 h2 h3' h4
  linarith [htot]



end Work.FTS_StreamBdry.SB6
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.sb2_dthDV_proved =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `sb2_dthDV_proved` — the frozen SB2 sub-leaf `StreamBdryIface.sb2_dthDV`

`∂_θ D_z V(psiP)` is bounded: the elliptic law for `psiP` (`SB3.law_psiP`) gives
`∂_θV(psiP) = -(αG²D_z² + 5αG D_z + 6)psiP - F`, and Clairaut (with `psiP ∈ C²`, `SB3.psiP_c2`)
turns `∂_θ D_zV(psiP)` into `D_z∂_θV(psiP)`, bounded by the `D_z^3` bound `hD3` and `|D_zF| ≤ Mf`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_StreamBdry

open Work.FTS.StreamBdryIface (SlotBd SrcOK psiP)
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **SB2 sub-leaf proved** (frozen type `sb2_dthDV`). -/
theorem sb2_dthDV_proved {αG M L Mf : ℝ} (hαG : 0 < αG) {F Ψ : Fn}
    (hsol : Work.FTS.StrongGlobal.IsBslSolPos αG F Ψ)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M) (hF : SrcOK F L Mf)
    (hD3 : ∃ K : ℝ, ∀ z θ, (z, θ) ∈ Work.Construction.Qd → ∀ j ≤ 3,
      |Work.Spaces.DzIter j (psiP αG Ψ) z θ| ≤ K * Work.Construction.s2 θ) :
    ∃ K' : ℝ, ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.pth (Work.Spaces.DzIter 1
        (Work.Construction.Vop (psiP αG Ψ))) z θ| ≤ K' :=
  SB2.sb2_dthDV hαG hsol h3 hslot hF hD3

end Work.FTS_StreamBdry
end
end
