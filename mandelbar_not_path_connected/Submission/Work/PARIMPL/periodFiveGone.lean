import Mathlib
import Submission.Work.PARIMPL.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- In `ℂ`, `m + w = m - w` forces `w = 0`. -/
private theorem add_eq_sub_eq_zero {m w : ℂ} (h : m + w = m - w) : w = 0 := by
  rw [sub_eq_add_neg] at h
  have h1 : w = -w := add_left_cancel h
  have h2 : w + w = 0 := by nth_rewrite 1 [h1]; exact neg_add_cancel w
  exact add_self_eq_zero.mp h2

theorem periodFiveGone {c₀ : ℂ} (d : Work.EL.RootParabolic c₀)
    (P : Work.PARIMPL.ParNormal d) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ c' ∈ P.Nm ∩ Metric.ball c₀ ρ, ∀ z ∈ Metric.ball d.z₁ δ,
        (LeanEval.ComplexAnalysis.Tantibar c')^[5] z ≠ z := by
  have hc₀ : c₀ ∈ Metric.ball c₀ P.ρ₀ := by simpa using P.hρ₀
  have hS : 0 < ‖P.s c₀‖ := norm_pos_iff.mpr (P.s_ne c₀ hc₀)
  have hcont_s : ContinuousAt P.s c₀ := P.cont_s.continuousAt (isOpen_ball.mem_nhds hc₀)
  have hcont_m : ContinuousAt P.m c₀ := P.cont_m.continuousAt (isOpen_ball.mem_nhds hc₀)
  -- a ball on which `‖s‖ ≥ ‖s c₀‖/2`
  obtain ⟨ρ₁, hρ₁, hρ₁sub⟩ :=
    Metric.continuousAt_iff.mp hcont_s.norm (‖P.s c₀‖ / 2) (by linarith)
  -- a ball on which `m` moves at most `r‖s c₀‖/4`
  obtain ⟨ρ₂, hρ₂, hρ₂sub⟩ :=
    Metric.continuousAt_iff.mp hcont_m (P.r * ‖P.s c₀‖ / 4)
      (div_pos (mul_pos P.hr hS) (by norm_num))
  have hU₁ : {c : ℂ | ‖P.s c₀‖ / 2 < ‖P.s c‖} ∈ 𝓝 c₀ := by
    refine Filter.mem_of_superset (Metric.ball_mem_nhds c₀ hρ₁) fun c hc => ?_
    have hd : dist ‖P.s c‖ ‖P.s c₀‖ < ‖P.s c₀‖ / 2 := hρ₁sub hc
    rw [Real.dist_eq] at hd
    have h2 := abs_lt.mp hd
    show ‖P.s c₀‖ / 2 < ‖P.s c‖
    linarith [h2.1, h2.2]
  have hU₂ : {c : ℂ | ‖P.m c - P.m c₀‖ < P.r * ‖P.s c₀‖ / 4} ∈ 𝓝 c₀ := by
    refine Filter.mem_of_superset (Metric.ball_mem_nhds c₀ hρ₂) fun c hc => ?_
    have hd : dist (P.m c) (P.m c₀) < P.r * ‖P.s c₀‖ / 4 := hρ₂sub hc
    rwa [dist_eq_norm] at hd
  have hU : ({c : ℂ | ‖P.s c₀‖ / 2 < ‖P.s c‖} ∩
      {c : ℂ | ‖P.m c - P.m c₀‖ < P.r * ‖P.s c₀‖ / 4}) ∩ Metric.ball c₀ P.ρ₀
      ∈ 𝓝 c₀ :=
    Filter.inter_mem (Filter.inter_mem hU₁ hU₂) (Metric.ball_mem_nhds c₀ P.hρ₀)
  obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨ρ, hρ, P.r * ‖P.s c₀‖ / 4,
    div_pos (mul_pos P.hr hS) (by norm_num), ?_⟩
  intro c' hc' z hz hfix
  obtain ⟨hc'Nm, hc'ρ⟩ := hc'
  obtain ⟨hAB, hc'ρ₀⟩ := hsub hc'ρ
  obtain ⟨hA, hB⟩ := hAB
  have hA' : ‖P.s c₀‖ / 2 < ‖P.s c'‖ := hA
  have hB' : ‖P.m c' - P.m c₀‖ < P.r * ‖P.s c₀‖ / 4 := hB
  have ha2 : P.a2 c' < 0 := (ParNormal.mem_Nm P).mp hc'Nm |>.2
  have hspos : (0 : ℝ) < ‖P.s c'‖ := by linarith
  have hsne : P.s c' ≠ 0 := by
    intro h'; rw [h', norm_zero] at hspos; linarith
  have hzδ : ‖z - d.z₁‖ < P.r * ‖P.s c₀‖ / 4 := by
    rw [Metric.mem_ball, dist_eq_norm] at hz; exact hz
  have hm_eq : ‖d.z₁ - P.m c'‖ = ‖P.m c' - P.m c₀‖ := by
    rw [norm_sub_rev d.z₁ (P.m c'), ← P.m₀]
  have hsplit : z - P.m c' = (z - d.z₁) + (d.z₁ - P.m c') := by ring
  have hnum : ‖z - P.m c'‖ < P.r * ‖P.s c₀‖ / 2 := by
    calc ‖z - P.m c'‖ = ‖(z - d.z₁) + (d.z₁ - P.m c')‖ := by rw [hsplit]
      _ ≤ ‖z - d.z₁‖ + ‖d.z₁ - P.m c'‖ := norm_add_le _ _
      _ = ‖z - d.z₁‖ + ‖P.m c' - P.m c₀‖ := by rw [hm_eq]
      _ < P.r * ‖P.s c₀‖ / 4 + P.r * ‖P.s c₀‖ / 4 := add_lt_add hzδ hB'
      _ = P.r * ‖P.s c₀‖ / 2 := by ring
  -- the chart coordinate of `z`
  have hζlt : ‖(z - P.m c') / P.s c'‖ < P.r := by
    rw [norm_div, div_lt_iff₀ hspos]
    have h1 : P.r * ‖P.s c₀‖ / 2 ≤ P.r * ‖P.s c'‖ := by nlinarith [P.hr, hA']
    linarith
  have hζmem : (z - P.m c') / P.s c' ∈ Metric.ball (0 : ℂ) P.r := by
    rw [Metric.mem_ball, dist_zero_right]; exact hζlt
  have hza : P.m c' + P.s c' * ((z - P.m c') / P.s c') = z := by
    field_simp; ring
  have hFz : Ft c' z = z := Ft_fixed_of_gtc_fixed hfix
  have hconj := P.conj c' hc'ρ₀ ((z - P.m c') / P.s c') hζmem
  have hnfc : Work.Implosion.normalForm (P.a c') (P.h c') ((z - P.m c') / P.s c')
      = (z - P.m c') / P.s c' := by
    have h3 : P.m c' + P.s c' *
        Work.Implosion.normalForm (P.a c') (P.h c') ((z - P.m c') / P.s c')
        = P.m c' + P.s c' * ((z - P.m c') / P.s c') := by
      rw [← hconj, hza, hFz]
    exact mul_left_cancel₀ hsne (add_left_cancel h3)
  have hζ0 : (z - P.m c') / P.s c' = P.a c' ∨ (z - P.m c') / P.s c' = -P.a c' :=
    (P.normalForm_eq_self_iff hc'ρ₀ hζlt).mp hnfc
  have hane : P.a c' ≠ 0 := by
    rw [P.a_of_mem_Nm hc'Nm]
    exact mul_ne_zero
      (by exact_mod_cast ne_of_gt (P.lam_pos_of_mem_Nm hc'Nm)) Complex.I_ne_zero
  rcases hζ0 with ha | ha
  · -- `z` is the "left" split fixed point of `F`, which `g` does not fix
    have hz_eq : z = P.m c' + P.s c' * P.a c' := by rw [← hza, ha]
    have hw : P.m c' + P.s c' * P.a c' = P.m c' - P.s c' * P.a c' :=
      calc P.m c' + P.s c' * P.a c' = z := hz_eq.symm
        _ = gtc c' z := hfix.symm
        _ = gtc c' (P.m c' + P.s c' * P.a c') := by rw [hz_eq]
        _ = P.m c' - P.s c' * P.a c' := P.swap c' hc'ρ₀ ha2
    exact mul_ne_zero hsne hane (add_eq_sub_eq_zero hw)
  · -- `z` is the "right" split fixed point; then `g z` is the left one
    have hz_eq : z = P.m c' - P.s c' * P.a c' := by rw [← hza, ha]; ring
    have ha_lt : ‖P.a c'‖ < P.r := by
      have h := hζlt; rwa [ha, norm_neg] at h
    have ha_mem : P.a c' ∈ Metric.ball (0 : ℂ) P.r := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact ha_lt
    have hFleft : Ft c' (P.m c' + P.s c' * P.a c') = P.m c' + P.s c' * P.a c' := by
      rw [P.conj c' hc'ρ₀ (P.a c') ha_mem, Work.Implosion.normalForm_fixed_left]
    have hgg : gtc c' (gtc c' (P.m c' + P.s c' * P.a c'))
        = Ft c' (P.m c' + P.s c' * P.a c') := by
      rw [Ft_eq_g_comp]; rfl
    have hw : P.m c' + P.s c' * P.a c' = P.m c' - P.s c' * P.a c' :=
      calc P.m c' + P.s c' * P.a c'
          = gtc c' (gtc c' (P.m c' + P.s c' * P.a c')) := by rw [hgg, hFleft]
        _ = gtc c' (P.m c' - P.s c' * P.a c') := by rw [P.swap c' hc'ρ₀ ha2]
        _ = gtc c' z := by rw [← hz_eq]
        _ = z := hfix
        _ = P.m c' - P.s c' * P.a c' := hz_eq
    exact mul_ne_zero hsne hane (add_eq_sub_eq_zero hw)

end Work.PARIMPL
