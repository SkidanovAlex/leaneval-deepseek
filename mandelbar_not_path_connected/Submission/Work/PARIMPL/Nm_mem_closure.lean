import Mathlib
import Submission.Work.PARIMPL.Basic
import Submission.Work.FBif.Main

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.PARIMPL.Nm_mem_closure` — `Nm` accumulates at the root parameter

The root parameter `c₀` of the period-`5` component lies in the closure of the **implosion
side** `P.Nm = {c ∈ ball c₀ ρ₀ | a₂ c < 0}` of a parameter normal form `P : ParNormal d`.

The argument is the FBif bifurcation side (`Work.FBif.bifSide`): arbitrarily close to `c₀` there
are parameters `c'` for which `(T_{c'})^[5]` has **no** fixed point in a fixed disc around the
parabolic point `z₁`.  We show that every such `c'` *must* have `a₂ c' < 0`, i.e. lie on the
implosion side:

* if `a₂ c' > 0`, then `P.fix` exhibits the two fixed points `m ± s·a` of the antiholomorphic
  square root `g = (T·)^[5]`, and for `c'` close to `c₀` they sit in the disc around `z₁`;
* if `a₂ c' = 0`, then `a c' = 0`, the chart centre `m c'` is a parabolic fixed point of
  `F = g ∘ g`, it is the only `F`-fixed point in the chart (the normal form is `ζ + ζ²h(ζ)`
  there), and since `g` maps `F`-fixed points to `F`-fixed points, `g` fixes `m c'` — again a
  period-`5` point.

Both cases are a continuity argument in `c` at `c₀` (`a₂ c₀ = 0`, `m c₀ = z₁`, `g c₀ z₁ = z₁`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

variable {c₀ : ℂ}

/-! ## Joint continuity of the antiholomorphic fifth iterate -/

/-- The uncurried map `(c, z) ↦ g c z = (T_c)^[5] z` is continuous. -/
theorem continuous_uncurry_gtc : Continuous (fun q : ℂ × ℂ => gtc q.1 q.2) := by
  have hG : Continuous fun q : ℂ × ℂ => (q.1, Tantibar q.1 q.2) := by
    unfold LeanEval.ComplexAnalysis.Tantibar
    exact continuous_fst.prodMk
      (((continuous_star.comp continuous_snd).pow 2).add continuous_fst)
  have hΦ : ∀ n : ℕ, Continuous fun q : ℂ × ℂ => (Tantibar q.1)^[n] q.2 := by
    intro n
    induction n with
    | zero => simpa using continuous_snd
    | succ n ih =>
      have hthis : (fun q : ℂ × ℂ => (Tantibar q.1)^[n.succ] q.2)
          = fun q : ℂ × ℂ => (Tantibar q.1)^[n] (Tantibar q.1 q.2) := by
        funext q
        rw [Function.iterate_succ_apply]
      rw [hthis]
      exact ih.comp hG
  simpa [gtc] using hΦ 5

/-! ## The degenerate case `a₂ = 0`: the square root fixes the parabolic point -/

/-- At a parameter `c` where `a₂ c = 0`, the antiholomorphic square root `g c = (T_c)^[5]`
fixes the chart centre `m c`.  Indeed `a c = 0`, so the normal form is `ζ + ζ²h(ζ)` and `m c`
is the only fixed point of `F c = g c ∘ g c` in the chart; `g` maps `F`-fixed points to
`F`-fixed points, and `g (m c)` is again in the chart when `c` is close enough to `c₀`. -/
theorem gtc_m_eq_self_of_a2_zero {d : Work.EL.RootParabolic c₀} (P : ParNormal d) {c : ℂ}
    (hc : c ∈ ball c₀ P.ρ₀) (ha2 : P.a2 c = 0)
    (hsmall : ‖gtc c (P.m c) - P.m c‖ < ‖P.s c₀‖ / 2 * P.r)
    (hsbig : ‖P.s c₀‖ / 2 ≤ ‖P.s c‖) :
    gtc c (P.m c) = P.m c := by
  have hs_ne : P.s c ≠ 0 := P.s_ne c hc
  have hspos : 0 < ‖P.s c‖ := norm_pos_iff.mpr hs_ne
  have ha0 : P.a c = 0 := by
    have h := P.a_sq c hc
    rw [ha2] at h
    simp only [Complex.ofReal_zero] at h
    exact sq_eq_zero_iff.mp h
  -- `m c` is a fixed point of `F c`
  have hFfix : Ft c (P.m c) = P.m c := by
    have h := P.conj c hc (0 : ℂ)
      (by rw [Metric.mem_ball, dist_zero_right, norm_zero]; exact P.hr)
    simpa [ha0, Work.Implosion.normalForm] using h
  -- `g` maps `F`-fixed points to `F`-fixed points
  have hcomp : gtc c (gtc c (P.m c)) = P.m c := by
    have h := hFfix
    rwa [Ft_eq_g_comp, Function.comp_apply] at h
  have hFg : Ft c (gtc c (P.m c)) = gtc c (P.m c) := by
    rw [Ft_eq_g_comp, Function.comp_apply]
    exact congrArg (gtc c) hcomp
  -- the chart coordinate of `g (m c)` is small
  have hζlt : ‖(gtc c (P.m c) - P.m c) / P.s c‖ < P.r := by
    rw [norm_div, div_lt_iff₀ hspos]
    have h1 : ‖P.s c₀‖ / 2 * P.r ≤ ‖P.s c‖ * P.r :=
      mul_le_mul_of_nonneg_right hsbig (le_of_lt P.hr)
    linarith [hsmall, h1]
  have hζball : (gtc c (P.m c) - P.m c) / P.s c ∈ ball (0 : ℂ) P.r := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hζlt
  -- `g (m c)` is the only possible `F`-fixed point in the chart
  have hnfix : Work.Implosion.normalForm (P.a c) (P.h c)
      ((gtc c (P.m c) - P.m c) / P.s c) = (gtc c (P.m c) - P.m c) / P.s c := by
    have h := P.conj c hc ((gtc c (P.m c) - P.m c) / P.s c) hζball
    have hza : P.m c + P.s c * ((gtc c (P.m c) - P.m c) / P.s c) = gtc c (P.m c) := by
      rw [mul_div_cancel₀ _ hs_ne]
      ring
    have h2 : P.m c + P.s c * Work.Implosion.normalForm (P.a c) (P.h c)
        ((gtc c (P.m c) - P.m c) / P.s c)
        = P.m c + P.s c * ((gtc c (P.m c) - P.m c) / P.s c) := by
      rw [← h, hza, hFg]
    exact mul_left_cancel₀ hs_ne (add_left_cancel h2)
  have hζ0 : (gtc c (P.m c) - P.m c) / P.s c = 0 := by
    rcases (P.normalForm_eq_self_iff hc hζlt).mp hnfix with h3 | h3
    · rw [ha0] at h3; exact h3
    · rw [ha0, neg_zero] at h3; exact h3
  have hzero : gtc c (P.m c) - P.m c = 0 := by
    have h := div_mul_cancel₀ (gtc c (P.m c) - P.m c) hs_ne
    rw [hζ0, zero_mul] at h
    exact h.symm
  exact sub_eq_zero.mp hzero

/-! ## The main theorem -/

/-- **`Work.PARIMPL.Nm_mem_closure`**: the implosion side of a parameter normal form
accumulates at the root parameter.  This discharges the `c_mem_closure` residual of
`Work.PARIMPL.ParImplInputs`. -/
theorem Nm_mem_closure {c₀ : ℂ} (d : Work.EL.RootParabolic c₀)
    (P : Work.PARIMPL.ParNormal d) : c₀ ∈ closure P.Nm := by
  obtain ⟨δ, hδ, hfb⟩ := Work.FBif.bifSide c₀ d
  have hc₀ : c₀ ∈ ball c₀ P.ρ₀ := by simpa using P.hρ₀
  have hs₀ : 0 < ‖P.s c₀‖ := norm_pos_iff.mpr (P.s_ne c₀ hc₀)
  have hKpos : 0 < δ / (2 * (‖P.s c₀‖ + 1)) := by positivity
  have hbound : 0 < ‖P.s c₀‖ / 2 * P.r := mul_pos (by linarith) P.hr
  -- the neighbourhood of `c₀` on which all the smallness conditions hold
  have hU₀ : ball c₀ P.ρ₀ ∈ 𝓝 c₀ := isOpen_ball.mem_nhds hc₀
  have hU₁ : {c : ℂ | ‖P.m c - d.z₁‖ < δ / 2} ∈ 𝓝 c₀ := by
    have hm : ContinuousAt (fun c : ℂ => ‖P.m c - d.z₁‖) c₀ :=
      ((P.cont_m.continuousAt hU₀).sub continuousAt_const).norm
    have h0 : ‖P.m c₀ - d.z₁‖ = 0 := by rw [P.m₀, sub_self, norm_zero]
    have hmem : (fun c : ℂ => ‖P.m c - d.z₁‖) ⁻¹' Set.Iio (δ / 2) ∈ 𝓝 c₀ :=
      hm.tendsto.eventually
        (by rw [h0]; exact isOpen_Iio.mem_nhds (show (0 : ℝ) < δ / 2 by linarith))
    exact hmem
  have hU₂ : {c : ℂ | ‖P.s c₀‖ / 2 < ‖P.s c‖} ∈ 𝓝 c₀ := by
    have hs : ContinuousAt (fun c : ℂ => ‖P.s c‖) c₀ := (P.cont_s.continuousAt hU₀).norm
    have hmem : (fun c : ℂ => ‖P.s c‖) ⁻¹' Set.Ioi (‖P.s c₀‖ / 2) ∈ 𝓝 c₀ :=
      hs.tendsto.eventually (isOpen_Ioi.mem_nhds
        (show ‖P.s c₀‖ / 2 < ‖P.s c₀‖ by linarith))
    exact hmem
  have hU₃ : {c : ℂ | ‖P.s c‖ < ‖P.s c₀‖ + 1} ∈ 𝓝 c₀ := by
    have hs : ContinuousAt (fun c : ℂ => ‖P.s c‖) c₀ := (P.cont_s.continuousAt hU₀).norm
    have hmem : (fun c : ℂ => ‖P.s c‖) ⁻¹' Set.Iio (‖P.s c₀‖ + 1) ∈ 𝓝 c₀ :=
      hs.tendsto.eventually (isOpen_Iio.mem_nhds
        (show ‖P.s c₀‖ < ‖P.s c₀‖ + 1 by linarith))
    exact hmem
  have hU₄ : {c : ℂ | |P.a2 c| < (δ / (2 * (‖P.s c₀‖ + 1))) ^ 2} ∈ 𝓝 c₀ := by
    have ha : ContinuousAt (fun c : ℂ => |P.a2 c|) c₀ := (P.cont_a2.continuousAt hU₀).abs
    have h0 : |P.a2 c₀| = 0 := by rw [P.a2₀, abs_zero]
    have hmem : (fun c : ℂ => |P.a2 c|) ⁻¹'
        Set.Iio ((δ / (2 * (‖P.s c₀‖ + 1))) ^ 2) ∈ 𝓝 c₀ :=
      ha.tendsto.eventually (by
        rw [h0]
        exact isOpen_Iio.mem_nhds
          (show (0 : ℝ) < (δ / (2 * (‖P.s c₀‖ + 1))) ^ 2 from pow_pos hKpos 2))
    exact hmem
  have hU₅ : {c : ℂ | ‖gtc c (P.m c) - P.m c‖ < ‖P.s c₀‖ / 2 * P.r} ∈ 𝓝 c₀ := by
    have hpair : ContinuousAt (fun c : ℂ => (c, P.m c)) c₀ :=
      continuousAt_id.prodMk (P.cont_m.continuousAt hU₀)
    have hcont' : ContinuousAt
        ((fun q : ℂ × ℂ => gtc q.1 q.2) ∘ (fun c : ℂ => (c, P.m c))) c₀ :=
      continuous_uncurry_gtc.continuousAt.comp hpair
    have hcont : ContinuousAt (fun c : ℂ => gtc c (P.m c)) c₀ := by
      refine hcont'.congr ?_
      filter_upwards with c
      rfl
    have hfn : ‖gtc c₀ (P.m c₀) - P.m c₀‖ = 0 := by
      have h1 : gtc c₀ (P.m c₀) = P.m c₀ := by
        rw [P.m₀]
        exact d.per_half
      rw [h1, sub_self, norm_zero]
    have hcont2 : ContinuousAt (fun c : ℂ => ‖gtc c (P.m c) - P.m c‖) c₀ := by
      have hsub : ContinuousAt (fun c : ℂ => gtc c (P.m c) - P.m c) c₀ :=
        hcont.sub (P.cont_m.continuousAt hU₀)
      exact hsub.norm
    have hmem : (fun c : ℂ => ‖gtc c (P.m c) - P.m c‖) ⁻¹'
        Set.Iio (‖P.s c₀‖ / 2 * P.r) ∈ 𝓝 c₀ :=
      hcont2.tendsto.eventually
        (by rw [hfn]; exact isOpen_Iio.mem_nhds (show (0 : ℝ) < ‖P.s c₀‖ / 2 * P.r from hbound))
    exact hmem
  have hGmem : (ball c₀ P.ρ₀ ∩ {c : ℂ | ‖P.m c - d.z₁‖ < δ / 2} ∩
      {c : ℂ | ‖P.s c₀‖ / 2 < ‖P.s c‖} ∩ {c : ℂ | ‖P.s c‖ < ‖P.s c₀‖ + 1} ∩
      {c : ℂ | |P.a2 c| < (δ / (2 * (‖P.s c₀‖ + 1))) ^ 2} ∩
      {c : ℂ | ‖gtc c (P.m c) - P.m c‖ < ‖P.s c₀‖ / 2 * P.r}) ∈ 𝓝 c₀ :=
    Filter.inter_mem (Filter.inter_mem (Filter.inter_mem (Filter.inter_mem
      (Filter.inter_mem hU₀ hU₁) hU₂) hU₃) hU₄) hU₅
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp hGmem
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨c', hc'ball, hc'noper⟩ := hfb (min ρ ε / 2) (by have := lt_min hρ hε; linarith)
  have hc'ρ : c' ∈ ball c₀ ρ := by
    rw [Metric.mem_ball] at hc'ball ⊢
    have h1 : min ρ ε / 2 < ρ := by have := min_le_left ρ ε; linarith
    linarith
  have hGc' := hρsub hc'ρ
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hGc'
  obtain ⟨⟨⟨⟨⟨hc'ρ₀, hm'⟩, hsbig'⟩, hssmall'⟩, ha2small'⟩, hgsmall'⟩ := hGc'
  have ha2neg : P.a2 c' < 0 := by
    by_contra hcon
    have hge : 0 ≤ P.a2 c' := le_of_not_gt hcon
    rcases lt_or_eq_of_le hge with hgt | heq
    · -- `a₂ c' > 0`: the square root fixes both split points, one of which is a period-5 point
      have hsa : ‖P.s c' * P.a c'‖ < δ / 2 := by
        have ha_norm : ‖P.a c'‖ = Real.sqrt |P.a2 c'| := by
          have h2 : ‖P.a c'‖ ^ 2 = |P.a2 c'| := by
            rw [← norm_pow, P.a_sq c' hc'ρ₀, Complex.norm_real, Real.norm_eq_abs]
          rw [← h2, Real.sqrt_sq (norm_nonneg _)]
        have hsqrt : Real.sqrt |P.a2 c'| < δ / (2 * (‖P.s c₀‖ + 1)) :=
          (Real.sqrt_lt' hKpos).mpr ha2small'
        have h1 : (‖P.s c₀‖ + 1) * (δ / (2 * (‖P.s c₀‖ + 1))) = δ / 2 := by
          field_simp
        rw [norm_mul, ha_norm]
        calc ‖P.s c'‖ * Real.sqrt |P.a2 c'|
            < (‖P.s c₀‖ + 1) * (δ / (2 * (‖P.s c₀‖ + 1))) :=
              mul_lt_mul'' hssmall' hsqrt (norm_nonneg _) (Real.sqrt_nonneg _)
          _ = δ / 2 := h1
      have hzmem : P.m c' + P.s c' * P.a c' ∈ ball d.z₁ δ := by
        rw [Metric.mem_ball, dist_eq_norm]
        have harg : P.m c' + P.s c' * P.a c' - d.z₁
            = (P.m c' - d.z₁) + P.s c' * P.a c' := by ring
        rw [harg]
        calc ‖(P.m c' - d.z₁) + P.s c' * P.a c'‖
            ≤ ‖P.m c' - d.z₁‖ + ‖P.s c' * P.a c'‖ := norm_add_le _ _
          _ < δ / 2 + δ / 2 := add_lt_add hm' hsa
          _ = δ := by ring
      exact hc'noper _ hzmem (P.fix c' hc'ρ₀ hgt).1
    · -- `a₂ c' = 0`: the parabolic point `m c'` is fixed by the square root
      refine hc'noper _ ?_ (gtc_m_eq_self_of_a2_zero P hc'ρ₀ heq.symm hgsmall'
        (le_of_lt hsbig'))
      rw [Metric.mem_ball, dist_eq_norm]
      linarith [hm', hδ]
  refine ⟨c', ⟨hc'ρ₀, ha2neg⟩, ?_⟩
  have hd : dist c' c₀ < min ρ ε / 2 := Metric.mem_ball.mp hc'ball
  have h1 : min ρ ε / 2 < ε := by have := min_le_right ρ ε; linarith
  rw [dist_comm]
  linarith

end Work.PARIMPL
