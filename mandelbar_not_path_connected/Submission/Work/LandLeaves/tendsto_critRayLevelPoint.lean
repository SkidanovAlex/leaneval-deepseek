import Mathlib
import Submission.Work.LANDCL.Defs
import Submission.Work.LandLeaves.Defs
import Submission.Work.LandLeaves.rayAccum_entry
import Submission.Work.LandLeaves.dynBottcherOnlyOnMandelbar
import Submission.Work.Landing.Rays.levelPoint_of_mem_mandelbar
import Submission.Work.NAKANE.All
import Submission.Work.Bottcher.CritBottcherExists

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Topology

namespace Work.LandLeaves

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **A critical-domain point of Böttcher level `t > 1` is bounded.**

If `z` lies in the critical domain of the parameter `f` and its Böttcher coordinate has modulus
`t > 1`, then `‖z‖` is bounded by a constant depending only on a bound `C ≥ ‖f‖` for the
parameter and on `t`.

Indeed, `‖varphiCrit f z‖ = exp (G_f z)` (`Work.ParamRays.IsCritBottcher_modulus`), so
`G_f z = log t`; if moreover `‖z‖ > max 2 C ≥ max 2 ‖f‖`, then `z` lies in the escape region of
`f`, where `log (‖z‖/2) ≤ G_f z` (`Work.Escape.log_half_le_green`); hence `‖z‖ ≤ 2 t`. -/
theorem norm_le_of_norm_varphiCrit {C t : ℝ} {f z : ℂ} (ht : 1 < t) (hf : ‖f‖ ≤ C)
    (hz : z ∈ Work.ParamRays.critDomain f)
    (h : ‖Work.Bottcher.varphiCrit f z‖ = t) :
    ‖z‖ ≤ max (max 2 C) (2 * t) := by
  by_contra hcon
  push_neg at hcon
  have hR : max 2 C < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hcon
  -- the Green function at `z` is `log t`
  have hmod := Work.ParamRays.IsCritBottcher_modulus
    (Work.Bottcher.isCritBottcher_varphiCrit f) hz
  have hgreen : Work.ParamRays.greenFun f z = Real.log t := by
    rw [hmod] at h
    rw [← h, Real.log_exp]
  -- `z` lies in the escape region of `f`
  have hregion : z ∈ Work.Escape.escapeRegion ‖f‖ := by
    rw [Work.Escape.mem_escapeRegion]
    exact lt_of_le_of_lt (max_le_max le_rfl hf) hR
  have hlog := Work.Escape.log_half_le_green (Tantibar f) 2 ‖f‖
    (Work.Escape.monicGrowth_Tantibar f) le_rfl hregion
  rw [← Work.NAKANE.greenFun_eq_green, hgreen] at hlog
  -- conclude `‖z‖ ≤ 2 t`
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have h2z : (2 : ℝ) < ‖z‖ := lt_of_le_of_lt (le_max_left 2 C) hR
  have hz0 : 0 < ‖z‖ / 2 := by linarith
  have hle : ‖z‖ / 2 ≤ t := (Real.log_le_log_iff hz0 ht0).mp hlog
  have hzt : ‖z‖ ≤ 2 * t := by linarith
  linarith [hzt, le_max_right (max 2 C) (2 * t)]

theorem tendsto_critRayLevelPoint {c : ℂ} (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar) {θ : ℝ}
    {t₀ : ℝ} (ht : 1 < t₀) :
    ∀ ε > 0, ∃ δ > 0, ∀ f : ℂ, ‖f - c‖ < δ → ∀ z : ℂ, z ∈ Work.ParamRays.critDomain f →
      Work.Bottcher.varphiCrit f z = (t₀ : ℂ) * Work.ParamRays.rayDir θ →
      ∃ z₀ : ℂ, z₀ ∈ Work.ParamRays.critDomain c ∧
        Work.Bottcher.varphiCrit c z₀ = (t₀ : ℂ) * Work.ParamRays.rayDir θ ∧ ‖z - z₀‖ ≤ ε := by
  intro ε hε
  set w : ℂ := (t₀ : ℂ) * Work.ParamRays.rayDir θ with hwdef
  have hwnorm : ‖w‖ = t₀ := by
    rw [hwdef, norm_mul, Work.ParamRays.norm_rayDir, mul_one]
    exact Complex.norm_of_nonneg (le_of_lt (lt_trans zero_lt_one ht))
  -- the (unique) level point at the limit parameter `c`
  obtain ⟨z₀, hz₀P, hz₀uniq⟩ :=
    Work.Landing.Rays.levelPoint_of_mem_mandelbar c hc ht θ
  have hz₀esc : Work.ParamRays.Escaping c z₀ := hz₀P.1
  have hz₀val : ∀ φ : ℂ → ℂ, Work.ParamRays.IsDynBottcher c φ → φ z₀ = w := hz₀P.2
  have hz₀crit : z₀ ∈ Work.ParamRays.critDomain c := by
    rw [Work.ParamRays.critDomain_eq_escapingSet hc]
    exact hz₀esc
  have hdyn : Work.ParamRays.IsDynBottcher c (Work.Bottcher.varphiCrit c) :=
    (Work.ParamRays.isCritBottcher_iff_isDynBottcher hc).mp
      (Work.Bottcher.isCritBottcher_varphiCrit c)
  have hz₀φ : Work.Bottcher.varphiCrit c z₀ = w := by
    rw [hwdef]
    exact hz₀val _ hdyn
  -- it suffices to exclude an arbitrarily close *bad* sequence of parameters
  by_contra hcon
  have hcon' : ∀ δ : ℝ, 0 < δ → ∃ f : ℂ, ‖f - c‖ < δ ∧ ∃ z : ℂ,
      z ∈ Work.ParamRays.critDomain f ∧ Work.Bottcher.varphiCrit f z = w ∧ ε < ‖z - z₀‖ := by
    intro δ hδ
    by_contra h
    refine hcon ⟨δ, hδ, fun f hf z hz hzv => ?_⟩
    exact ⟨z₀, hz₀crit, hz₀φ,
      not_lt.mp fun hlt => h ⟨f, hf, z, hz, hzv, hlt⟩⟩
  have hex : ∀ n : ℕ, ∃ f : ℂ, ‖f - c‖ < 1 / ((n : ℝ) + 1) ∧ ∃ z : ℂ,
      z ∈ Work.ParamRays.critDomain f ∧ Work.Bottcher.varphiCrit f z = w ∧ ε < ‖z - z₀‖ :=
    fun n => hcon' (1 / ((n : ℝ) + 1)) (by positivity)
  choose fseq hfspec using hex
  choose zseq hzspec using fun n => (hfspec n).2
  -- the sequence of parameters converges to `c`
  have hfn_le : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ 1 := by
    intro n
    rw [div_le_iff₀ (by positivity)]
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hfseq : Tendsto fseq atTop (𝓝 c) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _)
      (fun n => le_of_lt (hfspec n).1)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  -- and all the level points stay in a fixed ball
  set C : ℝ := ‖c‖ + 1 with hCdef
  have hfnorm : ∀ n : ℕ, ‖fseq n‖ ≤ C := by
    intro n
    have h1 : ‖fseq n - c‖ < 1 := lt_of_lt_of_le (hfspec n).1 (hfn_le n)
    have h2 : ‖fseq n‖ ≤ ‖fseq n - c‖ + ‖c‖ := by
      calc ‖fseq n‖ = ‖(fseq n - c) + c‖ := by ring_nf
        _ ≤ ‖fseq n - c‖ + ‖c‖ := norm_add_le _ _
    rw [hCdef]
    linarith
  set M : ℝ := max (max 2 C) (2 * t₀) with hMdef
  have hbound : ∀ n : ℕ, ‖zseq n‖ ≤ M := by
    intro n
    have hzval : ‖Work.Bottcher.varphiCrit (fseq n) (zseq n)‖ = t₀ := by
      rw [(hzspec n).2.1, hwnorm]
    have := norm_le_of_norm_varphiCrit ht (hfnorm n) (hzspec n).1 hzval
    rwa [hMdef]
  -- pass to a convergent subsequence
  have hmem : ∀ n : ℕ, zseq n ∈ Metric.closedBall (0 : ℂ) M := by
    intro n
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hbound n
  obtain ⟨zlim, _, φ, hφmono, hφtend⟩ :=
    (isCompact_closedBall (0 : ℂ) M).tendsto_subseq hmem
  have hf_tend : Tendsto (fun k : ℕ => fseq (φ k)) atTop (𝓝 c) :=
    hfseq.comp hφmono.tendsto_atTop
  have hpair : Tendsto (fun k : ℕ => (fseq (φ k), zseq (φ k))) atTop (𝓝 (c, zlim)) := by
    have := hf_tend.prodMk hφtend
    rwa [← nhds_prod_eq] at this
  -- the Green function of the subsequence is constant
  have hgreen_eq : ∀ n : ℕ, Work.ParamRays.greenFun (fseq n) (zseq n) = Real.log t₀ := by
    intro n
    have hmod := Work.ParamRays.IsCritBottcher_modulus
      (Work.Bottcher.isCritBottcher_varphiCrit (fseq n)) (hzspec n).1
    have hv : ‖Work.Bottcher.varphiCrit (fseq n) (zseq n)‖ = t₀ := by
      rw [(hzspec n).2.1, hwnorm]
    rw [hmod] at hv
    rw [← hv, Real.log_exp]
  have hzlimgreen : Work.ParamRays.greenFun c zlim = Real.log t₀ :=
    tendsto_nhds_unique
      ((Work.NAKANE.continuous_greenFun.tendsto (c, zlim)).comp hpair)
      (tendsto_const_nhds.congr'
        (Filter.Eventually.of_forall fun k => (hgreen_eq (φ k)).symm))
  -- so the limit point is in the critical domain of `c`
  have hzlimcrit : zlim ∈ Work.ParamRays.critDomain c := by
    rw [Work.ParamRays.mem_critDomain]
    have hp : Work.ParamRays.paramPotential c = 0 :=
      (Work.ParamRays.paramPotential_eq_zero_iff c).mpr hc
    rw [hp]
    have := Real.log_pos ht
    linarith
  -- and its Böttcher coordinate is the limit of the constant `w`
  have hzlimφ : Work.Bottcher.varphiCrit c zlim = w := by
    have hjointlim : (c, zlim) ∈ Work.NAKANE.jointDomain := hzlimcrit
    have hmem_joint : ∀ᶠ k : ℕ in atTop,
        (fseq (φ k), zseq (φ k)) ∈ Work.NAKANE.jointDomain :=
      Filter.Eventually.of_forall fun k => (hzspec (φ k)).1
    have hwith : Tendsto (fun k : ℕ => (fseq (φ k), zseq (φ k))) atTop
        (𝓝[Work.NAKANE.jointDomain] (c, zlim)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hpair, hmem_joint⟩
    have hjv : Tendsto (fun k : ℕ => Work.NAKANE.jointVarphi (fseq (φ k), zseq (φ k)))
        atTop (𝓝 (Work.NAKANE.jointVarphi (c, zlim))) :=
      ((Work.NAKANE.continuousOn_jointVarphi (c, zlim) hjointlim).tendsto).comp hwith
    have hconst : Tendsto (fun k : ℕ => Work.NAKANE.jointVarphi (fseq (φ k), zseq (φ k)))
        atTop (𝓝 w) :=
      tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun k => by
        show w = Work.Bottcher.varphiCrit (fseq (φ k)) (zseq (φ k))
        exact ((hzspec (φ k)).2.1).symm)
    have := tendsto_nhds_unique hjv hconst
    simpa [Work.NAKANE.jointVarphi_apply] using this
  -- uniqueness of the level point at `c` forces the limit to be `z₀`
  have hzlimeq : zlim = z₀ := by
    refine hz₀uniq zlim ⟨?_, ?_⟩
    · rw [← Work.ParamRays.mem_escapingSet, ← Work.ParamRays.critDomain_eq_escapingSet hc]
      exact hzlimcrit
    · intro ψ hψ
      rw [← Work.Bottcher.varphiCrit_unique hψ.isCritBottcher hzlimcrit, hzlimφ]
  -- but then the bad points would converge to `z₀`, contradicting `ε < ‖zseq (φ k) - z₀‖`
  have hlim : Tendsto (fun k : ℕ => ‖zseq (φ k) - z₀‖) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => zseq (φ k) - z₀) atTop (𝓝 (zlim - z₀)) :=
      hφtend.sub tendsto_const_nhds
    have h2 : Tendsto (fun k : ℕ => ‖zseq (φ k) - z₀‖) atTop (𝓝 ‖zlim - z₀‖) := h1.norm
    rw [hzlimeq, sub_self, norm_zero] at h2
    exact h2
  exact absurd (ge_of_tendsto' hlim fun k => le_of_lt (hzspec (φ k)).2.2) (not_le.mpr hε)

end Work.LandLeaves
