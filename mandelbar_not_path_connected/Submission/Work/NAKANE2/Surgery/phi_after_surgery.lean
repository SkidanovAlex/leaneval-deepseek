import Mathlib
import Submission.Work.NAKANE2.Defs
import Submission.Work.NAKANE2.IFT.Basic
import Submission.Work.NAKANE2.Surgery.W_basic
import Submission.Work.NAKANE2.Surgery.V_basic
import Submission.Work.NAKANE2.Surgery.gv_basic
import Submission.Work.NAKANE2.Surgery.gv_V_to_W
import Submission.Work.NAKANE2.Surgery.gv_ratio
import Submission.Work.NAKANE2.Surgery.gv_W_hits
import Submission.Work.NAKANE2.Surgery.glueMuW_eq_zero_of_mem
import Submission.Work.NAKANE2.Surgery.admissible_glueMuW
import Submission.Work.NAKANE2.Surgery.principal_zero_eq_zero
import Submission.Work.NAKANE2.Surgery.eqOn_of_isCritBottcher_sub
import Submission.Work.NAKANE2.Surgery.straighten
import Submission.Work.NAKANE2.Surgery.greenFun_transfer

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.NAKANE2.Surgery

open Filter Set Function
open scoped Topology ComplexConjugate

open LeanEval.ComplexAnalysis (Tantibar)

/-- If `P` holds for all `z` with `R ≤ ‖z‖` then `P` holds eventually in the cocompact
filter. -/
private lemma eventually_cocompact_of_norm_ge {P : ℂ → Prop} (R : ℝ)
    (h : ∀ z, R ≤ ‖z‖ → P z) : ∀ᶠ z in cocompact ℂ, P z := by
  change {z : ℂ | P z} ∈ cocompact ℂ
  rw [Filter.mem_cocompact]
  refine ⟨Metric.closedBall 0 R, isCompact_closedBall 0 R, ?_⟩
  intro z hz
  simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hz
  exact h z (le_of_lt hz)

/-- Admissibility of the invariant Beltrami coefficient of the surgery. -/
private lemma admissible_glueMuW_gv {c₀ : ℂ} (D : Work.NAKANE2.SurgeryData c₀) {v : ℂ}
    (hv : ‖v‖ < Work.NAKANE2.rConst D) :
    Work.MRMT.Found.Admissible
      (Work.NAKANE2.glueMuW (Work.NAKANE2.gv c₀ D.χ v) (Work.NAKANE2.W c₀)) := by
  refine admissible_glueMuW (κ := 2 * D.Λ * ‖v‖) (R := D.R₀) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · nlinarith [D.hΛ1, norm_nonneg v]
  · have h := Work.NAKANE2.norm_mul_Λ_le D hv
    nlinarith [h]
  · exact ((Work.NAKANE2.Surgery.gv_basic D v).1.continuous).measurable
  · exact (Work.NAKANE2.Surgery.W_basic D).1.measurableSet
  · exact (Work.NAKANE2.Surgery.gv_ratio D hv).1
  · exact (Work.NAKANE2.Surgery.gv_W_hits D hv).2
  · intro z hz
    exact Work.NAKANE2.Surgery.glueMuW_eq_zero_of_mem hz
  · exact D.hWc

/-- Route: with `θ = principal (glueMuW (gv c₀ D.χ v) (W c₀))` and `c'` from `straighten`,
`principal_zero_eq_zero` gives `θ 0 = 0`, `gv_basic` gives `gv c₀ D.χ v 0 = c₀ + v`, so
`c' = T_{c'} 0 = θ (c₀ + v)`.
`U := θ '' W c₀` and `ψ := Work.Bottcher.varphiCrit c₀ ∘ θ.symm` satisfy the hypotheses of
`eqOn_of_isCritBottcher_sub` with `φ := Work.Bottcher.varphiCrit c'` and
`Work.Bottcher.isCritBottcher_varphiCrit`:
`U` is preconnected (`W_basic`, `θ` is a homeomorphism), `T_{c'} U ⊆ U` (`hconj`), the Böttcher
equation for `ψ` follows from the equation for `varphiCrit c₀` and `θ ∘ gv = T_{c'} ∘ θ`,
`ψ` is continuous (`Work.Bottcher.varphiCrit_continuousOn`), nonvanishing
(`Work.Bottcher.varphiCrit_ne_zero`), and asymptotic to the identity (`hdecay`).
`U ⊆ critDomain c'`: `greenFun_transfer` at the point `c₀ + v ∈ W c₀` (from `D.hband`, since
`‖v‖ < rConst D ≤ D.ρ/2`) gives `greenFun c' c' = greenFun c₀ (c₀ + v)`, while for `θ z ∈ U` it
gives `greenFun c' (θ z) = greenFun c₀ z > 3/4 * Gcrit c₀ > greenFun c₀ (c₀+v)/2 = paramPotential c'`.
Finally `c' = θ (c₀+v) ∈ U`, so `Φ c' = varphiCrit c' c' = ψ c' = varphiCrit c₀ (c₀ + v)`, and
`paramPotential c' < greenFun c' c' = 2 * paramPotential c'` gives `c' ∉ Mb`. -/
theorem phi_after_surgery {c₀ : ℂ} (D : Work.NAKANE2.SurgeryData c₀) {v : ℂ}
    (hv : ‖v‖ < Work.NAKANE2.rConst D) :
    ∃ c' : ℂ, c' ∉ Work.NAKANE2.Mb ∧
      Work.NAKANE2.Phi c' = Work.Bottcher.varphiCrit c₀ (c₀ + v) ∧
      ‖c' - c₀‖ ≤ Work.NAKANE2.Kconst D * ‖v‖ := by
  have hμadm : Work.MRMT.Found.Admissible
      (Work.NAKANE2.glueMuW (Work.NAKANE2.gv c₀ D.χ v) (Work.NAKANE2.W c₀)) :=
    admissible_glueMuW_gv D hv
  set μ : ℂ → ℂ := Work.NAKANE2.glueMuW (Work.NAKANE2.gv c₀ D.χ v) (Work.NAKANE2.W c₀)
    with hμ
  set θ : ℂ ≃ₜ ℂ := Work.MRMT.Found.principal μ with hθ
  -- ## Straightening: the conjugacy and the Lipschitz bound (from `straighten`)
  obtain ⟨c', hconj₀, hnorm⟩ := straighten D hv
  have hconj : ∀ z : ℂ, θ (Work.NAKANE2.gv c₀ D.χ v z) = Tantibar c' (θ z) := by
    intro z
    simpa only [hθ, hμ] using hconj₀ z
  -- ## Elementary facts about `W`, `V` and `gv`
  have hWpre : IsPreconnected (Work.NAKANE2.W c₀) := (Work.NAKANE2.Surgery.W_basic D).2.1
  have hWTself : ∀ z ∈ Work.NAKANE2.W c₀, Tantibar c₀ z ∈ Work.NAKANE2.W c₀ :=
    (Work.NAKANE2.Surgery.W_basic D).2.2
  have hdisj : Disjoint (Work.NAKANE2.W c₀) (Work.NAKANE2.V c₀ D.ρ) :=
    (Work.NAKANE2.Surgery.V_basic D).2.2.1
  have hgvWT : ∀ z ∈ Work.NAKANE2.W c₀,
      Work.NAKANE2.gv c₀ D.χ v z = Tantibar c₀ z := by
    intro z hz
    exact (Work.NAKANE2.Surgery.gv_basic D v).2.2.2 z
      (fun hzV => (Set.disjoint_left.mp hdisj hz) hzV)
  have hgvWg : ∀ z ∈ Work.NAKANE2.W c₀, Work.NAKANE2.gv c₀ D.χ v z ∈ Work.NAKANE2.W c₀ := by
    intro z hz
    rw [hgvWT z hz]
    exact hWTself z hz
  -- ## The decay of the principal solution
  have hdecayθ : ∃ C R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖(θ : ℂ → ℂ) z - z‖ ≤ C / ‖z‖ := by
    have h := Work.MRMT.Found.principal_decay hμadm
    simpa only [hθ, hμ] using h
  -- ## The Green function transfers from `c₀` to `c'` on `W c₀`
  have htransfer : ∀ z ∈ Work.NAKANE2.W c₀,
      Work.ParamRays.greenFun c' (θ z) = Work.ParamRays.greenFun c₀ z :=
    greenFun_transfer (c₀ := c₀) (c' := c') (g := Work.NAKANE2.gv c₀ D.χ v)
      (θ := θ) hconj hdecayθ hgvWT hgvWg
  -- ## `c₀ + v` lies in `W c₀`
  have hcv_band : c₀ + v ∈ Metric.closedBall c₀ (3 * D.ρ) := by
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    have h1 : ‖v‖ < D.ρ := lt_trans hv (Work.NAKANE2.rConst_lt_ρ D)
    linarith [D.hρ]
  have hcvW : c₀ + v ∈ Work.NAKANE2.W c₀ := by
    rw [Work.NAKANE2.mem_W]
    have hband := (D.hband hcv_band).1
    have hp := D.Gcrit_pos
    linarith
  -- ## The principal solution fixes the origin, hence `c' = θ (c₀ + v)`
  have hθ0 : θ 0 = 0 :=
    principal_zero_eq_zero hconj (Work.NAKANE2.Surgery.gv_basic D v).2.2.1
  have hc'eq : c' = θ (c₀ + v) := by
    have h := hconj 0
    rw [(Work.NAKANE2.Surgery.gv_basic D v).2.1, hθ0, Work.Bottcher.Tantibar_zero] at h
    exact h.symm
  -- ## `paramPotential c' = G c₀ (c₀ + v) / 2`
  have hparam : Work.ParamRays.paramPotential c' = Work.NAKANE2.G c₀ (c₀ + v) / 2 := by
    have h1 : Work.ParamRays.greenFun c' c' = Work.ParamRays.greenFun c₀ (c₀ + v) := by
      have h := htransfer (c₀ + v) hcvW
      rwa [← hc'eq] at h
    have h2 := Work.NAKANE2.Gcrit_eq_two_paramPotential c'
    simp only [Work.NAKANE2.Gcrit] at h2
    simp only [Work.NAKANE2.G]
    linarith
  -- ## `W c₀ ⊆ critDomain c₀`
  have hWcrit : Work.NAKANE2.W c₀ ⊆ Work.ParamRays.critDomain c₀ := by
    intro z hz
    rw [Work.ParamRays.mem_critDomain]
    have hz' : 3 / 4 * Work.NAKANE2.Gcrit c₀ < Work.NAKANE2.G c₀ z := hz
    have hp := D.Gcrit_pos
    have h2 := Work.NAKANE2.Gcrit_eq_two_paramPotential c₀
    simp only [Work.NAKANE2.Gcrit, Work.NAKANE2.G] at hz' h2 hp ⊢
    linarith
  -- ## The pieces of the uniqueness theorem
  set ψ : ℂ → ℂ := fun z => Work.Bottcher.varphiCrit c₀ (θ.symm z) with hψ
  set U : Set ℂ := θ '' Work.NAKANE2.W c₀ with hU
  have hUpre : IsPreconnected U := by
    rw [hU]
    exact hWpre.image _ (θ.continuous.continuousOn (s := Work.NAKANE2.W c₀))
  have hUcrit : U ⊆ Work.ParamRays.critDomain c' := by
    intro w hw
    obtain ⟨z, hzW, rfl⟩ := hw
    rw [Work.ParamRays.mem_critDomain, hparam, htransfer z hzW]
    have hz' : 3 / 4 * Work.NAKANE2.Gcrit c₀ < Work.NAKANE2.G c₀ z := hzW
    have hband := (D.hband hcv_band).2
    have hp := D.Gcrit_pos
    simp only [Work.NAKANE2.Gcrit, Work.NAKANE2.G] at hz' hband hp ⊢
    linarith
  have hTU : ∀ z ∈ U, Tantibar c' z ∈ U := by
    intro z hz
    obtain ⟨w, hwW, rfl⟩ := hz
    rw [hU]
    exact ⟨Work.NAKANE2.gv c₀ D.χ v w, hgvWg w hwW, hconj w⟩
  have hψc : ContinuousOn ψ U := by
    rw [hψ, hU]
    have hcomp : ContinuousOn (fun z => Work.Bottcher.varphiCrit c₀ (θ.symm z))
        (θ '' Work.NAKANE2.W c₀) :=
      ContinuousOn.comp (g := Work.Bottcher.varphiCrit c₀) (f := ⇑(θ.symm))
        (s := θ '' Work.NAKANE2.W c₀) (t := Work.ParamRays.critDomain c₀)
        (Work.Bottcher.varphiCrit_continuousOn c₀)
        ((θ.symm.continuous).continuousOn (s := θ '' Work.NAKANE2.W c₀))
        (fun z hz => by
          obtain ⟨w, hwW, rfl⟩ := hz
          simpa only [Homeomorph.symm_apply_apply] using hWcrit hwW)
    simpa only [Function.comp_apply] using hcomp
  have hψ0 : ∀ z ∈ U, ψ z ≠ 0 := by
    intro z hz
    obtain ⟨w, hwW, rfl⟩ := hz
    rw [hψ]
    simpa only [Function.comp_apply, Homeomorph.symm_apply_apply] using
      Work.Bottcher.varphiCrit_ne_zero (hWcrit hwW)
  have hψeq : ∀ z ∈ U, ψ (Tantibar c' z) = star (ψ z) ^ 2 := by
    intro z hz
    obtain ⟨w, hwW, rfl⟩ := hz
    have hTw : Tantibar c' (θ w) = θ (Work.NAKANE2.gv c₀ D.χ v w) := (hconj w).symm
    rw [hTw, hψ]
    change Work.Bottcher.varphiCrit c₀ (θ.symm (θ (Work.NAKANE2.gv c₀ D.χ v w)))
      = star (Work.Bottcher.varphiCrit c₀ (θ.symm (θ w))) ^ 2
    rw [Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply, hgvWT w hwW]
    exact Work.Bottcher.varphiCrit_comm_Tantibar (hWcrit hwW)
  -- ## Asymptotics of `ψ`
  have hθdiv : Tendsto (fun w : ℂ => (θ : ℂ → ℂ) w / w) (cocompact ℂ) (nhds 1) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨C, R, hC⟩ := hdecayθ
    have hCnn : (0 : ℝ) ≤ max C 0 := le_max_right C 0
    have hClim : ∀ w : ℂ, max R 1 ≤ ‖w‖ → ‖(θ : ℂ → ℂ) w - w‖ ≤ (max C 0) / ‖w‖ := by
      intro w hw
      have hRw : R ≤ ‖w‖ := le_trans (le_max_left R 1) hw
      have hw1 : 1 ≤ ‖w‖ := le_trans (le_max_right R 1) hw
      have hwpos : 0 < ‖w‖ := lt_of_lt_of_le zero_lt_one hw1
      have h0 := hC w hRw
      have hdiv : C / ‖w‖ ≤ (max C 0) / ‖w‖ :=
        div_le_div_of_nonneg_right (le_max_left C 0) (le_of_lt hwpos)
      linarith
    refine eventually_cocompact_of_norm_ge
      (max (max R 1) (Real.sqrt ((max C 0) / ε) + 1)) ?_
    intro w hw
    have hwR : max R 1 ≤ ‖w‖ := le_trans (le_max_left _ _) hw
    have hw1 : 1 ≤ ‖w‖ := le_trans (le_max_right R 1) hwR
    have hw0 : w ≠ 0 := by
      intro h; rw [h, norm_zero] at hw1; linarith
    have hwpos : 0 < ‖w‖ := lt_of_lt_of_le zero_lt_one hw1
    have hslt : Real.sqrt ((max C 0) / ε) < ‖w‖ :=
      lt_of_lt_of_le (lt_add_one _) (le_trans (le_max_right (max R 1) _) hw)
    have hsqlt : (max C 0) / ε < ‖w‖ ^ 2 := by
      have h2 : Real.sqrt ((max C 0) / ε) ^ 2 < ‖w‖ ^ 2 :=
        pow_lt_pow_left₀ hslt (Real.sqrt_nonneg _) (by norm_num)
      rwa [Real.sq_sqrt (div_nonneg hCnn (le_of_lt hε))] at h2
    have hle : (max C 0) / ‖w‖ ^ 2 < ε := by
      rw [div_lt_iff₀ (pow_pos hwpos 2)]
      have hmul : ε * ((max C 0) / ε) = max C 0 := by field_simp
      have h2 := mul_lt_mul_of_pos_left hsqlt hε
      rwa [hmul] at h2
    rw [dist_eq_norm]
    have hsplit : (θ : ℂ → ℂ) w / w - 1 = ((θ : ℂ → ℂ) w - w) / w := by
      field_simp [hw0]
    rw [hsplit, norm_div]
    calc ‖(θ : ℂ → ℂ) w - w‖ / ‖w‖
        ≤ ((max C 0) / ‖w‖) / ‖w‖ :=
          div_le_div_of_nonneg_right (hClim w hwR) (le_of_lt hwpos)
      _ = (max C 0) / ‖w‖ ^ 2 := by rw [div_div, pow_two]
      _ < ε := hle
  have hs_proper : Tendsto (fun z : ℂ => (θ.symm : ℂ → ℂ) z) (cocompact ℂ) (cocompact ℂ) := by
    apply tendsto_cocompact_of_tendsto_dist_comp_atTop (0 : ℂ)
    rw [tendsto_atTop]
    intro B
    have hbdd : ∃ M : ℝ, ∀ u : ℂ, ‖u‖ ≤ max B 1 → ‖(θ : ℂ → ℂ) u‖ ≤ M := by
      obtain ⟨M, hM⟩ :=
        ((isCompact_closedBall (0 : ℂ) (max B 1)).image θ.continuous).isBounded.exists_norm_le
      exact ⟨M, fun u hu => hM (θ u) ⟨u, by rwa [Metric.mem_closedBall, dist_zero_right], rfl⟩⟩
    obtain ⟨M, hM⟩ := hbdd
    refine eventually_cocompact_of_norm_ge (max M 0 + 1) ?_
    intro z hz
    rw [dist_zero_right]
    by_contra hcon
    rw [not_le] at hcon
    have h1 : ‖(θ.symm : ℂ → ℂ) z‖ ≤ max B 1 :=
      le_of_lt (lt_of_lt_of_le hcon (le_max_left B 1))
    have h2 : ‖(θ : ℂ → ℂ) ((θ.symm : ℂ → ℂ) z)‖ ≤ M := hM _ h1
    rw [Homeomorph.apply_symm_apply] at h2
    have h3 : ‖z‖ ≤ max M 0 := le_trans h2 (le_max_left M 0)
    linarith
  have hψdiv : Tendsto (fun z : ℂ => ψ z / z) (cocompact ℂ) (nhds 1) := by
    have hg : Tendsto (fun w : ℂ => w / (θ : ℂ → ℂ) w) (cocompact ℂ) (nhds 1) := by
      have h := hθdiv.inv₀ (by norm_num : (1 : ℂ) ≠ 0)
      simpa only [inv_one, inv_div] using h
    have hratiow : Tendsto
        (fun w : ℂ => Work.Bottcher.varphiCrit c₀ w / (θ : ℂ → ℂ) w)
        (cocompact ℂ) (nhds 1) := by
      have h := (Work.Bottcher.varphiCrit_div_tendsto_one c₀).mul hg
      rw [one_mul] at h
      refine h.congr' ?_
      filter_upwards [eventually_cocompact_of_norm_ge 1 (fun z hz => hz)] with w hw
      have hw0 : w ≠ 0 := by
        intro hh; rw [hh, norm_zero] at hw; linarith
      rw [div_mul_div_comm, mul_comm w, mul_div_mul_right _ _ hw0]
    have h2 := hratiow.comp hs_proper
    refine h2.congr' ?_
    filter_upwards with z
    simp only [hψ, Function.comp_apply]
    rw [show (θ : ℂ → ℂ) ((θ.symm : ℂ → ℂ) z) = z from Homeomorph.apply_symm_apply θ z]
  have hψas : ∀ ε > 0, ∀ᶠ z : ℂ in cocompact ℂ, ‖ψ z - z‖ ≤ ε * ‖z‖ := by
    intro ε hε
    have h1 : ∀ᶠ z : ℂ in cocompact ℂ, dist (ψ z / z) 1 < ε := by
      have h := hψdiv
      rw [Metric.tendsto_nhds] at h
      exact h ε hε
    filter_upwards [h1, eventually_cocompact_of_norm_ge 1 (fun z hz => hz)] with z hz1 hz2
    rw [dist_eq_norm] at hz1
    have hz0 : z ≠ 0 := by
      intro h; rw [h, norm_zero] at hz2; linarith
    calc ‖ψ z - z‖ = ‖z * (ψ z / z - 1)‖ := by
          congr 1
          rw [mul_sub, mul_one, ← mul_div_assoc, mul_div_cancel_left₀ (ψ z) hz0]
      _ = ‖z‖ * ‖ψ z / z - 1‖ := norm_mul _ _
      _ ≤ ‖z‖ * ε := mul_le_mul_of_nonneg_left (le_of_lt hz1) (norm_nonneg z)
      _ = ε * ‖z‖ := by ring
  -- ## Finishing
  have hc'U : c' ∈ U := by
    rw [hU]
    exact ⟨c₀ + v, hcvW, hc'eq.symm⟩
  have hc'nMb : c' ∉ Work.NAKANE2.Mb := by
    intro hmem
    have hzero : Work.ParamRays.paramPotential c' = 0 :=
      (Work.ParamRays.paramPotential_eq_zero_iff c').mpr hmem
    have hpos : 0 < Work.ParamRays.paramPotential c' := by
      rw [hparam]
      have hb := (D.hband hcv_band).1
      have hp := D.Gcrit_pos
      simp only [Work.NAKANE2.G, Work.NAKANE2.Gcrit] at hb hp ⊢
      linarith
    linarith
  have hval : Work.Bottcher.varphiCrit c' c' = Work.Bottcher.varphiCrit c₀ (c₀ + v) := by
    have heq := Work.NAKANE2.Surgery.eqOn_of_isCritBottcher_sub
      (φ := Work.Bottcher.varphiCrit c') (ψ := ψ) (U := U)
      (Work.Bottcher.isCritBottcher_varphiCrit c') hUpre hUcrit hTU hψc hψ0 hψeq hψas
      c' hc'U
    rw [heq]
    simp only [hψ]
    rw [show (θ.symm : ℂ → ℂ) c' = c₀ + v from by
      rw [hc'eq, Homeomorph.symm_apply_apply]]
  exact ⟨c', hc'nMb, by rw [Work.NAKANE2.Phi_eq_varphiCrit hc'nMb]; exact hval, hnorm⟩

end Work.NAKANE2.Surgery
