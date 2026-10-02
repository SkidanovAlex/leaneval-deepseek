import Mathlib
import Submission.Work.SeedDyn.Defs
import Submission.Work.Bottcher.CritBottcherExists

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology
open Filter

namespace Work.SeedDyn

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **(D6) The derivative of the canonical critical Böttcher coordinate tends to `1` at
infinity.**

The Böttcher coordinate `φ = varphiCrit c` is tangent to the identity at infinity
(`‖φ w − w‖ ≤ ε' ‖w‖` eventually).  Applying the Cauchy estimate to `φ − id` on the
sphere of radius `‖z‖/4` about `z` (which lies in the escaping set once `‖z‖` is large,
since the escaping set contains the complement of a large disc) gives
`‖φ' z − 1‖ ≤ (ε' · (5‖z‖/4)) / (‖z‖/4) = 5ε'`, whence the claim with `ε' = ε/5`. -/
theorem deriv_varphiCrit_tendsto_one {c : ℂ} (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ →
      ‖deriv (Work.Bottcher.varphiCrit c) z - 1‖ ≤ ε := by
  intro ε hε
  have hε5 : 0 < ε / 5 := by linarith
  -- tangency of `varphiCrit c` to the identity at infinity
  have htang : ∀ᶠ w : ℂ in Filter.cocompact ℂ,
      ‖Work.Bottcher.varphiCrit c w - w‖ ≤ (ε / 5) * ‖w‖ :=
    (Work.Bottcher.isCritBottcher_varphiCrit c).2.2 (ε / 5) hε5
  rw [Filter.hasBasis_cocompact.eventually_iff] at htang
  obtain ⟨K, hKcpt, hK⟩ := htang
  obtain ⟨R₀, hR₀⟩ := hKcpt.isBounded.subset_closedBall (0 : ℂ)
  set M : ℝ := max R₀ (max 2 ‖c‖) with hMdef
  refine ⟨4 * (M + 1), ?_⟩
  intro z hz
  have hMpos : (0 : ℝ) < M := by rw [hMdef]; positivity
  have hRpos : 0 < 4 * (M + 1) := by linarith
  have hznorm : 0 < ‖z‖ := lt_of_lt_of_le hRpos hz
  set r : ℝ := ‖z‖ / 4 with hrdef
  have hr : 0 < r := by rw [hrdef]; linarith
  -- `3 (M+1) ≤ 3‖z‖/4` because `4(M+1) ≤ ‖z‖`
  have h3z : 3 * (M + 1) ≤ 3 * ‖z‖ / 4 := by linarith
  -- every point of the closed ball of radius `r` about `z` is in the escaping set
  have hfar : ∀ w : ℂ, dist w z ≤ r → w ∈ Work.SeedDyn.esc c := by
    intro w hw
    have hwz : ‖w - z‖ ≤ r := by rwa [dist_eq_norm] at hw
    have hwlb : 3 * ‖z‖ / 4 ≤ ‖w‖ := by
      have h := norm_sub_le w (w - z)
      have heq : w - (w - z) = z := by ring
      rw [heq] at h
      linarith [hrdef]
    have hlt : max 2 ‖c‖ < ‖w‖ := by
      have hMle : max 2 ‖c‖ ≤ M := by rw [hMdef]; exact le_max_right R₀ _
      have : 3 * (M + 1) ≤ ‖w‖ := le_trans h3z hwlb
      linarith
    exact Work.SeedDyn.mem_esc.mpr
      ((Work.ParamRays.greenFun_pos_iff_escaping c w).mp
        (Work.ParamRays.greenFun_pos_of_lt c w hlt))
  -- the closed ball is contained in the (open) escaping set, where `varphiCrit c` is analytic
  have hclosure : closure (Metric.ball z r) ⊆ Work.SeedDyn.esc c := by
    intro w hw
    have hsub : closure (Metric.ball z r) ⊆ Metric.closedBall z r :=
      closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall
    exact hfar w (Metric.mem_closedBall.mp (hsub hw))
  have han : AnalyticOnNhd ℂ (Work.Bottcher.varphiCrit c) (closure (Metric.ball z r)) :=
    (Work.SeedDyn.analyticOnNhd_varphiCrit_esc hc).mono hclosure
  have hdiff : DifferentiableOn ℂ (fun w : ℂ => Work.Bottcher.varphiCrit c w - w)
      (closure (Metric.ball z r)) := by
    have h1 : (fun w : ℂ => Work.Bottcher.varphiCrit c w - w)
        = (Work.Bottcher.varphiCrit c - (id : ℂ → ℂ)) := by funext w; simp
    rw [h1]
    exact (han.differentiableOn).sub differentiableOn_id
  have hdc : DiffContOnCl ℂ (fun w : ℂ => Work.Bottcher.varphiCrit c w - w)
      (Metric.ball z r) := hdiff.diffContOnCl
  -- the Cauchy estimate bound on the sphere
  have hbound : ∀ w ∈ Metric.sphere z r,
      ‖Work.Bottcher.varphiCrit c w - w‖ ≤ (ε / 5) * (5 * ‖z‖ / 4) := by
    intro w hw
    have hwz : ‖w - z‖ = r := by
      have h' := Metric.mem_sphere.mp hw
      rwa [dist_eq_norm] at h'
    have hwcheck : R₀ < ‖w‖ := by
      have h := norm_sub_le w (w - z)
      have heq : w - (w - z) = z := by ring
      rw [heq, hwz] at h
      have h3 : 3 * (M + 1) ≤ ‖w‖ := by
        have := h3z
        linarith
      have hR0M : R₀ ≤ M := by rw [hMdef]; exact le_max_left _ _
      linarith
    have hwk : w ∉ K := by
      intro hwK
      have h' := hR₀ hwK
      rw [Metric.mem_closedBall, dist_zero_right] at h'
      linarith
    have hb := hK hwk
    have hwup : ‖w‖ ≤ 5 * ‖z‖ / 4 := by
      have h := norm_add_le z (w - z)
      have heq : z + (w - z) = w := by ring
      rw [heq, hwz] at h
      linarith [hrdef]
    calc ‖Work.Bottcher.varphiCrit c w - w‖ ≤ (ε / 5) * ‖w‖ := hb
      _ ≤ (ε / 5) * (5 * ‖z‖ / 4) :=
          mul_le_mul_of_nonneg_left hwup (by positivity)
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hdc hbound
  have hval : ((ε / 5) * (5 * ‖z‖ / 4)) / r = ε := by
    rw [hrdef]
    field_simp
  have hmain : ‖deriv (fun w : ℂ => Work.Bottcher.varphiCrit c w - w) z‖ ≤ ε :=
    le_trans hcauchy (le_of_eq hval)
  -- translate back to `deriv (varphiCrit c) z`
  have hz_esc : z ∈ Work.SeedDyn.esc c := hfar z (by rw [dist_self]; exact hr.le)
  have hdφ : DifferentiableAt ℂ (Work.Bottcher.varphiCrit c) z :=
    ((Work.SeedDyn.analyticOnNhd_varphiCrit_esc hc).differentiableOn).differentiableAt
      ((Work.SeedDyn.isOpen_esc c).mem_nhds hz_esc)
  have hderiv : deriv (fun w : ℂ => Work.Bottcher.varphiCrit c w - w) z
      = deriv (Work.Bottcher.varphiCrit c) z - 1 := by
    have h1 : (fun w : ℂ => Work.Bottcher.varphiCrit c w - w)
        = (Work.Bottcher.varphiCrit c - (id : ℂ → ℂ)) := by funext w; simp
    rw [h1, deriv_sub hdφ differentiableAt_id, deriv_id]
  rw [hderiv] at hmain
  exact hmain

end Work.SeedDyn
