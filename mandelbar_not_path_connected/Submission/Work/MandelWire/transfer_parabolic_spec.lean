/-
# `Work.MandelWire.transfer_parabolic_spec`

The wiring lemma of `Work.FQC.transfer_parabolic`, strengthened from `Nonempty (RootParabolic c₂)`
to the *pinned* form `∃ d₂ : RootParabolic c₂, d₂.z₁ = θ d.z₁`: the transported root-parabolic
parameter bundle is the one whose parabolic point is the image `θ d.z₁` of the parabolic point of
`d` under the conjugating homeomorphism `θ`.

The transport of each field of `RootParabolic` is proved in
`Submission.Work.FQC.transfer_parabolic_aux`; this file replays that assembly with the extra
observation that the `z₁` field of the constructed bundle is definitionally `θ d.z₁`.
-/
import Mathlib
import Submission.Work.FQC.transfer_parabolic_aux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology ComplexConjugate
open Filter Set Function
open Classical

set_option linter.unusedVariables false

noncomputable section

namespace Work.MandelWire

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

theorem transfer_parabolic_spec {c : ℂ} (d : Work.EL.RootParabolic c) {c₂ : ℂ} (θ : ℂ ≃ₜ ℂ)
    (hconj : ∀ z : ℂ, θ (LeanEval.ComplexAnalysis.Tantibar c z) = LeanEval.ComplexAnalysis.Tantibar c₂ (θ z))
    (hdecay : ∃ C R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖θ z - z‖ ≤ C / ‖z‖)
    (h0 : θ 0 = 0)
    (hsimple : iteratedDeriv 2 (Work.EL.F c₂) (θ d.z₁) ≠ 0) :
    ∃ d₂ : Work.EL.RootParabolic c₂, d₂.z₁ = θ d.z₁ := by
  have hFc : ∀ z : ℂ, θ (Work.EL.F c z) = Work.EL.F c₂ (θ z) :=
    Work.FQC.conj_F θ hconj
  have hper : (Tantibar c₂)^[5] (θ d.z₁) = θ d.z₁ := by
    rw [← Work.FQC.theta_iterate θ hconj 5 d.z₁, d.per_half]
  have hne_per : ∀ j ∈ Finset.Ioo 0 5, (Tantibar c₂)^[j] (θ d.z₁) ≠ θ d.z₁ := by
    intro j hj h
    refine d.ne_per j hj (θ.injective ?_)
    rw [Work.FQC.theta_iterate θ hconj j d.z₁]
    exact h
  have hc₂ : c₂ = θ c := by
    have h1 : Tantibar c₂ 0 = c₂ := by simp [Tantibar]
    have h2 : Tantibar c 0 = c := by simp [Tantibar]
    rw [← h1, ← h0, ← hconj, h2]
  have hiter : ∀ n : ℕ, (Work.EL.F (θ c))^[n] (θ c) = θ ((Work.EL.F c)^[n] c) := by
    intro n
    have h := (Work.FQC.theta_iterate_F θ hFc n c).symm
    rw [hc₂] at h
    exact h
  have hcrit : Tendsto (fun n : ℕ => (Work.EL.F c₂)^[n] c₂) atTop (nhds (θ d.z₁)) ∧
      ∀ n : ℕ, (Work.EL.F c₂)^[n] c₂ ≠ θ d.z₁ := by
    have hrew : ∀ n : ℕ, (Work.EL.F c₂)^[n] c₂ = (Work.EL.F (θ c))^[n] (θ c) := by
      intro n
      rw [hc₂]
    have hconv : Tendsto (fun n : ℕ => (Work.EL.F (θ c))^[n] (θ c)) atTop (nhds (θ d.z₁)) := by
      have h3 := (θ.continuous.tendsto d.z₁).comp d.crit.1
      rw [show (fun n : ℕ => (Work.EL.F (θ c))^[n] (θ c)) = fun n => θ ((Work.EL.F c)^[n] c) from
        funext hiter]
      exact h3
    have hne' : ∀ n : ℕ, (Work.EL.F (θ c))^[n] (θ c) ≠ θ d.z₁ := by
      intro n hn
      exact d.crit.2 n (θ.injective (by rw [← hiter n]; exact hn))
    refine ⟨?_, ?_⟩
    · rw [show (fun n : ℕ => (Work.EL.F c₂)^[n] c₂) = fun n => (Work.EL.F (θ c))^[n] (θ c) from
        funext hrew]
      exact hconv
    · intro n
      rw [hrew n]
      exact hne' n
  have hN₂ : Work.EL.DynB c₂ (d.φ ∘ (θ.symm : ℂ → ℂ)) :=
    Work.FQC.nakane_transfer d.hN hconj hdecay
  have hrays : Work.Landing.landsAt c₂ Work.EL.alpha1 (θ d.z₁) ∧
      Work.Landing.landsAt c₂ Work.EL.alpha2 (θ d.z₁) :=
    ⟨(Work.FQC.landsAt_transfer θ hconj hdecay d.bottcher Work.EL.alpha1 d.z₁).mp d.rays.1,
     (Work.FQC.landsAt_transfer θ hconj hdecay d.bottcher Work.EL.alpha2 d.z₁).mp d.rays.2⟩
  have hwake : ∀ k : ℕ, 1 ≤ k →
      (Tantibar c₂)^[k] 0 ∈ Work.EL.wakeSide hN₂ (θ d.z₁) ((k - 1) % 5) := by
    intro k hk
    have h := d.wake k hk
    have hmem : θ ((Tantibar c)^[k] 0) ∈ θ '' Work.EL.wakeSide d.hN d.z₁ ((k - 1) % 5) :=
      ⟨_, h, rfl⟩
    have h2 := Work.FQC.wakeSide_transfer (hN := d.hN) (hN₂ := hN₂) hconj d.z₁ ((k - 1) % 5)
    rw [← h2] at hmem
    rwa [Work.FQC.theta_iterate θ hconj k 0, h0] at hmem
  exact ⟨⟨d.φ ∘ (θ.symm : ℂ → ℂ), Work.FQC.isDynBottcher_transfer d.bottcher hconj hdecay,
    hN₂, θ d.z₁, hper, hne_per, Work.FQC.multiplier_transfer d θ hconj hdecay, hsimple,
    hrays, hcrit, hwake⟩, rfl⟩

end Work.MandelWire
