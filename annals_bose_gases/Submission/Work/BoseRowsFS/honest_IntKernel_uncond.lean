import ChallengeDeps
import Submission.Work.BoseRowsFS.honest_A_ge_AB_regime
import Submission.Work.BoseRowsFS.honest_IntKernel_view
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsFS.honest_IntKernel_uncond`

**The honest `IntKernel` at the honest model, hypothesis-free.**

The two `P_H` mode rows of FS `lem:EstimateIntegral` (`A_pos`, `AB_kernel`) were
the only rows that `Work.BoseRowsFS.honest_IntKernel` took as *hypotheses*, and
the only ones that depend on the density `ρ` of the datum.  They are proved in
`Work.BoseRowsFS.honest_A_ge_AB` from the view `FSParamsView (KzEnvAt (honE …) ρ)`
of the datum (which bounds `|ρ − μ| ≤ μ/2`), and the version of that theorem with
the régime hypothesis taken pointwise — the form in which it is actually used —
is `Work.BoseRowsFS.honest_A_ge_AB_regime`.

The unconditional statement therefore assembles as

* `Work.BoseRowsFS.honest_IntKernel_view` — the row-collecting half of
  `honest_IntKernel`'s proof, with the two `P_H` rows taken *from the view*
  (so that they are available at the single `ρ` the caller has);
* `Work.BoseRowsFS.honest_A_ge_AB_regime` — the two rows themselves, from the
  view;

at the common threshold `ε₀ = min t₀ εg`, where `t₀` is the diluteness threshold
below which the `P_H` rows hold (so `ε₀` is positive, `≤ εg`, and both the row
hypotheses of the caller and the `P_H` rows may be used).
-/

namespace Work.BoseRowsFS

open scoped Real BigOperators Topology
open MeasureTheory Metric

open Work.BoseB7 Work.BoseB7A
open Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open _root_.BoseGases Submission.BoseGases

noncomputable section

set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

theorem honest_IntKernel_uncond {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (R : ℝ) (hR : 0 < R)
    (hav : 0 < _root_.BoseGases.a v)
    (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hdecayW : ∀ ℓ : ℝ, 1 ≤ ℓ → R ≤ ℓ * Submission.BoseGases.chiR0 →
      ∀ p : EuclideanSpace ℝ (Fin 3),
        |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p| * (1 + ‖p‖) ^ 2
          ≤ Cw * _root_.BoseGases.a v)
    (hdecayg : ∀ ℓ : ℝ, 1 ≤ ℓ → R ≤ ℓ * Submission.BoseGases.chiR0 →
      ∀ p : EuclideanSpace ℝ (Fin 3),
        |Work.BoseFixR.chat (Submission.BoseGases.g0 v h) p| * (1 + ‖p‖) ^ 2
          ≤ Cw * _root_.BoseGases.a v)
    (Ng : ℝ → ℕ) (εg : ℝ) (hεg : 0 < εg)
    (hrég : ∀ μ : ℝ, 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ εg →
      1 ≤ Work.BoseBoxFock.ellH v μ
        ∧ R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0)
    (hcut : ∀ μ : ℝ, 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ εg →
      1 / R ≤ 2 * Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) (Ng μ)
        ∧ Cw ^ 2 * Work.BoseBoxFock.ellH v μ
            ≤ (2 * Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) (Ng μ)) ^ 3)
    (htail : ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ),
      (∀ μ, Ng μ ≤ (HM μ).N) → ∀ μ : ℝ, 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ εg →
        (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ (-(3 : ℝ)) *
            ∑ k ∈ (Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N)).filter
                (fun k => Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N
                  < ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖),
              (Work.BoseFixR.chat (Submission.BoseGases.g0 v h)
                  ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom k) ^ 2
                + Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
                    ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom k) ^ 2)
                / ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ ^ 2
          ≤ Cw ^ 2 * _root_.BoseGases.a v
              * (R / Work.BoseBoxFock.ellH v μ) ^ 4)
    (hFSP : ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ), 0 < μ →
      μ * _root_.BoseGases.a v ^ 3 ≤ εg →
      Work.BoseB7.FSParamsView (Work.BoseRowsFS.honE v h fc fu HM μ)) :
    ∃ ε₀ K₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ εg ∧ 128 * Real.pi ≤ K₀ ∧
      ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ), (∀ μ, Ng μ ≤ (HM μ).N) →
      ∀ (μ ρ : ℝ),
        (hvK : Work.BoseB7.FSParamsView
          (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ)) →
        0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ ε₀ → 0 ≤ ρ →
        (Work.BoseRowsFS.honE v h fc fu HM μ).aScat
            * (Work.BoseRowsFS.honE v h fc fu HM μ).KH
            / ((Work.BoseRowsFS.honE v h fc fu HM μ).s
              * (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ≤ 1 / 16 →
        Work.BoseB7A.IntKernel K₀ R (Work.BoseRowsFS.honF v h fc fu HM μ)
          (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ)
          (fun k => Work.BoseFixR.chat (Submission.BoseGases.g0 v h)
            ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom k)) := by
  -- ## the two `P_H` rows, from the view, with their own diluteness threshold `t₀`
  obtain ⟨t₀, ht₀pos, hAreg⟩ := honest_A_ge_AB_regime (v := v) (h := h) (fc := fc) (fu := fu)
    R hR hav hv_nonneg hvrad hv_supp
  -- ## the common threshold
  set ε₀ : ℝ := min t₀ εg with hε₀def
  have hε₀pos : 0 < ε₀ := lt_min ht₀pos hεg
  have hε₀g : ε₀ ≤ εg := min_le_right _ _
  -- ## the two `P_H` rows at the common threshold
  have hArows : ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ ρ : ℝ)
      (hvK : Work.BoseB7.FSParamsView
        (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ)),
      0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ ε₀ → 0 ≤ ρ →
      (Work.BoseRowsFS.honE v h fc fu HM μ).aScat
          * (Work.BoseRowsFS.honE v h fc fu HM μ).KH
          / ((Work.BoseRowsFS.honE v h fc fu HM μ).s
            * (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ≤ 1 / 16 →
      (∀ k : Work.BoseBoxFock.Lab (HM μ).N,
        (Work.BoseRowsFS.honF v h fc fu HM μ).PH
            (Work.BoseRowsFS.honE v h fc fu HM μ).KH
            (Work.BoseRowsFS.honE v h fc fu HM μ).aScat k →
          0 < (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ).A k)
      ∧ (∀ k : Work.BoseBoxFock.Lab (HM μ).N,
        (Work.BoseRowsFS.honF v h fc fu HM μ).PH
            (Work.BoseRowsFS.honE v h fc fu HM μ).KH
            (Work.BoseRowsFS.honE v h fc fu HM μ).aScat k →
          2 * |(Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ).B k|
            ≤ (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ).A k) := by
    intro HM μ ρ hvK hμ hε₀ hρ hsc
    refine hAreg HM μ ρ hvK hμ ?_ hρ ?_ hsc
    · -- the régime `R ≤ ℓ_H χ_{R₀}` is the caller's `hrég` at this `μ`
      exact (hrég μ hμ (le_trans hε₀ hε₀g)).2
    · -- `hvK.t = μa³ ≤ ε₀ ≤ t₀`
      rw [view_t_eq_mu_a3 hvK]
      exact le_trans hε₀ (min_le_left _ _)
  -- ## the row-collecting half of `honest_IntKernel`, with the `P_H` rows from the view
  obtain ⟨K₀, hK₀, hIK⟩ := honest_IntKernel_view (v := v) (h := h) (fc := fc) (fu := fu)
    R hR hav hv_nonneg hvrad hv_supp
    Cw hCw hdecayW hdecayg Ng εg hεg hrég hcut htail hFSP ε₀ hε₀pos hε₀g hArows
  exact ⟨ε₀, K₀, hε₀pos, hε₀g, hK₀, hIK⟩

end

end Work.BoseRowsFS
