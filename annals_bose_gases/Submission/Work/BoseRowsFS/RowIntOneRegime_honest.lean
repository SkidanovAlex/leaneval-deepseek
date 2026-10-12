import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Submission.Work.BoseRowsFS.RowIntOne_of_IntKernel
import Submission.Work.BoseRowsFS.honest_IntKernel_uncond
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseRowsFS

open scoped Real BigOperators Topology
open MeasureTheory Metric

set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

theorem RowIntOneRegime_honest {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
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
      Work.BoseB7.FSParamsView (Work.BoseRowsFS.honE v h fc fu HM μ))
    (hvK : ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ ρ : ℝ), 0 < μ →
      μ * _root_.BoseGases.a v ^ 3 ≤ εg → Work.BoseGateFS.AdmRho
        (Work.BoseRowsFS.honE v h fc fu HM μ) ρ →
      Work.BoseB7.FSParamsView (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ))
    (hRKH : ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ), 0 < μ →
      μ * _root_.BoseGases.a v ^ 3 ≤ εg →
      (R / (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ^ 2
        ≤ (Work.BoseRowsFS.honE v h fc fu HM μ).KH⁻¹)
    (h16 : ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ), 0 < μ →
      μ * _root_.BoseGases.a v ^ 3 ≤ εg →
      (Work.BoseRowsFS.honE v h fc fu HM μ).aScat * (Work.BoseRowsFS.honE v h fc fu HM μ).KH
        / ((Work.BoseRowsFS.honE v h fc fu HM μ).s
          * (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ≤ 1 / 16) :
    ∃ ε₀ Kint : ℝ, 0 < ε₀ ∧ ε₀ ≤ εg ∧ 0 ≤ Kint ∧
      Work.BoseRowsFS.RowIntOneRegimeN (h := h) (fc := fc) (fu := fu) Ng R ε₀ Kint := by
  -- We assemble the two ingredients already in the corpus:
  -- * `honest_IntKernel_uncond` — the honest `IntKernel` in the dilute régime, at an
  --   effective threshold `ε₀ ≤ εg` (and, as its proof shows, `≤ (1/2)^323`);
  -- * `Work.BoseB7A.estIntegralOneA_pinned` — FS `lem:EstimateIntegral` from an
  --   `IntKernel` at any threshold `t ≤ (1/2)^323`.
  -- The caller's régime hypotheses are all stated at `εg`; we run them at the smaller
  -- threshold `εg' := min εg (1/2)^323`, so that the witness `ε₀` of
  -- `honest_IntKernel_uncond` is automatically `≤ (1/2)^323` as the pinned estimate requires.
  set εg' : ℝ := min εg ((1 / 2 : ℝ) ^ 323) with hεg'def
  have hεg'pos : 0 < εg' := lt_min hεg (by norm_num)
  have hεg'le : εg' ≤ εg := min_le_left _ _
  have hεg'323 : εg' ≤ (1 / 2 : ℝ) ^ 323 := min_le_right _ _
  obtain ⟨ε₀, K₀, hε₀pos, hε₀le, _hK₀, hIK⟩ :=
    honest_IntKernel_uncond (v := v) (h := h) (fc := fc) (fu := fu)
      R hR hav hv_nonneg hvrad hv_supp Cw hCw hdecayW hdecayg Ng εg' hεg'pos
      (fun μ hμ hdil => hrég μ hμ (le_trans hdil hεg'le))
      (fun μ hμ hdil => hcut μ hμ (le_trans hdil hεg'le))
      (fun HM hN μ hμ hdil => htail HM hN μ hμ (le_trans hdil hεg'le))
      (fun HM μ hμ hdil => hFSP HM μ hμ (le_trans hdil hεg'le))
  refine ⟨ε₀, 2000 * (max K₀ 1) ^ 5 + 2000, hε₀pos, le_trans hε₀le hεg'le,
    by positivity, ?_⟩
  intro HM hN μ hμ hεμ ρ hadm
  have hρ0 : 0 ≤ ρ := hadm.1
  -- the caller's hypotheses, read at `μ a³ ≤ εg`
  have hdilg : μ * _root_.BoseGases.a v ^ 3 ≤ εg := le_trans hεμ (le_trans hε₀le hεg'le)
  have hv : Work.BoseB7.FSParamsView (honE v h fc fu HM μ) := hFSP HM μ hμ hdilg
  have hviewK : Work.BoseB7.FSParamsView
      (Work.BoseFixR.KzEnvAt (honE v h fc fu HM μ) ρ) :=
    hvK HM μ ρ hμ hdilg hadm
  have hℓ : 0 < (honE v h fc fu HM μ).ell := Work.BoseB7.ell_pos (honE v h fc fu HM μ) hv
  have hρeq : (Work.BoseFixR.KzEnvAt (honE v h fc fu HM μ) ρ).rho = ρ := by
    rw [Work.BoseB7.Q3Env.rho, Work.BoseB7.rhoZ]
    show (Real.sqrt (ρ * (honE v h fc fu HM μ).ell ^ 3)) ^ 2
        / (honE v h fc fu HM μ).ell ^ 3 = ρ
    rw [Real.sq_sqrt (by positivity), mul_div_assoc,
      div_self (pow_ne_zero 3 (ne_of_gt hℓ)), mul_one]
  have ht : hviewK.t ≤ (1 / 2 : ℝ) ^ 323 := by
    rw [view_t_eq_mu_a3 hviewK]
    exact le_trans hεμ (le_trans hε₀le hεg'323)
  have hPH : (honF v h fc fu HM μ).PHset (Work.BoseFixR.KzEnvAt (honE v h fc fu HM μ) ρ)
      = (honF v h fc fu HM μ).PHset (honE v h fc fu HM μ) := rfl
  have hmain := Work.BoseB7A.estIntegralOneA_pinned K₀
    (honF v h fc fu HM μ) (Work.BoseFixR.KzEnvAt (honE v h fc fu HM μ) ρ) hviewK R
    (fun k => Work.BoseFixR.chat (Submission.BoseGases.g0 v h)
      ((honF v h fc fu HM μ).kmom k))
    ht (hRKH HM μ hμ hdilg) (hIK HM hN μ ρ hviewK hμ hεμ hρ0 (h16 HM μ hμ hdilg))
  rw [hPH] at hmain
  rw [hρeq] at hmain
  simpa [Work.BoseFixR.KzEnvAt] using hmain

end Work.BoseRowsFS
