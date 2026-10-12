import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.BoseB1Cube.Winchk
import Submission.Work.BoseFixB1B.cubeWordDefs
import Submission.Work.BoseFixB1B.integrable_qLHSden_regime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.AdmGate` — the parameter gate of the cube-window convergence

The target `Work.BoseB1Cube.tendsto_sbWordCube_cutProd` is gated by
`∃ ε₀ > 0, ∀ μ, Work.BoseBoxFix.Adm v ε₀ μ → …`, and its proof needs, from the diluteness
hypothesis alone, the following *parameter facts* at FS's parameters
`ℓ = sideAt μ (a v)`, `d = (paramsAt μ (a v)).d`, `M = (paramsAt μ (a v)).M`:

* `0 < μ`, `0 < ℓ`, `0 < d` (the box and the sliding parameter are non-degenerate);
* `4 ≤ M` (the regularity budget of the cube window: `chiSmallB M` is `C^{M-1}` and the chain
  needs `C³`);
* `R ≤ ℓ · d / 16` and `R ≤ ℓ · chiR0` — the support-radius conditions of the dilute regime
  (`Work.BoseFixB1.regime_sideAt_ge`), which are what `Work.BoseFixB1B.integrable_qLHSden_regime`
  needs to make the potential density `qLHSden` integrable on the box.

This module packages them; the diluteness threshold is the one of `regime_sideAt_ge` (any smaller
threshold works, and the caller picks the minimum with the other thresholds).
-/

noncomputable section

open MeasureTheory Metric
open scoped Topology Real

namespace Work.BoseB1Cube

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `4 ≤ Work.BoseBox.mValue`. -/
theorem four_le_mValue : 4 ≤ Work.BoseBox.mValue := Work.BoseFixB1B.four_le_mValue

/-- **The parameter gate.**  There is a diluteness threshold `ε₀ > 0` such that
`Work.BoseBoxFix.Adm v ε₀ μ` implies all the parameter facts needed by the cube-window
convergence at FS's parameters. -/
theorem admGate {v : E3 → ℝ} {R : ℝ} (hR : 0 < R) (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      0 < μ ∧ 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ∧
        0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ∧
        4 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M ∧
        R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
              * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d / 16 ∧
        R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0 := by
  obtain ⟨εreg, hεreg, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  refine ⟨εreg, hεreg, ?_⟩
  intro μ hμadm
  have hμ0 : 0 < μ := hμadm.1
  have hdil : μ * _root_.BoseGases.a v ^ 3 ≤ εreg := hμadm.2.1
  obtain ⟨hRd, hRχ⟩ := hreg μ hμ0 hdil
  have hM4 : 4 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
    have h1 : Work.BoseFixB1.bM v μ = Work.BoseBox.mValue := Work.BoseFixB1B.bM_eq_mValue v μ
    have h2 : Work.BoseFixB1.bM v μ = (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := rfl
    rw [h2] at h1
    rw [h1]
    exact Work.BoseFixB1B.four_le_mValue
  exact ⟨hμ0, Work.BoseFixB1.adm_ell_pos hμadm, Work.BoseFixB1.adm_d_pos hμadm, hM4, hRd, hRχ⟩

/-- **The potential integrability at the cube parameters.**  From the parameter gate and the
diluteness of `v`, the diagonal density `qLHSden` of the localised potential word is integrable on
the box. -/
theorem admGate_integrable_qLHSden {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {R ε₀ : ℝ}
    (hR : 0 < R) (hav : 0 < _root_.BoseGases.a v) (hv1 : MeasureTheory.MemLp v 1)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hε₀ : 0 < ε₀)
    {μ : ℝ} (hμ : Work.BoseBoxFix.Adm v ε₀ μ)
    (hRd : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
              * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d / 16)
    (hRχ : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0)
    {k : ℕ} (u : E3) :
    MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X k =>
        Submission.BoseGases.qLHSden k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          μ (Submission.BoseGases.wSmallPair (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u v)
          (Submission.BoseGases.wSmall1Pair h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) x)
      (Submission.BoseGases.abox k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) := by
  have hM1 : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
    have h1 : Work.BoseFixB1.bM v μ = Work.BoseBox.mValue := Work.BoseFixB1B.bM_eq_mValue v μ
    have h2 : Work.BoseFixB1.bM v μ = (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := rfl
    rw [h2] at h1
    rw [h1]
    rw [Work.BoseBox.mValue]; norm_num
  exact Work.BoseFixB1B.integrable_qLHSden_regime (h := h) hM1
    (Work.BoseFixB1.adm_ell_pos hμ) (Work.BoseFixB1.adm_d_pos hμ) hv1 hR hv_supp hRd hRχ u

end Work.BoseB1Cube
