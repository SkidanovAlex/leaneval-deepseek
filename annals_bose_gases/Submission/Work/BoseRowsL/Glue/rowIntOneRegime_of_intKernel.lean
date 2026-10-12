import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Submission.Work.BoseRowsFS.RowIntOneRegime_honest
import Submission.Work.BoseRowsL.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsL.Glue.rowIntOneRegime_of_intKernel`

The assembly step of `Work.BoseRowsL.Glue.rowIntOneRegime_of_interfaceL`: **from an honest
`IntKernel`** (FS `lem:EstimateIntegral`'s hypothesis, at the honest data and some effective
diluteness threshold `ε₁ ≤ hthr.εg`) **to FS §11's integral row** `RowIntOneRegimeN`
(`eq:CompIntegrals-Final`) at a possibly smaller threshold `≤ (1/2)³²³`.

The proof is the body of `Work.BoseRowsFS.RowIntOne_of_IntKernel` — which is *not* directly
applicable, because that theorem asks for the `IntKernel` at **every** mode family, while the
interface supplies it only for cube sizes `N ≥ H.Ng' μ` (and `RowIntOneRegimeN` is the row with
exactly that restriction).  The only inputs used are

* `H.fsp`, `H.fspKz` (the honest parameter view of the datum and of `KzEnvAt` at density `ρ`),
* `H.rkh` (`(R/ℓ)² ≤ K_H⁻¹`),
* `H.a16` (`a K_H/(sℓ) ≤ 1/16`, the extra hypothesis of the honest `IntKernel`),
* and `Work.BoseB7A.estIntegralOneA_pinned`, FS `lem:EstimateIntegral` in the threshold-pinned
  form (`t ≤ (1/2)³²³`), with the constant `2000(max K₀ 1)⁵ + 2000`.

Separating this step out keeps the module free of the (large) analytic bundle that produces the
`IntKernel`; the wrapper `rowIntOneRegime_of_interfaceL` instantiates `hIK` from the interface.

No `sorry`, no `axiom`.
-/

namespace Work.BoseRowsL.Glue

open scoped Real BigOperators Topology
open MeasureTheory Metric

open Work.BoseB7 Work.BoseB7A
open Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open _root_.BoseGases Submission.BoseGases

noncomputable section

set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

theorem rowIntOneRegime_of_intKernel {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {R : ℝ}
    {hthr : Work.BoseGateFS.GateThresholds v h fc fu R}
    (H : Work.BoseRowsL.HonestInterfaceL R hthr)
    (ε₁ K₀ : ℝ) (hε₁pos : 0 < ε₁) (hε₁le : ε₁ ≤ hthr.εg)
    (hIK : ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ), (∀ μ, H.Ng' μ ≤ (HM μ).N) →
      ∀ (μ ρ : ℝ),
        (hvK : Work.BoseB7.FSParamsView
          (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ)) →
        0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ ε₁ → 0 ≤ ρ →
        (Work.BoseRowsFS.honE v h fc fu HM μ).aScat
            * (Work.BoseRowsFS.honE v h fc fu HM μ).KH
            / ((Work.BoseRowsFS.honE v h fc fu HM μ).s
              * (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ≤ 1 / 16 →
        Work.BoseB7A.IntKernel K₀ R (Work.BoseRowsFS.honF v h fc fu HM μ)
          (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ)
          (fun k => Work.BoseFixR.chat (Submission.BoseGases.g0 v h)
            ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom k))) :
    ∃ ε₀ Kint : ℝ, 0 < ε₀ ∧ ε₀ ≤ hthr.εg ∧ 0 ≤ Kint ∧
      Work.BoseRowsFS.RowIntOneRegimeN (h := h) (fc := fc) (fu := fu) H.Ng' R ε₀ Kint := by
  -- ## the pinned threshold `(1/2)^323` of `estIntegralOneA_pinned`
  set ε₀ : ℝ := min ε₁ ((1 / 2 : ℝ) ^ (323 : ℕ)) with hε₀def
  have hε₀pos : 0 < ε₀ := lt_min hε₁pos (by norm_num)
  have hε₀le₁ : ε₀ ≤ ε₁ := min_le_left _ _
  have hε₀323 : ε₀ ≤ (1 / 2 : ℝ) ^ (323 : ℕ) := min_le_right _ _
  have hε₀leg : ε₀ ≤ hthr.εg := le_trans hε₀le₁ hε₁le
  refine ⟨ε₀, 2000 * (max K₀ 1) ^ 5 + 2000, hε₀pos, hε₀leg, by positivity, ?_⟩
  intro HM hN μ hμ hdil ρ hadm
  have hρ0 : 0 ≤ ρ := hadm.1
  have hdilg : μ * _root_.BoseGases.a v ^ 3 ≤ hthr.εg := le_trans hdil hε₀leg
  have hdil₁ : μ * _root_.BoseGases.a v ^ 3 ≤ ε₁ := le_trans hdil hε₀le₁
  -- ## the interface rows at the datum
  have hvE : Work.BoseB7.FSParamsView (Work.BoseRowsFS.honE v h fc fu HM μ) :=
    H.fsp HM μ hμ hdilg
  have hvK : Work.BoseB7.FSParamsView
      (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ) :=
    H.fspKz HM μ ρ hμ hdilg hadm
  have hℓ : 0 < (Work.BoseRowsFS.honE v h fc fu HM μ).ell := Work.BoseB7.ell_pos _ hvE
  have hρeq : (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ).rho = ρ := by
    rw [Work.BoseB7.Q3Env.rho, Work.BoseB7.rhoZ]
    show (Real.sqrt (ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ 3)) ^ 2
        / (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ 3 = ρ
    rw [Real.sq_sqrt (by positivity), mul_div_assoc,
      div_self (pow_ne_zero 3 (ne_of_gt hℓ)), mul_one]
  -- ## diluteness of the datum in the pinned normalisation
  have ht : hvK.t ≤ (1 / 2 : ℝ) ^ (323 : ℕ) := by
    rw [Work.BoseRowsFS.view_t_eq_mu_a3 hvK]
    exact le_trans hdil hε₀323
  have hPH : (Work.BoseRowsFS.honF v h fc fu HM μ).PHset
        (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ)
      = (Work.BoseRowsFS.honF v h fc fu HM μ).PHset (Work.BoseRowsFS.honE v h fc fu HM μ) := rfl
  -- ## FS `lem:EstimateIntegral`, pinned, at the honest `IntKernel`
  have hrow := Work.BoseB7A.estIntegralOneA_pinned K₀
    (Work.BoseRowsFS.honF v h fc fu HM μ)
    (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ) hvK R
    (fun k => Work.BoseFixR.chat (Submission.BoseGases.g0 v h)
      ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom k))
    ht (H.rkh HM μ hμ hdilg)
    (hIK HM hN μ ρ hvK hμ hdil₁ hρ0 (H.a16 HM μ hμ hdilg))
  rw [hPH] at hrow
  rw [hρeq] at hrow
  simpa [Work.BoseFixR.KzEnvAt] using hrow

end

end Work.BoseRowsL.Glue
