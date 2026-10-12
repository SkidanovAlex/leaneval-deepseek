import ChallengeDeps
import Submission.Work.BoseBoxFock.AllDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.viewFSAll_of_gateAll` — the `All` view at the honest family, from the gate

Design item 5 glue (D3), row 1: the `All`-vocabulary port of
`Work.BoseBoxFock.viewFS_of_gate` (`BoseBoxFock/viewFS_of_gate.lean`).  The corrected view
`RViewFSAll` at the honest family `HonestBoxFam v h fc fu HM` follows from the honest `All`
gate `HonestGateAtFSAll` alone: every conjunct of `RViewFSAll` is either

* a *definitional* unfolding of `HonestBoxFam`/`KzEnvHon`/`KzEnvFs` (the scalar/kernel pins,
  which are `rfl`),
* the χ-Bessel conjunct (`bessel_honest`, with `Cn = 48/π ≤ 16`),
* the `FSParamsView` of the canonical parameter point (`FSParamsViewCanon` via
  `nonempty_fsParamsView_HonestBoxFam`, whose fields do not involve the pin'd kernels),
* the `Ŵ₁` cut-off pin (the only conjunct that uses the lattice-size hypothesis `hN`),
* or the gate itself, now at `Q3KernelFSAll`.

The two conjunct lists of `RViewFS` and `RViewFSAll` are in the *same order* with the *same*
types (`AllDefs.lean` guarantees this by construction, so that positional destructuring
ports), so this is the same proof with the gate conjunct replaced.

The statement is copied verbatim (modulo full qualification) from
`Submission/Work/BOSE_ALL_STATEMENTS.lean.txt` (item 5 glue).
-/

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Filter Metric

namespace Work.BoseBoxFock

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox
open Work.BoseBoxFix Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

theorem viewFSAll_of_gateAll {v : ℝ³ → ℝ} (h : Work.UBB.ScatSol v) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, HonestModes v μ)
    (hN : ∀ μ, 0 < μ →
      4 * (((Work.BoseBox.paramsAt μ (BoseGases.a v)).Kl
              * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2) ^ (-(1 : ℝ))
            * Real.sqrt (μ * BoseGases.a v))
        ≤ uvRad (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N)
    {ε K₀ b₀ : ℝ} (hε1 : ε ≤ 1) (hgate : HonestGateAtFSAll v h fc fu HM ε K₀ b₀) :
    ∀ μ : ℝ, 0 < μ → μ * BoseGases.a v ^ 3 ≤ ε →
      (HonestBoxFam v h fc fu HM μ).viewFSAll v h μ := by
  intro μ hμ hμa
  -- the parameter point of the canonical environment
  have hdil : μ * BoseGases.a v ^ 3 ≤ 1 := le_trans hμa hε1
  have hellH : ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) := ellH_eq_sideAt' hμ hav
  -- the density of the honest environment
  have hρ : (HonestBoxFam v h fc fu HM μ).E.rho = μ := honestBoxFam_rho hμ hav
  -- the gate, at this `μ`
  have hbgap : b₀ ≤ (HonestBoxFam v h fc fu HM μ).E.b := hgate.2.2.1 μ hμ hμa
  have hQ3 : ∀ ρ : ℝ, CloseCondFS v μ ρ → Q3KernelFSAll K₀
      (HonestBoxFam v h fc fu HM μ).F (HonestBoxFam v h fc fu HM μ).T
      (KzEnvAt (HonestBoxFam v h fc fu HM μ).E ρ) := hgate.2.2.2 μ hμ hμa
  -- unfold the view
  unfold Work.BoseFixR.KzDatum.viewFSAll
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    ?_, ?_, ?_, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact nonempty_fsParamsView_HonestBoxFam (HM := HM) hμ hav hdil
  · -- `𝒜 = τ̃ + ρ_z Ŵ₁`
    funext k
    rw [hρ]
    rfl
  · -- `ℬ = ρ_z Ŵ₁`
    funext k
    rw [hρ]
    rfl
  · -- the `Ŵ₁` cut-off pin: `Λ_N = uvRad ℓ N` dominates `4K_L√(μa)`
    refine ⟨fu, uvRad (ellH v μ) (HM μ).N, ?_, ?_⟩
    · rw [hellH, honestBoxFam_KL μ]
      exact hN μ hμ
    · funext k
      simp only [HonestBoxFam, KzEnvHon, KzEnvFs, hellH, Work.BoseFixR.ell]
  · -- the low-momentum cut-off
    exact ⟨fc, rfl⟩
  · -- `n₊^H` on the χ-modes
    exact ⟨fu, rfl⟩
  · -- the Bessel conjunct (`bessel_honest`), with the absolute cap `48/π ≤ 16`
    exact ⟨48 / Real.pi, by positivity, fortyEight_div_pi_le_sixteen, bessel_honest v h fc fu HM μ⟩
  · -- the gate itself
    exact ⟨K₀, b₀, hgate.1, hgate.2.1, hbgap, hQ3⟩

end Work.BoseBoxFock

namespace Work.BoseAllGlue

/-- The `Work.BoseAllGlue` name of `Work.BoseBoxFock.viewFSAll_of_gateAll`. -/
alias viewFSAll_of_gateAll := Work.BoseBoxFock.viewFSAll_of_gateAll

end Work.BoseAllGlue
