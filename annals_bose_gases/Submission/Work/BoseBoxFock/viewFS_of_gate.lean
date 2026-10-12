import ChallengeDeps
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseBoxFock.bessel_honest
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.viewFS_of_gate` — the view at the honest family, from the gate

The corrected view `Work.BoseBoxFock.RViewFS` at the honest family
`HonestBoxFam v h fc fu HM` follows from the honest gate `HonestGateAtFS`
alone: every conjunct of `RViewFS` is either a *definitional* unfolding of
`HonestBoxFam`/`KzEnvHon`/`KzEnvFs` (the scalar/kernel pins — they are `rfl`), the
`χ`-Bessel conjunct (`bessel_honest`, with `Cn = 48/π ≤ 16`), the `FSParamsView`
of the canonical parameter point (`FSParamsViewCanon`, whose fields do not involve
the pin'd kernels `τ̃, Ŵ₁ζ, 𝒜, ℬ`), the `Ŵ₁` cut-off pin — the only conjunct that
uses the lattice-size hypothesis `hN` (the cut radius `Λ_N = uvRad ℓ N` must
dominate `4K_L√(μa)`), or the gate itself.

Nothing here is specific to the honest gate: the same proof says that any
`Q3KernelFS`-gate at the model gives the view.
-/

namespace Work.BoseBoxFock

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox
open Work.BoseBoxFix Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped BigOperators

/-- `ellH v μ = sideAt μ (a v)` in the physical range `μ > 0`, `a v > 0`.

Renamed from `ellH_eq_sideAt` to `ellH_eq_sideAt'` (curric-46 BoseWireFix, item 1 of
`Submission/Work/BOSE_INTEGRATION_AUDIT.md` §4): the name `Work.BoseBoxFock.ellH_eq_sideAt` is
also declared in `Submission/Work/BoseBoxFock/honestEnvNumeric.lean`, so the two modules could
not be imported into one cone.  This declaration is the *strictly stronger* of the two (its
hypotheses `0 < μ`, `0 < a v` imply `0 < sideAt μ (a v)`), and nothing outside this file used
it, so the rename is invisible to every importer.  A caller holding only
`0 < sideAt μ (a v)` should use `Work.BoseBoxFock.ellH_eq_sideAt` (honestEnvNumeric) instead. -/
lemma ellH_eq_sideAt' {v : ℝ³ → ℝ} {μ : ℝ} (hμ : 0 < μ) (hav : 0 < BoseGases.a v) :
    ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) := by
  unfold ellH
  rw [if_pos (Work.BoseBox.sideAt_pos hμ hav)]

/-- The condensate density `ρ_z = z²/ℓ³` of the honest environment is `μ`: the
environment's `z`/`ℓ` are those of the canonical `KzEnvFs`, whose density
`KzEnvFs_rho` is `μ`. -/
lemma rho_KzEnvHon {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ} (hμ : 0 < μ)
    (hav : 0 < BoseGases.a v) {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (F : Work.BoseB7.FockData Mode) (fc fu : Work.BoseBoxFix.LowCut)
    (N : ℕ) : (KzEnvHon v h μ F fc fu N).rho = μ := by
  have h1 : (KzEnvHon v h μ F fc fu N).rho = (Work.BoseFixR.KzEnvFs v h μ F fc).rho := rfl
  rw [h1]
  exact Work.BoseFixR.KzEnvFs_rho (v := v) (h := h) (μ := μ) hμ hav F fc

/-- **`FSParamsView` of the honest environment.**  `KzEnvHon` only replaces the
kernels `τ, Ŵ₁, 𝒜, ℬ` of `KzEnvFs`; every field of `FSParamsView` is a scalar of
`KzEnvFs`, so `FSParamsViewCanon` transfers verbatim. -/
lemma nonempty_fsParamsView_KzEnvHon {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ}
    (hμ : 0 < μ) (hav : 0 < BoseGases.a v) (ht1 : μ * BoseGases.a v ^ 3 ≤ 1)
    {Mode : Type} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData.{0, 0} Mode) (fc fu : Work.BoseBoxFix.LowCut) (N : ℕ) :
    Nonempty (Work.BoseB7.FSParamsView (KzEnvHon v h μ F fc fu N)) := by
  obtain ⟨hv⟩ := Work.BoseFixR.FSParamsViewCanon h hμ hav ht1 Mode F fc
  exact ⟨{ hv with }⟩

/-- `FSParamsView` at the honest family. -/
lemma nonempty_fsParamsView_HonestBoxFam {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {HM : ∀ μ : ℝ, HonestModes v μ} {μ : ℝ}
    (hμ : 0 < μ) (hav : 0 < BoseGases.a v) (ht1 : μ * BoseGases.a v ^ 3 ≤ 1) :
    Nonempty (Work.BoseB7.FSParamsView (HonestBoxFam v h fc fu HM μ).E) := by
  simp only [HonestBoxFam]
  exact nonempty_fsParamsView_KzEnvHon hμ hav ht1 _ fc fu _

/-- `ρ_z = μ` at the honest family. -/
lemma honestBoxFam_rho {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {fc fu : Work.BoseBoxFix.LowCut}
    {HM : ∀ μ : ℝ, HonestModes v μ} {μ : ℝ} (hμ : 0 < μ) (hav : 0 < BoseGases.a v) :
    (HonestBoxFam v h fc fu HM μ).E.rho = μ := by
  simp only [HonestBoxFam]
  exact rho_KzEnvHon hμ hav _ fc fu _

/-- The low-momentum cut-off of the honest environment. -/
lemma honestBoxFam_KL {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {fc fu : Work.BoseBoxFix.LowCut}
    {HM : ∀ μ : ℝ, HonestModes v μ} (μ : ℝ) :
    (HonestBoxFam v h fc fu HM μ).E.KL
      = ((paramsAt μ (BoseGases.a v)).Kl * (paramsAt μ (BoseGases.a v)).d ^ 2) ^ (-(1 : ℝ)) :=
  rfl

/-- `48/π ≤ 16` (the `Cn`-cap of the corrected view). -/
lemma fortyEight_div_pi_le_sixteen : (48 : ℝ) / Real.pi ≤ 16 := by
  rw [div_le_iff₀ Real.pi_pos]
  nlinarith [Real.pi_gt_three]

theorem viewFS_of_gate {v : ℝ³ → ℝ} (h : Work.UBB.ScatSol v) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut)
    (HM : ∀ μ : ℝ, HonestModes v μ)
    (hN : ∀ μ, 0 < μ →
      4 * (((Work.BoseBox.paramsAt μ (BoseGases.a v)).Kl
              * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2) ^ (-(1 : ℝ))
            * Real.sqrt (μ * BoseGases.a v))
        ≤ uvRad (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N)
    {ε K₀ b₀ : ℝ} (hε1 : ε ≤ 1) (hgate : HonestGateAtFS v h fc fu HM ε K₀ b₀) :
    ∀ μ : ℝ, 0 < μ → μ * BoseGases.a v ^ 3 ≤ ε →
      (HonestBoxFam v h fc fu HM μ).viewFS v h μ := by
  intro μ hμ hμa
  -- the parameter point of the canonical environment
  have hdil : μ * BoseGases.a v ^ 3 ≤ 1 := le_trans hμa hε1
  have hellH : ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) := ellH_eq_sideAt' hμ hav
  -- the density of the honest environment
  have hρ : (HonestBoxFam v h fc fu HM μ).E.rho = μ := honestBoxFam_rho hμ hav
  -- the gate, at this `μ`
  have hbgap : b₀ ≤ (HonestBoxFam v h fc fu HM μ).E.b := hgate.2.2.1 μ hμ hμa
  have hQ3 : ∀ ρ : ℝ, CloseCondFS v μ ρ → Q3KernelFS K₀
      (HonestBoxFam v h fc fu HM μ).F (HonestBoxFam v h fc fu HM μ).T
      (KzEnvAt (HonestBoxFam v h fc fu HM μ).E ρ) := hgate.2.2.2 μ hμ hμa
  -- unfold the view
  unfold Work.BoseFixR.KzDatum.viewFS
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
