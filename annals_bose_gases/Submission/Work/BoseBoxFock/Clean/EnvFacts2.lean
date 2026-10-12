import ChallengeDeps
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Submission.Work.BoseB7AK.W1rows.W1omega0_rows
import Submission.Work.BoseBoxFock.Clean.Parity
import Submission.Work.BoseBoxFock.KafzInst
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseBoxFock/Clean/EnvFacts2.lean`

**Why this module exists.**  The environment facts of the honest family
(`honestEnvFam_ell_pos`, `honestEnvFam_W1omega_zero_eq`, `honestEnvFam_parity`,
`honestEnvFam_W1omega0_nonneg`, `cHCF_nonneg`, in
`Submission/Work/BoseBoxFock/honestEnvFacts2.lean`) are needed by the environment bundle
`EnvFactsAt`, but their module imports `Submission.Work.BoseFixR.HonestEnvParity`, whose
module imports `Submission.Work.BoseFixR.RB5FSFixAux` — a module that (after the interface
change `F9`, `CloseCond` → `CloseCondFS`) no longer compiles, so the whole cone is
unloadable (including the honest `model_kafz` floor).

This file is a **verbatim copy** of the six lemmas used by `EnvFactsAt` (the two
bundle theorems `honestEnvFacts_of_nonneg`/`honestEnvFacts_of_view` are not needed here),
with `HonestEnvParity` replaced by the copy `Work.BoseBoxFock.Clean.Parity` (whose
`RB5FSFixAux` import was gratuitous) and re-scoped to `Work.BoseBoxFock.Clean`.
Nothing new is proved here.
-/

noncomputable section

open scoped Real

open MeasureTheory

namespace Work.BoseBoxFock.Clean

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## 1. The six conjuncts that follow from the requested hypotheses -/

/-- `E.ell = sideAt μ (a v) = K_ℓ(μa)^{-1/2} > 0` for `0 < μ`, `0 < a v`. -/
theorem honestEnvFam_ell_pos (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ)
    {μ : ℝ} (hμ : 0 < μ) (hav : 0 < BoseGases.a v) :
    0 < (HonestBoxFam v h fc fu HM μ).E.ell := by
  rw [show (HonestBoxFam v h fc fu HM μ).E.ell
      = Work.BoseBox.sideAt μ (BoseGases.a v) from rfl,
    Work.BoseBox.sideAt, Work.BoseBox.boxSide]
  refine mul_pos ?_ (Real.rpow_pos_of_pos (mul_pos hμ hav) _)
  show 0 < Work.BoseBox.fsXp (Work.BoseFixR.dil v μ) (-(3 / 2))
  exact Work.BoseBox.fsXp_pos (by unfold Work.BoseFixR.dil; positivity)

/-- `F.kmom 0 = 0` for the honest Fock data (`kmom_neg 0` and `2 • x = 0`). -/
theorem honestFam_kmom_zero (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ)
    (μ : ℝ) : (HonestBoxFam v h fc fu HM μ).F.kmom 0 = 0 := by
  have h0 := (HonestBoxFam v h fc fu HM μ).F.kmom_neg 0
  rw [neg_zero] at h0
  have h2 : (2 : ℝ) • (HonestBoxFam v h fc fu HM μ).F.kmom 0 = 0 := by
    rw [two_smul]; nth_rewrite 2 [h0]; exact add_neg_cancel _
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

/-- `E.W1omega 0 = E.W1omega0` (`W1omega = chat W₁ω` and `F.kmom 0 = 0`). -/
theorem honestEnvFam_W1omega_zero_eq (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ)
    (μ : ℝ) :
    (HonestBoxFam v h fc fu HM μ).E.W1omega 0
      = (HonestBoxFam v h fc fu HM μ).E.W1omega0 := by
  rw [show (HonestBoxFam v h fc fu HM μ).E.W1omega 0
      = Work.BoseFixR.chat (Work.BoseFixR.W1omegaFun v h (Work.BoseBox.sideAt μ (BoseGases.a v)))
          ((HonestBoxFam v h fc fu HM μ).F.kmom 0) from rfl,
    honestFam_kmom_zero v h fc fu HM μ]
  rfl

/-- The four parity conjuncts of the honest environment. -/
theorem honestEnvFam_parity (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ)
    (μ : ℝ) :
    (∀ k : Lab (HM μ).N,
        (HonestBoxFam v h fc fu HM μ).E.tau (-k) = (HonestBoxFam v h fc fu HM μ).E.tau k)
    ∧ (∀ k : Lab (HM μ).N,
        (HonestBoxFam v h fc fu HM μ).E.hatChi (-k)
          = (HonestBoxFam v h fc fu HM μ).E.hatChi k)
    ∧ (∀ k : Lab (HM μ).N,
        (HonestBoxFam v h fc fu HM μ).E.W1 (-k) = (HonestBoxFam v h fc fu HM μ).E.W1 k)
    ∧ (∀ k : Lab (HM μ).N,
        (HonestBoxFam v h fc fu HM μ).E.W1omega (-k)
          = (HonestBoxFam v h fc fu HM μ).E.W1omega k) :=
  ⟨fun k => honestBoxFam_tau_even k,
    fun k => by
      simp only [HonestBoxFam, KzEnvHon, Work.BoseFixR.KzEnvFs, Work.BoseB4.boxFockData,
        Work.BoseB4.b7FockDataBox, kmomLab_neg, Work.BoseB7AK.W1rows.chat_neg],
    fun k => honestBoxFam_W1_even k,
    fun k => by
      simp only [HonestBoxFam, KzEnvHon, Work.BoseFixR.KzEnvFs, Work.BoseB4.boxFockData,
        Work.BoseB4.b7FockDataBox, kmomLab_neg, Work.BoseB7AK.W1rows.chat_neg]⟩

/-! ## 2. The missing hypothesis: `0 ≤ v` (radial, compactly supported) -/

/-- `Ŵ₁ω(0) ≥ 0` for a nonnegative radial `v` of compact support: the numerator
`g₀ω = v(1−ω)ω` is nonnegative a.e. (`Work.BoseB7AK.W1rows.W1omegaNum_nonneg_ae`,
i.e. `scat_gomega_ae_bounds`), `(χ⋆χ)(·/ℓ) ≥ 0` everywhere
(`Submission.BoseGases.convScale_nonneg`), and `chat W 0 = ∫W`
(`Work.BoseB7AK.W1rows.chat_zero`). -/
theorem honestEnvFam_W1omega0_nonneg (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) {R : ℝ}
    (hR : 0 < R) (hv : 0 ≤ v) (hvrad : BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ)
    (μ : ℝ) : 0 ≤ (HonestBoxFam v h fc fu HM μ).E.W1omega0 := by
  rw [show (HonestBoxFam v h fc fu HM μ).E.W1omega0
      = Work.BoseFixR.chat (Work.BoseFixR.W1omegaFun v h (Work.BoseBox.sideAt μ (BoseGases.a v))) 0
      from rfl,
    Work.BoseB7AK.W1rows.chat_zero]
  refine MeasureTheory.integral_nonneg_of_ae ?_
  filter_upwards [Work.BoseB7AK.W1rows.W1omegaNum_nonneg_ae hR hv hvrad hv_supp h] with x hx
  rw [show Work.BoseFixR.W1omegaFun v h (Work.BoseBox.sideAt μ (BoseGases.a v)) x
      = Work.BoseB7AK.W1rows.W1omegaNum v h x
        / Submission.BoseGases.convScale (Work.BoseBox.sideAt μ (BoseGases.a v)) x from rfl]
  exact div_nonneg hx (Submission.BoseGases.convScale_nonneg _ _)

/-- `0 ≤ cHCF E (8π·a v)` from `0 < E.ell` and `0 ≤ E.W1omega0`:
`cHCF E ĝ₀ = ½ℓ⁻³(ĝ₀ + Ŵ₁ω(0))` with `ĝ₀ = 8π·a v > 0`. -/
theorem cHCF_nonneg {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) (v : ℝ³ → ℝ) (hℓ : 0 < E.ell)
    (hW : 0 ≤ E.W1omega0) (hav : 0 < BoseGases.a v) :
    0 ≤ cHCF E (8 * π * BoseGases.a v) := by
  rw [show cHCF E (8 * π * BoseGases.a v)
      = (1 / 2) * E.ell ^ (-(3 : ℝ)) * (8 * π * BoseGases.a v + E.W1omega0) from rfl]
  refine mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (le_of_lt hℓ) _)) ?_
  have h8 : 0 < 8 * π * BoseGases.a v := by
    have := Real.pi_pos; positivity
  linarith

end Work.BoseBoxFock.Clean
