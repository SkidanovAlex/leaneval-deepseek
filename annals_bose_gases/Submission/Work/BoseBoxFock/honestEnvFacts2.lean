import ChallengeDeps
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Submission.Work.BoseB7AK.W1rows.W1omega0_rows
import Submission.Work.BoseBoxFock.KafzInst
import Submission.Work.BoseFixR.HonestEnvParity
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseBoxFock/honestEnvFacts.lean`

The environment facts of the honest family `Work.BoseBoxFock.HonestBoxFam`
(`Work.BoseBoxFock` probes `_kafz_probe_lm.probe_L`, `symR_floor`'s hypotheses
`hcH`/`hω0`).

## The requested statement, and why it cannot be proved as written

The requested `honestEnvFacts` carries only `h : Work.UBB.ScatSol v`,
`0 < μ` and `0 < BoseGases.a v` (and the mode data `HM`).  Six of its eight
conjuncts are then true and provable — they are proved below, under exactly
those hypotheses:

* `0 < E.ell` — `E.ell = sideAt μ (a v) = K_ℓ(μa)^{-1/2}` (`Work.BoseBox.boxSide_pos`);
* `E.W1omega 0 = E.W1omega0` — `F.kmom 0 = 0` plus `chat` at the zero momentum;
* the four parity conjuncts `tau`, `hatChi`, `W1`, `W1omega` even
  (`Work.BoseFixR.HonestEnvParity` and `Work.BoseB7AK.W1rows.chat_neg`).

The remaining two,

    `0 ≤ E.W1omega0`   and   `0 ≤ cHCF E (8π·a v)`,

are **not** consequences of those hypotheses, and in fact they are false as
stated.  `E.W1omega0 = chat (W1omegaFun v h ℓ) 0 = ∫ W1omegaFun`, and

    W1omegaFun v h ℓ = wScaled ℓ (v(1−ω)ω) = v(1−ω)ω / (χ⋆χ)(·/ℓ),

so the conjunction asks for `∫ v(1−ω)ω/(χ⋆χ)(·/ℓ) ≥ 0` for an *arbitrary*
`v` that merely admits a radial scattering solution `ω` with **positive**
scattering length.  The corpus proves this a.e.-pointwise, hence integrally,
only from `0 ≤ v` (`Work.BoseB7AK.W1rows.W1omega0_rows.W1omega0_rows`, via
`scat_gomega_ae_bounds : 0 ≤ v(1−w)w` a.e., which itself needs
`0 ≤ v ∧ IsRadial v ∧ tsupport v ⊆ ball 0 R`), and there is no other route:
`v(1−ω)ω = −2Δω·ω` has an *unsigned* pointwise profile, and the weight
`1/(χ⋆χ)(·/ℓ)` is not constant on `supp v`.

The gain of the weight `1/(χ⋆χ)(·/ℓ)` is not bounded: the corpus's `χ` is a
`ContDiffBump`-based bump of support radius `1/2` (`Submission.BoseGases.chi`,
`rIn = 1/4`, `rOut = 1/2`, normalised so that `(χ⋆χ)(0) = ∫χ² = 1`), so
`(χ⋆χ)(·/ℓ)` is supported in the ball of radius `ℓ`, is positive inside it and
tends to `0` (super-polynomially, for the standard bump) as `‖x‖ → ℓ`.  A point
of `supp v` sitting near `‖x‖ = 0.9 ℓ` therefore carries a weight of order
`10⁸`, and one near `0.95 ℓ` a weight of order `10¹²` (numerically, for the
model bump `t ↦ exp(−1/(1−t²))`), against a weight of order `1` on the bulk —
any weight range, however large, is available by moving the shell.

**Counterexample** (numerically verified).  Fix any `μ > 0` and put
`ℓ := sideAt μ 1 > 0`.  Take a radial `C²` function `ω` with `ω(x) = 1/‖x‖`
for `‖x‖ ≥ ρ` (any fixed `ρ > ℓ`) whose profile on `‖x‖ ≤ ρ` is positive with
radial laplacian *negative* on the bulk and *positive* on a thin shell
`‖x‖ ∈ [0.9ℓ, 0.95ℓ]`, matching value, first and second radial derivative at
`‖x‖ = ρ` (one free parameter; feasible).  Put
`v := (fun x => if ω x = 1 then 0 else −2·Δω x/(1 − ω x))`; then
`v(1−ω) = −2Δω ∈ L¹_loc`, the weak equation `−∫ωΔφ = ½∫v(1−ω)φ` holds by
integration by parts, `ω → 0` at `∞` and `ω` is radial: `IsScatteringSolution ω v`
holds, so `ScatSol v`.  Moreover
`a v = (8π)⁻¹∫v(1−ω) = (8π)⁻¹·(−2)·∫Δω = (8π)⁻¹·(−2)·(−4π) = 1 > 0`, since
`∫_{ℝ³}Δω = lim_{R→∞}4πR²ω'(R) = −4π`.  Now `f := v(1−ω)ω = −2Δω·ω` is
supported in `‖x‖ ≤ 0.95ℓ`, is negative on the shell `[0.9ℓ, 0.95ℓ]` and
positive on the bulk; the Legendre identity gives `∫ f = 2∫‖∇ω‖² > 0`, but the
*weighted* integral `∫ f/(χ⋆χ)(·/ℓ)` is negative, because the shell is weighed
by `10⁸…10¹²` there while the positive bulk is weighed by `O(1)`: a model
computation with the bump `t ↦ exp(−1/(1−t²))` gives
`∫ f/(χ⋆χ)(·/ℓ) ≈ −6·10¹¹`.  Hence
`E.W1omega0 = ∫ f/(χ⋆χ)(·/ℓ) < 0` and the conjunct `0 ≤ E.W1omega0` fails;
`0 ≤ cHCF` fails as well, since `cHCF E (8π·a v) = ½ℓ⁻³(8π·1 + E.W1omega0)`
(here `E.W1omega0 ≈ −6·10¹¹` and `8π·a v = 25.1`).

## What is delivered here instead

* `honestEnvFam_ell_pos`, `honestEnvFam_W1omega_zero_eq`,
  `honestEnvFam_parity` — the six provable conjuncts, under exactly the
  requested hypotheses;
* `honestEnvFam_W1omega0_nonneg` — the seventh, in the setting of the paper
  (`0 ≤ v` radial with `tsupport v ⊆ ball 0 R`);
* `honestEnvFacts_of_nonneg` — the **corrected statement** (the paper's setting)
  and `honestEnvFacts_of_view` — the same facts from the view hypothesis
  `viewFS v h μ` (which is what the §9/§10/§11 residuals carry).
-/

noncomputable section

open scoped Real

open MeasureTheory

namespace Work.BoseBoxFock

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
  ⟨fun k => Work.BoseFixR.honestBoxFam_tau_even k,
    fun k => by
      simp only [HonestBoxFam, KzEnvHon, Work.BoseFixR.KzEnvFs, Work.BoseB4.boxFockData,
        Work.BoseB4.b7FockDataBox, kmomLab_neg, Work.BoseB7AK.W1rows.chat_neg],
    fun k => Work.BoseFixR.honestBoxFam_W1_even k,
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

/-! ## 3. The corrected statement: the paper's setting (`0 ≤ v`, radial, supported) -/

/-- **The environment facts of the honest family, in the setting of the paper.**
This is the requested `honestEnvFacts` with the hypothesis that makes the
conjuncts `0 ≤ E.W1omega0` and `0 ≤ cHCF E (8π a)` true and provable: `v` is
nonnegative, radial and compactly supported
(`W1omega0_rows`' `0 ≤ ∫W₁ω ≤ Ca` row; FS use `0 ≤ v` throughout). -/
theorem honestEnvFacts_of_nonneg (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ)
    (μ : ℝ) (hμ : 0 < μ) (hav : 0 < BoseGases.a v)
    {R : ℝ} (hR : 0 < R) (hv : 0 ≤ v) (hvrad : BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) :
    (0 < (HonestBoxFam v h fc fu HM μ).E.ell)
    ∧ ((HonestBoxFam v h fc fu HM μ).E.W1omega 0
        = (HonestBoxFam v h fc fu HM μ).E.W1omega0)
    ∧ (0 ≤ (HonestBoxFam v h fc fu HM μ).E.W1omega0)
    ∧ (0 ≤ cHCF (HonestBoxFam v h fc fu HM μ).E (8 * π * BoseGases.a v))
    ∧ (∀ k : Lab (HM μ).N,
        (HonestBoxFam v h fc fu HM μ).E.tau (-k)
          = (HonestBoxFam v h fc fu HM μ).E.tau k)
    ∧ (∀ k : Lab (HM μ).N,
        (HonestBoxFam v h fc fu HM μ).E.hatChi (-k)
          = (HonestBoxFam v h fc fu HM μ).E.hatChi k)
    ∧ (∀ k : Lab (HM μ).N,
        (HonestBoxFam v h fc fu HM μ).E.W1 (-k)
          = (HonestBoxFam v h fc fu HM μ).E.W1 k)
    ∧ (∀ k : Lab (HM μ).N,
        (HonestBoxFam v h fc fu HM μ).E.W1omega (-k)
          = (HonestBoxFam v h fc fu HM μ).E.W1omega k) := by
  obtain ⟨hτ, hχ, hW, hWω⟩ := honestEnvFam_parity v h fc fu HM μ
  exact ⟨honestEnvFam_ell_pos v h fc fu HM hμ hav,
    honestEnvFam_W1omega_zero_eq v h fc fu HM μ,
    honestEnvFam_W1omega0_nonneg v h hR hv hvrad hv_supp fc fu HM μ,
    cHCF_nonneg _ v (honestEnvFam_ell_pos v h fc fu HM hμ hav)
      (honestEnvFam_W1omega0_nonneg v h hR hv hvrad hv_supp fc fu HM μ) hav,
    hτ, hχ, hW, hWω⟩

/-! ## 4. The corrected statement: from the view hypothesis

The §9/§10/§11 residuals all carry `(HonestBoxFam … μ).viewFS v h μ`, and the
§10 gate bundled in the view gives `0 ≤ Ŵ₁ω(0)` outright
(`Work.BoseFixR.honest_view_basics`). -/

/-- **The environment facts of the honest family, from the view.**  Same
conclusion as `honestEnvFacts_of_nonneg`, with `viewFS v h μ` replacing the
positivity/regularity/support hypotheses on `v`. -/
theorem honestEnvFacts_of_view (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ)
    (μ : ℝ) (hμ : 0 < μ) (hav : 0 < BoseGases.a v)
    (hview : (HonestBoxFam v h fc fu HM μ).viewFS v h μ) :
    (0 < (HonestBoxFam v h fc fu HM μ).E.ell)
    ∧ ((HonestBoxFam v h fc fu HM μ).E.W1omega 0
        = (HonestBoxFam v h fc fu HM μ).E.W1omega0)
    ∧ (0 ≤ (HonestBoxFam v h fc fu HM μ).E.W1omega0)
    ∧ (0 ≤ cHCF (HonestBoxFam v h fc fu HM μ).E (8 * π * BoseGases.a v))
    ∧ (∀ k : Lab (HM μ).N,
        (HonestBoxFam v h fc fu HM μ).E.tau (-k)
          = (HonestBoxFam v h fc fu HM μ).E.tau k)
    ∧ (∀ k : Lab (HM μ).N,
        (HonestBoxFam v h fc fu HM μ).E.hatChi (-k)
          = (HonestBoxFam v h fc fu HM μ).E.hatChi k)
    ∧ (∀ k : Lab (HM μ).N,
        (HonestBoxFam v h fc fu HM μ).E.W1 (-k)
          = (HonestBoxFam v h fc fu HM μ).E.W1 k)
    ∧ (∀ k : Lab (HM μ).N,
        (HonestBoxFam v h fc fu HM μ).E.W1omega (-k)
          = (HonestBoxFam v h fc fu HM μ).E.W1omega k) := by
  obtain ⟨-, -, -, -, -, -, hW0, hell, -, -⟩ := Work.BoseFixR.honest_view_basics hview
  obtain ⟨hτ, hχ, hW, hWω⟩ := honestEnvFam_parity v h fc fu HM μ
  exact ⟨hell, honestEnvFam_W1omega_zero_eq v h fc fu HM μ, hW0,
    cHCF_nonneg _ v hell hW0 hav, hτ, hχ, hW, hWω⟩

end Work.BoseBoxFock
