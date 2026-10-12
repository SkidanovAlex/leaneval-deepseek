import ChallengeDeps
import Submission.Work.BoseBoxFock.KafzDict
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseBoxFock/EnvFacts.lean` — the environment bundle of the honest family

`Work.BoseBoxFock.model_kafz` is proved by the coherent-state (`c`-number) substitution
`Work.BoseBoxFock.bomb_H2ndHon_eq_integral`, a *pointwise* symbol floor
(`Re⟪v(z), symC z v(z)⟫ ≥ (λ − (B₂|z|² + B₁|z| + B₀))‖v(z)‖²`, from `symR_floor` + the
`valFS` floor) and the Gaussian moments `gauss_moments_le`.  The constants `B₂, B₁, B₀` are

    B₂ = 4·cHCF E ĝ(0),      B₁ = 4·ℓ⁻³(|Ŵ₁(0)|√Kc + Ŵ₁ω(0)√M),
    B₀ = |2·cHCF E ĝ(0) + μĝ(0)| + ℓ⁻³(Wsup + |Ŵ₁(0)+Ŵ₁ω(0)|)·Kc,

with `Kc = (48/π)M`, `Wsup` a bound for `|Ŵ₁(k)+Ŵ₁ω(k)|`, and every one of these is a
several-line arithmetic consequence of the *numerical facts* of the honest data
(`ℓ⁻³ ≤ Cμ`, `M ≤ Cμℓ³`, `μℓ³ ≥ 1`, `|Ŵ₁(k)|,|Ŵ₁ω(k)| ≤ Ca`, `0 ≤ Ŵ₁ω(0) ≤ Ca`,
`0 ≤ cHCF`), together with `n ≤ 2μℓ³`.

This file collects those facts in one `Prop`, so that

* the *regime* lemma (`Work.BoseBoxFock.honestEnvNumeric`) proves
  `∃ ε₀ C, 0 < ε₀ ∧ 0 ≤ C ∧ ∀ μ, Adm v ε₀ μ → EnvFactsAt … μ C` — the sources are
  `Work.BoseFixR.WindowRegime` (the monomial facts, including `R ≤ ℓ·χ_{R₀}`, which is what
  unlocks `Work.BoseB7AK.W1rows.W1hat_abs_le`) and the honest-environment identities
  (`Work.BoseBoxFock.honestEnvFacts2`: `0 < E.ell`, `E.W1omega 0 = E.W1omega0`,
  `0 ≤ E.W1omega0`, `0 ≤ cHCF`, and the four parity rows);
* the *arithmetic* lemmas consume it as a hypothesis, at a fixed `μ`.

The parity rows are here (rather than in the arithmetic) because `symDiscrep` needs them.
The `Σ_k χ̂_k² ≤ 1`, `Σ_{s≠0}(χ̂²_s)² ≤ 1` and `n₊^χ ≤ (48/π)n₊` rows (also needed by the
final assembly) are *not* here: they are `Adm`-independent and are delivered by
`Work.BoseBoxFock.honestEnvBessel`.
-/

noncomputable section

open scoped BigOperators Real

namespace Work.BoseBoxFock

open Work.BoseB4

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The numerical facts of the honest environment at `μ`, with constant `C`.** -/
def EnvFactsAt (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ C : ℝ) : Prop :=
  (0 < (HonestBoxFam v h fc fu HM μ).E.ell)
  ∧ ((HonestBoxFam v h fc fu HM μ).E.ell = Work.BoseBox.sideAt μ (BoseGases.a v))
  ∧ ((HonestBoxFam v h fc fu HM μ).E.mu = μ)
  ∧ (1 ≤ μ * (HonestBoxFam v h fc fu HM μ).E.ell ^ 3)
  ∧ ((HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ)) ≤ C * μ)
  ∧ ((HonestBoxFam v h fc fu HM μ).E.bigM
      ≤ C * μ * (HonestBoxFam v h fc fu HM μ).E.ell ^ 3)
  ∧ (∀ k : Lab (HM μ).N,
      |(HonestBoxFam v h fc fu HM μ).E.W1 k| ≤ C * BoseGases.a v)
  ∧ (∀ k : Lab (HM μ).N,
      |(HonestBoxFam v h fc fu HM μ).E.W1omega k| ≤ C * BoseGases.a v)
  ∧ (0 ≤ (HonestBoxFam v h fc fu HM μ).E.W1omega0)
  ∧ ((HonestBoxFam v h fc fu HM μ).E.W1omega0 ≤ C * BoseGases.a v)
  ∧ ((HonestBoxFam v h fc fu HM μ).E.W1omega 0
      = (HonestBoxFam v h fc fu HM μ).E.W1omega0)
  ∧ (0 ≤ cHCF (HonestBoxFam v h fc fu HM μ).E (8 * π * BoseGases.a v))
  ∧ (∀ k : Lab (HM μ).N,
      (HonestBoxFam v h fc fu HM μ).E.W1 (-k) = (HonestBoxFam v h fc fu HM μ).E.W1 k)
  ∧ (∀ k : Lab (HM μ).N,
      (HonestBoxFam v h fc fu HM μ).E.W1omega (-k)
        = (HonestBoxFam v h fc fu HM μ).E.W1omega k)
  ∧ (∀ k : Lab (HM μ).N,
      (HonestBoxFam v h fc fu HM μ).E.tau (-k) = (HonestBoxFam v h fc fu HM μ).E.tau k)
  ∧ (∀ k : Lab (HM μ).N,
      (HonestBoxFam v h fc fu HM μ).E.hatChi (-k) = (HonestBoxFam v h fc fu HM μ).E.hatChi k)

end Work.BoseBoxFock
