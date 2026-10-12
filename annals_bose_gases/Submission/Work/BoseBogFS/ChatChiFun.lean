import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB7AK.W1low.chat_sub_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.ChatChiFun` — `chat (χ_ℓ) = ℓ³ χ̂(ℓ • ·)` (local copy)

The two χ-rows the chapter's µ-layer needs (`hatChi_decay_uniform`), proved here directly from
the `chat`-cosine identity (`Work.BoseB7AK.W1low.chat_eq_integral_cos`) and the scaling lemma
(`Work.BoseB4.BoxData.integral_chiLam_mul_cos`) — exactly as `Work.BoseGateFS.ChiPin` does, but
**without importing that module**: `ChiPin` imports `BoseGateFS.GateHonest`, which sits in the
chapter's import cone; keeping this small local copy makes
`import Submission.Work.BoseBogFS.All` independent of the gate files of the sibling areas.

The result is the identity that makes `E.hatChi k = corpusBox.hatChi (ℓ • kmom k)` provable at
the honest environment, whose `hatChi` is the *normalised* `chat (χ_ℓ)` with normaliser
`chat (χ_ℓ²)(0) = ℓ³`.
-/

noncomputable section

open scoped BigOperators Pointwise

open MeasureTheory

namespace Work.BoseBogFS

open Work.BoseB7 Work.BoseB7A
open Work.BoseFixR Work.BoseBoxFix Work.UBB
open _root_.BoseGases Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `χ_ℓ` is integrable. -/
lemma integrable_chiFun (ℓ : ℝ) (hℓ : 0 < ℓ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin 3) => Work.BoseFixR.chiFun ℓ z) :=
  (Submission.BoseGases.chiScale_continuous ℓ).integrable_of_hasCompactSupport
    (Submission.BoseGases.chiScale_hasCompactSupport (ne_of_gt hℓ))

/-- The corpus `χ̂` at `ℓ • p` is the `chat`-transform of `χ_ℓ`, scaled by `ℓ³`. -/
theorem chat_chiFun_eq (ℓ : ℝ) (hℓ : 0 < ℓ) (p : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseFixR.chat (Work.BoseFixR.chiFun ℓ) p
      = ℓ ^ 3 * Work.BoseK15.corpusBox.hatChi (ℓ • p) := by
  rw [Work.BoseB7AK.W1low.chat_eq_integral_cos (integrable_chiFun ℓ hℓ) p]
  exact Work.BoseB4.BoxData.integral_chiLam_mul_cos Work.BoseK15.corpusBox hℓ p

end Work.BoseBogFS
