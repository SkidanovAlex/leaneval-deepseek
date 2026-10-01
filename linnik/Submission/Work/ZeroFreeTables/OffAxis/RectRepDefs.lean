/-
# ZeroFreeTables/OffAxis/RectRepDefs

Vocabulary shared by the pieces of the **repeated-zero `P₃` engine at rectangle height `H`**
(`OffAxis/RectP3RepEngineH`, HB Lemma 9.1 at a multiple zero): the wide form of HB Lemma 3.1's
log-derivative input, and the two elementary consequences of `IsMinWideAt` that the case lemmas
use.

## Why a *wide* input is needed

HB's §9 diagonal argument at a multiple zero `ρ₁` (`γ = Im ρ₁`, `L = log q`) runs the four points
`σ`, `σ+iγ`, `σ+2iγ`, `σ+3iγ` (`σ = 1 + a/L`), whose heights are `≤ 3H` — while the hypothesis
available is only `H ≤ log q`.  Hence the single-point `P₃` master bound must be available on the
whole range `|Im s| ≤ 10 log q` in which the proved `LinnikAreas.l31free.lemma3_1_free_gen`
(which is phrased with the divisor of the *primitive* completed `L`-function) supplies
`LogDerivHyp`.  `WideLogDerivHyp` is that hypothesis, with `InvNearSum` (`P3.DefsL`) as the
near-zero sum so that it can be fed to the `P₃` master bound verbatim.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.WideDefs
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.HB94.Lam0GeEngine

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.OffAxis

/-- **HB Lemma 3.1's input at heights up to `10 log q`.**  For a primitive non-principal `χ` and
`L ≥ log N`, the log-derivative of `L(·,χ)` at every point of the strip
`1 + 1/(L log L) ≤ Re s ≤ 1 + log L/L` with `|Im s| ≤ 10 L` satisfies
`-Re (L'/L)(s) + Σ_{near} Re (1/(s-u)) ≤ c L`, the near sum being taken over the zeros of the
completed `L`-function within `δ` of `1 + i Im s` (HB Lemma 3.1 with `φ = 1/3` gives
`c = 1/6 + ε`, `LinnikAreas.l31free.lemma3_1_free_gen`). -/
def WideLogDerivHyp {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (δ L c : ℝ) : Prop :=
  ∀ s : ℂ, 1 + 1 / (L * Real.log L) ≤ s.re → s.re ≤ 1 + Real.log L / L → |s.im| ≤ 10 * L →
    (-logDeriv (DirichletCharacter.LFunction χ) s).re
      + Work.ZeroFreeTables.InvNearSum N χ s δ ≤ c * L

/-! ## The three consequences of `IsMinWideAt` used by the case lemmas -/

/-- The character of a wide-minimal pair is non-principal. -/
theorem IsMinWideAt.ne_one {q : ℕ} [NeZero q] {H W : ℝ} {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (h : IsMinWideAt H W χ₁ ρ₁) : χ₁ ≠ 1 := h.1

/-- `λ(ρ₁) ≥ 0` for the zero of a wide-minimal pair. -/
theorem IsMinWideAt.lam_nonneg {q : ℕ} [NeZero q] {H W : ℝ} {χ₁ : DirichletCharacter ℂ q}
    {ρ₁ : ℂ} (h : IsMinWideAt H W χ₁ ρ₁) : 0 ≤ Work.LinnikContract.lamOf q ρ₁ :=
  Work.ZeroFreeTables.HB94.Lam0GeEngine.lamOf_nonneg_of_zeroMult h.2.1

/-- The wide minimality of `λ₁`, in the form used to drop near sums: a non-principal zero of
height `≤ W` has `λ(u) ≥ λ₁`. -/
theorem IsMinWideAt.lam_le {q : ℕ} [NeZero q] {H W : ℝ} {χ₁ : DirichletCharacter ℂ q}
    {ρ₁ : ℂ} (h : IsMinWideAt H W χ₁ ρ₁) (χ : DirichletCharacter ℂ q) (u : ℂ)
    (hχ : χ ≠ 1) (hzm : Work.LinnikContract.zeroMult χ u ≠ 0) (him : |u.im| ≤ W) :
    Work.LinnikContract.lamOf q ρ₁ ≤ Work.LinnikContract.lamOf q u :=
  h.2.2.2 χ u hχ hzm him

end Work.ZeroFreeTables.OffAxis
