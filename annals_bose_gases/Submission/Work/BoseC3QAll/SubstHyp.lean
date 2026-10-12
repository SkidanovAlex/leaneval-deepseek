import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Real.Basic
import Submission.Work.BoseC3QAll.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseC3QAll.SubstHyp` — the algebra-only hypotheses of the substitution

FS `lem:EstimatesOnQ3-js` rewrites `Q₃` in the squeezed modes
`b_k = a_k + α_k a_{−k}†` via `a_k = (1−α_k²)⁻¹(b_k − α_k b_{−k}†)`.  That step
is pure algebra; the *only* inputs are

* FS `eq:Commutator_general`, which makes `[b_{s−k},b_{−k}†]` a scalar and
  identifies the two squeezed commutators;
* the parities of `χ̂`, `χ̂²` and `α`;
* the non-vanishing of the substitution denominators `1−α_k²`, `1−α_{s−k}²` on
  the pairs `(s,k)` that occur.

## The guard `Ŵ₁ k ≠ 0`

The corrected gate `C3Q.Q3KernelFSAll` has its two label rows guarded by
`Ŵ₁ k ≠ 0` (F1): the pairs `(s−k,−k)` and `(k,k−s)` of the squeezed commutator
are `NoWrap` only when `Ŵ₁ k ≠ 0`, and `s − k` lands in `P_H^q` only then too.
So every field of `SubstHypG` that is read at a high index `k` carries that same
guard.  This costs nothing in §10: every `(s,k)` summand of the chapter carries
the factor `Ŵ₁(k)`, so the unguarded cases are exactly those where the summand
vanishes identically (the graded proofs branch on `Ŵ₁ k = 0` and close by
`zero_mul`/`zero_smul`).
-/

noncomputable section

open scoped BigOperators


namespace Work.BoseC3QAll

open Work.BoseB7

set_option linter.unusedVariables false

/-- The algebra-only hypotheses of the Bogoliubov substitution
`a_k = (1−α_k²)⁻¹(b_k − α_k b_{−k}†)`: FS's commutator kernel at the six pairs
§10 uses, the parities, and the non-vanishing of the denominators on the pairs
used.  The high index `k` of every row carries the gate's guard `Ŵ₁ k ≠ 0`. -/
structure SubstHypG {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) : Prop where
  /-- `χ̂` is even. -/
  hatChi_even : ∀ s : Mode, E.hatChi (-s) = E.hatChi s
  /-- `χ̂²` is even. -/
  hatChiSq_even : ∀ s : Mode, E.hatChiSq (-s) = E.hatChiSq s
  /-- `α` is even (`α = ℬ/(𝒜+√(𝒜²−ℬ²))` with `𝒜, ℬ` even). -/
  alpha_even : ∀ k : Mode, E.alpha (-k) = E.alpha k
  /-- the substitution denominators do not vanish on the pairs used. -/
  denom_ne : ∀ s k : Mode, E.fL s ≠ 0 → k ∈ F.PHset E → E.W1 k ≠ 0 →
    1 - E.alpha k ^ 2 ≠ 0 ∧ 1 - E.alpha (s - k) ^ 2 ≠ 0
  /-- FS `eq:Commutator_general` at `(s−k, −k)`. -/
  kerA : ∀ s k : Mode, E.fL s ≠ 0 → k ∈ F.PHset E → E.W1 k ≠ 0 →
    F.ccrK (s - k) (-k) = E.hatChiSq s - E.hatChi k * E.hatChi (s - k)
  /-- FS `eq:Commutator_general` at the transpose `(-k, s−k)`. -/
  kerA' : ∀ s k : Mode, E.fL s ≠ 0 → k ∈ F.PHset E → E.W1 k ≠ 0 →
    F.ccrK (-k) (s - k) = E.hatChiSq s - E.hatChi k * E.hatChi (s - k)
  /-- FS `eq:Commutator_general` at `(k, k−s)`. -/
  kerB : ∀ s k : Mode, E.fL s ≠ 0 → k ∈ F.PHset E → E.W1 k ≠ 0 →
    F.ccrK k (k - s) = E.hatChiSq s - E.hatChi k * E.hatChi (s - k)
  /-- FS `eq:Commutator_general` at the transpose `(k−s, k)`. -/
  kerB' : ∀ s k : Mode, E.fL s ≠ 0 → k ∈ F.PHset E → E.W1 k ≠ 0 →
    F.ccrK (k - s) k = E.hatChiSq s - E.hatChi k * E.hatChi (s - k)
  /-- FS `eq:Commutator_general` at `(s−k, s'−k)`. -/
  kerC : ∀ s s' k : Mode, E.fL s ≠ 0 → E.fL s' ≠ 0 → k ∈ F.PHset E → E.W1 k ≠ 0 →
    F.ccrK (s - k) (s' - k)
      = E.hatChiSq (s - s') - E.hatChi (s - k) * E.hatChi (s' - k)
  /-- FS `eq:Commutator_general` at `(k−s, k−s')`. -/
  kerD : ∀ s s' k : Mode, E.fL s ≠ 0 → E.fL s' ≠ 0 → k ∈ F.PHset E → E.W1 k ≠ 0 →
    F.ccrK (k - s) (k - s')
      = E.hatChiSq (s - s') - E.hatChi (s - k) * E.hatChi (s' - k)
  /-- FS `eq:Commutator_general` at `(k−s', k−s)`. -/
  kerE : ∀ s s' k : Mode, E.fL s ≠ 0 → E.fL s' ≠ 0 → k ∈ F.PHset E → E.W1 k ≠ 0 →
    F.ccrK (k - s') (k - s)
      = E.hatChiSq (s - s') - E.hatChi (s - k) * E.hatChi (s' - k)

/-- **`SubstHypG` from the corrected kernel gate.**  The six kernel evaluations
are the guarded API of `C3Q.Defs`; the parities, and the non-vanishing of the
substitution denominators (which needs the smallness of `t`, through
`kernel_basic` and `PH_subset_PHq_sub`), are supplied by the caller. -/
theorem substHypG_of_kernel {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (hK : Q3KernelFSAll K₀ F T E) (hαeven : ∀ k : Mode, E.alpha (-k) = E.alpha k)
    (hden : ∀ s k : Mode, E.fL s ≠ 0 → k ∈ F.PHset E → E.W1 k ≠ 0 →
      1 - E.alpha k ^ 2 ≠ 0 ∧ 1 - E.alpha (s - k) ^ 2 ≠ 0) :
    SubstHypG F T E :=
  { hatChi_even := hK.hatChi_even
    hatChiSq_even := hK.hatChiSq_even
    alpha_even := hαeven
    denom_ne := hden
    kerA := kerA hK
    kerA' := kerA' hK
    kerB := kerB hK
    kerB' := kerB' hK
    kerC := kerC hK
    kerD := kerD hK
    kerE := kerE hK }

end Work.BoseC3QAll
