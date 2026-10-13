/-
# `Work.FTS.Apriori.Limit.Defs` — the vocabulary of the lower-semicontinuity of `|·|_{ℋ⁴}`

This module sets up the notions used by `HkNorm_le_of_tendstoLocUnif`
(`Submission/Work/FTS/Apriori/Limit/HkNorm_le_of_tendstoLocUnif.lean`), the lower
semicontinuity of the `ℋ⁴`-norm under locally uniform convergence on the open quadrant
`Qd = (0,∞) × (0,π/2)`.

The `ℋ⁴`-integrand is a sum of squares of *weighted slot derivatives*
`mixed j i f · ρ`, where `ρ = w/sin(2θ)^{η/2}` for the pure `D_z`-slots (`i = 0`) and
`ρ = Wt α` for the mixed slots (`i ≥ 1`).  The lemmas in the companion modules are all
phrased in terms of the following notions:

* `slotWeight`, `slot` — the weight and the weighted slot `mixed j i f · slotWeight`;
* `activeSlots` — the finite set of slots appearing in `HkIntegrand α 4`;
* `TestQ` — the test functions `C_c^∞(Qd)` (smooth on the strip `(-1,∞) × (0,π/2)`, with
  compact support contained in the open quadrant);
* `adjZ`, `adjTh`, `adjDzIter`, `adjDthIter`, `adjMixed` — the formal adjoints of
  `D_z = z ∂_z`, `D_θ = sin(2θ) ∂_θ` and of `mixed j i = D_z^j D_θ^i` for the pairing
  `∫∫ (D g) ψ = ∫∫ g (D^* ψ)`;
* `HksqCut`, `Qμ` — the cut-off `ℋ⁴`-energy `∫∫ HkIntegrand α 4 f · η` and the product
  measure `dz dθ` restricted to the closed quadrant

  `Qμ = (volume.restrict Iz).prod (volume.restrict Iθ)`.

No mathematical content is proved here: the definitions are the shared interface of the
chapter.  Everything is stated with the fixed vocabulary of `Submission/Work/Spaces/Defs`
and `Submission/Work/FTS/LocData/Defs`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.LocData.SmoothChain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.Apriori.Limit

set_option autoImplicit false

open Work.FTS.LocData (SmoothQuad)

/-- The open quadrant `(0,∞) × (0,π/2)` of the self-similar variables (definitionally the
same set as `Work.Construction.Qd` and `Work.FTS.LocData.Qd`). -/
abbrev Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

/-- The weight of the slot `ji = (j,i)`: the pure `D_z`-slots (`i = 0`) carry
`w(z)/sin(2θ)^{η/2}` and the mixed slots (`i ≥ 1`) carry `Wt α = w(z)·sin(2θ)^{-γ/2}`. -/
def slotWeight (α : ℝ) (ji : ℕ × ℕ) (z θ : ℝ) : ℝ :=
  if ji.2 = 0 then Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
  else Work.Spaces.Wt α z θ

/-- The weighted slot `mixed j i f · slotWeight α (j,i)`. -/
def slot (α : ℝ) (ji : ℕ × ℕ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.Spaces.mixed ji.1 ji.2 f z θ * slotWeight α ji z θ

/-- The active slots of the `ℋ⁴`-norm: `(j,0)` with `j ≤ 4` (the pure `D_z`-slots) together
with `(j,i)` with `1 ≤ i` and `i + j ≤ 4` (the mixed slots with at least one `D_θ`). -/
def activeSlots : Finset (ℕ × ℕ) :=
  ((Finset.range 5) ×ˢ (Finset.range 5)).filter
    (fun ji => ji.2 = 0 ∨ (1 ≤ ji.2 ∧ ji.1 + ji.2 ≤ 4))

/-- The test functions of the pairing: `ψ` is smooth on the open quadrant
`(0,∞) × (0,π/2)` (the genuine `C^∞`-order `Work.Stability.smoothOrder`, as in
`SmoothQuad`, but only on the quadrant, where the weights are smooth) and has compact
support contained in it. -/
def TestQ (ψ : ℝ → ℝ → ℝ) : Prop :=
  ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry ψ) Qd ∧
    HasCompactSupport (Function.uncurry ψ) ∧ tsupport (Function.uncurry ψ) ⊆ Qd

/-- The formal adjoint of `D_z = z ∂_z`: `φ ↦ -∂_z(z φ)`. -/
def adjZ (φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -deriv (fun z' => z' * φ z' θ) z

/-- The formal adjoint of `D_θ = sin(2θ) ∂_θ`: `φ ↦ -∂_θ(sin(2θ) φ)`. -/
def adjTh (φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -deriv (fun θ' => Real.sin (2 * θ') * φ z θ') θ

/-- The `j`-fold adjoint of `D_z^j`, `(D_z^j)^* = ((D_z)^*)^j`. -/
def adjDzIter : ℕ → (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ)
  | 0, φ => φ
  | n + 1, φ => adjDzIter n (adjZ φ)

/-- The `i`-fold adjoint of `D_θ^i`, `(D_θ^i)^* = ((D_θ)^*)^i`. -/
def adjDthIter : ℕ → (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ)
  | 0, φ => φ
  | n + 1, φ => adjDthIter n (adjTh φ)

/-- The adjoint of `mixed j i = D_z^j ∘ D_θ^i`: `(D_z^j D_θ^i)^* = (D_θ^i)^* (D_z^j)^*`. -/
def adjMixed (ji : ℕ × ℕ) (φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  adjDthIter ji.2 (adjDzIter ji.1 φ)

/-- The product measure `dz dθ` restricted to the closed quadrant
`[0,∞) × [0,π/2]`, i.e. `(volume.restrict Iz).prod (volume.restrict Iθ)`. -/
def Qμ : Measure (ℝ × ℝ) :=
  (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)

/-- The cut-off `ℋ⁴`-energy: `∫∫ HkIntegrand α 4 f · η` over the closed quadrant, i.e. the
`L¹`-norm of the `ℋ⁴`-integrand of `f` against the cut-off `η` with respect to the product
measure `Qμ = dz dθ` on `Iz ×ˢ Iθ`. -/
def HksqCut (α : ℝ) (f η : ℝ → ℝ → ℝ) : ℝ :=
  ∫ p, Work.Spaces.HkIntegrand α 4 f p.1 p.2 * η p.1 p.2 ∂Qμ

end Work.FTS.Apriori.Limit
