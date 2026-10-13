/-
# `ApproxCC` — the `C^4`-approximation of a compactly supported profile by the family `famE`

This directory contains the proof of

`Work.FTS.GalBasis.exists_famE_hk_approx_cc`:
for `g` of class `CcOn 9` (compactly supported, `C^9`, supported strictly inside the open
quadrant) and every `ε > 0` there is a *finite* linear combination of the explicit family
`famE` of `Defs.lean`, with every index a *good* one (so that `Ccφ (famE (idx k))`), which
approximates `g` in the weighted `ℋ⁴`-norm up to `ε`.

## The plan

1. `ApproxCC/polyApproxC4.lean` — one-dimensional Weierstrass-with-derivatives: a `C^4`
   function on `[a,b]` is approximable, together with its derivatives up to order `4`, by a
   polynomial (delegated).
2. `ApproxCC/ThetaTaylor.lean` — the order-`4` Taylor estimate in the angular variable, with
   `z`-derivatives (delegated).
3. `ApproxCC/mixedMul.lean` — the Leibniz rule for the operators `D_z^a D_θ^b` on products of
   `C^5` functions (delegated).
4. `ApproxCC/Basic.lean` — the partition of unity of the family in the angular variable, the
   derivative bounds for the family bumps, and the `Ccφ`-membership of the good indices.
5. `exists_famE_hk_approx_cc.lean` — the construction and the assembly.

This file fixes the two *interface* definitions (`plainMixed`, `thTaylor`) in terms of which
the delegated estimates are stated.
-/
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.GalBasis.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.ApproxCC

set_option autoImplicit false

/-- **The plain mixed derivative** `∂_z^a ∂_θ^b g`, in the arrangement "the `θ`-derivative is
taken on the `z`-slice, and the `z`-derivative is taken afterwards":
`plainMixed a b g z θ = ∂_z^a (z' ↦ ∂_θ^b (θ' ↦ g z' θ') θ) (z)`.

Note that this is *not* the same expression as the `D`-operator iterate `Work.Spaces.mixed`,
but the two are related by the bounded-coefficient expansions `D_z^a = Σ c_i(z) ∂_z^i` and
`D_θ^b = Σ d_j(θ) ∂_θ^j` valid on a box `[A,B] × [C,D]` with `0 < A` (see
`ApproxCC/Basic.lean`). -/
def plainMixed (a b : ℕ) (g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => iteratedDeriv a (fun z' => iteratedDeriv b (fun θ' => g z' θ') θ) z

@[simp] theorem plainMixed_zero_left (b : ℕ) (g : ℝ → ℝ → ℝ) :
    plainMixed 0 b g = fun z θ => iteratedDeriv b (fun θ' => g z θ') θ := rfl

@[simp] theorem plainMixed_zero_right (a : ℕ) (g : ℝ → ℝ → ℝ) :
    plainMixed a 0 g = fun z θ => iteratedDeriv a (fun z' => g z' θ) z := by
  funext z θ
  simp [plainMixed]

theorem plainMixed_apply (a b : ℕ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    plainMixed a b g z θ = iteratedDeriv a (fun z' => iteratedDeriv b (fun θ' => g z' θ') θ) z :=
  rfl

/-- **The order-`4` angular Taylor polynomial** of `g` at the angle `θj`: the polynomial
`Σ_{b ≤ 4} (θ - θj)^b / b! · ∂_θ^b g(z, θj)`, whose coefficients are functions of `z`. -/
def thTaylor (g : ℝ → ℝ → ℝ) (θj : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => ∑ b ∈ Finset.range 5, (θ - θj) ^ b * ((b.factorial : ℝ)⁻¹) *
    iteratedDeriv b (fun θ' => g z θ') θj

theorem thTaylor_apply (g : ℝ → ℝ → ℝ) (θj z θ : ℝ) :
    thTaylor g θj z θ = ∑ b ∈ Finset.range 5, (θ - θj) ^ b * ((b.factorial : ℝ)⁻¹) *
      iteratedDeriv b (fun θ' => g z θ') θj := rfl

end Work.FTS.GalBasis.ApproxCC
