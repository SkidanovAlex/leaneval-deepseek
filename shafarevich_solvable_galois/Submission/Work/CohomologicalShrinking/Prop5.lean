/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Proposition 5 of Schmidt–Wingberg, as a structured hypothesis

Schmidt–Wingberg (arXiv:math/9809211, §2) prove

> **Proposition 5.** For every `τ = (i,j)` the `𝔽_p`-vector space homomorphism
> `φ_τ : (P/P^2)^{⊗j} → P_{(i,j)}/P_{(i,j)+1}`,
> `x₁ ⊗ ⋯ ⊗ x_j ↦ ([x₁,[x₂,[…,x_j]]])^{p^{i-j}} mod P_{(i,j)+1}`
> is well-defined and surjective.

and observe that, for `P = F(d)` (the free `G`-operator group of rank `d`), the map is
`G`-invariant and natural in `d`.

Note that `Prop5Data` is *weaker* than Proposition 5 in one respect and *stronger* in none:
it does not require `θ_τ(d)` to be the paper's specific commutator map
`x₁ ⊗ ⋯ ⊗ x_j ↦ ([x₁,[x₂,[…,x_j]]])^{p^{i-j}}`, only that *some* `G`-equivariant surjection exists
with the naturality of the family.  Every property that `Prop5Data` demands of `θ_τ` is a property
that the paper's map has, so Proposition 5 implies `Prop5Data` (i.e. `Prop5Data` is the exact
extraction of Proposition 5 used by the shrinking procedure).  The converse is not needed.

The proof of Proposition 5 is the only place in §2 of the paper where the commutator calculus
of **Lemma 4** — `(xy)^a ≡ x^a y^a (y,x)^{a(a-1)/2}` modulo higher `p`-central terms and
`[x^a,y] ≡ [x,y]^a [[x,y],x]^{a(a-1)/2}`, together with the Hall–Petrescu type structure
statement `F_i ∩ F^j = (F^j)^{p^{i-j}} … F^i` for a free `p`-group — is used.  That calculus is
*not* formalized here (see `NOTES.md` for the precise statement of what is missing); instead the
whole of Proposition 5 is isolated as the named hypothesis `Prop5Data` below, and Propositions 6
and 7 are *derived* from it.

Nothing else in this chapter depends on unproved input.

## Main definitions

* `Work.CohomologicalShrinking.Prop5Data` : the data of Proposition 5 for one fixed pair
  `τ = (i,j)` — the maps `θ_τ(d)`, their `G`-equivariance, surjectivity and naturality in `d`.

The case `τ = (1,1)` of the hypothesis is trivially satisfied: then
`F(d)_{(1,1)}/F(d)_{(1,2)} = F(d)/F(d)^2`, so that `θ` may be taken to be the canonical
identification `(F(d)/F(d)^2)^{⊗1} ≅ F(d)/F(d)^2`.  Hence `Prop5Data` is not a vacuous
assumption.
-/

import Mathlib
import Submission.Work.CohomologicalShrinking.Defs
import Submission.Work.CohomologicalShrinking.Refined
import Submission.Work.CohomologicalShrinking.Functorial
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

attribute [local instance] Classical.decEq

namespace Work.CohomologicalShrinking

set_option maxHeartbeats 800000

open scoped TensorProduct

universe u v w

variable {p : ℕ}

/-- **Proposition 5 of Schmidt–Wingberg, as structured data for a fixed `τ = (i,j)`.**

For every rank `d` we are given the canonical `G`-equivariant `𝔽_p`-linear surjection
`θ_τ(d) : (F(d)/F(d)^2)^{⊗j} ↠ E(d,τ)` of the paper, together with the naturality of this
family in `d` along surjective `G`-operator homomorphisms `F(m) → F(n)`:
`θ_τ(n) ∘ (ψ̄^{⊗j}) = ψ_* ∘ θ_τ(m)`.

(Only surjective operator homomorphisms occur in the shrinking procedure; the naturality is
therefore stated for those.) -/
structure Prop5Data (p : ℕ) [NeZero p] (G : Type*) [Group G] (i j : ℕ) where
  /-- The map `θ_τ(d) : (F(d)/F(d)^2)^{⊗j} → E(d,τ)`. -/
  θ : ∀ d : ℕ, (⨂[ZMod p]^j (squareQuotient p G d)) →ₗ[ZMod p] E p G d i j
  /-- `θ_τ(d)` is `G`-equivariant. -/
  θ_smul : ∀ (d : ℕ) (g : G) (x : ⨂[ZMod p]^j (squareQuotient p G d)),
    θ d (g • x) = g • θ d x
  /-- `θ_τ(d)` is surjective. -/
  θ_surjective : ∀ d : ℕ, Function.Surjective (θ d)
  /-- Naturality of `θ_τ` in the rank: for a surjective `G`-operator homomorphism
  `ψ : F(m) → F(n)` the square
  `θ_τ(n) ∘ (ψ̄^{⊗j}) = ψ_* ∘ θ_τ(m)` commutes. -/
  θ_natural : ∀ ⦃m n : ℕ⦄
      (ψ : Work.Shrinking.freeOperatorGroup G m →* Work.Shrinking.freeOperatorGroup G n)
      (hψ : Function.Surjective ψ)
      (hψG : ∀ (g : G) (y : Work.Shrinking.freeOperatorGroup G m), ψ (g • y) = g • ψ y),
    (θ n).comp (PiTensorProduct.map (fun _ : Fin j => quotMapLin p G ψ hψ))
      = (gradedMapLin p ψ hψ i j).comp (θ m)

end Work.CohomologicalShrinking
