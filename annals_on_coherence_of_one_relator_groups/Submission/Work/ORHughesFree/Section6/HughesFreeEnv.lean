/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The rank-free Hughes-freeness hypothesis `IsHughesFreeEnv`

This is hypothesis **H3** of the lead's audit (`OR_REMAINING_LEAD.md`, §3.1).  It replaces the
`IsHughesFreeRank` hypothesis of [JZLA20, Theorem 6.1] in the construction of the induction
environment `Thm61Step`.

## Why `IsHughesFreeRank` is replaced

`IsHughesFreeRank` (in `ORHughesFree/HughesFree.lean`) quantifies over *all* ring isomorphisms
`SkewMonoidAlgebra (MonoidAlgebra K N) (Multiplicative ℤ) ≃+* MonoidAlgebra K H` and all
`ℤ`-actions, does not require `N ⊴ H` or that `H/N` be infinite cyclic, and states the
natural-extension condition over the non-regular ring `K[N]` (where
`NaturalExtension.naturalExtension_unique` does not apply).  It is therefore strictly stronger
than the paper's hypothesis (there called (cond)), and it is not available for `U(G)`.

With a *faithful* rank function on a von Neumann regular ring, "the rank of the matrix `I + A t`
is `n`" is equivalent to "`I + A t` is invertible".  `IsHughesFreeEnv` records the latter
directly: for every finitely generated `H ≤ G` with `H = N ⋊ ⟨t⟩`, every matrix `A` over the
`∗`-regular closure `U_N = U_N(φ, H, N)` of `φ(K[N])` in `U` gives an invertible `I + A·φ(t)`.

This is exactly the form in which [JZLA20, Proposition 3.11] (Jaikin's survey, Corollary 12.2)
supplies the analytic input for `U(G)`, and it is what Step C of the construction of `Thm61Step`
consumes: it shows that `rkU ∘ θ` (where `θ : U_N[t^{±1};τ] →+* U` is the evaluation) satisfies
the second clause of `IsNaturalExtension`, so that `rkU ∘ θ = rkP ∘ f_ω` by
`NaturalExtension.naturalExtension_unique`.
-/
import Mathlib
import Submission.Work.ORHughesFree.HughesFree
import Submission.Work.Section6.StepA

set_option autoImplicit false

namespace Work.ORHughesFree

open Work.ORHughesFree

/-- **The `∗`-compatibility of `φ`.**  `φ` carries the group-like units of `K[G]` to the inverse
of the image of their inverses, i.e. `star (φ g) = φ g⁻¹`.  This is the part of "`U` is a positive
definite `∗`-regular `K[G]`-ring" that the twist `τ` of [JZLA20, Theorem 6.1] uses: it makes the
inner automorphism `x ↦ φ(t) x φ(t)⁻¹` a `∗`-automorphism. -/
def StarCompatible {K : Type} [Field K] {G : Type} [Group G] {U : Type} [Ring U]
    [StarRing U] (φ : MonoidAlgebra K G →+* U) : Prop :=
  ∀ g : G, star (φ (MonoidAlgebra.single g 1)) = φ (MonoidAlgebra.single g⁻¹ 1)

/-- **Hypothesis H3 of the lead's audit**: the rank-free form of Hughes-freeness of an epic
`K[G]`-ring `(U, φ)`.

For every finitely generated non-trivial `H ≤ G`, every normal `N ⊴ H` with `H = N ⋊ ⟨t⟩`
(`decomp`) and `t^k ∉ N` for `k ≠ 0` (`htinf`), and every matrix `A` over the `∗`-regular closure
`U_N ⊆ U` of the image of `K[N]`, the matrix `1 + A·φ(t)` is invertible.

`φ` here is `MonoidAlgebra K G →+* U`; the inclusion `K[H] → K[G]` is `inducedMapRing H` and the
inclusion `K[N] → K[H]` is `MonoidAlgebra.mapDomainRingHom K N.subtype`, so
`U_N = Work.Section6.UNty φ H N`. -/
def IsHughesFreeEnv {K : Type} [Field K] {G : Type} [Group G] {U : Type} [Ring U]
    [StarRing U] [IsStarRegular U] (φ : MonoidAlgebra K G →+* U) : Prop :=
  ∀ (H : Subgroup G), H.FG → H ≠ ⊥ → ∀ (N : Subgroup H), N.Normal → ∀ t : H,
    (∀ h : H, ∃ (n : N) (k : ℤ), h = (n : H) * t ^ k) →
    (∀ k : ℤ, t ^ k ∈ N → k = 0) →
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) (Work.Section6.UNty φ H N)),
      IsUnit (1 + A.map Subtype.val *
        Matrix.scalar (Fin n) ((φ.comp (inducedMapRing (K := K) H))
          (MonoidAlgebra.single t (1 : K))))

end Work.ORHughesFree
