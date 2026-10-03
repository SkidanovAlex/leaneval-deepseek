/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The environment of the induction step of [JZLA20, Theorem 6.1]

[JZLA20, Theorem 6.1] is proved by induction on the `G`-complexity `Tree_G` of an element
`a ∈ D = D_{K[G],U}`.  The induction step replaces `a` by an element of `D_{H,U}` for a finitely
generated subgroup `H ≤ G` with `H = N ⋊ ⟨t⟩` (`H/N ≅ ℤ`), and then runs [JZLA20, Proposition 5.1]
in an ambient ring `P` which contains the skew Laurent series ring `D_{N,P}((t;τ))`, with
`D_{H,P}` isomorphic to `D_{H,U}` as a `K[H]`-ring.

`Thm61Step K G U φ H` packages exactly the data of that ambient ring that the induction consumes:

* `data : Prop51Data (Kˣ × H) P DN` — [JZLA20, Proposition 5.1] for the pair `(H, N)`;
* `e : D_{H,U} ≃+* data.DH` — the isomorphism of `K[H]`-rings (constructed by [JZLA20, Theorem 2.9]
  and [JZLA20, Lemma 4.4(2)]), which transfers invertibility and complexity;
* `e_Phi` — the compatibility of `e` with the universal morphisms `Φ` of the rational
  `Kˣ × H`-semirings ([JZLA20, §4.3]): `e ∘ Φ_{H,U} = Φ_{H,P}`.  This is *exactly* the statement
  that `e` is an isomorphism of `E ∗ H`-rings (both sides are morphisms of rational
  `Kˣ × H`-semirings which agree on the images of group elements), and it is what lets the
  induction transfer the realisers of `D_{H,U}` to realisers of `D_{H,P}` — in particular it is
  what `Prop51Mono` is applied to.
* `e_tree` (derived below, `Thm61Step.e_tree_local`) — the isomorphism identifies the `H`-complexity of
  `D_{H,P}` with `Tree_H` of `D_{H,U}` (an immediate consequence of `e_Phi`: the two are the
  minima of `Tree` over the corresponding realiser sets, which correspond bijectively).

The construction of `Thm61Step` (the ultraproduct ring `P = P^{U_N}_{ω,τ}` with its series
embedding, and the isomorphism `e`) is the "Step A + Step B" of the route design; the induction
below (`Section6.Thm61OfStep`) only uses the fields displayed here.
-/
import Mathlib
import Submission.Work.ORHughesFree.Prop51
import Submission.Work.ORHughesFree.Section6.SubgroupComplexity
import Submission.Work.ORHughesFree.HughesFree.exists_normal_cyclic_quotient

set_option autoImplicit false

namespace Work.ORHughesFree

/-- The environment of the induction step of [JZLA20, Theorem 6.1] for a finitely generated
subgroup `H ≤ G` with a fixed decomposition `H = N ⋊ ⟨t⟩`. -/
structure Thm61Step (K : Type) [Field K] (G : Type) [Group G] (U : Type) [Ring U]
    (φ : MonoidAlgebra K G →+* U) (H : Subgroup G) where
  /-- the normal subgroup `N ⊴ H` with `H/N ≅ ℤ` -/
  N : Subgroup H
  /-- `N` is normal -/
  N_normal : N.Normal
  /-- `N ≢ H`, i.e. `H/N ≅ ℤ` is non-trivial -/
  N_ne_top : N ≠ ⊤
  /-- a generator of `H/N` -/
  t : H
  /-- `H = N · ⟨t⟩` -/
  decomp : ∀ h : H, ∃ (n : N) (k : ℤ), h = (n : H) * t ^ k
  /-- the ambient ring `P` of [JZLA20, Theorem 6.1] -/
  P : Type
  /-- `P` is a ring -/
  [ringP : Ring P]
  /-- `D_{N,P} ⊆ P` -/
  DN : Subring P
  /-- the twist `τ` on `D_{N,P}`, given by conjugation by the image of `t` in `P` -/
  [smulDN : MulSemiringAction (Multiplicative ℤ) ↥DN]
  /-- the data of [JZLA20, Proposition 5.1] for the pair `(H, N)` -/
  data : Prop51Data (Kˣ × H) P DN
  /-- `data.N` is `Kˣ × N` -/
  data_N : data.N = unitsTimesSubgroup (K := K) (G := H) N
  /-- `data.t` is the image of the generator `t` of `H/N` -/
  data_t : data.t = (1, t)
  /-- the isomorphism `D_{H,U} ≃+* D_{H,P}` of `K[H]`-rings -/
  e : ↥(divisionClosure (Set.range (φ.comp (inducedMapRing (K := K) H)))) ≃+* ↥data.DH
  /-- the isomorphism intertwines the universal morphisms of the rational `Kˣ × H`-semirings
  `D_{H,U}` and `D_{H,P}` ([JZLA20, §4.3]); equivalently, `e` is an isomorphism of `E ∗ H`-rings
  with `e (φ_{H,U} x) = φ_{H,P} x` on `K[H]` and both sides morphisms of rational semirings. -/
  e_Phi : ∀ β : RatU (Kˣ × H),
    e ((Phi (φ.comp (inducedMapRing (K := K) H))) β) = ⟨data.Φ β, data.map_mem β⟩

namespace Thm61Step

variable {K : Type} [Field K] {G : Type} [Group G] {U : Type} [Ring U]
  {φ : MonoidAlgebra K G →+* U} {H : Subgroup G}

/-- **The isomorphism `e` identifies the two complexities.**  Since `e` intertwines the universal
morphisms `Φ_{H,U}` and `Φ_{H,P}` (`e_Phi`), it is a bijection between the realisers of `x` for
`treeG (φ ∘ K[↥H] ↪ K[G])` and those of `e x` for `data.treeH`, so the two minima agree.

This is stated with `P`, `DN`, `data` and `e` as explicit *variables* (rather than through the
projections of a `Thm61Step`): a `Ring step.P` instance field of a structure is not visible to
instance search from the projections of a local hypothesis, so the consumers of `Thm61Step` first
introduce `letI : Ring step.P := step.ringP` and then apply this lemma. -/
theorem e_tree_local {P : Type} [Ring P] {DN : Subring P}
    [MulSemiringAction (Multiplicative ℤ) ↥DN] {data : Prop51Data (Kˣ × H) P DN}
    {e : ↥(divisionClosure (Set.range (φ.comp (inducedMapRing (K := K) H)))) ≃+* ↥data.DH}
    (e_Phi : ∀ β : RatU (Kˣ × H),
      e ((Phi (φ.comp (inducedMapRing (K := K) H))) β) = ⟨data.Φ β, data.map_mem β⟩)
    (x : ↥(divisionClosure (Set.range (φ.comp (inducedMapRing (K := K) H))))) :
    data.treeH (e x) = treeG (φ.comp (inducedMapRing (K := K) H)) x := by
  refine Tree.le_antisymm ?_ ?_
  · obtain ⟨⟨α, hα, hαt⟩, -⟩ := treeG_spec (φ.comp (inducedMapRing (K := K) H)) x
    have heq : e x = ⟨data.Φ α, data.map_mem α⟩ := by
      rw [← hα, e_Phi α]
    have heq_val : ((e x : ↥data.DH) : P) = data.Φ α := by
      rw [heq]
    have h' : Tree.le (data.treeH (data.Φ α))
        (treeG (φ.comp (inducedMapRing (K := K) H)) x) := by
      rw [← hαt]
      exact data.treeH_le_treeOfRat α
    rw [heq_val]
    exact h'
  · obtain ⟨⟨β, hβ, hβt⟩, -⟩ := data.treeH_spec (e x) (e x).2
    have heq : e ((Phi (φ.comp (inducedMapRing (K := K) H))) β) = e x := by
      rw [e_Phi β]
      exact Subtype.ext hβ
    have hx : (Phi (φ.comp (inducedMapRing (K := K) H))) β = x := e.injective heq
    have hle := (treeG_spec (φ.comp (inducedMapRing (K := K) H)) x).2 β hx
    rw [hβt] at hle
    exact hle

end Thm61Step

end Work.ORHughesFree
