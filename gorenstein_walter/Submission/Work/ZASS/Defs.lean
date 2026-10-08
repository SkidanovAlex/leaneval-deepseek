/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area ZASS: Zassenhaus groups of degree `q + 1` are `PSL(2, q)`

Vocabulary file of the area `ZASS` of the Gorenstein–Walter project.  The area implements the
recognition step of the blueprint: a group `G` acting faithfully and 2-transitively on `q + 1`
points, in which every nonidentity element fixes at most two points and the pointwise
stabilizer of two points has order `(q - 1)/2` (`q = p ^ k`, `p` an odd prime, `q ≥ 5`), is
isomorphic to `PSL(2, GaloisField p k)`.

## Contracts

* `Work.GW2.ZassHyps`, `Work.GW2.ZassOddProp`: the original contract, copied verbatim from
  `Submission/Work/_design_gw/Contracts2.lean` (namespace `GW2`).
* `Work.GW2.ZassHyps2`, `Work.GW2.ZassOdd2Prop`, `Work.GW2.Inverts`,
  `Work.GW2.ZassInvolutionSwapProp`, `Work.GW2.ZassInvertProp`: the amended contracts of
  design pass 2 (`Submission/Work/NOTES_LEAD_gw_design2.md`, §13/§14 and `_design_gw/Core2.lean`
  §A/§H), copied verbatim.  The area's deliverable is `ZassOdd2Prop`: the cyclicity clause of
  `ZassHyps` is dropped, because HB III XI 1.5/1.11 prove cyclicity (`ZassInvertProp`), and
  `ZassOddProp` follows from `ZassOdd2Prop` trivially.
* `Work.GW2.ZassWeylProp`: step Z6 as a single proposition, namely that the action of `G` on
  `X` is equivalent to the standard action of `PSL(2, GaloisField p k)` on the projective line
  `. This is the statement proved by the Z6 leaf Props and the coordinate step; from it the
  cardinality computation Z1–Z4 finishes `ZassOdd2Prop` (`Work.ZASS.zassOdd2_of_weyl`).

## Local vocabulary

In `Work.ZASS`: the conjugation predicates `FixedPointFreeConj`, `IsConjInvariant`, the
element `conjBy h u = h * u * h⁻¹`, the direct decomposition `IsDirectDecomp`, and the API
lemma `mem_conjBy_of_subgroupOf_normal` (if `U ⊴ B` and `U ≤ B`, then `b ∈ B` conjugates `U`
into itself).  The points and subgroups of the area are those of
`Submission/Work/Zassenhaus/Basic.lean`: `borel G inf = G_∞`, `pairStab G inf x = G_{∞x}`,
`fixesOnly G inf`, `fixesSome G inf`.
-/
import Mathlib
import Submission.Work.Zassenhaus.Basic
import Submission.Work.Zassenhaus.zass_coprime_pow_half
import Submission.Work.PSL2.Basic
import Submission.Work.PSL2.Card
import Submission.Work.ASM.Defs
import Submission.Work.BSW.Defs

open scoped MatrixGroups LinearAlgebra.Projectivization

namespace Work.GW2

/-! ## The original contract (`Contracts2.lean`) -/


/-! ## The amended contract (`Core2.lean`, design pass 2) -/


/-- HB 1.7(a)/(c): some involution interchanges two given points.

Copied verbatim from `Submission/Work/_design_gw/Core2.lean` (`GW2.ZassInvolutionSwapProp`). -/
def ZassInvolutionSwapProp : Prop :=
  ∀ (G X : Type) [Group G] [Finite G] [MulAction G X] [Finite X] (q : ℕ),
    Odd q → ZassHyps2 G X q → ∀ a b : X, a ≠ b → ∃ s : G, orderOf s = 2 ∧ s • a = b ∧ s • b = a

/-- HB 1.5 (`d` odd) and the proof of 1.11 (`d` even): an element interchanging the two fixed
points of `H = G_{a,b}` inverts `H`, and `H` is cyclic.

Copied verbatim from `Submission/Work/_design_gw/Core2.lean` (`GW2.ZassInvertProp`). -/
def ZassInvertProp : Prop :=
  ∀ (G X : Type) [Group G] [Finite G] [MulAction G X] [Finite X] (q : ℕ),
    Odd q → 5 ≤ q → IsSimpleGroup G → ZassHyps2 G X q → ∀ a b : X, a ≠ b →
      IsCyclic (MulAction.stabilizer G a ⊓ MulAction.stabilizer G b : Subgroup G) ∧
      ∀ s : G, s • a = b → s • b = a →
        Inverts s (MulAction.stabilizer G a ⊓ MulAction.stabilizer G b)

/-! ## Step Z6 as a single proposition -/

/-- **Step Z6** of the blueprint (design pass 2, §13): the action of `G` on `X` is
*equivalent*, as a permutation action, to the standard action of `PSL(2, GaloisField p k)` on
the projective line `ℙ¹(GaloisField p k)`.

Z6.1–Z6.4 (HB III XI 1.5, 1.7–1.11, the leaf Props `ZassInvolutionSwapProp` and
`ZassInvertProp`) identify `U = K` with a field of order `q` on which the point stabilizer
acts by multiplication; Z6.5 (HB 1.12) then shows that the remaining generator acts as
`x ↦ -1/x`, so that `G` acts inside `PSL(2,K)` on `ℙ¹(K)`.

The theorem `Work.ZASS.zassOdd2_of_weyl` deduces `ZassOdd2Prop` from this Prop plus the
cardinality computation of Z1–Z4 (`Work.ZASS.card_G` and `Work.PSL2.card_PSL2_galoisField`):
`Φ` is a bijection and the action is faithful, so `Ψ` is injective, and the two orders agree. -/
def ZassWeylProp : Prop :=
  ∀ (G X : Type) [Group G] [Finite G] [MulAction G X] [Finite X] (p k : ℕ) [Fact p.Prime],
    Odd p → 5 ≤ p ^ k → IsSimpleGroup G → ZassHyps2 G X (p ^ k) →
    ∃ (Φ : X ≃ ℙ (GaloisField p k) (Fin 2 → GaloisField p k))
      (Ψ : G →* PSL(2, GaloisField p k)),
      ∀ (g : G) (x : X), Φ (g • x) = Ψ g • Φ x

end Work.GW2

namespace Work.ZASS

open Work.Zassenhaus

section Vocabulary

variable {G : Type*} [Group G]

/-- The conjugate `h * u * h⁻¹` of `u` by `h`, the image of `u` under the conjugation action
of `H` on a subgroup `U` normalized by `H`. -/
def conjBy (h u : G) : G := h * u * h⁻¹

@[simp] theorem conjBy_one_left (u : G) : conjBy 1 u = u := by simp [conjBy]
@[simp] theorem conjBy_one_right (h : G) : conjBy h 1 = 1 := by simp [conjBy]

theorem conjBy_mem_of_le {U H : Subgroup G} (hUH : U ≤ H) {h : G} (hh : h ∈ H) {u : G}
    (hu : u ∈ U) : conjBy h u ∈ H :=
  H.mul_mem (H.mul_mem hh (hUH hu)) (H.inv_mem hh)

/-- `H` acts *fixed-point-freely* on `U` by conjugation: no nonidentity element of `H`
centralizes a nonidentity element of `U`.  This is Z3 of the blueprint. -/
def FixedPointFreeConj (U H : Subgroup G) : Prop :=
  ∀ h ∈ H, h ≠ 1 → ∀ u ∈ U, conjBy h u = u → u = 1

/-- `W` is invariant under conjugation by `H`. -/
def IsConjInvariant (H W : Subgroup G) : Prop :=
  ∀ h ∈ H, ∀ w ∈ W, conjBy h w ∈ W

/-- `K = A · C` with `A ⊓ C = ⊥`: `K` is the internal direct product of `A` and `C` (the
commutativity is supplied separately where it is needed). -/
def IsDirectDecomp (K A C : Subgroup G) : Prop := A ⊔ C = K ∧ A ⊓ C = ⊥

section Normal

variable {B U : Subgroup G}

/-- If `U ⊴ B` and `U ≤ B`, then `B` normalizes `U` elementwise. -/
theorem mem_conjBy_of_subgroupOf_normal (hUB : U ≤ B) (hN : (U.subgroupOf B).Normal)
    {h : G} (hh : h ∈ B) {u : G} (hu : u ∈ U) : conjBy h u ∈ U :=
  (Subgroup.normal_subgroupOf_iff hUB).mp hN u h hu hh

/-- Elementwise form of `(U.subgroupOf B).Normal`. -/
theorem subgroupOf_normal_of_mem_conjBy (hUB : U ≤ B)
    (h : ∀ g ∈ B, ∀ u ∈ U, conjBy g u ∈ U) : (U.subgroupOf B).Normal :=
  (Subgroup.normal_subgroupOf_iff hUB).mpr fun u g hu hg => h g hg u hu

end Normal

end Vocabulary

end Work.ZASS
