/-
Area CORE4 of the Gorenstein--Walter project: the `A₇` §4 structure fact of p. 226.

This file is the vocabulary module for the proof of `Work.CORE4.A7S4`
(`Submission/Work/CORE4/A7S4.lean`).  It contains the definitions (explicit permutations of
`Fin 7`, the two model four-groups `V₁`, `V₂` of `A₇`, element-level normaliser conditions and
explicit lists of order-`2` and order-`3` elements) on which the finite computation is run.

The §4 fact (Bender 1981, p. 226): in `A₇`, for a four-group `V ≤ S` (`S` a Sylow
`2`-subgroup) and an involution `s ∈ N_{A₇}(V)`, every subgroup `K ≤ N_{A₇}(V)` of order `3`
inverted by `s` has a *second* such companion `K' ≠ K`.

The four-groups of `A₇` fall into exactly two conjugacy classes, represented by

* `V₁ = ⟨t, u⟩ = {1, (01)(23), (02)(13), (03)(12)}` (the Klein four-group of the alternating
  group on `{0,1,2,3}`), and
* `V₂ = ⟨t, v⟩ = {1, (01)(23), (01)(45), (23)(45)}` (three `2`-cycles and a fixed point),

where `t = (01)(23)`, `u = (02)(13)`, `v = (01)(45)`.  The proof verifies the claim on the two
representatives by finite computation and transports it by conjugacy.

The finite computation is phrased over *elements*: normalising `V₁` is the decidable condition
`InN1 x` (`x` conjugates each of the three nontrivial elements of `V₁` into `V₁`), and the
elements of `N(V₁)` of order `2` resp. `3` are listed explicitly in `n1Inv` resp. `n1Ord3`.
Everything is checked by `decide` in the sibling modules.

The lists were computed with `GAP` (`Normalizer(AlternatingGroup(7), V)`); the permutations are
written as products of `Equiv.swap`s, and `Equiv.Perm (Fin 7)` composition is `(f * g) x = f (g x)`,
so the cycle `(a b c)` is `Equiv.swap a b * Equiv.swap b c`.

## How the finite checks are proved

The checks of this area (`n1Inv_mem`, `n1Ord3_mem`, `n2Inv_mem`, `n2Ord3_mem`, `n1Check`,
`n2Check`, `partnerConj`) are *closed decidable* statements about explicit permutations, so each is
proved by a single `decide`, for instance

    set_option maxRecDepth 100000 in
    set_option maxHeartbeats 0 in
    theorem n1Inv_mem : ∀ s : Equiv.Perm (Fin 7), N1InvCond s → s ∈ n1Inv := by decide

Both options are needed: reducing `Finset.univ` for `Equiv.Perm (Fin 7)` (`5040` elements) is deep
(so `maxRecDepth` must be raised well above the default) and slow (so `maxHeartbeats` must be
switched off).  One such check takes a few minutes of CPU and several GB of memory, so
**keep at most one such check per module**.
-/
import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.A7.Defs

open scoped MatrixGroups

namespace Work.CORE4

/-- `A₇` as a subgroup of the permutations of `Fin 7`. -/
abbrev A7 := alternatingGroup (Fin 7)

/-! ## The model elements of `A₇` -/

/-- `t = (0 1)(2 3)`, the model involution. -/
abbrev a7T : A7 := Work.A7.a7Invol

/-- `u = (0 2)(1 3)`, so that `V₁ = ⟨t, u⟩`. -/
abbrev a7U : A7 := Work.A7.a7Dswap 0 2 1 3 (by decide) (by decide)

/-- `v = (0 1)(4 5)`, so that `V₂ = ⟨t, v⟩`. -/
abbrev a7V : A7 := Work.A7.a7Dswap 0 1 4 5 (by decide) (by decide)

/-! ## The two model four-groups -/

/-- The carrier of `V₁ = {1, t, u, tu}`. -/
abbrev VaMem (x : A7) : Prop := x = 1 ∨ x = a7T ∨ x = a7U ∨ x = a7T * a7U

/-- The carrier of `V₂ = {1, t, v, tv}`. -/
abbrev VbMem (x : A7) : Prop := x = 1 ∨ x = a7T ∨ x = a7V ∨ x = a7T * a7V

/-- `V₁ = {1, t, u, tu}` as an explicit subgroup of `A₇`. -/
def V1sub : Subgroup A7 where
  carrier := {x | VaMem x}
  mul_mem' := by
    rintro x y (rfl | rfl | rfl | rfl) <;> rintro (rfl | rfl | rfl | rfl) <;> decide
  one_mem' := Or.inl rfl
  inv_mem' := by rintro x (rfl | rfl | rfl | rfl) <;> decide

/-- `V₂ = {1, t, v, tv}` as an explicit subgroup of `A₇`. -/
def V2sub : Subgroup A7 where
  carrier := {x | VbMem x}
  mul_mem' := by
    rintro x y (rfl | rfl | rfl | rfl) <;> rintro (rfl | rfl | rfl | rfl) <;> decide
  one_mem' := Or.inl rfl
  inv_mem' := by rintro x (rfl | rfl | rfl | rfl) <;> decide

/-- `x` normalises `V₁`: the conjugation action of `x` maps each of `t`, `u`, `tu` into `V₁`.
This is the normaliser membership condition, expressed elementwise so that it is decidable. -/
abbrev InN1 (x : A7) : Prop :=
  VaMem (x * a7T * x⁻¹) ∧ VaMem (x * a7U * x⁻¹) ∧ VaMem (x * (a7T * a7U) * x⁻¹)

/-- `x` normalises `V₂`, elementwise. -/
abbrev InN2 (x : A7) : Prop :=
  VbMem (x * a7T * x⁻¹) ∧ VbMem (x * a7V * x⁻¹) ∧ VbMem (x * (a7T * a7V) * x⁻¹)

/-! ## The same conditions on permutations of `Fin 7`

The large finite checks (`decide` over dominating the whole of `A₇`) run faster over
`Equiv.Perm (Fin 7)` (whose `Fintype` computes) than over the subtype `A₇`, so the element level
conditions are also recorded on permutations.  The two versions are related in
`Submission/Work/CORE4/A7S4.lean`. -/

/-- `t = (0 1)(2 3)` as a permutation of `Fin 7`. -/
abbrev tP : Equiv.Perm (Fin 7) := Work.A7.dswapPerm 0 1 2 3

/-- `u = (0 2)(1 3)` as a permutation of `Fin 7`. -/
abbrev uP : Equiv.Perm (Fin 7) := Work.A7.dswapPerm 0 2 1 3

/-- `v = (0 1)(4 5)` as a permutation of `Fin 7`. -/
abbrev vP : Equiv.Perm (Fin 7) := Work.A7.dswapPerm 0 1 4 5

/-- The carrier of `V₁ = {1, t, u, tu}`, on permutations. -/
abbrev VaMemP (x : Equiv.Perm (Fin 7)) : Prop := x = 1 ∨ x = tP ∨ x = uP ∨ x = tP * uP

/-- The carrier of `V₂ = {1, t, v, tv}`, on permutations. -/
abbrev VbMemP (x : Equiv.Perm (Fin 7)) : Prop := x = 1 ∨ x = tP ∨ x = vP ∨ x = tP * vP

/-- `x` normalises `V₁` (permutation version). -/
abbrev InN1P (x : Equiv.Perm (Fin 7)) : Prop :=
  VaMemP (x * tP * x⁻¹) ∧ VaMemP (x * uP * x⁻¹) ∧ VaMemP (x * (tP * uP) * x⁻¹)

/-- `x` normalises `V₂` (permutation version). -/
abbrev InN2P (x : Equiv.Perm (Fin 7)) : Prop :=
  VbMemP (x * tP * x⁻¹) ∧ VbMemP (x * vP * x⁻¹) ∧ VbMemP (x * (tP * vP) * x⁻¹)

/-! ## Cheap pruning conditions

The kernel evaluation of `decide` over `Equiv.Perm (Fin 7)` (5040 elements) is expensive, so the
element level checks below carry cheap *necessary* conditions first:  they cut the number of
elements for which the more expensive `InN1P`/`InN2P` tests are evaluated.

`Blk1 s` says that `s` maps `{0,1,2,3}` into itself (equivalently onto itself).  Every element of
`N(V₁)` has this property, because `V₁` acts regularly on `{0,1,2,3}` and fixes `4,5,6`.

`Blk2 s` says that `s` preserves the blocks `{0,1}`, `{2,3}`, `{4,5}` of the orbits of `V₂`
(and hence fixes `6`); every element of `N(V₂)` has this property.

`Fix456 w` says that `w` maps `{4,5,6}` into itself; every `w` commuting with `t = (01)(23)`
has this property, since `4,5,6` are exactly the fixed points of `t`. -/

/-- `s` maps `{0,1,2,3}` into itself. -/
abbrev Blk1 (s : Equiv.Perm (Fin 7)) : Prop :=
  (s 0).val < 4 ∧ (s 1).val < 4 ∧ (s 2).val < 4 ∧ (s 3).val < 4

/-- `s` permutes the blocks `{0,1}`, `{2,3}`, `{4,5}` (and fixes `6`), i.e. maps each block onto a
block.  With `s` injective this is equivalent to `s 0` and `s 1` lying in one block, etc. -/
abbrev Blk2 (s : Equiv.Perm (Fin 7)) : Prop :=
  (s 0).val / 2 = (s 1).val / 2 ∧ (s 2).val / 2 = (s 3).val / 2 ∧ (s 4).val / 2 = (s 5).val / 2 ∧
    s 6 = 6

/-- `w` maps `{4,5,6}` into itself. -/
abbrev Fix456 (w : Equiv.Perm (Fin 7)) : Prop := 4 ≤ (w 4).val ∧ 4 ≤ (w 5).val ∧ 4 ≤ (w 6).val

/-- Decidability instances, so that `decide` does not have to unfold the definitions. -/
instance decidablePredVaMemP : DecidablePred VaMemP := fun x => inferInstance

instance decidablePredVbMemP : DecidablePred VbMemP := fun x => inferInstance

instance decidablePredInN1P : DecidablePred InN1P := fun x => inferInstance

instance decidablePredInN2P : DecidablePred InN2P := fun x => inferInstance

instance decidablePredBlk1 : DecidablePred Blk1 := fun x => inferInstance

instance decidablePredBlk2 : DecidablePred Blk2 := fun x => inferInstance

instance decidablePredFix456 : DecidablePred Fix456 := fun x => inferInstance

/-! ## Bundled conditions for the finite checks

Bundling the hypotheses into a single `abbrev` keeps the type class search for `Decidable` shallow
(each bundle has an explicit `DecidablePred` instance), which matters because the checks are run by
`decide` over all `5040` permutations of `Fin 7`.  The order of the conjuncts is chosen so that the
cheap ones are evaluated first. -/

/-- The hypotheses of the `N(V₁)`-involution check, bundled.  The `5040` permutations of `Fin 7`
having this property are exactly the `21` elements of `n1Inv`. -/
abbrev N1InvCond (s : Equiv.Perm (Fin 7)) : Prop :=
  s * s = 1 ∧ s ≠ 1 ∧ Equiv.Perm.sign s = 1 ∧ InN1P s

/-- The hypotheses of the `N(V₁)`-order-`3` element check, bundled: exactly the `26` elements of
`n1Ord3` satisfy it. -/
abbrev N1Ord3Cond (k : Equiv.Perm (Fin 7)) : Prop :=
  k * k * k = 1 ∧ k ≠ 1 ∧ k * k ≠ 1 ∧ Equiv.Perm.sign k = 1 ∧ InN1P k

/-- The hypotheses of the `N(V₂)`-involution check, bundled: exactly the `9` elements of `n2Inv`
satisfy it. -/
abbrev N2InvCond (s : Equiv.Perm (Fin 7)) : Prop :=
  s * s = 1 ∧ s ≠ 1 ∧ Equiv.Perm.sign s = 1 ∧ InN2P s

/-- The hypotheses of the `N(V₂)`-order-`3` element check, bundled: exactly the `8` elements of
`n2Ord3` satisfy it. -/
abbrev N2Ord3Cond (k : Equiv.Perm (Fin 7)) : Prop :=
  k * k * k = 1 ∧ k ≠ 1 ∧ k * k ≠ 1 ∧ Equiv.Perm.sign k = 1 ∧ InN2P k

/-- The hypotheses of the "companion of `t`" check, bundled. -/
abbrev PartnerCond (w : Equiv.Perm (Fin 7)) : Prop :=
  w * w = 1 ∧ w ≠ 1 ∧ w ≠ tP ∧ Equiv.Perm.sign w = 1 ∧ w * tP = tP * w

instance decidablePredN1InvCond : DecidablePred N1InvCond := fun x => inferInstance

instance decidablePredN1Ord3Cond : DecidablePred N1Ord3Cond := fun x => inferInstance

instance decidablePredN2InvCond : DecidablePred N2InvCond := fun x => inferInstance

instance decidablePredN2Ord3Cond : DecidablePred N2Ord3Cond := fun x => inferInstance

instance decidablePredPartnerCond : DecidablePred PartnerCond := fun x => inferInstance

/-! ## The explicit lists -/

/-- The `21` involutions of `N_{A₇}(V₁)`, as permutations of `Fin 7`. -/
def n1Inv : Finset (Equiv.Perm (Fin 7)) :=
  {(Equiv.swap 2 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 6 : Equiv.Perm (Fin 7)),
    (Equiv.swap 2 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 5 : Equiv.Perm (Fin 7)),
    (Equiv.swap 2 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 6 : Equiv.Perm (Fin 7)),
    (Equiv.swap 1 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 6 : Equiv.Perm (Fin 7)),
    (Equiv.swap 1 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 5 : Equiv.Perm (Fin 7)),
    (Equiv.swap 1 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 6 : Equiv.Perm (Fin 7)),
    (Equiv.swap 1 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 6 : Equiv.Perm (Fin 7)),
    (Equiv.swap 1 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 5 : Equiv.Perm (Fin 7)),
    (Equiv.swap 1 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 6 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 6 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 5 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 6 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 3 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 6 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 5 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 6 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 3 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 6 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 5 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 6 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 2 : Equiv.Perm (Fin 7))}

/-- The `26` elements of order `3` of `N_{A₇}(V₁)`. -/
def n1Ord3 : Finset (Equiv.Perm (Fin 7)) :=
  {(Equiv.swap 4 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 6 : Equiv.Perm (Fin 7)),
    (Equiv.swap 4 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 6 5 : Equiv.Perm (Fin 7)),
    (Equiv.swap 1 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 3 : Equiv.Perm (Fin 7)),
    (Equiv.swap 1 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 6 : Equiv.Perm (Fin 7)),
    (Equiv.swap 1 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 6 5 : Equiv.Perm (Fin 7)),
    (Equiv.swap 1 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 2 : Equiv.Perm (Fin 7)),
    (Equiv.swap 1 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 6 : Equiv.Perm (Fin 7)),
    (Equiv.swap 1 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 6 5 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 2 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 6 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 6 5 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 3 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 6 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 6 5 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 1 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 6 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 6 5 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 3 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 6 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 6 5 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 1 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 6 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 6 5 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 2 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 6 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 6 5 : Equiv.Perm (Fin 7))}

/-- The `9` involutions of `N_{A₇}(V₂)`. -/
def n2Inv : Finset (Equiv.Perm (Fin 7)) :=
  {(Equiv.swap 2 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 5 : Equiv.Perm (Fin 7)),
    (Equiv.swap 2 4 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 5 : Equiv.Perm (Fin 7)),
    (Equiv.swap 2 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 4 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 5 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 3 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 3 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 2 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 4 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 5 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 4 : Equiv.Perm (Fin 7))}

/-- The `8` elements of order `3` of `N_{A₇}(V₂)`. -/
def n2Ord3 : Finset (Equiv.Perm (Fin 7)) :=
  {(Equiv.swap 0 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 4 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 5 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 4 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 4 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 4 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 5 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 4 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 3 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 4 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 2 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 4 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 3 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 4 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 2 : Equiv.Perm (Fin 7))}

/-- The `24` elements of the centraliser `C_{A₇}(t)`. -/
def ctList : Finset (Equiv.Perm (Fin 7)) :=
  {1,
    (Equiv.swap 4 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 6 : Equiv.Perm (Fin 7)),
    (Equiv.swap 4 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 6 5 : Equiv.Perm (Fin 7)),
    (Equiv.swap 2 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 6 : Equiv.Perm (Fin 7)),
    (Equiv.swap 2 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 5 : Equiv.Perm (Fin 7)),
    (Equiv.swap 2 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 6 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 6 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 5 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 6 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 3 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 6 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 6 5 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 3 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 6 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 6 5 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 6 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 5 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 6 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 6 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 5 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 6 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 2 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 6 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 6 5 : Equiv.Perm (Fin 7))}



/-! ## The claim -/

/-- The §4 `A₇` claim at a four-group `V ≤ G`: every involution `s ∈ N_G(V)` and every subgroup
`K ≤ N_G(V)` of order `3` inverted by `s` has a companion `K' ≠ K` of the same kind. -/
def ClaimProp (G : Type*) [Group G] (V : Subgroup G) : Prop :=
  ∀ s ∈ Subgroup.normalizer (V : Set G), orderOf s = 2 →
    ∀ K : Subgroup G, K ≤ Subgroup.normalizer (V : Set G) → Nat.card K = 3 → Work.GW2.Inverts s K →
      ∃ K' : Subgroup G, K' ≤ Subgroup.normalizer (V : Set G) ∧ Nat.card K' = 3 ∧ K' ≠ K ∧
        Work.GW2.Inverts s K'

end Work.CORE4
