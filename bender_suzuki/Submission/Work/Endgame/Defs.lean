import Mathlib
import ChallengeDeps
import Submission.Blueprint.Interfaces

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The endgame of Bender–Suzuki: basic definitions

This file starts the `Endgame` area (`Submission/Work/Endgame/`, namespace `Work.Endgame`).

The area theorem `Work.Endgame.endgame` proves `Submission.Blueprint.EndgameProp`: Theorem B
(for groups in `Type`, i.e. universe `0`) together with Brauer–Suzuki and the model facts
implies the challenge in *every* universe `u`.

The only structural ingredient not already in the blueprint is that a finite group in `Type u`
is isomorphic to one living in `Type 0`, namely a group structure on `Fin n` (`n` = the order)
transported along an equivalence.  This file provides that transport (`groupOfEquiv`,
`transMul`, `mulEquivOfEquiv`), the invariance of the challenge predicate under isomorphism
(`IsSimpleBenderGroup.of_mulEquiv`), and the bookkeeping lemmas needed to move
`IsStronglyEmbedded` across an isomorphism (`conj_map_mulEquiv`).

## Conventions of the transport

`groupOfEquiv e : Group α` for `e : α ≃ β` and `[Group β]` is the pullback
`a * b = e.symm (e a * e b)`; `mulEquivOfEquiv e : α ≃* β` is `e`, seen as an isomorphism for
that structure.

The statements of `mulEquivOfEquiv` deliberately use `transMul e` (the pulled-back `Mul`, as an
explicit term) instead of `≃*` notation: when `α` already carries an unrelated `Mul` instance
(this is the case for `α = Fin n`!), type class synthesis for the `≃*` notation would pick that
instance up, and the statement would be about the wrong multiplication.  At a use site one
therefore introduces both a `Group` and a `Mul` local instance for the transported structure,
```
letI : Group (Fin n) := groupOfEquiv e.symm
letI : Mul (Fin n) := transMul e.symm
```
after which `Fin n ≃* X` notation is unambiguous again (a local instance shadows
`Fin.instMul`).
-/

set_option autoImplicit false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.Endgame

universe u v

/-! ## 1. Transport of a group structure along an equivalence -/

section Pullback

variable {α : Type u} {β : Type v} [Group β]

/-- **Transport of a group structure.**  Pull the group structure of `β` back along the
equivalence `e : α ≃ β`: `a * b := e.symm (e a * e b)`.  By construction the equivalence `e`
becomes a group isomorphism (`mulEquivOfEquiv`). -/
@[reducible] noncomputable def groupOfEquiv (e : α ≃ β) : Group α where
  mul a b := e.symm (e a * e b)
  one := e.symm 1
  inv a := e.symm (e a)⁻¹
  mul_assoc a b c := by
    show e.symm (e (e.symm (e a * e b)) * e c) = e.symm (e a * e (e.symm (e b * e c)))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, mul_assoc]
  one_mul a := by
    show e.symm (e (e.symm 1) * e a) = a
    rw [Equiv.apply_symm_apply, one_mul, Equiv.symm_apply_apply]
  mul_one a := by
    show e.symm (e a * e (e.symm 1)) = a
    rw [Equiv.apply_symm_apply, mul_one, Equiv.symm_apply_apply]
  inv_mul_cancel a := by
    show e.symm (e (e.symm (e a)⁻¹) * e a) = e.symm 1
    rw [Equiv.apply_symm_apply, inv_mul_cancel]

/-- The `Mul` structure attached to the group structure transported along `e`.  Stating a
`MulEquiv` type through `transMul` avoids the ambiguity of `≃*` notation on a type that already
carries an unrelated `Mul`. -/
noncomputable abbrev transMul (e : α ≃ β) : Mul α :=
  (groupOfEquiv e).toDivInvMonoid.toMonoid.toMulOneClass.toMul

/-- The equivalence `e` that defined `groupOfEquiv`, as a group isomorphism of the transported
structure with the original group. -/
noncomputable def mulEquivOfEquiv (e : α ≃ β) :
    @MulEquiv α β (transMul e) (inferInstance : Mul β) :=
  @MulEquiv.mk α β (transMul e) (inferInstance : Mul β) e
    (fun a b => e.apply_symm_apply (e a * e b))

end Pullback

/-! ## 2. Invariance of the challenge predicate under isomorphism -/

section Invariance

variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- `IsSimpleBenderGroup` is invariant under group isomorphism. -/
theorem IsSimpleBenderGroup.of_mulEquiv (h : IsSimpleBenderGroup G) (e : G ≃* H) :
    IsSimpleBenderGroup H := by
  rcases h with ⟨n, hn, e₁⟩ | ⟨n, hn, e₁⟩ | ⟨n, hn, e₁⟩
  · exact .isPSL2 n hn (e.symm.trans e₁)
  · exact .isSuzuki n hn (e.symm.trans e₁)
  · exact .isPSU3 n hn (e.symm.trans e₁)

/-- `IsSimpleBenderGroup` is invariant under group isomorphism (iff form). -/
theorem isSimpleBenderGroup_iff_of_mulEquiv (e : G ≃* H) :
    IsSimpleBenderGroup G ↔ IsSimpleBenderGroup H :=
  ⟨fun h => IsSimpleBenderGroup.of_mulEquiv h e,
    fun h => IsSimpleBenderGroup.of_mulEquiv h e.symm⟩

/-- Conjugation commutes with a group isomorphism: `e` carries the conjugate of `K` by `x` to
the conjugate of the image of `K` by the image of `x`.  This is the bookkeeping lemma behind the
transport of `IsStronglyEmbedded`. -/
theorem conj_map_mulEquiv (e : G ≃* H) (K : Subgroup G) (x : G) :
    conj (e x) (K.map e.toMonoidHom) = (conj x K).map e.toMonoidHom := by
  have hcomp : (MulAut.conj (e x)).toMonoidHom.comp e.toMonoidHom
      = e.toMonoidHom.comp (MulAut.conj x).toMonoidHom := by
    ext k
    change e x * e k * (e x)⁻¹ = e (x * k * x⁻¹)
    rw [map_mul, map_mul, map_inv]
  show Subgroup.map (MulAut.conj (e x)).toMonoidHom (Subgroup.map e.toMonoidHom K)
      = Subgroup.map e.toMonoidHom (Subgroup.map (MulAut.conj x).toMonoidHom K)
  rw [Subgroup.map_map, Subgroup.map_map, hcomp]

end Invariance

/-! ## 3. Evenness bookkeeping -/

section Even

variable {G : Type u} [Group G]

/-- An element of order `2` witnesses that the group has even order. -/
theorem even_natCard_of_orderOf_eq_two {t : G} (ht : orderOf t = 2) : Even (Nat.card G) := by
  rw [even_iff_two_dvd, ← ht]
  rw [← Nat.card_zpowers t]
  exact Subgroup.card_subgroup_dvd_card (Subgroup.zpowers t)

/-- A four-group witnesses that the group has even order. -/
theorem HasFourGroup.even_natCard (h : HasFourGroup G) : Even (Nat.card G) := by
  obtain ⟨a, b, ha, hb, hne, hcomm⟩ := h
  exact even_natCard_of_orderOf_eq_two ha

/-- A strongly embedded subgroup has even order, so the ambient group has even order. -/
theorem even_natCard_of_isStronglyEmbedded {M : Subgroup G} (h : IsStronglyEmbedded M) :
    Even (Nat.card G) := by
  have h2 : Even (Nat.card M) := h.2.1
  rw [even_iff_two_dvd] at h2 ⊢
  exact h2.trans (Subgroup.card_subgroup_dvd_card M)

end Even

end Work.Endgame
