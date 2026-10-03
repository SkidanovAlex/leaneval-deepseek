/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The normal form of a word in a binary free product, at mixed universe levels

This is the mixed-universe port of `Work.OROneRel.coprod_mk_injective_of_isReduced`.  The natural map

`Monoid.Coprod.mk : FreeMonoid (M ⊕ N) →* M ∗ N`

is injective on *reduced* words (`Work.ORBassSerre.CoprodTree.IsReduced`): lists of letters in which
no letter is an identity (`Sum.inl 1`, `Sum.inr 1`) and no two adjacent letters lie in the same
factor.  When `M` and `N` live in the same universe this is proved in `Submission.Work.OROneRel`;
here the two factors live in `Type u` and `Type v` respectively, which is what the Bass--Serre tree of
`ℤ/n ∗ F(γ)` needs.

## Strategy

Exactly as in the same-universe case, except that the two factors are embedded into the common
universe `max u v` by `ULift` before being made into the `Bool`-indexed family `CoprodFamily M N`
(`true ↦ ULift M`, `false ↦ ULift N`).  Mathlib's `CoprodI.Word` supplies the unique reduced normal
form in the indexed free product, and `CoprodI.Word.prod` is injective there.
-/
import Mathlib
import Submission.Work.ORBassSerre.CoprodTree.NormalFormDefs
import Submission.Work.OROneRel.coprod_mk_injective_of_isReduced

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v

namespace Work.ORBassSerre.CoprodTree

open Monoid

/-! ## A `Bool`-indexed presentation of the binary free product -/

/-- The two-element family whose free product is the binary free product of `M` and `N`: the index
`true` carries `M` and the index `false` carries `N`, both lifted into the common universe
`max u v`. -/
abbrev CoprodFamily (M : Type u) (N : Type v) : Bool → Type (max u v) :=
  fun b => cond b (ULift.{max u v, u} M) (ULift.{max u v, v} N)

instance instMonoidCoprodFamily {M : Type u} {N : Type v} [Monoid M] [Monoid N] :
    (b : Bool) → Monoid (CoprodFamily M N b)
  | true => inferInstanceAs (Monoid (ULift.{max u v, u} M))
  | false => inferInstanceAs (Monoid (ULift.{max u v, v} N))

/-- A letter `inl x` (resp. `inr y`) of a binary free-product word, regarded as an element of the
`Bool`-indexed `Σ`-type of letters of the indexed free product. -/
def coprodSigmaOf {M : Type u} {N : Type v} : M ⊕ N → Sigma (CoprodFamily M N)
  | Sum.inl x => ⟨true, ULift.up x⟩
  | Sum.inr y => ⟨false, ULift.up y⟩

@[simp] theorem coprodSigmaOf_inl {M : Type u} {N : Type v} (x : M) :
    coprodSigmaOf (Sum.inl x) = (⟨true, ULift.up x⟩ : Sigma (CoprodFamily M N)) := rfl

@[simp] theorem coprodSigmaOf_inr {M : Type u} {N : Type v} (y : N) :
    coprodSigmaOf (Sum.inr y) = (⟨false, ULift.up y⟩ : Sigma (CoprodFamily M N)) := rfl

theorem coprodSigmaOf_injective {M : Type u} {N : Type v} :
    Function.Injective (coprodSigmaOf (M := M) (N := N)) := by
  intro a b h
  cases a with
  | inl x =>
    cases b with
    | inl x' => simp at h ⊢; exact congrArg ULift.down h
    | inr y' => simp [coprodSigmaOf] at h
  | inr y =>
    cases b with
    | inl x' => simp [coprodSigmaOf] at h
    | inr y' => simp at h ⊢; exact congrArg ULift.down h

/-- Two letters with the same index under `coprodSigmaOf` lie in the same factor. -/
theorem coprodSigmaOf_sameFactor {M : Type u} {N : Type v} (a b : M ⊕ N) :
    (coprodSigmaOf a).1 = (coprodSigmaOf b).1 → SameFactor a b := by
  intro h
  cases a with
  | inl x => cases b with
             | inl x' => trivial
             | inr y' => exact absurd h (by simp [coprodSigmaOf])
  | inr y => cases b with
             | inl x' => exact absurd h (by simp [coprodSigmaOf])
             | inr y' => trivial

/-! ## The normal form of a reduced list -/

section Group

variable {M : Type u} {N : Type v} [Group M] [Group N]

theorem coprodSigmaOf_snd_ne_one {l : List (M ⊕ N)} (hl : IsReduced l) :
    ∀ c ∈ l, (coprodSigmaOf c).2 ≠ 1 := by
  intro c hc
  cases c with
  | inl x =>
    rw [coprodSigmaOf_inl]
    intro hx
    have hx' : (ULift.up x : ULift.{max u v, u} M) = ULift.up (1 : M) := hx
    exact (hl.1 (Sum.inl x) hc).1 (congrArg Sum.inl (ULift.up.inj hx'))
  | inr y =>
    rw [coprodSigmaOf_inr]
    intro hy
    have hy' : (ULift.up y : ULift.{max u v, v} N) = ULift.up (1 : N) := hy
    exact (hl.1 (Sum.inr y) hc).2 (congrArg Sum.inr (ULift.up.inj hy'))

/-- A reduced binary free-product word, packaged as a reduced word of the `Bool`-indexed free
product. -/
noncomputable def coprodWordOfReduced (l : List (M ⊕ N)) (hl : IsReduced l) :
    CoprodI.Word (CoprodFamily M N) where
  toList := l.map coprodSigmaOf
  ne_one := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    exact coprodSigmaOf_snd_ne_one hl c hc
  chain_ne := by
    refine List.isChain_map_of_isChain (R := fun a b => ¬ SameFactor a b)
      (S := fun a b : Sigma (CoprodFamily M N) => a.1 ≠ b.1) coprodSigmaOf ?_ hl.2
    intro a b hab
    exact fun h => hab (coprodSigmaOf_sameFactor a b h)

/-- The class of `inl x` (resp. `inr y`) in the `Bool`-indexed free product. -/
def coprodElemI (c : M ⊕ N) : CoprodI (CoprodFamily M N) :=
  CoprodI.of (M := CoprodFamily M N) (coprodSigmaOf c).2

theorem coprodWordOfReduced_prod (l : List (M ⊕ N)) (hl : IsReduced l) :
    (coprodWordOfReduced l hl).prod = (l.map coprodElemI).prod := by
  rw [CoprodI.Word.prod]
  conv_lhs => rw [show (coprodWordOfReduced l hl).toList = l.map coprodSigmaOf from rfl]
  rw [List.map_map]
  rfl

/-! ## The comparison map `M ∗ N →* CoprodI (CoprodFamily M N)` -/

/-- The inclusion of `M` into the common universe, as a monoid homomorphism. -/
noncomputable def uliftUp {M : Type u} [Monoid M] : M →* ULift.{max u v, u} M :=
  (MulEquiv.ulift (α := M)).symm.toMonoidHom

noncomputable def coprodOfTrue : M →* CoprodI (CoprodFamily M N) :=
  (CoprodI.of (M := CoprodFamily M N) (i := true)).comp uliftUp

noncomputable def coprodOfFalse : N →* CoprodI (CoprodFamily M N) :=
  (CoprodI.of (M := CoprodFamily M N) (i := false)).comp uliftUp

/-- The canonical comparison homomorphism from the binary free product to the `Bool`-indexed free
product. -/
noncomputable def coprodToCoprodI : (Monoid.Coprod M N) →* CoprodI (CoprodFamily M N) :=
  Monoid.Coprod.lift coprodOfTrue coprodOfFalse

theorem elim_coprodOf_eq_coprodElemI :
    Sum.elim (⇑coprodOfTrue) (⇑coprodOfFalse) = coprodElemI (M := M) (N := N) := by
  funext c
  cases c with
  | inl x => rfl
  | inr y => rfl

/-- `coprodToCoprodI` sends the class of a list to the product of the transported letters. -/
theorem coprodToCoprodI_mk_ofList (l : List (M ⊕ N)) :
    coprodToCoprodI (Monoid.Coprod.mk (FreeMonoid.ofList l)) = (l.map coprodElemI).prod := by
  rw [coprodToCoprodI, Monoid.Coprod.lift_apply_mk, FreeMonoid.lift_ofList,
    elim_coprodOf_eq_coprodElemI]

/-! ## The main theorem -/

theorem coprod_mk_injective_of_isReduced_univ {M : Type u} {N : Type v} [Group M] [Group N]
    {l₁ l₂ : List (M ⊕ N)} (h₁ : Work.ORBassSerre.CoprodTree.IsReduced l₁)
    (h₂ : Work.ORBassSerre.CoprodTree.IsReduced l₂)
    (h : Monoid.Coprod.mk l₁ = Monoid.Coprod.mk l₂) : l₁ = l₂ := by
  classical
  have key : ∀ (l : List (M ⊕ N)) (hl : IsReduced l),
      CoprodI.Word.prod (coprodWordOfReduced l hl) =
        coprodToCoprodI (Monoid.Coprod.mk (FreeMonoid.ofList l)) := by
    intro l hl
    rw [coprodToCoprodI_mk_ofList]
    exact coprodWordOfReduced_prod l hl
  have h' : coprodToCoprodI (Monoid.Coprod.mk (FreeMonoid.ofList l₁)) =
      coprodToCoprodI (Monoid.Coprod.mk (FreeMonoid.ofList l₂)) := by
    rw [show FreeMonoid.ofList l₁ = l₁ from rfl,
      show FreeMonoid.ofList l₂ = l₂ from rfl, h]
  have hw : coprodWordOfReduced l₁ h₁ = coprodWordOfReduced l₂ h₂ := by
    apply Work.OROneRel.coprodI_word_prod_injective
    rw [key l₁ h₁, key l₂ h₂, h']
  have hlist : l₁.map coprodSigmaOf = l₂.map coprodSigmaOf := by
    have := congrArg CoprodI.Word.toList hw
    simpa only [coprodWordOfReduced] using this
  exact (List.map_injective_iff.mpr coprodSigmaOf_injective) hlist

end Group

end Work.ORBassSerre.CoprodTree
