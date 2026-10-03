/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The normal form of a word in a binary free product

This file proves that the natural map

`Monoid.Coprod.mk : FreeMonoid (M ⊕ N) →* M ∗ N`

is injective on *reduced* words, i.e. on lists of letters in which no letter is an identity
(`Sum.inl 1`, `Sum.inr 1`) and no two adjacent letters lie in the same factor
(`Work.OROneRel.Coprod.IsReduced`).  This is the uniqueness half of the normal form theorem for
free products.

## Strategy

Mathlib defines the binary free product `M ∗ N` from scratch as a quotient and provides no normal
form for it, but it does provide a full normal form theory for the *indexed* coproduct: every element
of `Monoid.CoprodI M` is represented by a unique *reduced word* `Monoid.CoprodI.Word M`, and
`Monoid.CoprodI.Word.equiv : CoprodI M ≃ Word M` is a bijection whose inverse is
`Monoid.CoprodI.Word.prod`.  In particular `Word.prod` is injective
(`coprodI_word_prod_injective`).

It therefore suffices to transport a binary free product word into a `Bool`-indexed coproduct,
where the two factors are indexed by `true` and `false`, and to note that `IsReduced` is exactly the
condition on the list making the transported list a genuine reduced `Word`.  Concretely:

* `CoprodFamily M N : Bool → Type u` is the family `true ↦ M`, `false ↦ N`;
* `coprodToCoprodI : M ∗ N →* CoprodI (CoprodFamily M N)` is the canonical comparison map, which
  sends `inl x` to `CoprodI.of x` and `inr y` to `CoprodI.of y`;
* `coprodWordOfReduced l hl` packages the image of a reduced list `l` as a reduced `Word`;
* `coprodToCoprodI_mk` identifies `coprodToCoprodI (mk l)` with the product of the letters of `l`.

Applying `coprodToCoprodI` to the equation `mk l₁ = mk l₂` and using injectivity of `Word.prod`
then reduces the claim to `l₁.map coprodSigmaOf = l₂.map coprodSigmaOf`, and `coprodSigmaOf` is
injective.
-/
import Mathlib
import Submission.Work.OROneRel.CoprodNormalForm

namespace Work.OROneRel

open Monoid

universe u

/-! ## A `Bool`-indexed presentation of the binary free product -/

/-- The two-element family whose free product is the binary free product of `M` and `N`: the index
`true` carries `M`, the index `false` carries `N`. -/
abbrev CoprodFamily (M N : Type u) : Bool → Type u := fun b => cond b M N

instance instMonoidCoprodFamily {M N : Type u} [Monoid M] [Monoid N] :
    (b : Bool) → Monoid (CoprodFamily M N b)
  | true => inferInstanceAs (Monoid M)
  | false => inferInstanceAs (Monoid N)

/-- A letter `inl x` (resp. `inr y`) of a binary free-product word, regarded as an element of the
`Bool`-indexed `Σ`-type of letters of the indexed free product. -/
def coprodSigmaOf {M N : Type u} : M ⊕ N → Sigma (CoprodFamily M N)
  | Sum.inl x => ⟨true, x⟩
  | Sum.inr y => ⟨false, y⟩

@[simp] theorem coprodSigmaOf_inl {M N : Type u} (x : M) :
    coprodSigmaOf (Sum.inl x) = (⟨true, x⟩ : Sigma (CoprodFamily M N)) := rfl

@[simp] theorem coprodSigmaOf_inr {M N : Type u} (y : N) :
    coprodSigmaOf (Sum.inr y) = (⟨false, y⟩ : Sigma (CoprodFamily M N)) := rfl

theorem coprodSigmaOf_injective {M N : Type u} :
    Function.Injective (coprodSigmaOf (M := M) (N := N)) := by
  intro a b h
  cases a with
  | inl x =>
    cases b with
    | inl x' => simpa using h
    | inr y' => simp [coprodSigmaOf] at h
  | inr y =>
    cases b with
    | inl x' => simp [coprodSigmaOf] at h
    | inr y' => simpa using h

/-- Two letters with the same index under `coprodSigmaOf` lie in the same factor. -/
theorem coprodSigmaOf_sameFactor {M N : Type u} (a b : M ⊕ N) :
    (coprodSigmaOf a).1 = (coprodSigmaOf b).1 → Coprod.SameFactor a b := by
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

variable {M N : Type u} [Group M] [Group N]

theorem coprodSigmaOf_snd_ne_one {l : List (M ⊕ N)} (hl : Coprod.IsReduced l) :
    ∀ c ∈ l, (coprodSigmaOf c).2 ≠ 1 := by
  intro c hc
  cases c with
  | inl x =>
    have h := (hl.1 (Sum.inl x) hc).1
    intro hx
    exact h (congrArg Sum.inl hx)
  | inr y =>
    have h := (hl.1 (Sum.inr y) hc).2
    intro hy
    exact h (congrArg Sum.inr hy)

/-- A reduced binary free-product word, packaged as a reduced word of the `Bool`-indexed free
product. -/
noncomputable def coprodWordOfReduced (l : List (M ⊕ N)) (hl : Coprod.IsReduced l) :
    CoprodI.Word (CoprodFamily M N) where
  toList := l.map coprodSigmaOf
  ne_one := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    exact coprodSigmaOf_snd_ne_one hl c hc
  chain_ne := by
    refine List.isChain_map_of_isChain (R := fun a b => ¬ Coprod.SameFactor a b)
      (S := fun a b : Sigma (CoprodFamily M N) => a.1 ≠ b.1) coprodSigmaOf ?_ hl.2
    intro a b hab
    exact fun h => hab (coprodSigmaOf_sameFactor a b h)

/-- The class of `inl x` (resp. `inr y`) in the `Bool`-indexed free product. -/
def coprodElemI (c : M ⊕ N) : CoprodI (CoprodFamily M N) :=
  CoprodI.of (M := CoprodFamily M N) (coprodSigmaOf c).2

theorem coprodWordOfReduced_prod (l : List (M ⊕ N)) (hl : Coprod.IsReduced l) :
    (coprodWordOfReduced l hl).prod = (l.map coprodElemI).prod := by
  rw [CoprodI.Word.prod]
  conv_lhs => rw [show (coprodWordOfReduced l hl).toList = l.map coprodSigmaOf from rfl]
  rw [List.map_map]
  rfl

/-! ## The comparison map `M ∗ N →* CoprodI (CoprodFamily M N)` -/

noncomputable def coprodOfTrue : M →* CoprodI (CoprodFamily M N) :=
  CoprodI.of (M := CoprodFamily M N) (i := true)

noncomputable def coprodOfFalse : N →* CoprodI (CoprodFamily M N) :=
  CoprodI.of (M := CoprodFamily M N) (i := false)

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

/-! ## Injectivity of the product of reduced indexed words -/

/-- Reduced words in the indexed free product with the same product are equal: `Word.prod` is
injective.  (Mathlib's `Word.equiv` is a bijection whose inverse is `Word.prod`.) -/
theorem coprodI_word_prod_injective {ι : Type*} {M : ι → Type*} [∀ i, Monoid (M i)] :
    Function.Injective (CoprodI.Word.prod (M := M)) := by
  classical
  intro a b h
  have h1 : CoprodI.Word.equiv (CoprodI.Word.prod a) = a := by
    convert Equiv.right_inv (CoprodI.Word.equiv (M := M)) a using 1
    rfl
  have h2 : CoprodI.Word.equiv (CoprodI.Word.prod b) = b := by
    convert Equiv.right_inv (CoprodI.Word.equiv (M := M)) b using 1
    rfl
  rw [h] at h1
  rw [h1] at h2
  exact h2

/-! ## The main theorem -/

theorem coprod_mk_injective_of_isReduced {M N : Type u} [Group M] [Group N]
    {l₁ l₂ : List (M ⊕ N)} (h₁ : Work.OROneRel.Coprod.IsReduced l₁)
    (h₂ : Work.OROneRel.Coprod.IsReduced l₂)
    (h : Monoid.Coprod.mk l₁ = Monoid.Coprod.mk l₂) : l₁ = l₂ := by
  classical
  have key : ∀ (l : List (M ⊕ N)) (hl : Coprod.IsReduced l),
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
    apply coprodI_word_prod_injective
    rw [key l₁ h₁, key l₂ h₂, h']
  have hlist : l₁.map coprodSigmaOf = l₂.map coprodSigmaOf := by
    have := congrArg CoprodI.Word.toList hw
    simpa only [coprodWordOfReduced] using this
  exact (List.map_injective_iff.mpr coprodSigmaOf_injective) hlist

end Group

end Work.OROneRel
