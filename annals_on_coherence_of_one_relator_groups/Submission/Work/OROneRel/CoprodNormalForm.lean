/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# Reduced words in a free product

Mathlib defines the free product `Monoid.Coprod M N` as a quotient of the free monoid on `M ⊕ N`, but
provides no normal form.  This file sets up the normal form: a word is *reduced* if no letter is an
identity and no two adjacent letters lie in the same factor.

The normal form theorem and Kurosh's torsion theorem are then

* `Work.OROneRel.coprod_exists_isReduced` -- every word is congruent to a reduced word;
* `Work.OROneRel.coprod_mk_injective_of_isReduced` -- reduced words in the same class are equal;
* `Work.OROneRel.coprod_isOfFinOrder_conj` -- an element of finite order in `M ∗ N` is conjugate into
  one of the factors.

Together with the identification of the terminal one-relator group with a free product, these give the
torsion half of the Karrass--Magnus--Solitar theorem at terminal relators (where the one-relator group
is `F ∗ ℤ/l`), and they are the free product normal forms the Bass--Serre arguments elsewhere in the
project need.

Two routes are available for the proofs.  Everything can be done directly for the binary product
(induction on the length of a word, using `Monoid.Coprod.mk_of_inl`, `Monoid.Coprod.mk_of_inr` and
`free product` bookkeeping).  Alternatively, Mathlib already has a normal form for the *indexed*
coproduct: `Monoid.CoprodI.Word`, `Monoid.CoprodI.Word.equiv : CoprodI M ≃ Word M`, together with the
number of letters (`Word.length`) and `Word.prod`; the binary case follows from the bridge
`Work.OROneRel.coprodI_iso_coprod` (`CoprodI (fun i : Fin 2 => ![M, N] i) ≃* M ∗ N`).  The second
route reuses Mathlib's Conway/ping-pong API and is likely shorter.
-/
import Mathlib.GroupTheory.Coprod.Basic
import Mathlib.GroupTheory.OrderOfElement

namespace Work.OROneRel

namespace Coprod

universe u

variable {M N : Type u} [Group M] [Group N]

/-- Two letters of a word in a free product lie in the same factor. -/
def SameFactor : M ⊕ N → M ⊕ N → Prop
  | Sum.inl _, Sum.inl _ => True
  | Sum.inr _, Sum.inr _ => True
  | Sum.inl _, Sum.inr _ => False
  | Sum.inr _, Sum.inl _ => False

/-- A word in the generators of a free product is *reduced* if no letter is an identity and no two
adjacent letters lie in the same factor. -/
def IsReduced (l : List (M ⊕ N)) : Prop :=
  (∀ c ∈ l, c ≠ Sum.inl 1 ∧ c ≠ Sum.inr 1) ∧ l.IsChain fun a b => ¬ SameFactor a b

theorem isReduced_nil : IsReduced ([] : List (M ⊕ N)) :=
  ⟨by simp, List.isChain_nil⟩

theorem isReduced_singleton {c : M ⊕ N} (hc : c ≠ Sum.inl 1) (hc' : c ≠ Sum.inr 1) :
    IsReduced [c] :=
  ⟨by simpa using ⟨hc, hc'⟩, List.isChain_singleton c⟩

/-- A reduced word with no letters in one of the factors lies in the other factor: the "one letter"
case of a reduced word. -/
theorem eq_singleton_of_isReduced_length_one {c : M ⊕ N} (h : IsReduced [c]) :
    c ≠ Sum.inl 1 ∧ c ≠ Sum.inr 1 := h.1 c (by simp)

end Coprod

end Work.OROneRel
