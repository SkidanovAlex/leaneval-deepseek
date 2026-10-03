import Mathlib
import Submission.Work.OROneRel.padDefs
import Submission.Work.OROneRel.mk_flatten_prod
import Submission.Work.OROneRel.padBlock_props
import Submission.Work.OROneRel.isReduced_flatten_map

/-!
# The word of a padded group element

`padHom c : F α →* F (Option α)` sends the generator `a` to the block `a * z ^ (c a) * a`,
where `z = none` is a fresh letter.  The word `padList c L` is the concatenation of the words of
these blocks, read off the word `L`.

The point of the padding is that the block `a * z ^ (c a) * a` begins and ends with its own letter
`a`: consecutive blocks of a reduced word can never cancel against each other, so the concatenation
`padList c L` is itself reduced.  Consequently `toWord` is additive along the padding and

`(padHom c u).toWord = padList c u.toWord`,

which is the main theorem of this file.

The proof has two independent inputs, both proved in sibling modules:

* `Work.OROneRel.mk_flatten_prod`: `mk` turns the concatenation of a list of words into the product
  of their `mk`-images.  This gives `mk (padList c L) = padHom c (mk L)`.
* `Work.OROneRel.isReduced_flatten_map`, fed by `Work.OROneRel.padBlock_props`: the flattening of
  a reduced list of blocks, each block being reduced and starting and ending with the letter
  `(φ p.1, p.2)` for an injective `φ`, is reduced.  This gives that `padList c L` is reduced.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-! ### Elementary translation of the padding to `mk` -/

/-- `mk` of a padded block of `p` is the padded generator `padGen c p.1`, or its inverse according
to the sign `p.2`. -/
lemma mk_padBlock (c : α → ℤ) (p : α × Bool) :
    FreeGroup.mk (padBlock c p) = if p.2 then padGen c p.1 else (padGen c p.1)⁻¹ := by
  classical
  unfold padBlock
  split <;> exact FreeGroup.mk_toWord

/-- `mk` of the padding of a word is the product of the padded generators. -/
lemma mk_padList_prod (c : α → ℤ) (L : List (α × Bool)) :
    FreeGroup.mk (padList c L) =
      (L.map (fun p : α × Bool => if p.2 then padGen c p.1 else (padGen c p.1)⁻¹)).prod := by
  classical
  unfold padList
  rw [mk_flatten_prod, List.map_map]
  have hf : (FreeGroup.mk ∘ padBlock c) =
      (fun p : α × Bool => if p.2 then padGen c p.1 else (padGen c p.1)⁻¹) := by
    funext p
    exact mk_padBlock c p
  rw [hf]

/-- `mk` of the padding is the padding homomorphism: the padding is multiplicative. -/
lemma mk_padList_eq_padHom (c : α → ℤ) (L : List (α × Bool)) :
    FreeGroup.mk (padList c L) = padHom c (FreeGroup.mk L) := by
  rw [mk_padList_prod, padHom, FreeGroup.lift_mk]
  have hf : (fun p : α × Bool => if p.2 then padGen c p.1 else (padGen c p.1)⁻¹) =
      (fun p : α × Bool => bif p.2 then padGen c p.1 else (padGen c p.1)⁻¹) := by
    funext p
    cases p.2 <;> rfl
  rw [hf]

/-! ### Reducedness of the padding of a reduced word -/

/-- The padding of a reduced word is reduced: the blocks never cancel against one another. -/
lemma isReduced_padList [DecidableEq α] (c : α → ℤ) {L : List (α × Bool)}
    (hL : FreeGroup.IsReduced L) : FreeGroup.IsReduced (padList c L) := by
  have h := isReduced_flatten_map (φ := (some : α → PadT α))
    (fun a b h => Option.some.inj h) (padBlock c) L
    (fun p => (padBlock_props c p).1) (fun p => (padBlock_props c p).2.1)
    (fun p => (padBlock_props c p).2.2) hL
  simpa only [padList] using h

/-! ### The main theorem -/

theorem toWord_padHom {α : Type u} [DecidableEq α] (c : α → ℤ) (u : FreeGroup α) :
    (Work.OROneRel.padHom c u).toWord = Work.OROneRel.padList c u.toWord := by
  have hA : FreeGroup.mk (padList c u.toWord) = padHom c u := by
    rw [mk_padList_eq_padHom, FreeGroup.mk_toWord]
  have hred : FreeGroup.IsReduced (padList c u.toWord) :=
    isReduced_padList c FreeGroup.isReduced_toWord
  calc (padHom c u).toWord = (FreeGroup.mk (padList c u.toWord)).toWord := by rw [hA]
    _ = FreeGroup.reduce (padList c u.toWord) := FreeGroup.toWord_mk
    _ = padList c u.toWord := hred.reduce_eq

end Work.OROneRel
