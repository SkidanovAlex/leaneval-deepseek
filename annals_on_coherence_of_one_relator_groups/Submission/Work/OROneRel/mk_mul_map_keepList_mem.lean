import Mathlib
import Submission.Work.OROneRel.killTree

/-!
# The projection of the edge group onto `F (β)` kills the tree of the window

`keepList Wt c lo hi L` (`Submission/Work/OROneRel/killTree.lean`) is the `filterMap` of a list of
symbols of the level graph onto the alphabet `β = winBeta Wt c lo hi` of the window: the symbols
`p` with `p.1 ∈ winE c lo hi` and `coverClassAt Wt c p.1 ≠ 1` survive (as the subtype
`⟨p.1, ·, ·⟩` of `β`), the others are erased.

This file proves the identity announced there:

  `FreeGroup.mk L * (map Subtype.val (FreeGroup.mk (keepList Wt c lo hi L)))⁻¹ ∈ ⟪treeSet Wt c lo hi⟫`

i.e. the word `FreeGroup.mk L` of the edge group differs from the image of its projection by an
element of the normal closure of the tree of the window (the edges of the window of *trivial* loop
class).  It is what converts a statement about the normal closure of the tree of `[lo,hi]` together
with the walk word into a statement about the normal closure of `winRoot`.

## The argument

Both sides are products of one-letter words, so the difference is a product of the one-letter words
erased by the projection, each conjugated by the retained factors:

* a letter `p` with `p.1 ∈ winE c lo hi` and `coverClassAt Wt c p.1 = 1` is *erased*, and its
  one-letter word `FreeGroup.mk [p]` is `of p.1` or its inverse, hence lies in the normal closure of
  the tree because `FreeGroup.of p.1 ∈ treeSet Wt c lo hi`;
* a letter kept by the projection contributes the *same* letter to both sides, so it cancels up to
  conjugation.

Formally this is the induction `mk_mul_mk_filterMap_inv_mem` on the list, transported through
`FreeGroup.map.mk` by `map_keepList_eq`, which compares `keepList` with the `filterMap` over the
underlying list `(α × ℤ) × Bool` of the same letters.
-/

namespace Work.OROneRel

variable {α : Type*}

/-- A one-letter word lies in a normal subgroup as soon as its generator does. -/
private theorem mk_singleton_mem {N : Subgroup (FreeGroup α)} (_hN : N.Normal) {a : α}
    (ha : FreeGroup.of a ∈ N) (b : Bool) : FreeGroup.mk [(a, b)] ∈ N := by
  cases b
  · show (FreeGroup.of a)⁻¹ ∈ N
    exact N.inv_mem ha
  · exact ha

/-- `FreeGroup.mk` turns a cons into a product. -/
private theorem mk_cons_mul (p : α × Bool) (L : List (α × Bool)) :
    FreeGroup.mk (p :: L) = FreeGroup.mk [p] * FreeGroup.mk L := by
  rw [← List.singleton_append, ← FreeGroup.mul_mk]

/-- **Erasing the letters of `L` whose generator lies in a normal subgroup.**  If the generator of
every letter `p` of `L` satisfying `P p` lies in the normal subgroup `N`, then erasing those letters
from the word `FreeGroup.mk L` multiplies it by an element of `N`. -/
private theorem mk_mul_mk_filterMap_inv_mem (N : Subgroup (FreeGroup (α × ℤ))) (hN : N.Normal)
    (L : List ((α × ℤ) × Bool)) (P : ((α × ℤ) × Bool) → Prop) [DecidablePred P]
    (hP : ∀ p ∈ L, P p → FreeGroup.of p.1 ∈ N) :
    FreeGroup.mk L * (FreeGroup.mk (L.filterMap fun p => if P p then none else some p))⁻¹ ∈ N := by
  classical
  induction L with
  | nil => exact N.one_mem
  | cons p L ih =>
    by_cases hq : P p
    · -- the letter is erased: its one-letter word lies in `N` by `hP`
      have hf : (fun q => if P q then (none : Option ((α × ℤ) × Bool)) else some q) p = none := by
        simp [hq]
      rw [List.filterMap_cons_none
        (f := fun q => if P q then (none : Option ((α × ℤ) × Bool)) else some q)
        (a := p) (l := L) hf]
      rw [mk_cons_mul]
      have hmk : FreeGroup.mk [p] ∈ N :=
        mk_singleton_mem hN (hP p (List.mem_cons_self ..) hq) p.2
      have hD : FreeGroup.mk L *
          (FreeGroup.mk (L.filterMap fun p => if P p then none else some p))⁻¹ ∈ N :=
        ih (fun q hq' => hP q (List.mem_cons_of_mem p hq'))
      rw [mul_assoc]
      exact N.mul_mem hmk hD
    · -- the letter is kept: it contributes the same factor to both sides
      have hf : (fun q => if P q then (none : Option ((α × ℤ) × Bool)) else some q) p = some p := by
        simp [hq]
      rw [List.filterMap_cons_some
        (f := fun q => if P q then (none : Option ((α × ℤ) × Bool)) else some q)
        (a := p) (l := L) (b := p) hf]
      rw [mk_cons_mul, mk_cons_mul p (List.filterMap (fun q => if P q then none else some q) L)]
      have hD : FreeGroup.mk L *
          (FreeGroup.mk (L.filterMap fun p => if P p then none else some p))⁻¹ ∈ N :=
        ih (fun q hq' => hP q (List.mem_cons_of_mem p hq'))
      have hc := hN.conj_mem (FreeGroup.mk L *
        (FreeGroup.mk (L.filterMap fun p => if P p then none else some p))⁻¹) hD (FreeGroup.mk [p])
      convert hc using 1
      group

/-- `keepList Wt c lo hi L`, read back in the edge group: the `filterMap` of the underlying list
onto the letters of non-trivial loop class.  The two filters agree on `L` because every letter of
`L` traverses an edge of the window (`hL`). -/
private theorem map_keepList_eq {Wt : ℤ → FreeGroup α} {c : α → ℤ} {lo hi : ℤ}
    (L : List ((α × ℤ) × Bool)) (hL : ∀ p ∈ L, p.1 ∈ winE c lo hi)
    (P : ((α × ℤ) × Bool) → Prop) [DecidablePred P]
    (hP : ∀ p ∈ L, coverClassAt Wt c p.1 = 1 ↔ P p) :
    (keepList Wt c lo hi L).map (fun x => ((x.1 : winBeta Wt c lo hi).1, x.2)) =
      L.filterMap (fun p => if P p then none else some p) := by
  classical
  unfold keepList
  rw [List.map_filterMap]
  refine List.filterMap_congr (fun p hp => ?_)
  have hw : p.1 ∈ winE c lo hi := hL p hp
  have hc : coverClassAt Wt c p.1 = 1 ↔ P p := hP p hp
  by_cases hPp : P p
  · -- a letter of trivial loop class: dropped on both sides
    have hnd : ¬ (p.1 ∈ winE c lo hi ∧ coverClassAt Wt c p.1 ≠ 1) := by
      rintro ⟨-, hne⟩
      exact hne (hc.mpr hPp)
    simp only [dif_neg hnd, Option.map_none, if_pos hPp]
  · -- a letter of non-trivial loop class: kept on both sides, with the same letter
    have hcond : p.1 ∈ winE c lo hi ∧ coverClassAt Wt c p.1 ≠ 1 :=
      ⟨hw, fun hcl => hPp (hc.mp hcl)⟩
    simp only [dif_pos hcond, Option.map_some, if_neg hPp]

theorem mk_mul_map_keepList_mem (Wt : ℤ → FreeGroup (Fin 2)) (c : Fin 2 → ℤ) (lo hi : ℤ)
    (L : List ((Fin 2 × ℤ) × Bool)) (hL : ∀ p ∈ L, p.1 ∈ Work.OROneRel.winE c lo hi) :
    FreeGroup.mk L * (FreeGroup.map (Subtype.val : Work.OROneRel.winBeta Wt c lo hi → Fin 2 × ℤ)
        (FreeGroup.mk (Work.OROneRel.keepList Wt c lo hi L)))⁻¹ ∈
      Subgroup.normalClosure (Work.OROneRel.treeSet Wt c lo hi) := by
  classical
  -- the image of the projected word is the word with the tree letters erased
  have hmap : FreeGroup.map (Subtype.val : winBeta Wt c lo hi → Fin 2 × ℤ)
      (FreeGroup.mk (keepList Wt c lo hi L)) =
      FreeGroup.mk (L.filterMap (fun p => if coverClassAt Wt c p.1 = 1 then none else some p)) := by
    rw [show FreeGroup.map (Subtype.val : winBeta Wt c lo hi → Fin 2 × ℤ)
        (FreeGroup.mk (keepList Wt c lo hi L))
        = FreeGroup.mk ((keepList Wt c lo hi L).map (fun x => (x.1.1, x.2))) from rfl]
    rw [map_keepList_eq L hL (fun p => coverClassAt Wt c p.1 = 1) (fun p _ => Iff.rfl)]
  rw [hmap]
  -- the difference is carried by the erased letters, which are exactly the tree of the window
  exact mk_mul_mk_filterMap_inv_mem (Subgroup.normalClosure (treeSet Wt c lo hi))
    Subgroup.normalClosure_normal L (fun p => coverClassAt Wt c p.1 = 1)
    (fun p hp hcl => Subgroup.subset_normalClosure (mem_treeSet ⟨hL p hp, hcl⟩))

end Work.OROneRel
