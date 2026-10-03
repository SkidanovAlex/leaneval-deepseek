/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The Tietze step killing the tree edges of the band's `2`-cell

`Submission/Work/OROneRel/bandCell.lean` defines, in the edge group `F(E(D))` of the window
`winE c lo hi` of the `ℤ`-cover of the one-relator complex,

* `walkCell c lo hi j w h` -- the walk of the relator `w` started at level `j`, decorated by
  `decor c j (wordOf w)` (its letters read in the window: the hypothesis `h`),
* `treeKill Wt c lo hi` -- the homomorphism killing the tree edges (`winTree Wt c lo hi`, the
  window edges of trivial loop class) and fixing the other window edges,
* `betaKill Wt c lo hi L` -- the same decorated walk with the tree edges deleted, read in the
  alphabet `winBeta Wt c lo hi` of non-tree edges.

This file proves that the two operations agree:

`treeKill (walkCell …) = betaKill (decor c j (wordOf w))`,

i.e. reading the walk in `F(E(D))` and then killing the tree generators gives exactly the walk
with its tree traversals deleted.  This is the Tietze step removing the tree generators from the
band's presentation `⟨E(D) | tree ∪ walkCell⟩`.

The proof is bookkeeping: `walkCellList` is `.attach.map` of the decorated walk and `betaKillList`
is a `.filterMap` of the same walk, while `treeKill` is `FreeGroup.lift` of the generator map
sending a tree edge to `1` and a non-tree edge to itself.  `FreeGroup.lift_mk` evaluates that lift
on `FreeGroup.mk` as a product of letters; the only work is to see that the `1`-letters of that
product are exactly the deleted ones (`prod_map_cond_eq_prod_filterMap`) and that the `.attach.map`
of the edge group is the same list as the decorated walk up to the `filterMap`
(`attach_map_filterMap`).
-/
import Mathlib
import Submission.Work.OROneRel.bandCell

set_option autoImplicit false

namespace Work.OROneRel

universe u

variable {α : Type u}

/-! ### Two general list lemmas -/

/-- `FreeGroup.mk` of a list is the product of its letters, read with their sign. -/
theorem mk_eq_prod_cond {β : Type*} (L : List (β × Bool)) :
    FreeGroup.mk L =
      List.prod (L.map fun x => cond x.2 (FreeGroup.of x.1) (FreeGroup.of x.1)⁻¹) := by
  rw [← FreeGroup.lift_of_apply (FreeGroup.mk L)]
  exact FreeGroup.lift_mk

/-- **A product with trivial letters is a product over the non-trivial letters.**

Let `L` be a list of signed letters of `ι` and let `g : ι → FreeGroup κ` be such that each
signed letter `cond x.2 (g x.1) (g x.1)⁻¹` is either trivial or is the corresponding signed
letter of the free group on `κ` (`V` records which, `V x = none` meaning "trivial").  Then the
product over `L` equals the product of the (signed) free letters `V x` of `L`. -/
theorem prod_map_cond_eq_prod_filterMap {ι : Type*} {κ : Type*}
    (L : List (ι × Bool)) (g : ι → FreeGroup κ) (V : ι × Bool → Option (κ × Bool))
    (hV : ∀ x : ι × Bool, cond x.2 (g x.1) (g x.1)⁻¹
      = (V x).elim 1 (fun y => cond y.2 (FreeGroup.of y.1) (FreeGroup.of y.1)⁻¹)) :
    (L.map (fun x => cond x.2 (g x.1) (g x.1)⁻¹)).prod
      = ((L.filterMap V).map fun y => cond y.2 (FreeGroup.of y.1) (FreeGroup.of y.1)⁻¹).prod := by
  induction L with
  | nil => simp
  | cons x L ih =>
    have hx := hV x
    cases hv : V x with
    | none =>
      simp only [hv, Option.elim_none] at hx
      simp only [List.map_cons, List.filterMap_cons, hv] at *
      rw [List.prod_cons, hx, ih, one_mul]
    | some y =>
      simp only [hv, Option.elim_some] at hx
      simp only [List.map_cons, List.filterMap_cons, hv] at *
      rw [List.prod_cons, hx, ih, List.prod_cons]

/-- **`attach`-`map` commutes with `filterMap`.**

`φ` reads a list element *together with* its membership proof in `L`, and `V` filters the
result; `W` filters the bare list elements.  If the two filters agree on every element of `L`,
the filtered lists agree. -/
theorem attach_map_filterMap {ι : Type*} {κ : Type*} {β : Type*} (L : List ι)
    (φ : {x // x ∈ L} → κ) (V : κ → Option β) (W : ι → Option β)
    (hVW : ∀ x (hx : x ∈ L), V (φ ⟨x, hx⟩) = W x) :
    (L.attach.map φ).filterMap V = L.filterMap W := by
  revert φ V W
  induction L with
  | nil => intro φ V W _; simp
  | cons a l ih =>
    intro φ V W hVW
    have hWa : V (φ ⟨a, List.mem_cons_self⟩) = W a := hVW a List.mem_cons_self
    have hmap : List.map φ (List.map (fun x : {x // x ∈ l} =>
        (⟨x.1, List.mem_cons_of_mem a x.2⟩ : {y // y ∈ a :: l})) l.attach)
        = List.map (fun x : {x // x ∈ l} => φ ⟨x.1, List.mem_cons_of_mem a x.2⟩) l.attach := by
      rw [List.map_map]
      refine List.map_congr_left ?_
      rintro ⟨x, hx⟩ _
      exact congrArg φ (Subtype.ext rfl)
    have hVW' : ∀ (x : ι) (hx : x ∈ l),
        V ((fun x : {x // x ∈ l} => φ ⟨x.1, List.mem_cons_of_mem a x.2⟩) ⟨x, hx⟩) = W x := by
      intro x hx
      exact hVW x (List.mem_cons_of_mem a hx)
    have ih' := ih (fun x : {x // x ∈ l} => φ ⟨x.1, List.mem_cons_of_mem a x.2⟩) V W hVW'
    rw [List.attach_cons, List.map_cons, List.filterMap_cons, List.filterMap_cons]
    rw [hmap, hWa]
    cases W a <;> simp [ih']

/-! ### The two alphabet maps of the band -/

/-- The generator map of `treeKill`, exposed: `treeKill` is the free-group lift of this map,
which sends a tree edge (trivial loop class) to `1` and any other window edge to itself. -/
noncomputable def treeKillGen (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) :
    ↥(winE c lo hi) → FreeGroup (winBeta Wt c lo hi) := by
  classical
  exact fun e => if h : coverClassAt Wt c (e : α × ℤ) = 1 then 1
    else FreeGroup.of ⟨(e : α × ℤ), e.2, h⟩

/-- `treeKill` is the lift of `treeKillGen`. -/
theorem treeKill_eq_lift (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) :
    treeKill Wt c lo hi = FreeGroup.lift (treeKillGen Wt c lo hi) := by
  unfold treeKill treeKillGen
  rfl

/-- The "delete the tree edges" operation, on the **window's** edge group: a tree letter is
deleted, a non-tree letter is kept as the corresponding letter of `winBeta Wt c lo hi`. -/
noncomputable def winBetaOpt (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) :
    ↥(winE c lo hi) × Bool → Option (winBeta Wt c lo hi × Bool) := by
  classical
  exact fun x => if h : coverClassAt Wt c (x.1 : α × ℤ) = 1 then none
    else some (⟨(x.1 : α × ℤ), x.1.2, h⟩, x.2)

/-- The "delete the tree edges" operation on the **decorated walk**: this is the filter of which
`betaKillList` is the `filterMap`. -/
noncomputable def decorBetaOpt (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) :
    (α × ℤ) × Bool → Option (winBeta Wt c lo hi × Bool) := by
  classical
  exact fun p => if hh : coverEdge p ∈ winE c lo hi ∧ coverClassAt Wt c (coverEdge p) ≠ 1
    then some (⟨coverEdge p, hh.1, hh.2⟩, p.2) else none

/-- `betaKillList` is the `filterMap` of `decorBetaOpt`. -/
theorem betaKillList_eq_filterMap (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ)
    (L : List ((α × ℤ) × Bool)) :
    betaKillList Wt c lo hi L = L.filterMap (decorBetaOpt Wt c lo hi) := by
  unfold betaKillList decorBetaOpt
  rfl

/-! ### The two pointwise comparisons -/

/-- A generator of `treeKill` is either `1` (tree edge) or the corresponding window letter, and
`winBetaOpt` records exactly which. -/
theorem treeKillGen_cond (Wt : ℤ → FreeGroup α) (c : α → ℤ) {lo hi : ℤ}
    (x : ↥(winE c lo hi) × Bool) :
    cond x.2 (treeKillGen Wt c lo hi x.1) (treeKillGen Wt c lo hi x.1)⁻¹
      = (winBetaOpt Wt c lo hi x).elim 1
          (fun y => cond y.2 (FreeGroup.of y.1) (FreeGroup.of y.1)⁻¹) := by
  classical
  by_cases hc : coverClassAt Wt c (x.1 : α × ℤ) = 1
  · rw [treeKillGen, dif_pos hc, winBetaOpt, dif_pos hc]
    simp
  · rw [treeKillGen, dif_neg hc, winBetaOpt, dif_neg hc]
    rfl

/-- Reading a decorated letter of the walk as a window letter and then applying `winBetaOpt` is
the same as applying `decorBetaOpt` to it: the window-membership proof `h` is irrelevant. -/
theorem winBetaOpt_comp (Wt : ℤ → FreeGroup α) (c : α → ℤ) {lo hi j : ℤ} (w : FreeGroup α)
    (h : ∀ p ∈ decor c j (wordOf w), coverEdge p ∈ winE c lo hi)
    (p : (α × ℤ) × Bool) (hp : p ∈ decor c j (wordOf w)) :
    winBetaOpt Wt c lo hi (⟨coverEdge p, h p hp⟩, p.2) = decorBetaOpt Wt c lo hi p := by
  classical
  by_cases hc : coverClassAt Wt c (coverEdge p) = 1
  · rw [winBetaOpt, dif_pos hc, decorBetaOpt, dif_neg (fun hh => hh.2 hc)]
  · rw [winBetaOpt, dif_neg hc, decorBetaOpt, dif_pos ⟨h p hp, hc⟩]

/-! ### The Tietze step -/

theorem treeKill_walkCell {α : Type*} (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi j : ℤ)
    (w : FreeGroup α)
    (h : ∀ p ∈ Work.OROneRel.decor c j (Work.OROneRel.wordOf w),
      Work.OROneRel.coverEdge p ∈ Work.OROneRel.winE c lo hi) :
    Work.OROneRel.treeKill Wt c lo hi (Work.OROneRel.walkCell c lo hi j w h) =
      Work.OROneRel.betaKill Wt c lo hi (Work.OROneRel.decor c j (Work.OROneRel.wordOf w)) := by
  classical
  -- the walk in the window's edge group, evaluated by `treeKill`
  have hL : treeKill Wt c lo hi (walkCell c lo hi j w h)
      = (List.map (fun x : ↥(winE c lo hi) × Bool =>
          cond x.2 (treeKillGen Wt c lo hi x.1) (treeKillGen Wt c lo hi x.1)⁻¹)
          (walkCellList c lo hi j w h)).prod := by
    rw [treeKill_eq_lift, walkCell]
    exact FreeGroup.lift_mk
  -- the walk with the tree traversals deleted, as a product
  have hR : betaKill Wt c lo hi (decor c j (wordOf w))
      = ((betaKillList Wt c lo hi (decor c j (wordOf w))).map
          (fun y => cond y.2 (FreeGroup.of y.1) (FreeGroup.of y.1)⁻¹)).prod := by
    unfold betaKill
    exact mk_eq_prod_cond _
  -- the tree letters of `walkCellList` are exactly the ones deleted by `betaKillList`
  have hfil : (walkCellList c lo hi j w h).filterMap (winBetaOpt Wt c lo hi)
      = betaKillList Wt c lo hi (decor c j (wordOf w)) := by
    rw [betaKillList_eq_filterMap]
    exact attach_map_filterMap (decor c j (wordOf w))
      (fun p => (⟨coverEdge p.1, h p.1 p.2⟩, p.1.2)) (winBetaOpt Wt c lo hi)
      (decorBetaOpt Wt c lo hi) (fun p hp => winBetaOpt_comp Wt c w h p hp)
  rw [hL, hR, prod_map_cond_eq_prod_filterMap (walkCellList c lo hi j w h)
    (treeKillGen Wt c lo hi) (winBetaOpt Wt c lo hi) (fun x => treeKillGen_cond Wt c x), hfil]

end Work.OROneRel
