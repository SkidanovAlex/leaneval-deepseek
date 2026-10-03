import Mathlib
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.gauge_truncation
import Submission.Work.OROneRel.filterMap_map_prod

/-!
# The telescoping identity `winRho (winRoot) = u` of the window decomposition

This file proves `Work.OROneRel.winRho_winRoot`: for a weight `c : α → ℤ` with `cohom c u = 1`, a
gauge `Wt : ℤ → FreeGroup α` with `Wt 0 = 1`, and a window `[lo,hi]` containing (both endpoints of)
every edge traversed by the walk of `u` (`hwin`), the class map of the vertex `winRho` sends the
deleted walk word `winRoot` (the traversals of the walk of `u` whose edge lies in the window and has
non-trivial loop class, indexed by their *edge* and carrying the *sign* of their traversal) to `u`
itself.

## The argument

Write `D = decor c 0 (wordOf u)` for the decorated walk of `u` and
`β = winBeta Wt c lo hi` for the alphabet of non-tree edges of the window.  Every decorated letter
`p = ((x,i),b)` contributes the sign-corrected class

`coverClass Wt c p = coverClassAt Wt c (coverEdge p) ^ (sign b)`

(`coverClass_eq_ite`), and the telescoping identity `GaugeDefs.gauge_decor_zero` says that the
product of these contributions over *all* of `D` is `u`.  Since by `hwin` each edge of `D` lies in
the window, `winRootList` keeps exactly the letters of `D` of non-trivial loop class; the letters it
drops contribute `1`, so the product is unchanged.  That step is the general list identity
`filterMap_map_prod`, applied through the step function `winRootStep` of `winRootList`
(`winRootList_eq`), together with the sign computation `winRootStep_elim_eq`.  Finally
`winRho (mk L)` is the product of the class images of the letters of `L`
(`gauge_truncation.map_prod_eq_of_mk`), which converts the product over `β` back into the value of
`winRho` at `winRoot`.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-! ## The step function of `winRootList` -/

/-- The function whose `filterMap` is `winRootList`: a decorated letter is kept -- with the sign of
its traversal -- exactly if its edge lies in the window and has non-trivial loop class. -/
noncomputable def winRootStep (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) :
    ((α × ℤ) × Bool) → Option (winBeta Wt c lo hi × Bool) := by
  classical
  exact fun p => if h : coverEdge p ∈ winE c lo hi ∧ coverClassAt Wt c (coverEdge p) ≠ 1
    then some (⟨coverEdge p, h.1, h.2⟩, p.2) else none

/-- `winRootList` is the `filterMap` of `winRootStep`. -/
theorem winRootList_eq (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (u : FreeGroup α) :
    winRootList Wt c lo hi u
      = (decor c 0 (wordOf u)).filterMap (winRootStep Wt c lo hi) := by
  classical
  unfold winRootList winRootStep
  rfl

/-- `winRoot` is the word spelled by `winRootList` -- the defining equation of `winRoot`, stated with
`winRootList` replaced by its `filterMap` description. -/
theorem winRoot_eq (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (u : FreeGroup α) :
    winRoot Wt c lo hi u
      = FreeGroup.mk ((decor c 0 (wordOf u)).filterMap (winRootStep Wt c lo hi)) := by
  simp only [winRoot, winRootList_eq]

/-- The value of `winRootStep` on a decorated letter whose edge lies in the window and has
non-trivial loop class. -/
theorem winRootStep_of (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (p : (α × ℤ) × Bool)
    (hp : coverEdge p ∈ winE c lo hi) (hcl : coverClassAt Wt c (coverEdge p) ≠ 1) :
    winRootStep Wt c lo hi p = some (⟨coverEdge p, hp, hcl⟩, p.2) := by
  classical
  unfold winRootStep
  rw [dif_pos ⟨hp, hcl⟩]

/-- The value of `winRootStep` on a decorated letter of trivial loop class (whose edge nevertheless
lies in the window). -/
theorem winRootStep_none (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (p : (α × ℤ) × Bool)
    (hcl : coverClassAt Wt c (coverEdge p) = 1) :
    winRootStep Wt c lo hi p = none := by
  classical
  unfold winRootStep
  rw [dif_neg (by rintro ⟨-, h2⟩; exact h2 hcl)]

/-! ## The sign conventions -/

/-- `winRho` of a sign-corrected generator is the sign-corrected loop class of its edge. -/
theorem winRho_of_signed (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (e : winBeta Wt c lo hi)
    (b : Bool) :
    winRho Wt c lo hi (if b then FreeGroup.of e else (FreeGroup.of e)⁻¹)
      = if b then coverClassAt Wt c e.1 else (coverClassAt Wt c e.1)⁻¹ := by
  cases b <;> simp

/-- The loop class of a decorated letter is the sign-corrected loop class of its edge. -/
theorem coverClass_eq_ite (Wt : ℤ → FreeGroup α) (c : α → ℤ) (p : (α × ℤ) × Bool) :
    coverClass Wt c p = if p.2 then coverClassAt Wt c p.1 else (coverClassAt Wt c p.1)⁻¹ := by
  obtain ⟨⟨a, i⟩, b⟩ := p
  cases b <;> simp [coverClass, coverClassAt, gaugeMap_of, map_inv]

/-! ## The pointwise comparison -/

/-- **The contribution of a decorated letter.**  If the edge of `p` lies in the window, then the
`β`-word `winRootStep` attaches to `p` (with the sign of the traversal) is mapped by `winRho` to the
loop class of `p`, or to `1` if `p` is deleted. -/
theorem winRootStep_elim_eq (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (p : (α × ℤ) × Bool)
    (hp : coverEdge p ∈ winE c lo hi) :
    (winRootStep Wt c lo hi p).elim (1 : FreeGroup α)
        (fun q => winRho Wt c lo hi (if q.2 then FreeGroup.of q.1 else (FreeGroup.of q.1)⁻¹))
      = coverClass Wt c p := by
  classical
  by_cases hcl : coverClassAt Wt c (coverEdge p) ≠ 1
  · rw [winRootStep_of Wt c lo hi p hp hcl]
    refine (winRho_of_signed Wt c lo hi ⟨coverEdge p, hp, hcl⟩ p.2).trans ?_
    rw [coverClass_eq_ite]
    rfl
  · have hcl1 : coverClassAt Wt c p.1 = 1 := not_not.mp hcl
    rw [winRootStep_none Wt c lo hi p hcl1]
    show (1 : FreeGroup α) = coverClass Wt c p
    rw [coverClass_eq_ite, hcl1]
    cases hb : p.2 <;> simp

/-! ## The product over the deleted walk word -/

/-- **The product of the class images of the deleted walk word.**  If every edge of the decorated
list `l` lies in the window, then the product of the `winRho`-images of the letters of the deleted
word is the product of the loop classes of the letters of `l`.

The `filterMap` is converted into a `map` by the general list identity
`Work.OROneRel.filterMap_map_prod` (delegated, `Submission/Work/OROneRel/filterMap_map_prod.lean`),
after which the comparison is pointwise (`winRootStep_elim_eq`). -/
theorem winRootList_prod_eq (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ)
    (l : List ((α × ℤ) × Bool)) (hl : ∀ p ∈ l, coverEdge p ∈ winE c lo hi) :
    ((l.filterMap (winRootStep Wt c lo hi)).map
        (fun q => winRho Wt c lo hi (if q.2 then FreeGroup.of q.1 else (FreeGroup.of q.1)⁻¹))).prod
      = (l.map (fun p => coverClass Wt c p)).prod := by
  classical
  have hmap : List.map (fun d => (winRootStep Wt c lo hi d).elim (1 : FreeGroup α)
        (fun q => winRho Wt c lo hi (if q.2 then FreeGroup.of q.1 else (FreeGroup.of q.1)⁻¹))) l
      = List.map (fun p => coverClass Wt c p) l :=
    List.map_congr_left (fun p hp => winRootStep_elim_eq Wt c lo hi p (hl p hp))
  rw [filterMap_map_prod, hmap]

/-! ## The telescoping identity -/

theorem winRho_winRoot {α : Type*} {c : α → ℤ} {u : FreeGroup α} (Wt : ℤ → FreeGroup α)
    (hW0 : Wt 0 = 1) (hu : Work.OROneRel.cohom c u = 1) (lo hi : ℤ)
    (hwin : ∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
      Work.OROneRel.coverEdge p ∈ Work.OROneRel.winE c lo hi) :
    Work.OROneRel.winRho Wt c lo hi (Work.OROneRel.winRoot Wt c lo hi u) = u := by
  classical
  rw [winRoot_eq]
  rw [(map_prod_eq_of_mk (winRho Wt c lo hi)
    ((decor c 0 (wordOf u)).filterMap (winRootStep Wt c lo hi))).symm]
  rw [winRootList_prod_eq Wt c lo hi (decor c 0 (wordOf u)) hwin]
  simp only [coverClass]
  rw [map_prod_eq_of_mk (gaugeMap Wt c) (decor c 0 (wordOf u))]
  exact gauge_decor_zero Wt hW0 hu

end Work.OROneRel
