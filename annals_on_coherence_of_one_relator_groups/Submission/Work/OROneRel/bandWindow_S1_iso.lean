import Mathlib
import Submission.Work.OROneRel.gateBookkeeping
import Submission.Work.OROneRel.bandCell
import Submission.Work.OROneRel.presentedGroup_treeDelete_iso
import Submission.Work.OROneRel.treeKill_walkCell_pow

/-!
# The band presentation of a window is the vertex presentation of its walk

**The `N = 1` vertex identification.**  For a window `[lo,hi]` of the `ℤ`-cover of the one-relator
complex `⟨α | u ^ l⟩`, the band's presentation — the window's full edge group `F(↥(winE c lo hi))`
together with the tree relators (`treeRel`) and the single walk `2`-cell `walkCell c lo hi 0 (u ^ l)`
at level `0` — is isomorphic to the *vertex* presentation `⟨winBeta | winRoot ^ l⟩` on the alphabet
of the non-tree edges of the window.

The proof assembles three already-available pieces:

1. `presentedGroup_treeDelete_iso` (Tietze, deleting the tree generators): for a set `T` of "tree"
   edges inside `winE c lo hi` and a word `w`, `⟨E | {of t : t ∈ T} ∪ {w}⟩ ≅ ⟨Tᶜ | {killsProj T w}⟩`.
   Here `T = winTreeSub Wt c lo hi`, the window's tree read inside its edge set, and `treeRel` is
   exactly `{of t : t ∈ T}` (`hset`).
2. `winTreeBetaEquiv : ↥(Tᶜ) ≃ winBeta Wt c lo hi` identifies the surviving letters with the
   vertex alphabet (`winTreeSub = winTree Wt c lo hi` read inside `↥(winE c lo hi)`); Mathlib's
   `PresentedGroup.equivPresentedGroup` transports the presentation along it.
3. The key computation `freeGroup_map_winTreeBetaEquiv_comp_killsProj` shows that transporting
   `killsProj T` along this identification is `treeKill` (the map of `bandCell.lean` killing the
   tree edges and fixing the others), so the transported relator is
   `treeKill (walkCell …) = winRoot Wt c lo hi u ^ l` (`treeKill_walkCell_pow`, using that the walk
   of `u` returns to level `0` because `cohom c u = 1`).
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-! ## The window's tree inside the window's edge set, and the two alphabets -/

/-- **The window's tree, as a subset of the window's edge set.**  An edge of `winE c lo hi` is a
"tree edge" when its loop class is trivial, i.e. when it lies in `winTree Wt c lo hi`. -/
def winTreeSub (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) : Set ↥(winE c lo hi) :=
  {e | (e : α × ℤ) ∈ winTree Wt c lo hi}

@[simp] theorem mem_winTreeSub {Wt : ℤ → FreeGroup α} {c : α → ℤ} {lo hi : ℤ}
    {e : ↥(winE c lo hi)} :
    e ∈ winTreeSub Wt c lo hi ↔ (e : α × ℤ) ∈ winTree Wt c lo hi := Iff.rfl

/-- **The two alphabets agree.**  The complement of the window's tree inside the window's edge set is
canonically the alphabet `winBeta Wt c lo hi` of the non-tree edges of the window: both are given by
the same underlying edge `α × ℤ` with the same two proofs (membership in `winE`, non-triviality of
the loop class). -/
def winTreeBetaEquiv (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) :
    ↥((winTreeSub Wt c lo hi)ᶜ) ≃ winBeta Wt c lo hi where
  toFun s :=
    ⟨(s.1 : α × ℤ), s.1.2, fun hc => s.2 (mem_winTreeSub.mpr (mem_winTree.mpr ⟨s.1.2, hc⟩))⟩
  invFun b := ⟨⟨b.1, b.2.1⟩, fun h => b.2.2 (mem_winTree.mp h).2⟩
  left_inv s := Subtype.ext (Subtype.ext rfl)
  right_inv b := Subtype.ext rfl

@[simp] theorem winTreeBetaEquiv_apply (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ)
    (s : ↥((winTreeSub Wt c lo hi)ᶜ)) :
    (winTreeBetaEquiv Wt c lo hi s).1 = (s.1 : α × ℤ) := rfl

/-! ## `killsProj` on generators, and the gate to `treeKill` -/

/-- **`killsProj` kills a tree generator.** -/
theorem killsProj_of_mem {E : Type u} (T : Set E) {e : E} (h : e ∈ T) :
    killsProj T (FreeGroup.of e) = 1 := by
  classical
  rw [killsProj, FreeGroup.lift_apply_of, dif_pos h]

/-- **`killsProj` fixes the other generators.** -/
theorem killsProj_of_notMem {E : Type u} (T : Set E) {e : E} (h : e ∉ T) :
    killsProj T (FreeGroup.of e) = FreeGroup.of ⟨e, h⟩ := by
  classical
  rw [killsProj, FreeGroup.lift_apply_of, dif_neg h]

/-- **The gate between the two alphabets.**  Transporting the tree-killing map `killsProj T` (which
lands in the free group on the *complement* of the window's tree) along the identification
`winTreeBetaEquiv : Tᶜ ≃ winBeta` is exactly `treeKill`, the map of `bandCell.lean` which sends a
tree edge to `1` and a non-tree edge to itself. -/
theorem freeGroup_map_winTreeBetaEquiv_comp_killsProj (Wt : ℤ → FreeGroup α) (c : α → ℤ)
    (lo hi : ℤ) :
    (FreeGroup.map (winTreeBetaEquiv Wt c lo hi :
        ↥((winTreeSub Wt c lo hi)ᶜ) → winBeta Wt c lo hi)).comp
        (killsProj (winTreeSub Wt c lo hi)) = treeKill Wt c lo hi := by
  classical
  apply FreeGroup.ext_hom
  intro e
  rw [MonoidHom.comp_apply]
  by_cases hW : (e : α × ℤ) ∈ winTree Wt c lo hi
  · have hT : e ∈ winTreeSub Wt c lo hi := mem_winTreeSub.mpr hW
    rw [killsProj_of_mem _ hT, map_one, treeKill_of_tree Wt c hW]
  · have hT : e ∉ winTreeSub Wt c lo hi := fun h => hW (mem_winTreeSub.mp h)
    rw [killsProj_of_notMem _ hT, FreeGroup.map.of, treeKill_of_notMem Wt c hW]
    exact congrArg FreeGroup.of (Subtype.ext rfl)

theorem bandWindow_S1_iso {α : Type*} (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ)
    (u : FreeGroup α) (l : ℕ)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (hcu : Work.OROneRel.cohom c u = 1)
    (hwin : ∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf (u ^ l)),
      Work.OROneRel.coverEdge p ∈ Work.OROneRel.winE c lo hi) :
    Nonempty (PresentedGroup (Work.OROneRel.treeRel Wt c lo hi ∪
        {Work.OROneRel.walkCell c lo hi 0 (u ^ l) hwin})
      ≃* PresentedGroup ({Work.OROneRel.winRoot Wt c lo hi u ^ l} :
        Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi)))) := by
  classical
  -- the `treeRel` relators are precisely the generators of the window's tree
  have hset : Work.OROneRel.treeRel Wt c lo hi ∪
        {Work.OROneRel.walkCell c lo hi 0 (u ^ l) hwin}
      = {x : FreeGroup ↥(Work.OROneRel.winE c lo hi) |
          (∃ t : ↥(Work.OROneRel.winTreeSub Wt c lo hi),
              x = FreeGroup.of (t : ↥(Work.OROneRel.winE c lo hi))) ∨
            x = Work.OROneRel.walkCell c lo hi 0 (u ^ l) hwin} := by
    ext x
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_singleton_iff, Work.OROneRel.treeRel]
    constructor
    · rintro (⟨e, he, rfl⟩ | h)
      · exact Or.inl ⟨⟨e, he⟩, rfl⟩
      · exact Or.inr h
    · rintro (⟨t, rfl⟩ | h)
      · exact Or.inl ⟨t.1, t.2, rfl⟩
      · exact Or.inr h
  -- the Tietze step deleting the tree generators, then the transport along `winTreeBetaEquiv`
  obtain ⟨φ⟩ := Work.OROneRel.presentedGroup_treeDelete_iso
    (Work.OROneRel.winTreeSub Wt c lo hi) (Work.OROneRel.walkCell c lo hi 0 (u ^ l) hwin)
  have ψ := PresentedGroup.equivPresentedGroup
    ({Work.OROneRel.killsProj (Work.OROneRel.winTreeSub Wt c lo hi)
        (Work.OROneRel.walkCell c lo hi 0 (u ^ l) hwin)} :
      Set (FreeGroup ↥((Work.OROneRel.winTreeSub Wt c lo hi)ᶜ)))
    (Work.OROneRel.winTreeBetaEquiv Wt c lo hi)
  -- the transported relator is the vertex relator
  have hmap : FreeGroup.freeGroupCongr (Work.OROneRel.winTreeBetaEquiv Wt c lo hi)
        (Work.OROneRel.killsProj (Work.OROneRel.winTreeSub Wt c lo hi)
          (Work.OROneRel.walkCell c lo hi 0 (u ^ l) hwin))
      = Work.OROneRel.winRoot Wt c lo hi u ^ l := by
    rw [FreeGroup.freeGroupCongr_apply]
    exact (DFunLike.congr_fun
      (Work.OROneRel.freeGroup_map_winTreeBetaEquiv_comp_killsProj Wt c lo hi) _).trans
      (Work.OROneRel.treeKill_walkCell_pow Wt c lo hi u l hcyc hcu hwin)
  have himg : FreeGroup.freeGroupCongr (Work.OROneRel.winTreeBetaEquiv Wt c lo hi) ''
        ({Work.OROneRel.killsProj (Work.OROneRel.winTreeSub Wt c lo hi)
            (Work.OROneRel.walkCell c lo hi 0 (u ^ l) hwin)} :
          Set (FreeGroup ↥((Work.OROneRel.winTreeSub Wt c lo hi)ᶜ)))
      = ({Work.OROneRel.winRoot Wt c lo hi u ^ l} :
          Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi))) := by
    rw [Set.image_singleton, hmap]
  rw [himg] at ψ
  refine ⟨?_⟩
  rw [hset]
  exact φ.trans ψ

end Work.OROneRel
