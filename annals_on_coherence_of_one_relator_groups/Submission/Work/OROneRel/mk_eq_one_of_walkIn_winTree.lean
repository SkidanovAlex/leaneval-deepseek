import Mathlib
import Submission.Work.OROneRel.delWordDefs
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.GaugeDefs
import Submission.Work.OROneRel.gauge_truncation
import Submission.Work.OROneRel.coverRootDefs
import Submission.Work.OROneRel.coverCoedgeDefs

/-!
# A closed walk inside the tree of the window spells the trivial word

Let `Wt : ℤ → FreeGroup α` be a gauge and `c : α → ℤ` a weight.  The tree of the window `[lo,hi]` is
`winTree Wt c lo hi = {e ∈ winE c lo hi | coverClassAt Wt c e = 1}`, i.e. the edges of the window of
trivial loop class.  If a word `L` is such that the walk of `L` started at the level `a` uses only
edges of the tree, and `L` has vanishing total weight, then `L` spells the trivial element of
`F α`.

Indeed the telescoping identity `gauge_decor` computes the image of the decorated walk under the
gauge map as

`gaugeMap Wt c (mk (decor c a L)) = Wt a * mk L * (Wt (a + lsig c L))⁻¹`,

while `gaugeMap Wt c (mk (decor c a L)) = List.prod ((decor c a L).map (coverClass Wt c))`
(`FreeGroup.lift_mk`): the product of the loop classes of the traversals.  Each traversal has tree
edge, hence trivial loop class, so the product is `1`; with `lsig c L = 0` the telescoping identity
then gives `Wt a * mk L * (Wt a)⁻¹ = 1` and `mk L = 1`.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- The gauge map of a decorated walk is the product of the loop classes of its traversals. -/
theorem gaugeMap_mk_decor_eq_prod (W : ℤ → FreeGroup α) (c : α → ℤ) (a : ℤ)
    (L : List (α × Bool)) :
    gaugeMap W c (FreeGroup.mk (decor c a L)) = ((decor c a L).map (coverClass W c)).prod := by
  rw [gaugeMap, FreeGroup.lift_mk]
  congr 1
  apply List.map_congr_left
  intro q _
  rw [coverClass]
  cases q.2 <;> simp [gaugeMap_of]

/-- **A walk inside the tree has gauge image `1`.**  If every traversal of the walk of `L` from the
level `a` has an edge of trivial loop class, the product of the loop classes of its traversals — the
gauge image of the decorated walk — is trivial. -/
theorem gaugeMap_mk_decor_eq_one (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (a : ℤ)
    (L : List (α × Bool)) (hw : WalkIn c (winTree Wt c lo hi) a L) :
    gaugeMap Wt c (FreeGroup.mk (decor c a L)) = 1 := by
  rw [gaugeMap, FreeGroup.lift_mk]
  apply List.prod_eq_one
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨q, hq, rfl⟩ := hx
  have hq' : coverClassAt Wt c (coverEdge q) = 1 := (mem_winTree.mp (hw q hq)).2
  have hA : Wt q.1.2 * FreeGroup.of q.1.1 * (Wt (q.1.2 + c q.1.1))⁻¹ = 1 := by
    rw [← gaugeMap_of]
    exact hq'
  cases q.2 <;> simp [hA]

theorem mk_eq_one_of_walkIn_winTree {α : Type u} (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (a : ℤ) (L : List (α × Bool)) (hw : Work.OROneRel.WalkIn c (Work.OROneRel.winTree Wt c lo hi) a L) (h0 : Work.OROneRel.lsig c L = 0) : FreeGroup.mk L = 1 := by
  have hgm : gaugeMap Wt c (FreeGroup.mk (decor c a L)) = 1 :=
    gaugeMap_mk_decor_eq_one Wt c lo hi a L hw
  rw [gauge_decor, h0, add_zero] at hgm
  have h := congrArg (fun z => (Wt a)⁻¹ * z * Wt a) hgm
  rw [show (Wt a)⁻¹ * (Wt a * FreeGroup.mk L * (Wt a)⁻¹) * Wt a = FreeGroup.mk L from by group] at h
  simpa using h

end Work.OROneRel
