import Mathlib
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.GaugeDefs
import Submission.Work.OROneRel.exists_globalGauge_of_windowData
import Submission.Work.OROneRel.reflectData

/-!
# The global gauge extending a window gauge: the companion for a negative `x₀`-step

This file proves `Work.OROneRel.exists_globalGauge_of_windowData_neg`, the companion of
`Work.OROneRel.exists_globalGauge_of_windowData` in which the `x₀`-step is allowed to have *negative*
weight: the hypothesis `0 < c x₀` of the positive statement is replaced by `c x₀ ≠ 0` (and
`c x₀ ≤ hi - lo` by `|c x₀| ≤ hi - lo`).

## The reduction

The level graph of the weight `-c` is the reflection of the level graph of `c`: the map
`(x, i) ↦ (x, -i)` (`reflEdge`) carries

* the walk of a word at level `0` for the weight `-c` to its reflection at level `0` for `c`
  (`decor_neg_zero`),
* the window `[lo, hi]` of `-c` to the window `[-hi, -lo]` of `c` (`mem_winE_neg`),
* the loop class of an edge under the gauge `j ↦ Wt (-j)` to the loop class of the reflected edge
  under the gauge `Wt` (`coverClassAt_neg`), hence `winTree` to `winTree`,

and `cohom (-c) = (cohom c)⁻¹` (`cohom_neg`).  Consequently, if `c x₀ < 0`, then putting
`c' = -c`, `lo' = -hi`, `hi' = -lo` and `Wt' j = Wt (-j)`, the data `(c', Wt', lo', hi', x₀)` satisfy
the hypotheses of the *positive* theorem: `0 < c' x₀`, `c' x₀ = |c x₀| ≤ hi - lo = hi' - lo'`, the
gauge condition `cohom c' (Wt' i) = ofAdd i`, and the tree condition (`winTree_refl_transfer`).  The
positive theorem then produces the reflected global gauge `V`, and `j ↦ V (-j)` is the required
global gauge for `c`.  If `c x₀ > 0` the positive theorem applies directly.

## Contents

* `cohom_neg_inv` -- the inverse form `cohom c w = (cohom (-c) w)⁻¹` of `cohom_neg`;
* `coverClassAt_reflectGauge` -- the loop class of an edge under the reflected gauge is the loop
  class of the reflected edge under the gauge;
* `coverClassAt_reflGauge_reflected` -- and the mirror identity, used to reflect `winTree`;
* `mem_winTree_reflEdge` -- `winTree` of the reflected data is the reflection of `winTree`;
* `winTree_refl_transfer` -- hence the tree hypothesis of the window reflects into the tree
  hypothesis of the reflected window, in the direction needed here.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-! ## The reflection of the cohomological class -/

/-- The inverse form of `cohom_neg`: the class of a word for the weight `c` is the inverse of its
class for the negated weight `-c`. -/
theorem cohom_neg_inv (c : α → ℤ) (w : FreeGroup α) :
    cohom c w = (cohom (fun a => -c a) w)⁻¹ := by
  have h := cohom_neg c w
  have h2 := congrArg (fun z : Multiplicative ℤ => z⁻¹) h
  simpa using h2.symm

/-! ## The reflection of the loop classes -/

/-- **The loop class under the reflected gauge**: reading the edge `e` at the weight `c` with the
gauge `j ↦ Wt (-j)` gives the loop class of the reflected edge `reflEdge e` at the weight `-c` with
the gauge `Wt`. -/
theorem coverClassAt_reflectGauge (Wt : ℤ → FreeGroup α) (c : α → ℤ) (e : α × ℤ) :
    coverClassAt (fun j => Wt (-j)) c e = coverClassAt Wt (fun a => -c a) (reflEdge e) := by
  have h := coverClassAt_neg Wt c (reflEdge e)
  rw [reflEdge_invol] at h
  exact h.symm

/-- **The mirrored identity**: reading the reflected edge at the weight `-c` with the reflected gauge
gives the loop class of the edge at the weight `c` with the gauge `Wt`. -/
theorem coverClassAt_reflGauge_reflected (Wt : ℤ → FreeGroup α) (c : α → ℤ) (e : α × ℤ) :
    coverClassAt (fun j => Wt (-j)) (fun a => -c a) (reflEdge e) = coverClassAt Wt c e := by
  have h := coverClassAt_reflEdge_neg (fun m : ℤ => Wt (-m)) c e
  have hfun : (fun j : ℤ => (fun m : ℤ => Wt (-m)) (-j)) = Wt := by
    funext j
    simp
  rw [hfun] at h
  exact h

/-- **The tree of the reflected window.**  The reflected edge `reflEdge e` is a tree edge of the
window `[-hi, -lo]` of the weight `-c` for the reflected gauge `j ↦ Wt (-j)` exactly when `e` is a
tree edge of the window `[lo, hi]` of the weight `c` for the gauge `Wt`. -/
theorem mem_winTree_reflEdge (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (e : α × ℤ) :
    reflEdge e ∈ winTree (fun j => Wt (-j)) (fun a => -c a) (-hi) (-lo) ↔
      e ∈ winTree Wt c lo hi := by
  have hE : reflEdge e ∈ winE (fun a => -c a) (-hi) (-lo) ↔ e ∈ winE c lo hi := by
    rw [mem_winE_reflEdge (c := c) (lo := -hi) (hi := -lo)]
    simp
  have hC : coverClassAt (fun j => Wt (-j)) (fun a => -c a) (reflEdge e)
      = coverClassAt Wt c e := coverClassAt_reflGauge_reflected Wt c e
  rw [mem_winTree, mem_winTree, hE, hC]

/-! ## The reflection of the tree hypothesis -/

/-- **The tree hypothesis reflects**, in the direction needed to reduce a window whose `x₀`-step has
negative weight to the positive case.  If the walk of `Wt k` (`lo ≤ k ≤ hi`) uses only tree edges of
the window `[lo, hi]` for the weight `c`, then the walk of `Wt (-i)` (`-hi ≤ i ≤ -lo`) uses only tree
edges of the reflected window `[-hi, -lo]` for the weight `-c` and the reflected gauge
`j ↦ Wt (-j)`. -/
theorem winTree_refl_transfer {α : Type*} (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ)
    (h : ∀ i : ℤ, lo ≤ i → i ≤ hi → ∀ e ∈ Work.OROneRel.decor c 0
        (Work.OROneRel.wordOf (Wt i)),
      Work.OROneRel.coverEdge e ∈ Work.OROneRel.winTree Wt c lo hi) :
    ∀ i : ℤ, -hi ≤ i → i ≤ -lo → ∀ e ∈ Work.OROneRel.decor (fun a => -c a) 0
        (Work.OROneRel.wordOf (Wt (-i))),
      Work.OROneRel.coverEdge e ∈
        Work.OROneRel.winTree (fun j => Wt (-j)) (fun a => -c a) (-hi) (-lo) := by
  intro i h1 h2 e he
  rw [decor_neg_zero c (wordOf (Wt (-i)))] at he
  obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
  have h' := h (-i) (by omega) (by omega) e' he'
  simpa using (mem_winTree_reflEdge Wt c lo hi (coverEdge e')).mpr h'

theorem exists_globalGauge_of_windowData_neg {α : Type*} [DecidableEq α]
    (c : α → ℤ) (Wt : ℤ → FreeGroup α) (lo hi : ℤ) (x₀ : α)
    (hlo : lo ≤ 0) (hhi : 0 ≤ hi)
    (hcx : c x₀ ≠ 0) (hd : |c x₀| ≤ hi - lo)
    (hW0 : Wt 0 = 1)
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom c (Wt i) = Multiplicative.ofAdd i)
    (htree : ∀ i : ℤ, lo ≤ i → i ≤ hi →
      ∀ e ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge e ∈ Work.OROneRel.winTree Wt c lo hi) :
    ∃ Wt' : ℤ → FreeGroup α,
      (∀ i : ℤ, lo ≤ i → i ≤ hi → Wt' i = Wt i) ∧
      (∀ i : ℤ, Work.OROneRel.cohom c (Wt' i) = Multiplicative.ofAdd i) ∧
      (∀ j : ℤ, ∀ e ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf (Wt' j)),
        Work.OROneRel.coverClassAt Wt' c (Work.OROneRel.coverEdge e) = 1) := by
  rcases lt_trichotomy (c x₀) 0 with hneg | hzero | hpos
  · -- ### the step `x₀` has negative weight: reflect the level line
    have hle : (fun a => -c a) x₀ ≤ (-lo) - (-hi) := by
      have h := hd
      rw [abs_of_neg hneg] at h
      have hbeta : (fun a => -c a) x₀ = -c x₀ := rfl
      rw [hbeta]
      linarith
    have hcoh' : ∀ i : ℤ, cohom (fun a => -c a) ((fun j : ℤ => Wt (-j)) i)
        = Multiplicative.ofAdd i := by
      intro i
      show cohom (fun a => -c a) (Wt (-i)) = Multiplicative.ofAdd i
      rw [cohom_neg, hcoh (-i), ← ofAdd_neg, neg_neg]
    have htree' : ∀ i : ℤ, (-hi) ≤ i → i ≤ (-lo) →
        ∀ e ∈ decor (fun a => -c a) 0 (wordOf ((fun j : ℤ => Wt (-j)) i)),
          coverEdge e ∈ winTree (fun j : ℤ => Wt (-j)) (fun a => -c a) (-hi) (-lo) :=
      fun i h1 h2 => winTree_refl_transfer Wt c lo hi htree i h1 h2
    obtain ⟨V, hag, hcohV, htrivV⟩ :=
      exists_globalGauge_of_windowData (fun a => -c a) (fun j : ℤ => Wt (-j)) (-hi) (-lo) x₀
        (by omega) (by omega) (by simpa using hneg) hle (by simpa using hW0) hcoh' htree'
    refine ⟨fun j => V (-j), ?_, ?_, ?_⟩
    · -- agreement on the window `[lo,hi]`
      intro i h1 h2
      have h := hag (-i) (by omega) (by omega)
      simpa using h
    · -- the reflected gauge is a gauge for `c`
      intro j
      rw [cohom_neg_inv, hcohV (-j), ← ofAdd_neg, neg_neg]
    · -- every walk of the reflected gauge is trivial
      intro j e he
      have hmem : reflSym e ∈ decor (fun a => -c a) 0 (wordOf (V (-j))) := by
        rw [decor_neg_zero]
        exact List.mem_map.mpr ⟨e, he, rfl⟩
      have htriv := htrivV (-j) (reflSym e) hmem
      rw [coverEdge_reflSym] at htriv
      rw [coverClassAt_reflectGauge V c (coverEdge e)]
      exact htriv
  · exact absurd hzero hcx
  · -- ### the step `x₀` has positive weight: the positive theorem applies as it stands
    refine exists_globalGauge_of_windowData c Wt lo hi x₀ hlo hhi hpos ?_ hW0 hcoh htree
    have h := hd
    rwa [abs_of_pos hpos] at h

end Work.OROneRel
