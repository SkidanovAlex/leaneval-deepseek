import Mathlib
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.winRho_winRoot

/-!
# Casting the window alphabet `β` along a gauge that agrees on the window

Let `c : α → ℤ` be a weight, `lo hi : ℤ` a window, and `Wt Wt' : ℤ → FreeGroup α` two gauges whose
loop classes agree on every edge of the window:

`hband : ∀ e ∈ winE c lo hi, coverClassAt Wt' c e = coverClassAt Wt c e`.

Then the two window alphabets `winBeta Wt c lo hi` and `winBeta Wt' c lo hi` -- the non-tree edges of
the window, i.e. the edges `e ∈ winE c lo hi` with `coverClassAt _ c e ≠ 1` -- have the *same*
underlying set of edges, so there is a canonical bijection `φ` between them (the identity on the
underlying pair `e : α × ℤ`), with inverse `ψ`.  This file proves that this bijection is compatible
with the whole vertex datum of the window:

* `FreeGroup.map ψ (FreeGroup.map φ x) = x` for all `x ∈ F (β)`;
* `winRho Wt' c lo hi (FreeGroup.map φ x) = winRho Wt c lo hi x` for all `x` (the class maps
  intertwine `φ`, because they agree on generators by `hband`);
* `FreeGroup.map φ (winRoot Wt c lo hi u) = winRoot Wt' c lo hi u` for all `u` (the deleted walk
  word is transported: `winRootList` keeps an edge of the walk of `u` exactly when the edge lies in
  the window and has non-trivial loop class, a condition which is the same for `Wt` and `Wt'`, and
  the surviving generators are matched on the nose by `φ`).

The last point is the reason for the hypothesis: `winRoot Wt c lo hi u` is an element of
`F (winBeta Wt c lo hi)`, a group that depends on the gauge, so comparing the walk words of two
gauges requires casting the alphabet.  The comparison is done on the level of the *lists* of
decorated letters (`winRootList`), through `winRootStep`, `List.map_filterMap` and
`FreeGroup.map.mk`.
-/

namespace Work.OROneRel

/-- The step function of `winRootList` is `none` at a decorated letter whose edge lies outside the
window (then the first conjunct in its `if` already fails). -/
theorem winRootStep_none_of_not_mem {α : Type*} {Wt : ℤ → FreeGroup α} {c : α → ℤ} {lo hi : ℤ}
    {p : (α × ℤ) × Bool} (h : coverEdge p ∉ winE c lo hi) :
    winRootStep Wt c lo hi p = none := by
  classical
  unfold winRootStep
  rw [dif_neg (fun hh : coverEdge p ∈ winE c lo hi ∧ coverClassAt Wt c (coverEdge p) ≠ 1 =>
    h hh.1)]

theorem betaCast_spec {α : Type*} {Wt Wt' : ℤ → FreeGroup α} {c : α → ℤ} {lo hi : ℤ}
    (hband : ∀ e ∈ winE c lo hi, coverClassAt Wt' c e = coverClassAt Wt c e) :
    ∃ (φ : winBeta Wt c lo hi → winBeta Wt' c lo hi) (ψ : winBeta Wt' c lo hi → winBeta Wt c lo hi),
      (∀ x : FreeGroup (winBeta Wt c lo hi), FreeGroup.map ψ (FreeGroup.map φ x) = x) ∧
      (∀ x : FreeGroup (winBeta Wt c lo hi),
        winRho Wt' c lo hi (FreeGroup.map φ x) = winRho Wt c lo hi x) ∧
      (∀ u : FreeGroup α, FreeGroup.map φ (winRoot Wt c lo hi u) = winRoot Wt' c lo hi u) := by
  classical
  -- the two alphabets have the same underlying pair, so `φ` and `ψ` are the identity on values
  let φ : winBeta Wt c lo hi → winBeta Wt' c lo hi := fun e =>
    ⟨e.1, e.2.1, fun h => e.2.2 ((hband e.1 e.2.1).symm.trans h)⟩
  let ψ : winBeta Wt' c lo hi → winBeta Wt c lo hi := fun e =>
    ⟨e.1, e.2.1, fun h => e.2.2 ((hband e.1 e.2.1).trans h)⟩
  have hψφ : ∀ e, ψ (φ e) = e := fun e => Subtype.ext rfl
  refine ⟨φ, ψ, ?_, ?_, ?_⟩
  · -- `ψ ∘ φ = id` on generators, hence `map ψ (map φ x) = x`
    intro x
    rw [FreeGroup.map.comp]
    have hcomp : ψ ∘ φ = id := funext fun e => hψφ e
    rw [hcomp, FreeGroup.map.id]
  · -- the class maps intertwine `φ`, since they agree on the generators of `β`
    intro x
    have hhom : (winRho Wt' c lo hi).comp (FreeGroup.map φ) = winRho Wt c lo hi := by
      refine FreeGroup.ext_hom _ _ fun e => ?_
      rw [MonoidHom.comp_apply, FreeGroup.map.of, winRho_of, winRho_of]
      exact hband e.1 e.2.1
    show ((winRho Wt' c lo hi).comp (FreeGroup.map φ)) x = winRho Wt c lo hi x
    rw [hhom]
  · -- the deleted walk words agree after casting
    intro u
    have hstep : ∀ p : (α × ℤ) × Bool,
        winRootStep Wt' c lo hi p
          = Option.map (fun q : winBeta Wt c lo hi × Bool => (φ q.1, q.2))
              (winRootStep Wt c lo hi p) := by
      intro p
      by_cases hwin : coverEdge p ∈ winE c lo hi
      · by_cases hcl : coverClassAt Wt c (coverEdge p) = 1
        · rw [winRootStep_none Wt c lo hi p hcl,
              winRootStep_none Wt' c lo hi p ((hband (coverEdge p) hwin).trans hcl)]
          rfl
        · rw [winRootStep_of Wt c lo hi p hwin hcl,
              winRootStep_of Wt' c lo hi p hwin
                (fun h => hcl ((hband (coverEdge p) hwin).symm.trans h))]
          exact congrArg some (Prod.ext (Subtype.ext rfl) rfl)
      · rw [winRootStep_none_of_not_mem (Wt := Wt) hwin,
            winRootStep_none_of_not_mem (Wt := Wt') hwin]
        rfl
    have hL : (winRootList Wt c lo hi u).map (fun q : winBeta Wt c lo hi × Bool => (φ q.1, q.2))
        = winRootList Wt' c lo hi u := by
      rw [winRootList_eq, winRootList_eq, List.map_filterMap]
      exact List.filterMap_congr (fun p _ => (hstep p).symm)
    have h3 : FreeGroup.map φ (FreeGroup.mk (winRootList Wt c lo hi u))
        = FreeGroup.mk (winRootList Wt' c lo hi u) := by
      rw [FreeGroup.map.mk, hL]
    simpa only [winRoot] using h3

end Work.OROneRel
