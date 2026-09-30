import Mathlib
import Submission.Work.ConvexCells.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ConvexCells

open scoped BigOperators

open PolytopeData

variable {d : ℕ} (P : PolytopeData d)

/-- A constraint is tight at the relative interior point `posR f` of a face `f` exactly when
it belongs to the tight set of `f`. -/
private theorem inner_posR_eq_iff (h : P.Ok) (f : Fin P.K) (k : Fin P.m) :
    inner ℝ (P.nR k) (P.posR f) = P.bR k ↔ k ∈ P.tight f := by
  constructor
  · intro heq
    by_contra hk
    exact absurd heq (ne_of_lt (inner_posR_of_not_mem P h f k hk))
  · exact inner_posR_of_mem P h f k

/-- A constraint is tight at every face of a flag iff it is tight at the *last* (largest) face.
`IsFlag` orders the faces from the smallest to the largest, so the tight sets decrease along the
list and their common intersection is the tight set of the last entry. -/
private theorem flag_forall_tight_iff (s : P.FlagPt) (k : Fin P.m) :
    (∀ i : Fin s.flag.length, k ∈ P.tight (s.flag.get i)) ↔ k ∈ P.tight s.topFace := by
  have hpos : 0 < s.flag.length := List.length_pos_of_ne_nil s.flag_ne_nil
  have hlast : s.flag.get ⟨s.flag.length - 1, by omega⟩ = s.flag.getLast s.flag_ne_nil := by
    rw [List.get_eq_getElem, List.getLast_eq_getElem]
  constructor
  · intro hh
    rw [PolytopeData.FlagPt.topFace, ← hlast]
    exact hh _
  · intro hk i
    rw [PolytopeData.FlagPt.topFace, ← hlast] at hk
    by_cases hi : i = (⟨s.flag.length - 1, by omega⟩ : Fin s.flag.length)
    · rw [hi]; exact hk
    · have hlt : i < (⟨s.flag.length - 1, by omega⟩ : Fin s.flag.length) := by
        show (i : ℕ) < s.flag.length - 1
        have hi' := i.isLt
        have hne : (i : ℕ) ≠ s.flag.length - 1 := fun hc => hi (Fin.ext hc)
        omega
      have hsub := List.Pairwise.rel_get_of_lt s.isFlag hlt
      exact hsub.1 hk

/-- The tight set of the affine realization of a flag is the tight set of the top (largest) face
of the flag.  Every `posR (flag.get i)` is a point of `Pset` (`posR_mem_Pset`), the combination
`toE'` has strictly positive weights summing to one, so `tightAt_combo` computes the tight set as
the intersection of the `tight` sets of the faces of the flag; `IsFlag` orders the list from the
smallest face to the largest, so the intersection is `tight (flag.getLast) = tight s.topFace`. -/
theorem tightAt_flagPt {d : ℕ} (P : PolytopeData d) (h : P.Ok) (s : P.FlagPt) :
    P.tightAt s.toE' = P.tight s.topFace := by
  ext k
  have hstep : k ∈ P.tightAt s.toE' ↔ (∀ i : Fin s.flag.length, k ∈ P.tight (s.flag.get i)) := by
    unfold PolytopeData.FlagPt.toE'
    have hc := tightAt_combo P (s := Finset.univ) (w := s.wt)
      (z := fun i => P.posR (s.flag.get i))
      (fun i _ => le_of_lt (s.wt_pos i)) s.wt_sum
      (fun i _ => posR_mem_Pset P h (s.flag.get i)) k
    rw [hc]
    constructor
    · intro hh i
      rw [← inner_posR_eq_iff P h (s.flag.get i) k]
      exact hh i (Finset.mem_univ i) (ne_of_gt (s.wt_pos i))
    · intro hh i _ _
      rw [inner_posR_eq_iff P h (s.flag.get i) k]
      exact hh i
  rw [hstep]
  exact flag_forall_tight_iff P s k

end Work.ConvexCells
