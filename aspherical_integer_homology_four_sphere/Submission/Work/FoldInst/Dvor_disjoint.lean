import Mathlib
import Submission.Work.FoldInst.CertFlip
import Submission.Work.FoldInst.Voronoi

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FoldInst

/-- **Two representatives in the same copy with `S` a wall of the first but not of the second, and
`T` a wall of the second but not of the first, have disjoint Voronoi pieces.**  Indeed membership in
`Dvor i r` gives `slack S < slack T` (from the index of `S` and the non-walness of `T`), while
membership in `Dvor i s` gives `slack T < slack S`. -/
theorem Dvor_disjoint_of_wall_cross (i : Fin 98) {r s : Fin (foldCodim i) → Bool}
    {t u : Fin (foldCodim i)}
    (ht : ∀ u' : Fin (foldCodim i), foldWalls i s u' ≠ foldWalls i r t)
    (hu : ∀ t' : Fin (foldCodim i), foldWalls i r t' ≠ foldWalls i s u) :
    Disjoint (Dvor i r) (Dvor i s) := by
  rw [Set.disjoint_left]
  intro x hxr hxs
  rw [mem_Dvor] at hxr hxs
  rw [mem_VoronoiOpen] at hxr hxs
  have h1 : sideSlack (foldWalls i r t) x.2.1 < sideSlack (foldWalls i s u) x.2.1 :=
    (hxr.2.1 (foldWalls i s u) hu).2 t
  have h2 : sideSlack (foldWalls i s u) x.2.1 < sideSlack (foldWalls i r t) x.2.1 :=
    (hxs.2.1 (foldWalls i r t) ht).2 u
  exact absurd h1 (not_lt.mpr (le_of_lt h2))

/-- The Voronoi pieces of two distinct sign indices of one fold class lie in different copies of
`Q̄`, hence are disjoint. -/
theorem Dvor_disjoint_of_copy_ne (i : Fin 98) {r s : Fin (foldCodim i) → Bool}
    (hc : foldCr i r ≠ foldCr i s) : Disjoint (Dvor i r) (Dvor i s) := by
  rw [Set.disjoint_left]
  intro x hxr hxs
  rw [mem_Dvor] at hxr hxs
  exact hc (hxr.1.symm.trans hxs.1)

theorem Dvor_disjoint (i : Fin 98) {r s : Fin (foldCodim i) → Bool} (h : r ≠ s) :
    Disjoint (Dvor i r) (Dvor i s) := by
  by_cases hc : foldCr i r = foldCr i s
  · -- same copy: `foldWalls_inj` produces a side that is a wall of one but not of the other
    have hAB : ¬ (∀ t : Fin (foldCodim i), ∃ u : Fin (foldCodim i),
        foldWalls i s u = foldWalls i r t) :=
      fun hh => h (foldWalls_inj i r s hc hh)
    push Not at hAB
    obtain ⟨t, ht⟩ := hAB
    have hBA : ¬ (∀ u : Fin (foldCodim i), ∃ t : Fin (foldCodim i),
        foldWalls i r t = foldWalls i s u) :=
      fun hh => h (foldWalls_inj i s r hc.symm hh).symm
    push Not at hBA
    obtain ⟨u, hu⟩ := hBA
    exact Dvor_disjoint_of_wall_cross i ht hu
  · exact Dvor_disjoint_of_copy_ne i hc

end Work.FoldInst
