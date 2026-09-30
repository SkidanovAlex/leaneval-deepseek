/-
# The fold charts cover `M̄` minus the truncation set

Every point of `Q̄` off the truncation facets has, as its set of tight sides, the wall set of some
representative of some fold class (`Work.FoldInst.fold_cover_sides`).  The generated tables
`flipCopyI`/`flipCopyJ` (`Work.FoldInst.CoverData`) provide, for every representative, a
representative in the *other* copy of `Q̄` with the same wall set; hence the representative can be
chosen in the copy of the given point of `Xbar`.  Therefore every point of `M̄ ∖ Tset` lies in a
Voronoi piece `Dvor i r`, i.e. in the source of a fold chart.
-/
import Mathlib
import Submission.Work.FoldInst.CoverData
import Submission.Work.FoldInst.Quotient
import Submission.Work.FoldInst.fold_cover_sides
import Submission.Work.FoldInst.Connected

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FoldInst

/-- **A point of `Xbar` off the truncation facets lies in a Voronoi piece.** -/
theorem cover_source (x : Xbar) (hx : x ∉ Xtrunc) :
    ∃ (i : Fin 98) (r : Fin (foldCodim i) → Bool), x ∈ Dvor i r := by
  have hT : ∀ w : Fin 24, truncSlack w x.2.1 ≠ 0 := fun w h => hx ⟨w, h⟩
  obtain ⟨i, r, hr⟩ := fold_cover_sides x.2.1 x.2.2 hT
  -- the representative in the other copy with the same wall set
  obtain ⟨r', hr'⟩ := (isReal_iff (flipCopyI i (foldRepOf i r)) (flipCopyJ i (foldRepOf i r))).mp
    (cert_flipCopy_isReal i (foldRepOf i r))
  have hcopy : foldCr (flipCopyI i (foldRepOf i r)) r' = foldCr i r + 1 := by
    rw [foldCr, foldCr, ← hr', cert_flipCopy_copy i (foldRepOf i r)]
  have hmask : wallMask (flipCopyI i (foldRepOf i r)) (foldRepOf (flipCopyI i (foldRepOf i r)) r')
      = wallMask i (foldRepOf i r) := by
    rw [← hr', cert_flipCopy_mask i (foldRepOf i r) (isReal_repOf i r)]
  have hwalls : ∀ S : Fin 24,
      (∃ t' : Fin (foldCodim (flipCopyI i (foldRepOf i r))),
        foldWalls (flipCopyI i (foldRepOf i r)) r' t' = S) ↔
      (∃ t : Fin (foldCodim i), foldWalls i r t = S) := by
    intro S
    rw [← wallMask_spec (flipCopyI i (foldRepOf i r)) r' S,
      ← wallMask_spec i r S, hmask]
  have key : ∀ (i : Fin 98) (r : Fin (foldCodim i) → Bool), foldCr i r = x.1 →
      (∀ S : Fin 24, sideSlack S x.2.1 = 0 ↔ ∃ t : Fin (foldCodim i), foldWalls i r t = S) →
      x ∈ Dvor i r := by
    intro i r hc hr'
    refine ⟨hc.symm, ?_, ?_⟩
    · intro S hS
      have hne : sideSlack S x.2.1 ≠ 0 := by
        intro h0
        obtain ⟨t, ht⟩ := (hr' S).mp h0
        exact hS t ht
      have hpos : 0 < sideSlack S x.2.1 := lt_of_le_of_ne (x.2.2.1 S) (Ne.symm hne)
      refine ⟨hpos, fun t => ?_⟩
      rw [show sideSlack (foldWalls i r t) x.2.1 = 0 from (hr' _).mpr ⟨t, rfl⟩]
      exact hpos
    · intro w
      have hw0 : 0 < truncSlack w x.2.1 := lt_of_le_of_ne (x.2.2.2 w) (Ne.symm (hT w))
      refine ⟨hw0, fun t => ?_⟩
      rw [show sideSlack (foldWalls i r t) x.2.1 = 0 from (hr' _).mpr ⟨t, rfl⟩]
      exact hw0
  rcases zmod2_eq_zero_or_one x.1 with hx0 | hx1
  · rcases zmod2_eq_zero_or_one (foldCr i r) with h0 | h0
    · exact ⟨i, r, key i r (by rw [h0, hx0]) hr⟩
    · have hc' : foldCr (flipCopyI i (foldRepOf i r)) r' = x.1 := by rw [hcopy, h0, hx0]; decide
      exact ⟨_, r', key _ r' hc' (fun S => (hr S).trans (hwalls S).symm)⟩
  · rcases zmod2_eq_zero_or_one (foldCr i r) with h0 | h0
    · have hc' : foldCr (flipCopyI i (foldRepOf i r)) r' = x.1 := by rw [hcopy, h0, hx1]; decide
      exact ⟨_, r', key _ r' hc' (fun S => (hr S).trans (hwalls S).symm)⟩
    · exact ⟨i, r, key i r (by rw [h0, hx1]) hr⟩

/-- **The fold charts cover `M̄ ∖ Tset`.** -/
theorem cover_foldCharts (p : Mbar) (hp : p ∉ Tset) :
    ∃ i : Fin 98, p ∈ ⋃ r : Fin (foldCodim i) → Bool, mk '' Dvor i r := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep p
  have hx : x ∉ Xtrunc := fun h => hp ⟨x, h, rfl⟩
  obtain ⟨i, r, hxr⟩ := cover_source x hx
  exact ⟨i, Set.mem_iUnion.mpr ⟨r, ⟨x, hxr, rfl⟩⟩⟩

end Work.FoldInst
