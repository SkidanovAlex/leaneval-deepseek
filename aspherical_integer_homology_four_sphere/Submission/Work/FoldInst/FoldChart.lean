/-
# The fold charts of `M̄`, in the form the `Space/` area consumes

For every one of the 98 face classes `i` of `M̄` (all of them outside the truncation facets) this
file produces an `OpenPartialHomeomorph Mbar E4` whose source is the union of the Voronoi pieces of
the class and whose value on the piece `Dvor i r` is the chart map `foldTheta i r`.  The sources of
the 98 charts cover `M̄ ∖ Tset` and are disjoint from `Tset`.

This is the FOLD interface for `Work.Space`: the charts have exactly the type
`OpenPartialHomeomorph Mbar E4` of `Work.Space.FinAtlas.chart`, and
`mem_foldChart_source`/`iUnion_foldChart_source` are the cover statements the atlas assembly needs
(the remaining charts — the cusp charts — belong to the CUSP area).
-/
import Mathlib
import Submission.Work.FoldInst.exists_foldChart
import Submission.Work.FoldInst.Cover
import Submission.Work.FoldInst.Connected

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FoldInst

noncomputable section

/-- The saturation of the truncation facets is the truncation set itself. -/
theorem XtruncSat_eq : XtruncSat = Xtrunc := by
  ext y
  constructor
  · rintro ⟨x, hx, h⟩
    obtain ⟨γ, hγ, rfl⟩ := h
    exact actX_mem_Xtrunc hx
  · exact fun hy => Xtrunc_subset_sat hy

/-- **The fold chart of the face class `i`.**  Its source is the union of the Voronoi pieces of the
class, on which it is the map `foldTheta i r`. -/
def foldChart (i : Fin 98) : OpenPartialHomeomorph Mbar E4 :=
  Classical.choose (exists_foldChart i)

theorem foldChart_source (i : Fin 98) :
    (foldChart i).source = ⋃ r : Fin (foldCodim i) → Bool, mk '' Dvor i r :=
  (Classical.choose_spec (exists_foldChart i)).1

theorem foldChart_apply (i : Fin 98) (r : Fin (foldCodim i) → Bool) (x : Xbar) (hx : x ∈ Dvor i r) :
    foldChart i (mk x) = foldTheta i r x.2.1 :=
  (Classical.choose_spec (exists_foldChart i)).2 r x hx

/-- **The inverse of a fold chart**, on the image of a piece: it is the class of the point itself.
Together with `foldChart_apply` this identifies the transition `foldChart j ∘ (foldChart i).symm`
locally with `foldTheta j r' ∘ (foldTheta i r)⁻¹`, i.e. with a Möbius map — which is how the
smoothness and the isometry of the transitions are obtained from `HypModel`. -/
theorem foldChart_symm_apply (i : Fin 98) (r : Fin (foldCodim i) → Bool) (x : Xbar)
    (hx : x ∈ Dvor i r) : (foldChart i).symm (foldTheta i r x.2.1) = mk x := by
  have hmem : mk x ∈ (foldChart i).source := by
    rw [foldChart_source]
    exact Set.mem_iUnion.mpr ⟨r, ⟨x, hx, rfl⟩⟩
  rw [← foldChart_apply i r x hx]
  exact (foldChart i).left_inv hmem

/-- **The source of a fold chart does not meet the truncation set.** -/
theorem foldChart_source_disjoint_Tset (i : Fin 98) : Disjoint (foldChart i).source Tset := by
  rw [Set.disjoint_left]
  intro p hp hq
  rw [foldChart_source] at hp
  obtain ⟨r, x, hxr, rfl⟩ := Set.mem_iUnion.mp hp
  obtain ⟨y, hy, hyx⟩ := hq
  -- `x` and `y` have the same class, and `y` is in the truncation set, which is saturated
  have hrel : rel y x := Quotient.eq.mp hyx
  have hxsat : x ∈ XtruncSat := ⟨y, hy, hrel⟩
  rw [XtruncSat_eq] at hxsat
  obtain ⟨w, hw⟩ := hxsat
  exact absurd hw (ne_of_gt (hxr.2.2 w).1)

theorem foldChart_source_subset_compl_Tset (i : Fin 98) :
    (foldChart i).source ⊆ Tsetᶜ := fun _ hp hq =>
  Set.disjoint_left.mp (foldChart_source_disjoint_Tset i) hp hq

/-- **The 98 fold charts cover `M̄ ∖ Tset`.** -/
theorem iUnion_foldChart_source : Tsetᶜ ⊆ ⋃ i : Fin 98, (foldChart i).source := by
  intro p hp
  obtain ⟨i, hi⟩ := cover_foldCharts p hp
  exact Set.mem_iUnion.mpr ⟨i, by rw [foldChart_source]; exact hi⟩

theorem mem_foldChart_source {p : Mbar} (hp : p ∉ Tset) :
    ∃ i : Fin 98, p ∈ (foldChart i).source :=
  Set.mem_iUnion.mp (iUnion_foldChart_source hp)

end

end Work.FoldInst
