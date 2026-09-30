import Mathlib
import Submission.Work.DeltaHomology.CellData
import Submission.Work.DeltaHomology.PunctSimplex
import Submission.Work.DeltaHomology.PunctSkelBasic
import Submission.Work.DeltaHomology.mem_intCell_iff

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.DeltaHomology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Convexity Work.Homology

namespace Work.DeltaHomology

/-- **The punctured cell is the closed cell minus its barycentre.**  For a realized `Δ`-complex, an
`n`-simplex `σ` and a point of the closed cell which is not its barycentre, that point is also not
the barycentre of any *other* `n`-simplex, so `punctCell n σ` (`punctSkel n` intersected with the
closed cell) and `cell n σ \ {cellBarycenter n σ}` agree.

Route: `punctCell χ n σ = χ.punctSkel n ∩ Set.range (χ.cls n σ)` (its definition in
`Submission.Work.DeltaHomology.PunctSimplex`) and `punctSkel n = skelSet n \ barycenterSet n`, so
the statement reduces to `range (cls n σ) ∩ barycenterSet n = {cellBarycenter n σ}`; this is
`DeltaRealization.cls_eq_barycenter_iff` (if `cls n σ y` is a barycentre then `y` is the
barycentre), together with `cell_subset_skelSet` and `cellBarycenter_mem_cell`. -/
theorem punctCell_eq_sdiff {K : DeltaCx} {X : TopCat} (R : DeltaRealization K X)
    (n : ℕ) (σ : Fin (K.card n)) :
    R.toDeltaSimplexMap.punctCell n σ =
      R.toDeltaSimplexMap.cell n σ \ {R.toDeltaSimplexMap.cellBarycenter n σ} := by
  ext x
  constructor
  · -- A point of the collar lying in the closed cell: it is in the closed cell and off
    -- every barycentre, in particular off the barycentre of `σ`.
    intro hx
    rw [DeltaSimplexMap.punctCell] at hx
    obtain ⟨hxskel, hxr⟩ := hx
    rw [DeltaSimplexMap.punctSkel] at hxskel
    obtain ⟨_, hxbar⟩ := hxskel
    obtain ⟨y, hy⟩ := hxr
    refine ⟨⟨y, hy⟩, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro hxc
    apply hxbar
    refine ⟨σ, ?_⟩
    rw [DeltaSimplexMap.cellBarycenter] at hxc
    exact hxc.symm
  · -- A point of the closed cell which is not the barycentre of `σ` lies in the collar.
    intro hx
    obtain ⟨⟨y, hy⟩, hxc⟩ := hx
    rw [DeltaSimplexMap.punctCell]
    refine ⟨?_, ⟨y, hy⟩⟩
    rw [DeltaSimplexMap.punctSkel]
    refine ⟨?_, ?_⟩
    · rw [← hy]
      exact DeltaSimplexMap.cell_subset_skelSet R.toDeltaSimplexMap σ (Set.mem_range_self y)
    · -- If it were a barycentre, it would be the barycentre of `σ`.
      intro hbar
      have hbm : (R.toDeltaSimplexMap.cls n σ y : X) ∈ R.toDeltaSimplexMap.barycenterSet n := by
        rw [hy]; exact hbar
      have h := (R.cls_eq_barycenter_iff n σ y).mp hbm
      apply hxc
      simp only [Set.mem_singleton_iff]
      rw [DeltaSimplexMap.cellBarycenter, ← h]
      exact hy.symm

end Work.DeltaHomology

/-! ## The same lemma under its flat name

The lemma above is registered in the namespace `Work.DeltaHomology.Work.DeltaHomology` (the
file carries two identical `namespace Work.DeltaHomology` lines, as it was delivered).  The
statement below is the *same* lemma, restated in the namespace `Work.DeltaHomology`, which is
the name under which the rest of the project refers to it
(`Work.DeltaHomology.punctCell_eq_sdiff`). -/
theorem punctCell_eq_sdiff {K : DeltaCx} {X : TopCat} (R : DeltaRealization K X)
    (n : ℕ) (σ : Fin (K.card n)) :
    R.toDeltaSimplexMap.punctCell n σ =
      R.toDeltaSimplexMap.cell n σ \ {R.toDeltaSimplexMap.cellBarycenter n σ} :=
  _root_.Work.DeltaHomology.Work.DeltaHomology.punctCell_eq_sdiff R n σ

end Work.DeltaHomology
