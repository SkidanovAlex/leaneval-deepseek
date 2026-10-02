import Mathlib
import Submission.Work.SeedExist.Setup

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedExist.Fatou

open LeanEval.ComplexAnalysis (Tantibar)

/-- The filled Julia set `K c` is forward invariant under `Tantibar c`: a bounded orbit stays
bounded after one more step. -/
theorem mapsTo_tantibar_K (c : ℂ) :
    Set.MapsTo (Tantibar c) (Work.EL.K c) (Work.EL.K c) := by
  intro z hz
  exact hz.shift 1

/-- **A point whose connected component in `s` is nonempty belongs to `s`.**  Every set of the
family whose union defines `connectedComponentIn s x` contains `x`, so a nonempty connected
component of `x` forces `x ∈ s`. -/
theorem mem_of_connectedComponentIn_nonempty {α : Type*} [TopologicalSpace α] {s : Set α} {x : α}
    (h : (connectedComponentIn s x).Nonempty) : x ∈ s := by
  obtain ⟨y, hy⟩ := h
  by_contra hx
  rw [connectedComponentIn_eq_empty hx] at hy
  exact hy

/-- **Fatou's theorem puts the critical point and the critical value in the interior of the
filled Julia set.**

The first component of `FatouCritInBasin` says that some `T_c`-iterate of a point of the petal
`Pg` lies in the connected component of `0` inside `interior (K c)`.  A connected component of
`0` in a set is empty unless `0` belongs to that set, so this is exactly the statement
`0 ∈ interior (K c)`.

Since `T_c` is an open map and `K c` is forward invariant, the image of the open set
`interior (K c)` is an open subset of `K c`, hence contained in `interior (K c)`.  Applying this
to the critical point `0` gives `c = T_c 0 ∈ interior (K c)`. -/
theorem interior_of_fatou {c : ℂ} {z₁ : ℂ}
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.FSeed.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) z₁)
    (hfat : Work.SeedExist.FatouCritInBasin c z₁ fl.Pg) :
    c ∈ interior (Work.EL.K c) ∧ (0 : ℂ) ∈ interior (Work.EL.K c) := by
  -- the critical point `0` is an interior point of the filled Julia set
  have h0 : (0 : ℂ) ∈ interior (Work.EL.K c) := by
    obtain ⟨i, _hi, x, _hx, hmem⟩ := hfat.1
    exact mem_of_connectedComponentIn_nonempty ⟨_, hmem⟩
  -- `c = T_c 0` is then an interior point too, because `T_c` is open and `K c` is invariant
  have hc : c ∈ interior (Work.EL.K c) := by
    have himg : Tantibar c '' interior (Work.EL.K c) ⊆ Work.EL.K c := by
      rintro w ⟨z, hz, rfl⟩
      exact mapsTo_tantibar_K c (interior_subset hz)
    have hopen : IsOpen (Tantibar c '' interior (Work.EL.K c)) :=
      (Work.ELPull.isOpenMap_Tantibar c) _ isOpen_interior
    have hmem : Tantibar c 0 ∈ Tantibar c '' interior (Work.EL.K c) := ⟨0, h0, rfl⟩
    have hsub : Tantibar c 0 ∈ interior (Work.EL.K c) := interior_maximal himg hopen hmem
    have hc0 : Tantibar c 0 = c := by simp [LeanEval.ComplexAnalysis.Tantibar]
    rwa [hc0] at hsub
  exact ⟨hc, h0⟩

end Work.SeedExist.Fatou
