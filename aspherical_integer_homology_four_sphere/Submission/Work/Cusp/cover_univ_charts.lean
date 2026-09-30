/-
# The cover theorem at the level of chart sources

`Work.Cusp.cover_univ` (`Submission/Work/Cusp/cover_univ.lean`) proves that `M̂` is covered by the
images of the *layers* of the filling pieces together with the images of a family of charts of the
hyperbolic piece `M̄`:

`(⋃ i, incMbar '' (Φ i).source) ∪ ⋃_v incW v '' (collar layer) ∪ ⋃_v incW v '' (polar layer)
   ∪ ⋃_v incW v '' (core layer) = univ`.

This file converts that statement into the form in which the assembly area consumes it: the union of
the *sources of the chart families itself* is `univ`,

`(⋃ i, incMbar '' (Φ i).source) ∪ (⋃ j, (Ψc j).source) ∪ (⋃ j, (Ψp j).source)
   ∪ (⋃ j, (Ψk j).source) = univ`.

## The layer hypotheses

The three filling families must cover the three layers *on which they are charts*:

* **collar** (`Ψc`, the charts `Work.Cusp.cuspChartTop` of the unslabbed family): the collar layer
  `‖p‖∞ ≥ 1/2`.  This is where the slab-free box and the tall window `(s₁, sTop)` with
  `sTop > s_J` are needed: the collar layer contains the four **corner directions** of the square
  (`u(p) ∈ ℤ`, i.e. `p ∝ (±1,±1)`), whose lifts have meridian parameter `≡ 0 (mod 1)` and hence lie
  in **no** translate of the slab `(0,1)` of the slabbed box `cuspChartBox`, and it contains the
  **junction** `‖p‖∞ = 1/2` (UHS height exactly `s_J`), which the open window `(s₁, s_J)` does not
  contain.  The family `cuspChartTop` covers all of it
  (`Work.Cusp.collarLayer_subset_range_cuspCoordMTop`).
* **polar** (`Ψp`, the charts `Work.Cusp.polarChart`): the *inner* polar layer
  `1/24 < ‖p‖∞ < 1/2`.  The polar charts are pinned to `r < r_J`, i.e. `‖p‖∞ < 1/2`, so
  the junction is *not* among them — it is covered by the collar charts above.  Getting this
  hypothesis right is the reason this file had to be restated: the previous version demanded that
  the polar charts cover the whole of `polarLayer = {1/24 < ‖p‖∞}`, which is false.
* **core** (`Ψk`, the charts `Work.Cusp.coreChart`): the core layer `‖p‖∞ < 1/12` (the charts are
  defined on the disk `r < 1/2`, i.e. `‖p‖∞ < 1/12`).

## The fold hypothesis

The fold charts `Φ i` cover `M̄ ∖ Tset`; in the second theorem below they are moreover required to
have sources in `Tsetᶜ`, which is the form in which `Work.RTInstance.FillData.fill_cover` needs the
statement: every point of `M̂` which is not the image of a point of the open hyperbolic piece lies in
the source of one of the filling charts.
-/
import Mathlib
import Submission.Work.Cusp.Assembly
import Submission.Work.Cusp.cover_univ

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function

namespace Work.Cusp

/-- **The cover theorem for chart families.**  If the fold charts `Φ i` cover `M̄ ∖ Tset`, if the
collar charts `Ψc` cover the collar layer `‖p‖∞ ≥ 1/2` of every filling piece, if the polar charts
`Ψp` cover the inner polar layer `1/24 < ‖p‖∞ < 1/2` and if the core charts `Ψk` cover the core
layer `‖p‖∞ < 1/12`, then the union of the sources of the fold, collar, polar and core charts is all
of `M̂`. -/
theorem cover_univ_charts (a : Work.Space.Assembly) (ι : Type) [Fintype ι]
    (Φ : ι → OpenPartialHomeomorph a.Mbar E4)
    (hfold : {x : a.Mbar | x ∉ a.Tset} ⊆ ⋃ i, (Φ i).source)
    (nc : ℕ) (Ψc : Fin nc → OpenPartialHomeomorph a.Mhat E4)
    (hcollar : ∀ (v : Work.Space.Cusp) (q : Work.Space.SquarePt × a.Torus v),
      q ∈ collarLayer (a.Torus v) → ∃ j, a.incW v q ∈ (Ψc j).source)
    (np : ℕ) (Ψp : Fin np → OpenPartialHomeomorph a.Mhat E4)
    (hpolar : ∀ (v : Work.Space.Cusp) (q : Work.Space.SquarePt × a.Torus v),
      q ∈ polarLayer (a.Torus v) → nrm (q.1 : E2) < 1/2 → ∃ j, a.incW v q ∈ (Ψp j).source)
    (nk : ℕ) (Ψk : Fin nk → OpenPartialHomeomorph a.Mhat E4)
    (hcore : ∀ (v : Work.Space.Cusp) (q : Work.Space.SquarePt × a.Torus v),
      q ∈ coreLayer (a.Torus v) → ∃ j, a.incW v q ∈ (Ψk j).source) :
    (⋃ i, a.incMbar '' (Φ i).source) ∪ (⋃ j, (Ψc j).source) ∪ (⋃ j, (Ψp j).source) ∪
      (⋃ j, (Ψk j).source) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro z
  have hcov := cover_univ a ι Φ hfold
  have hz : z ∈ (⋃ i, a.incMbar '' (Φ i).source) ∪
      (⋃ v : Work.Space.Cusp, a.incW v '' (collarLayer (a.Torus v))) ∪
      (⋃ v : Work.Space.Cusp, a.incW v '' (polarLayer (a.Torus v))) ∪
      (⋃ v : Work.Space.Cusp, a.incW v '' (coreLayer (a.Torus v))) := by
    rw [hcov]
    exact Set.mem_univ z
  rcases hz with ((hzA | hzB) | hzC) | hzD
  · exact Or.inl (Or.inl (Or.inl hzA))
  · -- a point of the collar layer: the collar charts cover it
    obtain ⟨v, q, hq, rfl⟩ := Set.mem_iUnion.mp hzB
    obtain ⟨j, hj⟩ := hcollar v q hq
    exact Or.inl (Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨j, hj⟩)))
  · -- a point of the polar layer: below the junction the polar charts cover it, at or above it the
    -- collar charts do
    obtain ⟨v, q, hq, rfl⟩ := Set.mem_iUnion.mp hzC
    rcases lt_or_ge (nrm (q.1 : E2)) (1/2) with hlt | hge
    · obtain ⟨j, hj⟩ := hpolar v q hq hlt
      exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨j, hj⟩))
    · have hc : q ∈ collarLayer (a.Torus v) := hge
      obtain ⟨j, hj⟩ := hcollar v q hc
      exact Or.inl (Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨j, hj⟩)))
  · -- a point of the core layer
    obtain ⟨v, q, hq, rfl⟩ := Set.mem_iUnion.mp hzD
    obtain ⟨j, hj⟩ := hcore v q hq
    exact Or.inr (Set.mem_iUnion.mpr ⟨j, hj⟩)

/-- **The cover of the filling charts**, in the form of `Work.RTInstance.FillData.fill_cover`:
every point of `M̂` which is not the image of a point of the open hyperbolic piece `M̄ ∖ Tset` lies in
the source of one of the filling charts.  The single filling family `Ψ` must cover the three layers
as in `cover_univ_charts` (the collar layer `‖p‖∞ ≥ 1/2`, the inner polar layer
`1/24 < ‖p‖∞ < 1/2` and the core layer `‖p‖∞ < 1/12`). -/
theorem fill_cover_of_layer_cover (a : Work.Space.Assembly) (ι : Type) [Fintype ι]
    (Φ : ι → OpenPartialHomeomorph a.Mbar E4)
    (hfold : {x : a.Mbar | x ∉ a.Tset} ⊆ ⋃ i, (Φ i).source)
    (hfoldsub : ∀ i, (Φ i).source ⊆ a.Tsetᶜ)
    (n : ℕ) (Ψ : Fin n → OpenPartialHomeomorph a.Mhat E4)
    (hcollar : ∀ (v : Work.Space.Cusp) (q : Work.Space.SquarePt × a.Torus v),
      q ∈ collarLayer (a.Torus v) → ∃ j, a.incW v q ∈ (Ψ j).source)
    (hpolar : ∀ (v : Work.Space.Cusp) (q : Work.Space.SquarePt × a.Torus v),
      q ∈ polarLayer (a.Torus v) → nrm (q.1 : E2) < 1/2 → ∃ j, a.incW v q ∈ (Ψ j).source)
    (hcore : ∀ (v : Work.Space.Cusp) (q : Work.Space.SquarePt × a.Torus v),
      q ∈ coreLayer (a.Torus v) → ∃ j, a.incW v q ∈ (Ψ j).source) :
    ∀ x : a.Mhat, (∀ p : a.Mbar, p ∉ a.Tset → a.incMbar p ≠ x) → ∃ j, x ∈ (Ψ j).source := by
  intro x hx
  have hcov := cover_univ a ι Φ hfold
  have hz : x ∈ (⋃ i, a.incMbar '' (Φ i).source) ∪
      (⋃ v : Work.Space.Cusp, a.incW v '' (collarLayer (a.Torus v))) ∪
      (⋃ v : Work.Space.Cusp, a.incW v '' (polarLayer (a.Torus v))) ∪
      (⋃ v : Work.Space.Cusp, a.incW v '' (coreLayer (a.Torus v))) := by
    rw [hcov]
    exact Set.mem_univ x
  rcases hz with ((hzA | hzB) | hzC) | hzD
  · obtain ⟨i, p, hp, rfl⟩ := Set.mem_iUnion.mp hzA
    exact absurd rfl (hx p (hfoldsub i hp))
  · obtain ⟨v, q, hq, rfl⟩ := Set.mem_iUnion.mp hzB
    exact hcollar v q hq
  · obtain ⟨v, q, hq, rfl⟩ := Set.mem_iUnion.mp hzC
    rcases lt_or_ge (nrm (q.1 : E2)) (1/2) with hlt | hge
    · exact hpolar v q hq hlt
    · exact hcollar v q hge
  · obtain ⟨v, q, hq, rfl⟩ := Set.mem_iUnion.mp hzD
    exact hcore v q hq

end Work.Cusp
