/-
# The fold chart lemma

This file assembles the `OpenPartialHomeomorph` glued from a `FoldGlue` datum: the *fold chart*.
Given `2^c` pieces `C r` of a space `Y`, charts `ψ r` into the closed orthants of `E4 = ℝ⁴` that
agree on the overlaps and fold onto each other by the coordinate reflections, the glued map is an
open partial homeomorphism with

* source `⋃ r, U r` (the union of the source pieces), and
* target `foldMap c hc ⁻¹' (ψ (oneSign c) '' U (oneSign c))`, the full preimage under the fold map
  of the relatively open image of the `+`-piece.

This is the general tool with which the Davis/Tschantz hyperbolic piece `M̄` gets its atlas: for
every face class `F` of `M̄` (not contained in a truncation facet) the `2^codim F` corner pieces of
`M̄` around `F` are glued into one chart `foldChart (D F) hc`.

The two non-elementary inputs are delegated to separate modules and imported here:

* `Work.Fold.glued_continuousOn` (`Submission.Work.Fold.glued_continuousOn`),
* `Work.Fold.invFun_continuousOn` (`Submission.Work.Fold.invFun_continuousOn`).
-/
import Submission.Work.Fold.GlueDefs
import Submission.Work.Fold.glued_continuousOn
import Submission.Work.Fold.invFun_continuousOn

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.Fold

open Set

variable {Y : Type*} [TopologicalSpace Y] {c : ℕ}

/-- **The fold chart** attached to a fold gluing. -/
def foldChart (D : FoldGlue Y c) (hc : c ≤ 4) : OpenPartialHomeomorph Y E4 where
  toFun := D.glued
  invFun := D.invFun hc
  source := D.source
  target := D.target hc
  map_source' := fun _ hy => D.glued_mem_target hc hy
  map_target' := fun _ hx => D.invFun_mem hc hx
  left_inv' := fun _ hy => D.invFun_glued hc hy
  right_inv' := fun _ hx => D.glued_invFun hc hx
  open_source := D.isOpen_source
  open_target := D.isOpen_target hc
  continuousOn_toFun := glued_continuousOn D
  continuousOn_invFun := invFun_continuousOn D hc

@[simp] lemma foldChart_apply (D : FoldGlue Y c) (hc : c ≤ 4) (y : Y) :
    foldChart D hc y = D.glued y := rfl

@[simp] lemma foldChart_symm_apply (D : FoldGlue Y c) (hc : c ≤ 4) (x : E4) :
    (foldChart D hc).symm x = D.invFun hc x := rfl

@[simp] lemma foldChart_source (D : FoldGlue Y c) (hc : c ≤ 4) :
    (foldChart D hc).source = D.source := rfl

@[simp] lemma foldChart_target (D : FoldGlue Y c) (hc : c ≤ 4) :
    (foldChart D hc).target = D.target hc := rfl

/-- On the `r`-th source piece, the fold chart is the chart `ψ r`. -/
theorem foldChart_apply_of_mem (D : FoldGlue Y c) (hc : c ≤ 4) {p : Y} {r : Sign c}
    (hp : p ∈ D.U r) : foldChart D hc p = D.ψ r p := D.glued_apply hp

/-- **The fold chart lemma.**  Gluing `2^c` closed pieces which fold onto each other over their
common coordinate hyperplanes produces an open partial homeomorphism of `Y` into `E4`, with source
the union of the source pieces and target the full fold-preimage of the relatively open image of
the `+`-piece. -/
theorem fold_chart_lemma (D : FoldGlue Y c) (hc : c ≤ 4) :
    ∃ Φ : OpenPartialHomeomorph Y E4,
      Φ.source = D.source ∧ Φ.target = D.target hc ∧
      (∀ r p, p ∈ D.U r → Φ p = D.ψ r p) :=
  ⟨foldChart D hc, rfl, rfl, fun _ _ hp => D.glued_apply hp⟩

/-- The fold chart maps its source onto its target. -/
theorem foldChart_image_source (D : FoldGlue Y c) (hc : c ≤ 4) :
    foldChart D hc '' D.source = D.target hc :=
  (foldChart D hc).image_source_eq_target

/-- The fold chart is an open map on its source. -/
theorem isOpen_foldChart_image (D : FoldGlue Y c) (hc : c ≤ 4) {W : Set Y} (hW : IsOpen W)
    (hWU : W ⊆ D.source) : IsOpen (foldChart D hc '' W) :=
  (foldChart D hc).isOpen_image_of_subset_source hW (by rwa [foldChart_source])

/-- The fold chart is injective on its source. -/
theorem foldChart_injOn (D : FoldGlue Y c) (hc : c ≤ 4) : InjOn (foldChart D hc) D.source :=
  D.glued_injOn hc

/-- The fold chart maps the `r`-th source piece onto the `r`-th reflected model corner. -/
theorem foldChart_image_piece (D : FoldGlue Y c) (hc : c ≤ 4) (r : Sign c) :
    foldChart D hc '' D.U r = reflVec r '' D.S := by
  show foldChart D hc '' D.U r = reflVec r '' (D.ψ (oneSign c) '' D.U (oneSign c))
  calc foldChart D hc '' D.U r = D.glued '' D.U r := rfl
    _ = D.ψ r '' D.U r := Set.image_congr fun _ hp => D.glued_apply hp
    _ = reflVec r '' (D.ψ (oneSign c) '' D.U (oneSign c)) := D.himage r

/-- A point of the source of a fold gluing lies in one of the source pieces. -/
theorem mem_source_iff_foldChart (D : FoldGlue Y c) (hc : c ≤ 4) {y : Y} :
    y ∈ (foldChart D hc).source ↔ ∃ r : Sign c, y ∈ D.U r := by
  rw [foldChart_source]; exact D.mem_source_iff

/-- **The cover form of the fold chart lemma.**  If a family of fold gluings covers a set `S` by
their sources, then the corresponding fold charts cover `S`.  This is the form in which the cover
theorem of the `M̄` atlas is used: `⋃_F (foldChart F).source ⊇ M̄ ∖ truncation facets`. -/
theorem iUnion_foldChart_source {ι : Type*} (D : ι → FoldGlue Y c) (hc : c ≤ 4) {S : Set Y}
    (h : S ⊆ ⋃ i, (D i).source) : S ⊆ ⋃ i, (foldChart (D i) hc).source := by
  intro y hy
  obtain ⟨i, hi⟩ := mem_iUnion.mp (h hy)
  exact mem_iUnion.mpr ⟨i, by rw [foldChart_source]; exact hi⟩

end Work.Fold
