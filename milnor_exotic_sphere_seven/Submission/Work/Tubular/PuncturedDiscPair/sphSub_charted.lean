import Mathlib
import Submission.Work.SphHomology.PieceCharted
import Submission.Work.SphHomology.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The sphere bundle of a Euclidean bundle over an `8`-manifold is charted

For a Euclidean real bundle `Z` of rank `k ≥ 1` over a base `B` charted on `ℝ⁸`, the unit sphere
bundle `S(Z)` (`Work.Thom.SphSub Z`) is a charted space modelled on `ℝ^{8 + (k-1)}`.

The argument is local.  Around a point `p` of `S(Z)`, choose a trivialising set `Z.baseSet i`
containing the base point of `p` (`i := Z.indexAt p.1.1`).  The part `SphPiece Z i` of the sphere
bundle over `Z.baseSet i` is homeomorphic to `↥(Z.baseSet i) × S^{k-1}`, hence — as an open piece of
an `8`-manifold times the sphere `S^{k-1}`, with the model identification
`ℝ^{8+(k-1)} ≅ ℝ⁸ × ℝ^{k-1}` — it carries a `ChartedSpace` structure modelled on
`ℝ^{8 + (k-1)}` (`Work.SphHomology.sphPiece_charted`).  Since `SphPiece Z i` is an open subspace of
`S(Z)`, every chart of the piece extends to an open partial homeomorphism of `S(Z)`
(`OpenPartialHomeomorph.lift_openEmbedding`), and these charts cover `S(Z)` because the trivialising
sets `Z.baseSet i` cover `B`.  This yields the `ChartedSpace` structure explicitly, with
`chartAt p` the extension of the chart of the piece at `p`.

No compatibility between the charts is needed: a `ChartedSpace` structure in Mathlib is just an
atlas of open partial homeomorphisms whose sources cover the space.
-/

open Work.TangentClasses

namespace Work.Tubular.PuncturedDiscPair

noncomputable section

/-- **A piece of the sphere bundle is charted.**  The part of the unit sphere bundle of `Z` over a
trivialising set `Z.baseSet i` is a charted space modelled on `ℝ^{8 + (k-1)}`
(`Work.SphHomology.sphPiece_charted`, made into a class instance by choosing a witness). -/
abbrev pieceCharted {B : Type} [TopologicalSpace B]
    [ChartedSpace (EuclideanSpace ℝ (Fin 8)) B] {k : ℕ} (hk : 1 ≤ k) {ι : Type}
    (Z : RealBundle B (EuclideanSpace ℝ (Fin k)) ι) (hZ : Work.Thom.IsEuclidean Z) (i : ι) :
    ChartedSpace (EuclideanSpace ℝ (Fin (8 + (k - 1)))) (Work.SphHomology.SphPiece Z i) :=
  (Work.SphHomology.sphPiece_charted hk Z hZ i).some

/-- **A chart of the sphere bundle of `Z`, read in a trivialising set.**  The chart at a point `q`
of the piece `SphPiece Z i`, extended to the whole sphere bundle along the open embedding
`SphPiece Z i ↪ S(Z)`; its source is the image of the source of the chart of the piece. -/
noncomputable def sphChartAt {B : Type} [TopologicalSpace B]
    [ChartedSpace (EuclideanSpace ℝ (Fin 8)) B] {k : ℕ} (hk : 1 ≤ k) {ι : Type}
    (Z : RealBundle B (EuclideanSpace ℝ (Fin k)) ι) (hZ : Work.Thom.IsEuclidean Z)
    (i : ι) (q : Work.SphHomology.SphPiece Z i) :
    OpenPartialHomeomorph (Work.Thom.SphSub Z) (EuclideanSpace ℝ (Fin (8 + (k - 1)))) :=
  (ChartedSpace.chartAt (self := pieceCharted hk Z hZ i) q).lift_openEmbedding
    (Work.SphHomology.isOpen_sphPiece Z i).isOpenEmbedding_subtypeVal

/-- **The preferred chart of the sphere bundle at a point `p`**, read in the trivialising set
`Z.baseSet (Z.indexAt p.1.1)` containing the base point of `p`. -/
noncomputable def sphChart {B : Type} [TopologicalSpace B]
    [ChartedSpace (EuclideanSpace ℝ (Fin 8)) B] {k : ℕ} (hk : 1 ≤ k) {ι : Type}
    (Z : RealBundle B (EuclideanSpace ℝ (Fin k)) ι) (hZ : Work.Thom.IsEuclidean Z)
    (p : Work.Thom.SphSub Z) :
    OpenPartialHomeomorph (Work.Thom.SphSub Z) (EuclideanSpace ℝ (Fin (8 + (k - 1)))) :=
  sphChartAt hk Z hZ (Z.indexAt p.1.1)
    ⟨p, Work.SphHomology.mem_sphOver.mpr (Z.mem_baseSet_at p.1.1)⟩

/-- A point `q` of a piece of the sphere bundle lies in the source of the chart of the sphere
bundle built at `q`. -/
theorem mem_sphChartAt_source {B : Type} [TopologicalSpace B]
    [ChartedSpace (EuclideanSpace ℝ (Fin 8)) B] {k : ℕ} (hk : 1 ≤ k) {ι : Type}
    (Z : RealBundle B (EuclideanSpace ℝ (Fin k)) ι) (hZ : Work.Thom.IsEuclidean Z)
    (i : ι) (q : Work.SphHomology.SphPiece Z i) :
    (q : Work.Thom.SphSub Z) ∈ (sphChartAt hk Z hZ i q).source := by
  rw [sphChartAt, OpenPartialHomeomorph.lift_openEmbedding_source]
  exact ⟨q, ChartedSpace.mem_chart_source (self := pieceCharted hk Z hZ i) q, rfl⟩

/-- Every point of the sphere bundle lies in the source of its preferred chart. -/
theorem sphChart_source {B : Type} [TopologicalSpace B]
    [ChartedSpace (EuclideanSpace ℝ (Fin 8)) B] {k : ℕ} (hk : 1 ≤ k) {ι : Type}
    (Z : RealBundle B (EuclideanSpace ℝ (Fin k)) ι) (hZ : Work.Thom.IsEuclidean Z)
    (p : Work.Thom.SphSub Z) : p ∈ (sphChart hk Z hZ p).source := by
  rw [sphChart]
  exact mem_sphChartAt_source hk Z hZ _ _

theorem sphSub_charted {B : Type} [TopologicalSpace B]
    [ChartedSpace (EuclideanSpace ℝ (Fin 8)) B] {ι : Type} {k : ℕ} (hk : 1 ≤ k)
    (Z : Work.TangentClasses.RealBundle B (EuclideanSpace ℝ (Fin k)) ι)
    (hZ : Work.Thom.IsEuclidean Z) :
    Nonempty (ChartedSpace (EuclideanSpace ℝ (Fin (8 + (k - 1)))) (Work.Thom.SphSub Z)) := by
  refine ⟨{ atlas := Set.range (sphChart hk Z hZ)
            chartAt := sphChart hk Z hZ
            mem_chart_source := fun p => sphChart_source hk Z hZ p
            chart_mem_atlas := fun p => Set.mem_range_self p }⟩

end

end Work.Tubular.PuncturedDiscPair
