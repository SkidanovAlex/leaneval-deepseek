import Mathlib
import Submission.Work.RTOwed.cuspChartBeta
import Submission.Work.RTOwed.cuspChartRegion
import Submission.Work.RTOwed.chartKlein_strict
import Submission.Work.RTOwed.chartKlein_mem
import Submission.Work.RTOwed.mk_injOn_interior
import Submission.Work.RTOwed.chartKlein_wall
import Submission.Work.RTOwed.cuspCertWalls
import Submission.Work.FoldInst.Quotient
import Submission.Work.RTOwed.cuspCert.mbarPt_continuous
import Submission.Work.Cusp.Assembly
import Submission.Work.Cusp.TopBox
import Submission.Work.Cusp.isOpen_cuspChartBox
import Submission.Work.Cusp.isOpen_cuspBoxTop
import Submission.Work.RTOwed.CuspPiece
import Submission.Work.RTOwed.chartKlein_image_open
import Submission.Work.RTOwed.isOpen_piece
import Submission.Work.RTOwed.cuspWall_step
import Submission.Work.RTOwed.piece_subset_regionPre
import Submission.Work.RTOwed.regionPre_subset_pieces

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section
open Set Topology Function
open scoped BigOperators

namespace Work.RTOwed

/-- **The image of the region of a box is open.** -/
theorem mbarLow_image_open (v : Fin 5) {B : Set CuspE4} (hB : IsOpen B)
    (hBhi : ∀ q ∈ B, 11 / 10 ≤ q 3) : IsOpen (mbarLow v '' chartRegion B) := by
  have hBpos : ∀ q ∈ B, 0 < q 3 := fun q hq => lt_of_lt_of_le (by norm_num) (hBhi q hq)
  have h_eq : regionPre v B
      = ⋃ a : {a : Fin 48 // Cusp.cubeCusp a = v}, ⋃ k : Fin 3 → ℤ, piece v a.1 k B := by
    refine Set.Subset.antisymm ?_ ?_
    · intro y hy
      simpa only [Set.mem_iUnion] using regionPre_subset_pieces v hB hBhi hy
    · refine Set.iUnion_subset fun a => Set.iUnion_subset fun k => ?_
      exact piece_subset_regionPre v hB hBpos a.2 k
  refine (FoldInst.isOpen_quotient_iff_preimage
    (U := mbarLow v '' chartRegion B)).mpr ?_
  show IsOpen (regionPre v B)
  rw [h_eq]
  exact isOpen_iUnion fun a => isOpen_iUnion fun k => isOpen_piece v hB hBpos a.1 k

/-- **Openness of the image of the cusp chart** (the fields `mbarLow_open` and `mbarLow_openTop` of `Work.Cusp.CuspGlueData`, for the concrete `Work.RTOwed.mbarLow`). -/
theorem mbarLow_open (v : Fin 5) (c : Work.Cusp.E3) (δ : ℝ) :
    IsOpen (Work.RTOwed.mbarLow v ''
      {q : Work.Cusp.E4 | q ∈ Work.Cusp.cuspChartBox v c δ ∧
        q 3 ≤ Work.Cusp.beta (Work.Cusp.xOf q)}) ∧
    IsOpen (Work.RTOwed.mbarLow v ''
      {q : Work.Cusp.E4 | q ∈ Work.Cusp.cuspBoxTop v c δ ∧
        q 3 ≤ Work.Cusp.beta (Work.Cusp.xOf q)}) := by
  constructor
  · have hset : {q : Work.Cusp.E4 | q ∈ Work.Cusp.cuspChartBox v c δ ∧
        q 3 ≤ Work.Cusp.beta (Work.Cusp.xOf q)} = chartRegion (Work.Cusp.cuspChartBox v c δ) := by
      ext q
      simp only [chartRegion, Set.mem_inter_iff, Set.mem_ofPred_eq, xOf4_eq_xOf]
    rw [hset]
    exact mbarLow_image_open v (Work.Cusp.isOpen_cuspChartBox v c δ)
      (fun q hq => le_of_lt (by simpa only [Work.Cusp.s1] using hq.2.1))
  · have hset : {q : Work.Cusp.E4 | q ∈ Work.Cusp.cuspBoxTop v c δ ∧
        q 3 ≤ Work.Cusp.beta (Work.Cusp.xOf q)} = chartRegion (Work.Cusp.cuspBoxTop v c δ) := by
      ext q
      simp only [chartRegion, Set.mem_inter_iff, Set.mem_ofPred_eq, xOf4_eq_xOf]
    rw [hset]
    exact mbarLow_image_open v (Work.Cusp.isOpen_cuspBoxTop v c δ)
      (fun q hq => le_of_lt (by simpa only [Work.Cusp.s1] using hq.2.1))

end Work.RTOwed
