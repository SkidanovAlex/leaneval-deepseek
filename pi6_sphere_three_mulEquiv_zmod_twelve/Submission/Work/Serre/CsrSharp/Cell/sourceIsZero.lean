import Mathlib
import Submission.Work.Serre.CsrSharp.Defs
import Submission.Work.Serre.csrDefs
import Submission.Work.Serre.Csr.Chain
import Submission.Work.Serre.Csr.DiscPair
import Submission.Work.Serre.Csr.Base
import Submission.Work.Serre.Csr.Defs
import Submission.Work.Serre.Csr.Transfer
import Submission.Work.Serre.PerCell.exists_homeo_pair
import Submission.Work.Cohomology.relChainsHomeomorphCompat
import Submission.Work.RatHurewicz.AttachPush.CellInterior

namespace Work.Serre.CsrSharp.Cell

/-- The vanishing of the relative rational homology of the source pair of the per-cell map below
the cell dimension: for a Serre fibration `q : E → Z` over `Z = attachCells n Y ι f` and `o` the open
half-ball around the centre `c` of the `i`-th cell, the pair `(q⁻¹'o, q⁻¹'(o \ {c}))` has vanishing
relative rational homology in every degree `m < n+2`.

Proof route: `Work.Serre.Csr.csrTransferPair` (the transfer homeomorphism
`(pPre f q i (dOpen n (1/2)), pPre f q i (dPunct n (1/2))) ≅ (q⁻¹'o, q⁻¹'(o\{c}))`), then
`Work.Serre.csrDiscChain` and `Work.Serre.Csr.csrSourceDisc_isZero` (the vanishing of the disc pair
of the pullback below `n+2`, over `ℤ`), and base change
(`Work.Serre.Csr.isZero_relChainsR_rat_of_isZero_int`). -/
theorem sourceIsZero (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (hq : Work.StemsB.IsSerreFibration q)
    (i : ι) (m : ℕ) (hm : m < n+2) :
    CategoryTheory.Limits.IsZero
      ((Work.StemsB.relChainsR ℚ (TopCat.of ↥(q ⁻¹' Work.Serre.csrOpenBall n Y ι f i))
        {x : ↥(q ⁻¹' Work.Serre.csrOpenBall n Y ι f i) |
          (x : E) ∈ q ⁻¹' (Work.Serre.csrOpenBall n Y ι f i \ {Work.Serre.csrCentre n Y ι f i})}).homology m) := by
  refine Work.Serre.Csr.isZero_relChainsR_rat_of_isZero_int
    (TopCat.of ↥(q ⁻¹' Work.Serre.csrOpenBall n Y ι f i))
    {x : ↥(q ⁻¹' Work.Serre.csrOpenBall n Y ι f i) |
      (x : E) ∈ q ⁻¹' (Work.Serre.csrOpenBall n Y ι f i \ {Work.Serre.csrCentre n Y ι f i})}
    m ?_
  obtain ⟨e₁⟩ := Work.Serre.Csr.csrTransferPair n Y ι f q i m
  obtain ⟨e₂⟩ := Work.Serre.csrDiscChain f q hq i (1/4) (by norm_num) (by norm_num) m
  exact (Work.Serre.Csr.csrSourceDisc_isZero n Y ι f q hq i m hm).of_iso (e₁.symm ≪≫ e₂)

end Work.Serre.CsrSharp.Cell
