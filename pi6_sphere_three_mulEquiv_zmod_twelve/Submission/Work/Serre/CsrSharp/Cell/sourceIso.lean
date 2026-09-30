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

open CategoryTheory CategoryTheory.Limits

/-- The relative rational homology of the source pair of the per-cell map: for a Serre fibration
`q : E → Z` over `Z = attachCells n Y ι f`, the pair `(q⁻¹'o, q⁻¹'(o \ {c}))` (with `o` the open
half-ball around the centre `c` of the `i`-th cell) has, in degree `k + (n+2)`, the homology of the
fibre of `q` over `c` in degree `k`.

Proof route: `Work.Serre.Csr.csrTransferPair` gives
`H_m(q⁻¹'o, q⁻¹'(o\{c});ℤ) ≅ H_m(pPre f q i (dOpen n (1/2)), pPre f q i (dPunct n (1/2));ℤ)` (the
homeomorphism `transferHomeo` of `Submission/Work/Serre/Csr/Transfer.lean`); then
`Work.Serre.csrDiscChain` (the open-ball pair is the disc pair up to compression) and
`Work.Serre.Csr.csrSourceDiscIso` (Serre's E2(d) computation for the pullback of `q` along the
characteristic map), both over `ℤ`; finally base change to `ℚ`
(`Work.Serre.Csr.relChainsRHomologyIsoRat`, `Work.Serre.Csr.absHomologyIsoRat`, noting
`csrCentre = cellOrigin` definitionally). -/
theorem sourceIso (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (hq : Work.StemsB.IsSerreFibration q)
    (i : ι) (k : ℕ) :
    Nonempty ((Work.StemsB.relChainsR ℚ (TopCat.of ↥(q ⁻¹' Work.Serre.csrOpenBall n Y ι f i))
        {x : ↥(q ⁻¹' Work.Serre.csrOpenBall n Y ι f i) |
          (x : E) ∈ q ⁻¹' (Work.Serre.csrOpenBall n Y ι f i \ {Work.Serre.csrCentre n Y ι f i})}).homology
          (k + (n+2))
      ≅ (Work.Cohomology.singularChains ℚ
          (TopCat.of (Work.StemsB.fibre q (Work.Serre.csrCentre n Y ι f i)))).homology k) := by
  -- The pair condition describing the relative part of the target pair.
  obtain ⟨eT⟩ := Work.Serre.Csr.csrTransferPair n Y ι f q i (k + (n+2))
  -- The open model ball pair is the closed disc pair, up to compression.
  obtain ⟨eD⟩ := Work.Serre.csrDiscChain f q hq i (1/4) (by norm_num) (by norm_num) (k + (n+2))
  -- Serre's E2(d) computation for the pullback along the characteristic map, over `ℤ`.
  obtain ⟨eS⟩ := Work.Serre.Csr.csrSourceDiscIso n Y ι f q hq i k
  -- Base change of the relative homology of the target pair.
  obtain ⟨eR⟩ := Work.Serre.Csr.relChainsRHomologyIsoRat
    (TopCat.of ↥(q ⁻¹' Work.Serre.csrOpenBall n Y ι f i))
    {x : ↥(q ⁻¹' Work.Serre.csrOpenBall n Y ι f i) |
      (x : E) ∈ q ⁻¹' (Work.Serre.csrOpenBall n Y ι f i \ {Work.Serre.csrCentre n Y ι f i})}
    (k + (n+2))
  -- Base change of the absolute homology of the fibre (`csrCentre = cellOrigin` definitionally).
  obtain ⟨eA⟩ := Work.Serre.Csr.absHomologyIsoRat
    (TopCat.of (Work.StemsB.fibre q (Work.Serre.csrCentre n Y ι f i))) k
  exact ⟨eR ≪≫ Work.StemsB.IntRatF.mapIso (eT.symm ≪≫ eD ≪≫ eS) ≪≫ eA.symm⟩

end Work.Serre.CsrSharp.Cell
