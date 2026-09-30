/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Work.Subdivision.Basic
import Submission.Work.Subdivision.OrderComplex
import Submission.Work.Subdivision.orderD_comp
import Submission.Work.Subdivision.CellChain
import Submission.Work.Subdivision.Subdiv
import Submission.Work.Subdivision.subdivCell_support
import Submission.Work.Subdivision.D_coneLM
import Submission.Work.Subdivision.D_coneLM_zero
import Submission.Work.Subdivision.D_subdivCell
import Submission.Work.Subdivision.SdChain
import Submission.Work.Subdivision.SubdivChain
import Submission.Work.Subdivision.subdivCpt_comm
import Submission.Work.Subdivision.SubdivAssembly
import Submission.Work.Subdivision.SubComplex
import Submission.Work.Subdivision.quotD_comp_quotD
import Submission.Work.Subdivision.incl_proj
import Submission.Work.Subdivision.SubDataQuot
import Submission.Work.Subdivision.shortComplexOf_shortExact
import Submission.Work.Subdivision.SubDataCpt
import Submission.Work.Subdivision.restrictCptMap_comm
import Submission.Work.Subdivision.quotCptMap_comm
import Submission.Work.Subdivision.incl_restrictCptMap
import Submission.Work.Subdivision.proj_quotCptMap
import Submission.Work.Subdivision.SubDataSES
import Submission.Work.Subdivision.quasiIso_tau2
import Submission.Work.Subdivision.quasiIso_tau2_poly
import Submission.Work.Subdivision.SubDataQuasiIso
import Submission.Work.Subdivision.Filtration
import Submission.Work.Subdivision.subdivCpt_mem
import Submission.Work.Subdivision.ComapChain
import Submission.Work.Subdivision.comapChain_comm
import Submission.Work.Subdivision.ComapChainIso
import Submission.Work.Subdivision.SkelLevel
import Submission.Work.Subdivision.SkelInduction
import Submission.Work.Subdivision.rel_hf
import Submission.Work.Subdivision.subdivSkel_zero
import Submission.Work.Subdivision.cellRelIso_subdivSkel
import Submission.Work.Subdivision.quasiIso_subdiv_of_maxDim
import Submission.Work.Subdivision.exists_sd_deltaCx
import Submission.Work.Subdivision.Support
import Submission.Work.Subdivision.Local
import Submission.Work.Subdivision.Level
import Submission.Work.Subdivision.sdTopMod_insert
import Submission.Work.Subdivision.sdTopMod_inf_leSub
import Submission.Work.Subdivision.cellTopMod_insert_succ
import Submission.Work.Subdivision.cellTopMod_inf_span
import Submission.Work.Subdivision.Piece
import Submission.Work.Subdivision.PieceEquiv
import Submission.Work.Subdivision.PieceQuot
import Submission.Work.Subdivision.sdPieceMapLin_bijective
import Submission.Work.Subdivision.sdPieceMapLin_comm
import Submission.Work.Subdivision.cellPieceCoeffF_bijective
import Submission.Work.Subdivision.subdivCpt_mem_top
import Submission.Work.Subdivision.PieceIso
import Submission.Work.Subdivision.LevelMap
import Submission.Work.Subdivision.SubDataEq
import Submission.Work.Subdivision.PieceSquare
import Submission.Work.Subdivision.PieceInduction
import Submission.Work.Subdivision.GradeMap
import Submission.Work.Subdivision.LocalIso
import Submission.Work.Subdivision.LocalIsoCx
import Submission.Work.Subdivision.starLM_subdivCell
import Submission.Work.Subdivision.LocalIsoMain

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.Subdivision` — single import for the whole area

Importing this module gives the whole subdivision chapter:

* `PolyCW` (`Basic`), the order complex `Simplex`/`D`/`orderD_comp`
  (`OrderComplex`, `orderD_comp`), the cellular chain complex `cellChain`
  (`CellChain`),
* the cone recursion `coneLM`/`subdivCell`/`subdivLM` (`Subdiv`) with the support
  invariant and the cone identities (`subdivCell_support`, `D_coneLM`,
  `D_coneLM_zero`, `D_subdivCell`),
* the subdivided chain complex `sdChain` (`SdChain`) and the subdivision chain
  map `subdiv : cellChain P ⟶ sdChain P` (`SubdivAssembly`) with the chain-map
  equation `PolyCW.subdiv_comm`,
* the sub/quotient machinery `SubData.chain/quot/incl/proj/shortComplexOf` with
  its short exactness (`SubComplex`, `SubDataQuot`, `shortComplexOf_shortExact`),
  its functoriality (`SubDataCpt`, `SubDataSES`, `SubDataQuasiIso`,
  `incl_restrictCptMap`, `proj_quotCptMap`, `restrictCptMap_comm`,
  `quotCptMap_comm`) and the five lemma for a compatible subcomplex
  `Work.Subdivision.quasiIso_of_sub_quot`,
* the relative subcomplexes of a filtration (`ComapChain`, `ComapChainIso`,
  `comapChain_comm`),
* the skeletal filtrations `cellSub`/`sdSub` (`Filtration`), the relative
  subcomplexes `cellRel`/`sdRel` with their identification with the previous
  skeleta (`SkelLevel`), and the skeletal induction
  `PolyCW.subdiv_quasiIso` (`SkelInduction`).

* the local complex of a cell `locCx` (`Local`), its generator `locClsAux`, the local
  map `locMap`/`locMapAux` and the per-cell condition `LocallySpherical`,
* the refined per-cell filtrations `cellTop`/`sdTop` of a skeletal level and their
  pieces (`Level`, `Piece`), and the degreewise identification of the pieces with
  the local modules (`PieceEquiv`).

* the per-cell local complex `locCx` together with its generator and the per-cell
  condition `LocallySpherical` (`Local`),
* the two pieces of a skeletal level and their identification with the local
  complex of the new cell and with `unitCx (n+1)` (`PieceQuot`, `PieceIso`,
  `PieceSquare`),
* the cell-by-cell induction over the refined filtrations (`LevelMap`,
  `PieceInduction`), and

**`PolyCW.subdiv_quasiIso_of_local (hdd) (haug) (LocallySpherical P hdd haug) :
QuasiIso (subdiv P hdd haug)`** — the blueprinted `subdiv_quasiIso`, with the local
hypothesis supplied per cell.  `PolyCW.gradeMap_quasiIso_of_local` derives the
graded-map hypothesis `hlocal` of `PolyCW.subdiv_quasiIso` from it as well
(`GradeMap`).  The transport of subcomplex data along an equality
(`SubData.isoOfSubEq`, `SubData.quasiIso_sub_data_eq`) lives in `SubDataEq`.

See `NOTES.md` in this directory for the conventions and for the precise shape of
the local hypothesis of `subdiv_quasiIso`.
-/
