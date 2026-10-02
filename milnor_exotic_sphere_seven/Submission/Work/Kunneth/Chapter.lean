import Submission.Work.Kunneth.TensorDefs
import Submission.Work.Kunneth.TensorCo
import Submission.Work.Kunneth.Algebra
import Submission.Work.Kunneth.homology_tpC_homSum
import Submission.Work.Kunneth.kunneth_homology
import Submission.Work.Kunneth.kunneth_cohomology
import Submission.Work.Kunneth.kunneth_cohomology_cpn
import Submission.Work.Kunneth.kunneth_space
import Submission.Work.Kunneth.CrossGen
import Submission.Work.Kunneth.KunnethCross
import Submission.Work.Kunneth.tpMap_homotopy
import Submission.Work.Kunneth.homology_dual_tpC_ezaw
import Submission.Work.Kunneth.homology_dual_tpC_homSum
import Submission.Work.Kunneth.cpn_kunneth_hypotheses
import Submission.Work.Kunneth.CrossSum
import Submission.Work.Kunneth.Tensor
import Submission.Work.Kunneth.Basic
import Submission.Work.Kunneth.awHom_d
import Submission.Work.Kunneth.AW
import Submission.Work.Kunneth.ezSummand
import Submission.Work.Kunneth.EZ
import Submission.Work.Kunneth.EZMap
import Submission.Work.Kunneth.ezHom_d
import Submission.Work.Kunneth.Cross
import Submission.Work.Kunneth.crossCochain_apply
import Submission.Work.Kunneth.crossCochain_isCocycle
import Submission.Work.Kunneth.CrossCup
import Submission.Work.Kunneth.CrossH
import Submission.Work.Kunneth.crossH_bilinear
import Submission.Work.Kunneth.crossTensor
import Submission.Work.Kunneth.CrossHBilin
import Submission.Work.Kunneth.aw_ez_homotopy
import Submission.Work.Kunneth.ez_aw_homotopy
import Submission.Work.Kunneth.TopCat
import Submission.Work.Kunneth.ez_aw_homotopyT
import Submission.Work.Kunneth.tpDpq_comp
import Submission.Work.Kunneth.tpD_comp_tpD
import Submission.Work.Kunneth.EZAWTensor
import Submission.Work.Kunneth.exists_splitting
import Submission.Work.Kunneth.ctens_dual_tpC
import Submission.Work.Kunneth.homology_ctens
import Submission.Work.Kunneth.piFinIso
import Submission.Work.Kunneth.kunneth_h4_cp2cp2
import Submission.Work.Kunneth.spanCriterion
import Submission.Work.Kunneth.kronecker_ezChain
import Submission.Work.Kunneth.ShuffleGood
import Submission.Work.Kunneth.CrossShuffle
import Submission.Work.Kunneth.HomCross
import Submission.Work.Kunneth.pullbackH_cohomologyClassOf
import Submission.Work.Kunneth.crossH_cohomologyClassOf
import Submission.Work.Kunneth.cp2Cross
import Submission.Work.Kunneth.cohomologyClassOf_comp_normP
import Submission.Work.Kunneth.kronH_unconditional
import Submission.Work.Kunneth.pullbackHCup
import Submission.Work.Kunneth.span_of_unimodular_pairing
import Submission.Work.Kunneth.cp2cp2Fund
import Submission.Work.Kunneth.cp2cp2Pairing
import Submission.Work.Kunneth.cp2cp2Span
import Submission.Work.Kunneth.kunneth_cpn_free
import Submission.Work.Kunneth.cp2cp2Model
import Submission.Work.Kunneth.cp2H_uCoh
import Submission.Work.Kunneth.ssetNaturality
import Submission.Work.Kunneth.cp2cp2ModelCpp
import Submission.Work.Kunneth.cp2cp2H8
import Submission.Work.Kunneth.cp2cp2H8Span
import Submission.Work.Kunneth.HomQuot
import Submission.Work.Kunneth.HomValue
import Submission.Work.Kunneth.FlatDefs
import Submission.Work.Kunneth.hIn_tpLof_cycle
import Submission.Work.Kunneth.FlatGen
import Submission.Work.Kunneth.exists_splitting_transparent
import Submission.Work.Kunneth.flatKunneth_exists
import Submission.Work.Kunneth.kunnethCrossExistence

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The `Work.Kunneth` chapter

Single entry point for the Eilenberg–Zilber / Künneth chapter.  See
`Submission/Work/Kunneth/README.md` for the conventions, the list of results and the parts that
are still open.

**The `ℂP² × ℂP²` results and their consumers.**  `Work.Kunneth.cp2cp2ModelCpp` inhabits
`Work.Projective.CP2CP2Model cppSSet` for the space `ℂP² × ℂP²`, and
`Work.Kunneth.cppC_generates : Submodule.span ℤ {cp2cp2ModelCpp.c} = ⊤` is the `hc` argument of
`Work.Gen.cp2cp2NumbersOf`; the module `Submission.Work.Kunneth.cp2cp2H8Span` is written in the
default instance convention precisely so that these statements are interchangeable with the ones
of area GEN (`Module ℤ ↥M` resolves to `M.isModule` on both sides).

**Importers** of the tensor-product statements should add the `attribute` line they need; see the
module docstring of `Work.Kunneth.TensorDefs` and §6 of `README.md`:

```
attribute [-instance] AddCommGroup.toIntModule
```
-/

