import Mathlib
import Submission.Work.ThomBordism.Grassmann.CxAssembly

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The complexification of the standard rank-`2` real bundle over `ℂP²`

`Work.ThomBordism.Grassmann.zStd` is the rank-`2` real bundle over `ℂP²` obtained from the
tautological dual line bundle `O(1)` of `ℂP²` by forgetting the complex structure and changing the
fibre to `ℝ²`.  Its complexification `zStd ⊗_ℝ ℂ` is `O(1) ⊕ O(-1)`, presented as the Whitney sum
`Work.Whitney.whitneySum (Work.Gen.tautDual 2) (Work.Gen.tautLine 2)`:

    `Work.ThomBordism.Grassmann.zStd_complexification_iso`.

The proof is that of `Work.ThomBordism.Grassmann.nonempty_complexificationCore_zStd_lineC`
(`Submission/Work/ThomBordism/Grassmann/CxAssembly.lean`), whose gauge is built from

* the diagonalisation of the model map `cMat a` (the complexification of the real `2 × 2` matrix
  `[[Re a, -Im a],[Im a, Re a]]`) in the eigenbasis `(1, ∓i)` of `qMat`,
* the squared-norm gauge `Work.Gen.gaugeFun`, which compares the conjugate transition scalar `ā`
  with `a⁻¹`, and
* the fact that the abstract identification `equivC1R2` of `zStd` enters only through
  `Gm = cxTrans (equivC1R2 ∘ expC⁻¹)`, which conjugates `cMat` into the transition function of
  `complexificationCore zStd`.
-/

namespace Work.ThomBordism.Grassmann

theorem zStd_complexification_iso :
    Nonempty (Work.Thom.BundleIso
      (Work.Thom.complexificationCore Work.ThomBordism.Grassmann.zStd)
      (Work.Whitney.whitneySum (Work.Gen.tautDual 2) (Work.Gen.tautLine 2))) :=
  nonempty_complexificationCore_zStd_lineC

end Work.ThomBordism.Grassmann
