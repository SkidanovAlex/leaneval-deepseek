import Mathlib
import Submission.Work.ThomBordism.Grassmann.TB.tbZL_complexification_iso
import Submission.Work.Agree.mapFibreIso
import Submission.Work.Agree.complexificationIso
import Submission.Work.Agree.whitneySumRCongr
import Submission.Work.Gen.tautDual_iso_conjLine
import Submission.Work.Whitney.nonempty_bundleIso_whitneySum_comm

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# `ℂ ⊗_ℝ (equivC1R2 (realification (tautLine 4))) ≅ O(1) ⊕ O(-1)` over `ℂP⁴`

The real rank-`2` bundle `A₄ = mapFibre equivC1R2 (realification (tautLine 4))` is the underlying
real bundle of the tautological line bundle `O(-1)` of `ℂP⁴`, transported to the standard fibre
`ℝ²` through `equivC1R2`; its complexification is `O(-1) ⊕ \overline{O(-1)}`, which is
`O(1) ⊕ O(-1)` up to conjugation of the second summand and interchange of the summands.

The proof assembles three already-proved isomorphisms:

* `complexificationCore A₄ ≅ complexificationCore tbZL` — the two bundles differ only by the change
  of fibre `equivC1R2 ↔ expC`, and a change of fibre does not change the complexification
  (`Work.Agree.nonempty_bundleIso_mapFibre_of_iso` followed by
  `Work.Agree.nonempty_complexificationCore_bundleIso`);
* `complexificationCore tbZL ≅ O(-1) ⊕ \overline{O(-1)}` — the port of the `ℂP²` computation to
  `ℂP⁴` (`Work.ThomBordism.Grassmann.TB.tbZL_complexification_iso`);
* `O(-1) ⊕ \overline{O(-1)} ≅ O(1) ⊕ O(-1)` — conjugation of the tautological line bundle
  (`Work.Gen.tautDual_iso_conjLine`) together with the commutativity of the Whitney sum
  (`Work.Whitney.nonempty_bundleIso_whitneySum_comm`).
-/

namespace Work.ThomBordism.Grassmann.P2Base

open Work.TangentClasses

noncomputable section

/-- `A₄ = mapFibre equivC1R2 (realification (tautLine 4))`: the underlying real bundle of the
tautological line bundle of `ℂP⁴` in the standard fibre `ℝ²`. -/
abbrev A4c : Work.TangentClasses.RealBundle (Work.Projective.CP 4)
    (EuclideanSpace ℝ (Fin 2)) (Fin 5) :=
  RealBundle.mapFibre equivC1R2 (Work.Thom.realification (Work.Gen.tautLine 4))

/-- The two presentations `mapFibre equivC1R2` and `mapFibre expC` of the realification of
`O(-1)` have isomorphic complexifications: they differ only by the change of fibre. -/
theorem nonempty_complexificationCore_A4_tbZL :
    Nonempty (Work.Thom.BundleIso (Work.Thom.complexificationCore A4c)
      (Work.Thom.complexificationCore Work.ThomBordism.Grassmann.tbZL)) := by
  obtain ⟨e⟩ := Work.Agree.nonempty_bundleIso_mapFibre_of_iso
    (Work.Thom.realification (Work.Gen.tautLine 4))
    (Work.Thom.realification (Work.Gen.tautLine 4))
    equivC1R2 expC ⟨Work.Thom.BundleIso.refl _⟩
  exact Work.Agree.nonempty_complexificationCore_bundleIso _ _ e

/-- The conjugation of `O(-1)` and the commutativity of the Whitney sum turn
`O(-1) ⊕ \overline{O(-1)}` into `O(1) ⊕ O(-1)`. -/
theorem nonempty_bundleIso_conjLine_comm :
    Nonempty (Work.Thom.BundleIso
      (Work.Whitney.whitneySum (Work.Gen.tautLine 4) (Work.Gen.conjLine 4))
      (Work.Whitney.whitneySum (Work.Gen.tautDual 4) (Work.Gen.tautLine 4))) := by
  obtain ⟨eDC⟩ := Work.Gen.tautDual_iso_conjLine 4
  obtain ⟨eA⟩ := Work.Agree.nonempty_bundleIso_sumCore_congr (𝕜 := ℂ)
    (Work.Whitney.sumFibreC 1 1) (Work.Whitney.sumFibreC 1 1)
    (Work.Gen.tautLine 4) (Work.Gen.tautLine 4)
    (Work.Gen.conjLine 4) (Work.Gen.tautDual 4)
    (Work.Thom.BundleIso.refl _) eDC.symm
  obtain ⟨eComm⟩ := Work.Whitney.nonempty_bundleIso_whitneySum_comm
    (Work.Gen.tautLine 4) (Work.Gen.tautDual 4)
  exact ⟨eA.trans eComm⟩

theorem cxA_iso :
    Nonempty (Work.Thom.BundleIso
      (Work.Thom.complexificationCore
        (Work.TangentClasses.RealBundle.mapFibre Work.ThomBordism.Grassmann.equivC1R2
          (Work.Thom.realification (Work.Gen.tautLine 4))))
      (Work.Whitney.whitneySum
        (Work.Gen.tautDual 4) (Work.Gen.tautLine 4))) := by
  obtain ⟨e1⟩ := nonempty_complexificationCore_A4_tbZL
  obtain ⟨e2⟩ := Work.ThomBordism.Grassmann.TB.tbZL_complexification_iso
  obtain ⟨e3⟩ := nonempty_bundleIso_conjLine_comm
  exact ⟨e1.trans (e2.trans e3)⟩

end

end Work.ThomBordism.Grassmann.P2Base
