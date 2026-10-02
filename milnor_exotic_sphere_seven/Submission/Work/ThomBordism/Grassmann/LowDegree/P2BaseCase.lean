import Mathlib
import Submission.Work.ThomBordism.Grassmann.Model
import Submission.Work.Projective.Basic
import Submission.Work.ThomBordism.Grassmann.P2Base.Gauge
import Submission.Work.ThomBordism.Grassmann.P2Base.cxA_iso
import Submission.Work.ThomBordism.Grassmann.LowDegree.P2GaugeIso
import Submission.Work.ThomBordism.Grassmann.c4_tautSum4_CP4_rat_ne_zero
import Submission.Work.Whitney.complexificationCore_whitneySumR
import Submission.Work.Agree.complexificationIso
import Submission.Work.Agree.whitneySumRCongr

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# The base case `(k,m) = (4,8)` of the `p₂`-probe

`P2Base.p2Map : ℂP⁴ → G̃r₄(ℝ¹²)` pulls `p₂(γ)` back to a rationally non-zero class:

`p₂(γ_{4,8}) ↦ p₂(V₄)` (`pontryaginClass_comap`), `= c₄(ℂ ⊗ V₄)`, and
`ℂ ⊗ V₄ ≅ ℂ ⊗ Z₄ = (ℂ ⊗ A₄) ⊕ (ℂ ⊗ A₄) ≅ (O(1) ⊕ O(-1))² = tautSum4`, whose `c₄` is rationally
non-zero by `c4_tautSum4_CP4_rat_ne_zero`.

The isomorphisms are `cxV_iso` (from the gauge `gaugeIso : V₄ ≅ Z₄`, proved in
`LowDegree/P2GaugeIso.lean`) and `cxZ_iso` (from `P2Base.cxA_iso`, i.e.
`ℂ ⊗ A₄ ≅ O(1) ⊕ O(-1)` over `ℂP⁴`, proved in `P2Base/cxA_iso.lean`).
-/

namespace Work.ThomBordism.Grassmann.LowDegree

open Work.TangentClasses Work.Projective
open Work.ThomBordism.Grassmann.P2Base

noncomputable section

abbrev L4 : VectorBundleCore ℂ (CP 4) (EuclideanSpace ℂ (Fin 1)) (Fin 5) := Work.Gen.tautLine 4

abbrev Ld4 : VectorBundleCore ℂ (CP 4) (EuclideanSpace ℂ (Fin 1)) (Fin 5) := Work.Gen.tautDual 4

theorem cxZ_iso : Nonempty (Work.Thom.BundleIso (Work.Thom.complexificationCore Z4)
    (Work.Whitney.whitneySum (Work.Gen.lineC 4) (Work.Gen.lineC 4))) := by
  have hZ : Work.Thom.complexificationCore Z4
      = Work.Whitney.whitneySum (Work.Thom.complexificationCore A4)
        (Work.Thom.complexificationCore A4) :=
    Work.Whitney.complexificationCore_whitneySumR A4 A4
  obtain ⟨e⟩ := P2Base.cxA_iso
  obtain ⟨e2⟩ := Work.Agree.nonempty_bundleIso_sumCore_congr
    (Work.Whitney.sumFibreC 2 2) (Work.Whitney.sumFibreC 2 2)
    (Work.Thom.complexificationCore A4) (Work.Whitney.whitneySum Ld4 L4)
    (Work.Thom.complexificationCore A4) (Work.Whitney.whitneySum Ld4 L4) e e
  rw [hZ]
  exact ⟨e2⟩

theorem cxV_iso : Nonempty (Work.Thom.BundleIso (Work.Thom.complexificationCore V4)
    (Work.Thom.complexificationCore Z4)) := by
  obtain ⟨e⟩ := gaugeIso
  exact Work.Agree.nonempty_complexificationCore_bundleIso V4 Z4 e

/-- **The base case of the `p₂`-probe**: the map `ℂP⁴ → G̃r₄(ℝ¹²)` of
`Submission/Work/ThomBordism/Grassmann/P2Base/Frame.lean` detects `p₂`. -/
theorem p2ProbeCP4BaseWitness :
    ∃ σ : C(CP 4, OG 4 8),
      TensorProduct.tmul ℤ (1 : ℚ) ((Work.Thom.CohMap σ ℤ 8).hom (p2 4 8)) ≠ 0 := by
  refine ⟨P2Base.p2Map, ?_⟩
  have h1 : (Work.Thom.CohMap P2Base.p2Map ℤ (4 * 2)).hom
        (Work.Thom.pontryaginClass 2 (tautologicalBundle 4 8))
      = Work.Thom.pontryaginClass 2
        (Work.Thom.bundleComap (tautologicalBundle 4 8) P2Base.p2Map) :=
    (Work.Thom.pontryaginClass_comap (i := 2) (tautologicalBundle 4 8) P2Base.p2Map).symm
  have h2 : Work.Thom.pontryaginClass 2
        (Work.Thom.bundleComap (tautologicalBundle 4 8) P2Base.p2Map)
      = Work.Thom.chernClass 4 4
        (Work.Thom.complexificationCore
          (Work.Thom.bundleComap (tautologicalBundle 4 8) P2Base.p2Map)) := by
    unfold Work.Thom.pontryaginClass
    rw [Work.Thom.cohTransport_self]
    simp
  have h3 : Work.Thom.chernClass 4 4
        (Work.Thom.complexificationCore
          (Work.Thom.bundleComap (tautologicalBundle 4 8) P2Base.p2Map))
      = Work.Thom.chernClass 4 4
        (Work.Whitney.whitneySum (Work.Gen.lineC 4) (Work.Gen.lineC 4)) := by
    obtain ⟨eV⟩ := cxV_iso
    obtain ⟨eZ⟩ := cxZ_iso
    rw [Work.Thom.chernClass_BundleIso
      (Work.Thom.complexificationCore V4)
      (Work.Thom.complexificationCore Z4) eV]
    rw [Work.Thom.chernClass_BundleIso
      (Work.Thom.complexificationCore Z4)
      (Work.Whitney.whitneySum (Work.Gen.lineC 4) (Work.Gen.lineC 4)) eZ]
  change TensorProduct.tmul ℤ (1 : ℚ)
    ((Work.Thom.CohMap P2Base.p2Map ℤ 8).hom
      (Work.Thom.pontryaginClass 2 (tautologicalBundle 4 8))) ≠ 0
  rw [h1, h2, h3]
  exact c4_tautSum4_CP4_rat_ne_zero

end

end Work.ThomBordism.Grassmann.LowDegree
