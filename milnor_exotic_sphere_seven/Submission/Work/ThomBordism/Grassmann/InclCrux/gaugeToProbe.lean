import Mathlib
import Submission.Work.ThomBordism.Grassmann.Model
import Submission.Work.Projective.Basic
import Submission.Work.ThomBordism.Grassmann.P2Base.Frame
import Submission.Work.ThomBordism.Grassmann.P2Base.Gauge
import Submission.Work.ThomBordism.Grassmann.P2Base.cxA_iso
import Submission.Work.ThomBordism.Grassmann.CxAssembly
import Submission.Work.ThomBordism.Grassmann.c4_tautSum4_CP4_rat_ne_zero
import Submission.Work.Whitney.complexificationCore_whitneySumR
import Submission.Work.Whitney.nonempty_bundleIso_whitneySum_comm
import Submission.Work.Agree.complexificationIso
import Submission.Work.Agree.whitneySumRCongr

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
# From the gauge `V₄ ≅ Z₄` to the `p₂`-probe at `(4,8)`

The gauge isomorphism `P2Base.V4 ≅ P2Base.Z4` identifies the pullback of the tautological oriented
`4`-plane bundle along `p2Map : ℂP⁴ → G̃r₄(ℝ¹²)` with `A4 ⊕_ℝ A4`,
`A4 = mapFibre equivC1R2 (realification O(-1))`, whose complexification is
`O(1) ⊕ O(-1)`.  Hence the pullback of `p₂` is `c₄(O(1)² ⊕ O(-1)²) = c₄(tautSum4)` up to a bundle
isomorphism, which is rationally non-zero (`c4_tautSum4_CP4_rat_ne_zero`).
-/

namespace Work.ThomBordism.Grassmann.InclCrux

open Work.TangentClasses

noncomputable section

/-- `O(-1)` over `ℂP⁴`. -/
abbrev L4 : VectorBundleCore ℂ (Work.Projective.CP 4) (EuclideanSpace ℂ (Fin 1)) (Fin 5) :=
  Work.Gen.tautLine 4

/-- `O(1)` over `ℂP⁴`. -/
abbrev Ld4 : VectorBundleCore ℂ (Work.Projective.CP 4) (EuclideanSpace ℂ (Fin 1)) (Fin 5) :=
  Work.Gen.tautDual 4

/-- The complexification of `Z4 = A4 ⊕_ℝ A4` is the sum of two copies of `O(1) ⊕ O(-1)`. -/
theorem cxZ_iso : Nonempty (Work.Thom.BundleIso (Work.Thom.complexificationCore P2Base.Z4)
    (Work.Whitney.whitneySum (Work.Gen.lineC 4) (Work.Gen.lineC 4))) := by
  have hZ : Work.Thom.complexificationCore P2Base.Z4
      = Work.Whitney.whitneySum (Work.Thom.complexificationCore P2Base.A4)
        (Work.Thom.complexificationCore P2Base.A4) :=
    Work.Whitney.complexificationCore_whitneySumR P2Base.A4 P2Base.A4
  obtain ⟨e⟩ := P2Base.cxA_iso
  obtain ⟨e2⟩ := Work.Agree.nonempty_bundleIso_sumCore_congr
    (Work.Whitney.sumFibreC 2 2) (Work.Whitney.sumFibreC 2 2)
    (Work.Thom.complexificationCore P2Base.A4) (Work.Whitney.whitneySum Ld4 L4)
    (Work.Thom.complexificationCore P2Base.A4) (Work.Whitney.whitneySum Ld4 L4) e e
  rw [hZ]
  exact ⟨e2⟩

/-- **The `p₂`-probe at `(4,8)` from the gauge.** -/
theorem p2ProbeBase8_of_gauge
    (hg : Nonempty (Work.Thom.BundleIso P2Base.V4 P2Base.Z4)) :
    ∃ σ : C(Work.Projective.CP 4, OG 4 8),
      TensorProduct.tmul ℤ (1 : ℚ) ((Work.Thom.CohMap σ ℤ 8).hom (p2 4 8)) ≠ 0 := by
  refine ⟨P2Base.p2Map, ?_⟩
  have hcxV : Nonempty (Work.Thom.BundleIso (Work.Thom.complexificationCore P2Base.V4)
      (Work.Thom.complexificationCore P2Base.Z4)) := by
    obtain ⟨e⟩ := hg
    exact Work.Agree.nonempty_complexificationCore_bundleIso P2Base.V4 P2Base.Z4 e
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
    obtain ⟨eV⟩ := hcxV
    obtain ⟨eZ⟩ := cxZ_iso
    rw [Work.Thom.chernClass_BundleIso
      (Work.Thom.complexificationCore P2Base.V4)
      (Work.Thom.complexificationCore P2Base.Z4) eV]
    rw [Work.Thom.chernClass_BundleIso
      (Work.Thom.complexificationCore P2Base.Z4)
      (Work.Whitney.whitneySum (Work.Gen.lineC 4) (Work.Gen.lineC 4)) eZ]
  change TensorProduct.tmul ℤ (1 : ℚ)
    ((Work.Thom.CohMap P2Base.p2Map ℤ 8).hom
      (Work.Thom.pontryaginClass 2 (tautologicalBundle 4 8))) ≠ 0
  rw [h1, h2, h3]
  exact c4_tautSum4_CP4_rat_ne_zero

end

end Work.ThomBordism.Grassmann.InclCrux
