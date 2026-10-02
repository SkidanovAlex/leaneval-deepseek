import Mathlib
import Submission.Work.Gen.Basic
import Submission.Work.Thom.chernClass
import Submission.Work.Thom.realification
import Submission.Work.Gen.ChernGenerator
import Submission.Work.Gen.uSqGenerates
import Submission.Work.Projective.CP4Concrete
import Submission.Work.Thom.Gysin
import Submission.Work.Gen.chernClass_tautLine
import Submission.Work.Gen.ConjIso
import Submission.Work.Gen.tautDual_iso_conjLine

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# `H^k` of the punctured `realification (tautLine 4)` vanishes off degrees `0` and `9`

The punctured total space of the tautological line bundle `O(-1) = tautLine 4` on `ℂP⁴` is the
punctured model space `ℂ⁵∖0 ≃ S⁹`.  Rather than rebuilding the homeomorphism `tautDualPunctHomeo`
for `tautLine`, we transport the already proved vanishing for the *dual* bundle
(`Work.Gen.uSqGen_puncturedTautDual4HZero`) across the two line-bundle isomorphisms

* `O(1) ≅ \overline{O(-1)}` (`Work.Gen.tautDual_iso_conjLine`, complex) and
* `\overline{O(-1)} ≅ O(-1)` (`Work.Gen.conjIso`, real, fibrewise conjugation),

each of which induces a homeomorphism of the punctured total spaces
(`Work.Thom.punctHomeo`, `Work.Thom.BundleIso.punctHomeomorph`).
-/

namespace Work.ThomBordism.Grassmann

/-- A homotopy equivalence induces an isomorphism on cohomology, hence transports `Subsingleton`. -/
private theorem subsingleton_cohomology_of_homotopyEquiv {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ)
    (h : Subsingleton (Work.Thom.Coh ℤ n X)) : Subsingleton (Work.Thom.Coh ℤ n Y) := by
  obtain ⟨iso⟩ := Work.Cohomology.cohomologyIso_of_homotopyEquiv e n
  have hsurj : Function.Surjective ⇑(iso.hom) :=
    (ModuleCat.epi_iff_surjective iso.hom).mp inferInstance
  exact ⟨fun a b => by
    obtain ⟨a', rfl⟩ := hsurj a
    obtain ⟨b', rfl⟩ := hsurj b
    rw [h.elim a' b']⟩

theorem subsingleton_zeroComplement_tautLineFour (k : ℕ) (hk0 : k ≠ 0) (hktop : k ≠ 9) :
    Subsingleton (Work.Thom.Coh ℤ k
      ↥(Work.Thom.zeroComplement (Work.Thom.realification (Work.Gen.tautLine 4)))) := by
  obtain ⟨eDC⟩ := Work.Gen.tautDual_iso_conjLine 4
  have h₁ : ↥(Work.Thom.zeroComplement (Work.Thom.realification (Work.Gen.tautDual 4))) ≃ₜ
      ↥(Work.Thom.zeroComplement (Work.Thom.realification (Work.Gen.conjLine 4))) :=
    Work.Thom.punctHomeo (Work.Gen.tautDual 4) (Work.Gen.conjLine 4) eDC
  have h₂ : ↥(Work.Thom.zeroComplement (Work.Thom.realification (Work.Gen.conjLine 4))) ≃ₜ
      ↥(Work.Thom.zeroComplement (Work.Thom.realification (Work.Gen.tautLine 4))) :=
    Work.Thom.BundleIso.punctHomeomorph (Work.Gen.conjIso 4)
  have hz : Subsingleton (Work.Thom.Coh ℤ k
      ↥(Work.Thom.zeroComplement (Work.Thom.realification (Work.Gen.tautDual 4)))) :=
    ModuleCat.subsingleton_of_isZero (Work.Gen.uSqGen_puncturedTautDual4HZero k hk0 hktop)
  exact subsingleton_cohomology_of_homotopyEquiv h₂.toHomotopyEquiv k
    (subsingleton_cohomology_of_homotopyEquiv h₁.toHomotopyEquiv k hz)

end Work.ThomBordism.Grassmann
