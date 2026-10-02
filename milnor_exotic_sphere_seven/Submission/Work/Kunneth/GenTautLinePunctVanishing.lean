import Mathlib
import Submission.Work.Gen.uSqGenerates
import Submission.Work.Gen.tautDual_iso_conjLine
import Submission.Work.Gen.ConjIso
import Submission.Work.Projective.cpn_cohomology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace Work.Kunneth

open CategoryTheory.Limits

/-!
# `H^k` of the punctured total space of `realification (tautLine n)` vanishes off `0` and `2n+1`

The complement of the zero section of the tautological line bundle `O(-1) = tautLine n` on `ℂPⁿ`
is homotopy equivalent to the sphere `S^{2n+1}`, so its cohomology vanishes in every degree
`k ≠ 0, 2n+1`.

The route is the one already used for `n = 4`
(`Work.ThomBordism.Grassmann.subsingleton_zeroComplement_tautLineFour`), now for arbitrary `n`:
the punctured total space of the *dual* bundle `O(1) = tautDual n` is the punctured model space
`ℂ^{n+1} ∖ {0}` (`Work.Gen.ChernGen.tautDualPunctHomeo`, chart-free, available for every `n`),
whose cohomology vanishes off `0` and `2n+1` because `cpU (n+1) ∩ cpV (n+1) ↪ ℂP^{n+1}` is that
punctured model space (`Work.Projective.cpnUV_homeo`) and its cohomology is
`Work.Projective.cpnUV_cohomology_zero`.  The vanishing then transports across the two line-bundle
isomorphisms `O(1) ≅ \overline{O(-1)}` (`Work.Gen.tautDual_iso_conjLine`, complex) and
`\overline{O(-1)} ≅ O(-1)` (`Work.Gen.conjIso`, real, fibrewise conjugation).
-/

/-- **The punctured model space `ℂ^{n+1} ∖ {0}` has no cohomology off degrees `0` and `2n+1`.**
`cpU (n+1) ∩ cpV (n+1) ⊆ ℂP^{n+1}` is `ℂ^{n+1} ∖ {0}` by the chart at `0`
(`Work.Projective.cpnUV_homeo n`), and its cohomology vanishes there
(`Work.Projective.cpnUV_cohomology_zero n`). -/
theorem puncturedCPVHZero (n k : ℕ) (hk0 : k ≠ 0) (hktop : k ≠ 2 * n + 1) :
    IsZero (Work.Cohomology.singularCohomology ℤ k
      (TopCat.of {z : Work.Projective.CPV n // z ≠ 0})) := by
  obtain ⟨e⟩ := Work.Cohomology.cohomologyIso_of_homotopyEquiv
    (Work.Projective.cpnUV_homeo (n + 1)).toHomotopyEquiv k
  have hz : IsZero (Work.Cohomology.singularCohomology ℤ k
      (TopCat.of ↥(Work.Projective.cpU (n + 1) ∩ Work.Projective.cpV (n + 1)))) :=
    Work.Projective.cpnUV_cohomology_zero n k hk0 hktop
  exact IsZero.of_iso hz e.symm

/-- **`H^k` of the punctured total space of the dual tautological line bundle `O(1)` on `ℂPⁿ`
vanishes** off the degrees `0` and `2n+1`: that space is the punctured model space `ℂ^{n+1}∖0`
(`Work.Gen.ChernGen.tautDualPunctHomeo`). -/
theorem puncturedTautDualHZero (n k : ℕ) (hk0 : k ≠ 0) (hktop : k ≠ 2 * n + 1) :
    IsZero (Work.Thom.Coh ℤ k
      ↥(Work.Thom.zeroComplement (Work.Thom.realification (Work.Gen.tautDual n)))) := by
  obtain ⟨e⟩ := Work.Gen.ChernGen.tautDualPunctHomeo n
  obtain ⟨iso⟩ := Work.Cohomology.cohomologyIso_of_homotopyEquiv e.toHomotopyEquiv k
  exact IsZero.of_iso (puncturedCPVHZero n k hk0 hktop) iso

/-- A homotopy equivalence induces an isomorphism on cohomology, hence transports
`Subsingleton`. -/
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

theorem GenTautLinePunctVanishing (n k : ℕ) (hk0 : k ≠ 0) (hktop : k ≠ 2 * n + 1) :
    Subsingleton (Work.Thom.Coh ℤ k
      ↥(Work.Thom.zeroComplement (Work.Thom.realification (Work.Gen.tautLine n)))) := by
  obtain ⟨eDC⟩ := Work.Gen.tautDual_iso_conjLine n
  have h₁ : ↥(Work.Thom.zeroComplement (Work.Thom.realification (Work.Gen.tautDual n))) ≃ₜ
      ↥(Work.Thom.zeroComplement (Work.Thom.realification (Work.Gen.conjLine n))) :=
    Work.Thom.punctHomeo (Work.Gen.tautDual n) (Work.Gen.conjLine n) eDC
  have h₂ : ↥(Work.Thom.zeroComplement (Work.Thom.realification (Work.Gen.conjLine n))) ≃ₜ
      ↥(Work.Thom.zeroComplement (Work.Thom.realification (Work.Gen.tautLine n))) :=
    Work.Thom.BundleIso.punctHomeomorph (Work.Gen.conjIso n)
  have hz : Subsingleton (Work.Thom.Coh ℤ k
      ↥(Work.Thom.zeroComplement (Work.Thom.realification (Work.Gen.tautDual n)))) :=
    ModuleCat.subsingleton_of_isZero (puncturedTautDualHZero n k hk0 hktop)
  exact subsingleton_cohomology_of_homotopyEquiv h₂.toHomotopyEquiv k
    (subsingleton_cohomology_of_homotopyEquiv h₁.toHomotopyEquiv k hz)

end Work.Kunneth
