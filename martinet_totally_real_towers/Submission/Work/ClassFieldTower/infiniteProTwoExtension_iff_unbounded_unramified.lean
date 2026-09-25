import Mathlib
import Submission.Work.ClassFieldTower.ProTwoDefs
import Submission.Work.ClassFieldTower.Objects
import Submission.Work.ClassFieldTower.exists_maximalUnramifiedProP
import Submission.Work.ClassFieldTower.exists_unramifiedLevel_of_infinite

set_option linter.style.haveILetI false

namespace Work.ClassFieldTower

theorem infiniteProTwoExtension_iff_unbounded_unramified {F : Type} [Field F] [NumberField F] :
    Work.ClassFieldTower.InfiniteProTwoExtension F ↔
      ∀ N : ℕ, ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra F L)
        (_ : FiniteDimensional F L) (_ : IsGalois F L),
        N ≤ Module.finrank F L ∧
          differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers L) = ⊤ ∧
          IsPGroup 2 (L ≃ₐ[F] L) := by
  constructor
  · -- ⟹ : the maximal extension itself, via `infinite_galoisGroup_iff_unbounded_subfields`
    intro h N
    obtain ⟨M, hinf⟩ := h
    obtain ⟨L, hfd, hgal, hN⟩ := M.exists_finite_galois_subfield_finrank_ge hinf N
    haveI : FiniteDimensional F ↥L := hfd
    haveI : IsGalois F ↥L := hgal
    haveI : NumberField ↥L := NumberField.of_module_finite F ↥L
    exact ⟨↥L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hN,
      M.unramified L hfd hgal, M.proP L hfd hgal⟩
  · -- ⟸ : embed each unramified level into `F_∅` and transport the invariants
    intro h
    obtain ⟨M⟩ := exists_maximalUnramifiedProP F 2
    refine ⟨M, ?_⟩
    rw [M.infinite_galoisGroup_iff_unbounded_subfields]
    intro N
    obtain ⟨L, iL, iNL, iAL, hfd, hgal, hN, hdiff, hpg⟩ := h N
    letI : Field L := iL
    letI : NumberField L := iNL
    letI : Algebra F L := iAL
    letI : FiniteDimensional F L := hfd
    letI : IsGalois F L := hgal
    obtain ⟨φ, -⟩ := M.universal L hpg hdiff
    let e : L ≃ₐ[F] ↥(φ.fieldRange) := AlgEquiv.ofInjectiveField φ
    haveI : FiniteDimensional F ↥(φ.fieldRange) := e.toLinearEquiv.finiteDimensional
    haveI : IsGalois F ↥(φ.fieldRange) := IsGalois.of_algEquiv e
    exact ⟨φ.fieldRange, inferInstance, inferInstance,
      by rw [← e.toLinearEquiv.finrank_eq]; exact hN⟩

end Work.ClassFieldTower
