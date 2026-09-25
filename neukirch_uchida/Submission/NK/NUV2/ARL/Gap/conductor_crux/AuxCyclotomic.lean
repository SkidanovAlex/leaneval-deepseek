/-
# Two cyclotomic compositum lemmas, local copies

The lemmas proved here (`Aux_adjoin_zeta_eq_top`,
`Aux_sup_restrictScalars_adjoin_zeta_eq_top`) are the two facts about
`Ω = CyclotomicField M L = L(ζ_M)` needed by `AuxSetup`.  They are stated and
proved here (with an `Aux` prefix) so that the present development does not
depend on `Submission.NK.CFTLib.ARL.auxiliary_field_single`, which is being
modified concurrently.
-/
import Mathlib

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open NumberField
open scoped NumberField

noncomputable section

namespace NK.NUV2.ARL.Gap.conductor_crux

/-- **`CyclotomicField M L` is `L` adjoined with a primitive `M`-th root of unity.** -/
theorem Aux_adjoin_zeta_eq_top (L : Type) [Field L] [CharZero L] (M : ℕ) [NeZero M] :
    (⊤ : IntermediateField L (CyclotomicField M L)) =
      IntermediateField.adjoin L
        ({IsCyclotomicExtension.zeta M L (CyclotomicField M L)} :
          Set (CyclotomicField M L)) := by
  haveI htop : IsCyclotomicExtension {M} L
      ↥(⊤ : IntermediateField L (CyclotomicField M L)) :=
    IsCyclotomicExtension.equiv {M} L (CyclotomicField M L)
      (IntermediateField.topEquiv (F := L)).symm
  exact (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin M L
    (CyclotomicField M L) ⊤ (IsCyclotomicExtension.zeta_spec M L _)).mp htop

/-- **`L(ζ_M) = L ⊔ K(ζ_M)`** as intermediate fields of `CyclotomicField M L` over `K`. -/
theorem Aux_sup_restrictScalars_adjoin_zeta_eq_top (K L : Type) [Field K] [Field L] [CharZero L]
    [Algebra K L] (M : ℕ) [NeZero M] :
    (⊥ : IntermediateField L (CyclotomicField M L)).restrictScalars K ⊔
      IntermediateField.adjoin K
        ({IsCyclotomicExtension.zeta M L (CyclotomicField M L)} :
          Set (CyclotomicField M L)) = ⊤ := by
  set A : IntermediateField K (CyclotomicField M L) :=
    (⊥ : IntermediateField L (CyclotomicField M L)).restrictScalars K with hA
  set ζ := IsCyclotomicExtension.zeta M L (CyclotomicField M L) with hζ
  set B : IntermediateField K (CyclotomicField M L) :=
    IntermediateField.adjoin K ({ζ} : Set (CyclotomicField M L)) with hB
  have htop : (⊤ : IntermediateField L (CyclotomicField M L)) =
      IntermediateField.adjoin L ({ζ} : Set (CyclotomicField M L)) :=
    Aux_adjoin_zeta_eq_top L M
  have hsub : (IntermediateField.adjoin L ({ζ} : Set (CyclotomicField M L)) :
      Set (CyclotomicField M L)) ⊆
      (IntermediateField.adjoin K
        ((A ⊔ B : IntermediateField K (CyclotomicField M L)) :
          Set (CyclotomicField M L))) := by
    rw [IntermediateField.adjoin_subset_adjoin_iff]
    constructor
    · rintro y ⟨l, rfl⟩
      refine IntermediateField.subset_adjoin K _ ((le_sup_left : A ≤ A ⊔ B) ?_)
      rw [hA]
      exact (IntermediateField.mem_restrictScalars K).mpr (IntermediateField.mem_bot.mpr ⟨l, rfl⟩)
    · intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact IntermediateField.subset_adjoin K _
        ((le_sup_right : B ≤ A ⊔ B)
          (IntermediateField.subset_adjoin K _ (Set.mem_singleton ζ)))
  have hle : IntermediateField.adjoin K
      ((A ⊔ B : IntermediateField K (CyclotomicField M L)) :
        Set (CyclotomicField M L)) ≤ A ⊔ B :=
    IntermediateField.adjoin_le_iff.mpr (fun x hx => hx)
  have huniv : (IntermediateField.adjoin L ({ζ} : Set (CyclotomicField M L)) :
      Set (CyclotomicField M L)) = Set.univ := by
    rw [← htop]
    rfl
  change A ⊔ B = ⊤
  refine le_antisymm le_top ?_
  intro x hx
  exact hle (hsub (huniv ▸ Set.mem_univ x))

end NK.NUV2.ARL.Gap.conductor_crux
