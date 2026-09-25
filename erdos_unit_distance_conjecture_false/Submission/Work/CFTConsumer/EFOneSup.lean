import Mathlib
import Submission.Work.CFTConsumer.Defs

/-!
# Complete splitting ascends to finite composita

`Work.CFTConsumer.EFOne F L 𝔭` (every prime of `𝓞 L` above `𝔭` has ramification index and inertia
degree `1` over `𝓞 F`) ascends to binary and finite suprema of finite-dimensional intermediate
fields of an arbitrary `F`-algebra `A`.

The binary case is proved in the ambient `↥(E₁ ⊔ E₂)`: the two restrictions `Eᵢ.restrict` are
identified with the `Eᵢ` (`IntermediateField.restrictAlgEquiv`), `SplitsCompletelyIn` ascends by
`Work.Tower.SplitsCompletelyIn_sup`, and their supremum is `⊤` because `lift` preserves binary
suprema and inverts `restrict` (`IntermediateField.lift_sup`, `lift_restrict`, `lift_top`,
`lift_injective`).

This is the input that lets the tower-cutting endgame (whose maximal field is the supremum of all
`T`-split good extensions, `Work.Tower.TowerCut.goodImages`) conclude that its maximal field splits
`T` completely — the extra hypothesis required by `CFTLib.ShafBound`.
-/

open NumberField
open Work.Tower
open scoped Classical nonZeroDivisors

namespace Work.CFTConsumer

theorem efOne_sup {F A : Type} [Field F] [NumberField F] [Field A] [Algebra F A]
    {E₁ E₂ : IntermediateField F A} [FiniteDimensional F E₁] [FiniteDimensional F E₂]
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsPrime) (h𝔭0 : 𝔭 ≠ ⊥)
    (h₁ : EFOne F ↥E₁ 𝔭) (h₂ : EFOne F ↥E₂ 𝔭) :
    EFOne F ↥(E₁ ⊔ E₂) 𝔭 := by
  haveI : NumberField ↥(E₁ ⊔ E₂) := NumberField.of_module_finite F ↥(E₁ ⊔ E₂)
  haveI : NumberField ↥E₁ := NumberField.of_module_finite F ↥E₁
  haveI : NumberField ↥E₂ := NumberField.of_module_finite F ↥E₂
  haveI hfd1' : FiniteDimensional F ↥(E₁.restrict (le_sup_left : E₁ ≤ E₁ ⊔ E₂)) :=
    LinearEquiv.finiteDimensional (IntermediateField.restrictAlgEquiv (le_sup_left : E₁ ≤ E₁ ⊔ E₂)).toLinearEquiv
  haveI hfd2' : FiniteDimensional F ↥(E₂.restrict (le_sup_right : E₂ ≤ E₁ ⊔ E₂)) :=
    LinearEquiv.finiteDimensional (IntermediateField.restrictAlgEquiv (le_sup_right : E₂ ≤ E₁ ⊔ E₂)).toLinearEquiv
  haveI : NumberField ↥(E₁.restrict (le_sup_left : E₁ ≤ E₁ ⊔ E₂)) :=
    NumberField.of_module_finite F _
  haveI : NumberField ↥(E₂.restrict (le_sup_right : E₂ ≤ E₁ ⊔ E₂)) :=
    NumberField.of_module_finite F _
  have ef1 : EFOne F ↥(E₁.restrict (le_sup_left : E₁ ≤ E₁ ⊔ E₂)) 𝔭 :=
    EFOne.of_algEquiv h𝔭 h𝔭0 (IntermediateField.restrictAlgEquiv (le_sup_left : E₁ ≤ E₁ ⊔ E₂)) h₁
  have ef2 : EFOne F ↥(E₂.restrict (le_sup_right : E₂ ≤ E₁ ⊔ E₂)) 𝔭 :=
    EFOne.of_algEquiv h𝔭 h𝔭0 (IntermediateField.restrictAlgEquiv (le_sup_right : E₂ ≤ E₁ ⊔ E₂)) h₂
  have hsup : SplitsCompletelyIn F ↥((E₁.restrict (le_sup_left : E₁ ≤ E₁ ⊔ E₂)) ⊔
      (E₂.restrict (le_sup_right : E₂ ≤ E₁ ⊔ E₂))) 𝔭 :=
    (SplitsCompletelyIn_sup).mpr ⟨ef1.splitsCompletelyIn h𝔭 h𝔭0, ef2.splitsCompletelyIn h𝔭 h𝔭0⟩
  have htop : (E₁.restrict (le_sup_left : E₁ ≤ E₁ ⊔ E₂)) ⊔
      (E₂.restrict (le_sup_right : E₂ ≤ E₁ ⊔ E₂)) = ⊤ := by
    refine IntermediateField.lift_injective (E₁ ⊔ E₂) ?_
    rw [IntermediateField.lift_sup, IntermediateField.lift_restrict, IntermediateField.lift_restrict,
      IntermediateField.lift_top]
  have htopEF : EFOne F ↥(⊤ : IntermediateField F ↥(E₁ ⊔ E₂)) 𝔭 := by
    rw [← htop]
    exact EFOne.of_splitsCompletelyIn h𝔭0 hsup
  exact EFOne.of_algEquiv h𝔭 h𝔭0 IntermediateField.topEquiv htopEF

theorem efOne_iSup_finite {F A : Type} [Field F] [NumberField F] [Field A] [Algebra F A]
    {ι : Type} [Finite ι] [Nonempty ι] (M : ι → IntermediateField F A)
    [∀ i, FiniteDimensional F ↥(M i)] {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsPrime) (h𝔭0 : 𝔭 ≠ ⊥)
    (h : ∀ i, EFOne F ↥(M i) 𝔭) : EFOne F ↥(⨆ i, M i) 𝔭 := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have key : ∀ t : Finset ι, FiniteDimensional F ↥((insert i₀ t).sup M) ∧
      EFOne F ↥((insert i₀ t).sup M) 𝔭 := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        rw [Finset.insert_empty, Finset.sup_singleton]
        exact ⟨inferInstance, h i₀⟩
    | insert a s _ ih =>
        rw [Finset.insert_comm i₀ a s, Finset.sup_insert]
        haveI : FiniteDimensional F ↥((insert i₀ s).sup M) := ih.1
        exact ⟨inferInstance, efOne_sup h𝔭 h𝔭0 (h a) ih.2⟩
  rw [← Finset.sup_univ_eq_iSup, ← Finset.insert_erase (Finset.mem_univ i₀)]
  exact (key (Finset.univ.erase i₀)).2

end Work.CFTConsumer
