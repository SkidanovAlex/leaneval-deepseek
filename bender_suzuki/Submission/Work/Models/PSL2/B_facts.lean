import Mathlib
import Submission.Work.Models.PSL2.Defs
import Submission.Work.Models.PSL2.U_facts
import Submission.Work.Models.PSL2.card_D
import Submission.Work.Models.PSL2.exists_mul_of_mem_B
import Submission.Work.Models.PSL2.B_le_normalizer_U
import Submission.Work.Models.PSL2.inf_U_D

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Models.PSL2.B_facts` — the standard Borel of `SL(2,F)`

Concrete data for the standard Borel `B` of upper triangular matrices of `SL(2,F)`
(`F` a field of characteristic `2`):

* `|B| = |F| * (|F| - 1)`;
* `B = U ⊔ D`, where `U` is the unipotent radical and `D` the split torus;
* `U ⊓ D = ⊥`;
* `B ≤ N(U)`, i.e. `B` normalizes `U`.

The first two together with `U ⊓ D = ⊥` give a bijection `U × D ≃ B` (multiplication),
whence `|B| = |U| * |D| = |F| * (|F| - 1)`.  The decomposition `B = U · D` is
`exists_mul_of_mem_B`; the triviality of `U ⊓ D` is `inf_U_D`; the normalizer statement is
`B_le_normalizer_U`; the orders are `card_U` and `card_D`.
-/

namespace Work.Models.PSL2

open Matrix

variable {F : Type*} [Field F] [CharP F 2]

/-- The multiplication map `U × D → B`, `(u, d) ↦ u * d`. -/
noncomputable def fUD : ↥(U (F := F)) × ↥(D (F := F)) → ↥(B (F := F)) :=
  fun p => ⟨(p.1 : SL2 F) * (p.2 : SL2 F),
    mul_mem (U_le_B (F := F) p.1.2) (D_le_B (F := F) p.2.2)⟩

lemma fUD_injective : Function.Injective (fUD (F := F)) := by
  rintro ⟨u₁, d₁⟩ ⟨u₂, d₂⟩ h
  have h' : (u₁ : SL2 F) * (d₁ : SL2 F) = (u₂ : SL2 F) * (d₂ : SL2 F) := by
    simpa [fUD] using congrArg (Subtype.val) h
  have hkey : (u₂ : SL2 F)⁻¹ * (u₁ : SL2 F) = (d₂ : SL2 F) * (d₁ : SL2 F)⁻¹ := by
    have := congrArg
      (fun x => (u₂ : SL2 F)⁻¹ * x * (d₁ : SL2 F)⁻¹) h'
    simpa [mul_assoc] using this
  have hmem : (u₂ : SL2 F)⁻¹ * (u₁ : SL2 F) ∈ U (F := F) ⊓ D (F := F) := by
    refine ⟨?_, ?_⟩
    · exact mul_mem ((U (F := F)).inv_mem u₂.2) u₁.2
    · rw [hkey]; exact mul_mem d₂.2 ((D (F := F)).inv_mem d₁.2)
  rw [inf_U_D] at hmem
  have hone : (u₂ : SL2 F)⁻¹ * (u₁ : SL2 F) = 1 := Subgroup.mem_bot.mp hmem
  have hu : (u₁ : SL2 F) = (u₂ : SL2 F) := by
    calc (u₁ : SL2 F) = 1 * (u₁ : SL2 F) := by rw [one_mul]
      _ = ((u₂ : SL2 F) * (u₂ : SL2 F)⁻¹) * (u₁ : SL2 F) := by rw [mul_inv_cancel]
      _ = (u₂ : SL2 F) * ((u₂ : SL2 F)⁻¹ * (u₁ : SL2 F)) := by rw [mul_assoc]
      _ = (u₂ : SL2 F) * 1 := by rw [hone]
      _ = (u₂ : SL2 F) := by rw [mul_one]
  have hd : (d₁ : SL2 F) = (d₂ : SL2 F) := by
    have h2 : (u₂ : SL2 F) * (d₁ : SL2 F) = (u₂ : SL2 F) * (d₂ : SL2 F) := by
      simpa [hu] using h'
    exact mul_left_cancel h2
  simp only [Prod.ext_iff, Subtype.ext_iff]
  exact ⟨hu, hd⟩

lemma fUD_surjective : Function.Surjective (fUD (F := F)) := by
  rintro ⟨A, hA⟩
  obtain ⟨u, hu, d, hd, rfl⟩ := exists_mul_of_mem_B (F := F) hA
  exact ⟨(⟨u, hu⟩, ⟨d, hd⟩), by simp [fUD]⟩

/-- `|B| = |U| * |D| = |F| * (|F| - 1)`. -/
theorem card_B {F : Type*} [Field F] [CharP F 2] [Finite F] :
    Nat.card ↥(B (F := F)) = Nat.card F * (Nat.card F - 1) := by
  have hbij : Function.Bijective (fUD (F := F)) := ⟨fUD_injective, fUD_surjective⟩
  rw [← Nat.card_congr (Equiv.ofBijective (fUD (F := F)) hbij), Nat.card_prod,
    card_U (F := F), card_D (F := F)]

/-- `B = U ⊔ D`. -/
theorem sup_U_D : U (F := F) ⊔ D (F := F) = B (F := F) := by
  refine le_antisymm (sup_le (U_le_B (F := F)) (D_le_B (F := F))) ?_
  intro A hA
  obtain ⟨u, hu, d, hd, rfl⟩ := exists_mul_of_mem_B (F := F) hA
  exact mul_mem (le_sup_left (a := U (F := F)) (b := D (F := F)) hu)
    (le_sup_right (a := U (F := F)) (b := D (F := F)) hd)

theorem B_facts {F : Type*} [Field F] [CharP F 2] [Finite F] :
    Nat.card ↥(Work.Models.PSL2.B (F := F)) = Nat.card F * (Nat.card F - 1) ∧
      Work.Models.PSL2.U (F := F) ⊔ Work.Models.PSL2.D (F := F) = Work.Models.PSL2.B (F := F) ∧
      Work.Models.PSL2.U (F := F) ⊓ Work.Models.PSL2.D (F := F) = ⊥ ∧
      Work.Models.PSL2.B (F := F) ≤ Subgroup.normalizer
        ((Work.Models.PSL2.U (F := F) : Subgroup (Work.Models.SL2 F)) : Set (Work.Models.SL2 F)) :=
  ⟨card_B, sup_U_D, inf_U_D, B_le_normalizer_U⟩

end Work.Models.PSL2
