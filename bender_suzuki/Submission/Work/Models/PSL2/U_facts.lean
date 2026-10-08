import Mathlib
import Submission.Work.Models.PSL2.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Models.PSL2

open Matrix

variable {F : Type*} [Field F] [CharP F 2]

/-- The parametrisation `b ↦ 1 + b E₀₁` of the unipotent radical is injective. -/
lemma unip_injective : Function.Injective (unip (F := F)) := by
  intro a b h
  have := congrArg (fun A : SL2 F => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simpa [unip_coe] using this

/-- The bijection `F ≃ U`, `b ↦ 1 + b E₀₁`. -/
noncomputable def unipEquiv : F ≃ U (F := F) where
  toFun b := ⟨unip b, ⟨b, rfl⟩⟩
  invFun A := A.2.choose
  left_inv b := by
    have h := (⟨unip b, ⟨b, rfl⟩⟩ : U (F := F)).2.choose_spec
    exact (unip_injective h).symm
  right_inv A := by
    apply Subtype.ext
    exact (A.2.choose_spec).symm

/-- `U` has order `|F|`, since `b ↦ 1 + b E₀₁` is a bijection `F ≃ U`. -/
lemma card_U : Nat.card ↥(U (F := F)) = Nat.card F :=
  (Nat.card_congr (unipEquiv (F := F))).symm

/-- Every element of `U` is an involution, so `U` has exponent `2`. -/
lemma U_sq_one (g : ↥(U (F := F))) : g ^ 2 = 1 := by
  obtain ⟨b, hb⟩ := g.2
  have hg : g = ⟨unip b, ⟨b, rfl⟩⟩ := Subtype.ext hb
  have h : (⟨unip b, ⟨b, rfl⟩⟩ : ↥(U (F := F))) * ⟨unip b, ⟨b, rfl⟩⟩ = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_one]
    rw [← unip_add, CharTwo.add_self_eq_zero, unip_zero]
  rw [hg, pow_two]
  exact h

theorem U_facts {F : Type*} [Field F] [CharP F 2] [Finite F] :
    Nat.card ↥(Work.Models.PSL2.U (F := F)) = Nat.card F ∧
      IsPGroup 2 ↥(Work.Models.PSL2.U (F := F)) ∧
      ∀ x ∈ Work.Models.PSL2.U (F := F), ∀ y ∈ Work.Models.PSL2.U (F := F), x * y = y * x := by
  refine ⟨card_U, ?_, ?_⟩
  · intro g
    exact ⟨1, by rw [pow_one]; exact U_sq_one g⟩
  · intro x hx y hy
    rw [mem_U_iff] at hx hy
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    rw [← unip_add, ← unip_add, add_comm]

end Work.Models.PSL2
