import Mathlib
import Submission.Work.CharCore.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Induction

theorem sum_conj_eq_card_mul {G : Type*} [Group G] [Fintype G] {H : Subgroup G} [Fintype ↥H]
    (ψ : H → ℂ) (hψ : Work.CharCore.IsClassFun ψ) (c : H) :
    ∑ a : H, ψ (a * c * a⁻¹) = (Nat.card H : ℂ) * ψ c := by
  have h : ∀ a : H, ψ (a * c * a⁻¹) = ψ c := fun a => hψ c a
  rw [Finset.sum_congr rfl (fun a _ => h a), Finset.sum_const, Finset.card_univ]
  rw [Nat.card_eq_fintype_card]
  ring

end Work.Induction
