import Mathlib
import Submission.Work.DoubleTransitivity.App1.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThreePoints.S4Prop2

open Submission.Blueprint

theorem ncard_involutions_conj {G : Type} [Group G] (g : G) (H : Subgroup G) :
    (Submission.Blueprint.involutions (Submission.Blueprint.conj g H : Set G)).ncard =
      (Submission.Blueprint.involutions (H : Set G)).ncard := by
  -- Conjugation by `g` restricts to a bijection `involutions H → involutions (g H g⁻¹)`.
  have hcoe : ∀ x : G, (MulAut.conj g).toMonoidHom x = g * x * g⁻¹ := fun x => by
    change MulAut.conj g x = g * x * g⁻¹
    rw [MulAut.conj_apply]
  rw [eq_comm]
  refine Set.ncard_congr (fun x _ => g * x * g⁻¹) ?_ ?_ ?_
  · intro a ha
    simp only [involutions, Set.mem_ofPred_eq] at ha ⊢
    obtain ⟨haH, ha2⟩ := ha
    refine ⟨?_, ?_⟩
    · show g * a * g⁻¹ ∈ H.map (MulAut.conj g).toMonoidHom
      rw [Subgroup.mem_map]
      exact ⟨a, haH, hcoe a⟩
    · rw [← hcoe a]
      exact (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective a).trans ha2
  · intro a b ha hb hab
    exact mul_left_cancel (mul_right_cancel hab)
  · intro b hb
    simp only [involutions, Set.mem_ofPred_eq] at hb
    obtain ⟨hbH, hb2⟩ := hb
    change b ∈ H.map (MulAut.conj g).toMonoidHom at hbH
    rw [Subgroup.mem_map] at hbH
    obtain ⟨a, haH, haeq⟩ := hbH
    refine ⟨a, ?_, ?_⟩
    · simp only [involutions, Set.mem_ofPred_eq]
      refine ⟨haH, ?_⟩
      rw [← orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective a, haeq, hb2]
    · rw [← hcoe a]; exact haeq

end Work.ThreePoints.S4Prop2
