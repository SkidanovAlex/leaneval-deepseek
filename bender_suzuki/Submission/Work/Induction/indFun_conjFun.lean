import Mathlib
import Submission.Work.Induction.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Induction

open Classical
open scoped Pointwise

-- Induction is invariant under conjugation of the inducing function by an element of the
-- normalizer: for `x ∈ N_G(H)` and `φ : H → ℂ` (arbitrary), `Ind_H^G (φ^x) = Ind_H^G φ` where
-- `φ^x (h) = φ (x * h * x⁻¹)` (`Work.Induction.conjFun`).  Pointwise, reindex the defining sum
-- of `Ind_H^G (φ^x) (g)` by `z = x * y` (`y ↦ x * y` is a bijection `G → G`); the condition
-- `y * g * y⁻¹ ∈ H` is equivalent to `z * g * z⁻¹ ∈ H` because `x ∈ N_G(H)`.
theorem indFun_conjFun {G : Type*} [Group G] [Fintype G] (H : Subgroup G)
    (x : Work.Induction.normalizer H) (φ : H → ℂ) :
    Work.Induction.indFun H (Work.Induction.conjFun H x φ) = Work.Induction.indFun H φ := by
  ext g
  simp only [indFun_apply_def]
  congr 1
  -- Reindex the defining sum by the bijection `y ↦ x * y` of `G`.
  let e : G ≃ G :=
    Equiv.ofBijective (fun y : G => (x : G) * y)
      ⟨fun a b h => mul_left_cancel h, fun b => ⟨(x : G)⁻¹ * b, by simp⟩⟩
  refine Fintype.sum_equiv e _ _ ?_
  intro y
  have hyy : e y = (x : G) * y := rfl
  rw [hyy]
  -- Membership in `H` of `y * g * y⁻¹` and of `(x * y) * g * (x * y)⁻¹` are equivalent,
  -- because `x` normalizes `H`.
  have hmem : y * g * y⁻¹ ∈ H ↔ (x : G) * y * g * ((x : G) * y)⁻¹ ∈ H := by
    have h1 := (Subgroup.mem_normalizer_iff.mp x.2 (y * g * y⁻¹))
    rwa [show (x : G) * (y * g * y⁻¹) * (x : G)⁻¹ =
        (x : G) * y * g * ((x : G) * y)⁻¹ by group] at h1
  by_cases hy : y * g * y⁻¹ ∈ H
  · have hz : (x : G) * y * g * ((x : G) * y)⁻¹ ∈ H := hmem.mp hy
    rw [dite_eq_left hy, dite_eq_left hz]
    change φ (conjMem H x ⟨y * g * y⁻¹, hy⟩) =
      φ ⟨(x : G) * y * g * ((x : G) * y)⁻¹, hz⟩
    congr 1
    exact Subtype.ext (by
      show (x : G) * (y * g * y⁻¹) * (x : G)⁻¹ = (x : G) * y * g * ((x : G) * y)⁻¹
      group)
  · have hz : ¬ ((x : G) * y * g * ((x : G) * y)⁻¹ ∈ H) := fun h => hy (hmem.mpr h)
    rw [dite_eq_right hy, dite_eq_right hz]

end Work.Induction
