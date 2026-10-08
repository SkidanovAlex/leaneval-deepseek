import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.mem_comap_center_iff

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.HS

theorem erad_mem_iff {P : Type} [Group P] [Finite P] {A : Subgroup P} [hAn : A.Normal]
    [hA2n : (Work.Higman.powSub A 2).Normal] {x : P} :
    x ∈ Subgroup.comap (QuotientGroup.mk' (Work.Higman.powSub A 2))
        (Subgroup.center (P ⧸ (Work.Higman.powSub A 2)))
      ↔ ∀ y : P, x * y * x⁻¹ * y⁻¹ ∈ Work.Higman.powSub A 2 := by
  rw [Work.Higman.mem_comap_center_iff]
  constructor
  · intro h y
    have h' : (y * x * y⁻¹ * x⁻¹)⁻¹ ∈ Work.Higman.powSub A 2 :=
      (Work.Higman.powSub A 2).inv_mem (h y)
    rwa [show (y * x * y⁻¹ * x⁻¹)⁻¹ = x * y * x⁻¹ * y⁻¹ by group] at h'
  · intro h g
    have h' : (x * g * x⁻¹ * g⁻¹)⁻¹ ∈ Work.Higman.powSub A 2 :=
      (Work.Higman.powSub A 2).inv_mem (h g)
    rwa [show (x * g * x⁻¹ * g⁻¹)⁻¹ = g * x * g⁻¹ * x⁻¹ by group] at h'

end Work.Higman.HS
