import Mathlib
import Submission.Work.ZJB2.Defs

namespace Work.ZJB2

/-- If `M` is a normal `p'`-subgroup and `T` is a `p`-subgroup then `T` is a Sylow
`p`-subgroup of the product `M ⊔ T` (= `MT`).

The proof is the standard one: `T ≤ M ⊔ T` and `T` is a `p`-group; for maximality, a
`p`-subgroup `Q` with `T ≤ Q ≤ M ⊔ T` satisfies `M ⊓ Q = ⊥` (a `p`-group meets a
`p'`-group trivially).  Writing `x ∈ Q ≤ T ⊔ M` as `x = y * z` with `y ∈ T`, `z ∈ M`
(legitimate because `M` is normal, `Subgroup.mem_sup_of_normal_right`), we get
`z = y⁻¹ * x ∈ Q`, hence `z ∈ M ⊓ Q = ⊥`, so `x = y ∈ T`. -/
theorem nrfSylowSup {H : Type} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (M : Subgroup H) [M.Normal] (T : Subgroup H)
    (hM : Subgroup.IsPiSubgroup ({p}ᶜ) M) (hT : IsPGroup p T) :
    Work.ZJB.IsSylowIn p T (M ⊔ T) := by
  refine ⟨le_sup_right, hT, ?_⟩
  intro Q hTQ hQle hQ
  -- A `p`-group meets the `p'`-group `M` trivially.
  have hbot : M ⊓ Q = ⊥ :=
    OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup.inf_eq_bot_of_isPGroup_not_mem hM hQ (by simp)
  refine le_antisymm ?_ hTQ
  intro x hx
  have hx' : x ∈ T ⊔ M := by rw [sup_comm]; exact hQle hx
  rw [Subgroup.mem_sup_of_normal_right] at hx'
  obtain ⟨y, hy, z, hz, hyz⟩ := hx'
  have hzQ : z ∈ Q := by
    have hzeq : z = y⁻¹ * x := by rw [← hyz]; group
    rw [hzeq]
    exact mul_mem (inv_mem (hTQ hy)) hx
  have hzbot : z ∈ (⊥ : Subgroup H) := by
    rw [← hbot]
    exact ⟨hz, hzQ⟩
  rw [Subgroup.mem_bot] at hzbot
  rw [← hyz, hzbot, mul_one]
  exact hy

end Work.ZJB2
