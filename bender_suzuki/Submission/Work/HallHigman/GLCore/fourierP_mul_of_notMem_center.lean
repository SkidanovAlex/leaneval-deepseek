import Mathlib
import Submission.Work.HallHigman.GLCore.FourierSetup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.HallHigman.GLCore

/-- The Fourier projector annihilates `σ g · β` for `g ∉ Z(E)` and `β ∈ End_E(V)`: expanding
`P = fourierP σ` gives `Σ_f σ(f g f⁻¹) · β = (Σ_f λ([f,g])) • σ g · β`, and the character
`f ↦ λ([f,g])` is nontrivial (`sum_commChar_eq_zero`). -/
theorem fourierP_mul_of_notMem_center {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] [Nontrivial V] {E : Type*} [Group E] [Fintype E]
    (σ : E →* Module.End K V)
    (hsc : ∀ z ∈ Subgroup.center E, ∃ c : K, σ z = algebraMap K (Module.End K V) c)
    (hfaith : ∀ z ∈ Subgroup.center E, σ z = 1 → z = 1)
    (hcomm : ∀ e f : E, e * f * e⁻¹ * f⁻¹ ∈ Subgroup.center E)
    {g : E} (hg : g ∉ Subgroup.center E)
    {β : Module.End K V} (hβ : β ∈ Work.HallHigman.commutantOf σ) :
    Work.HallHigman.GLCore.fourierP σ (σ g * β) = 0 := by
  rw [fourierP_apply]
  -- For `β` in the commutant, `σ e · (σ g · β) · σ e⁻¹ = σ (e g e⁻¹) · β`.
  have hsum : (∑ e : E, σ e * (σ g * β) * σ e⁻¹)
      = (∑ e : E, σ (e * g * e⁻¹)) * β := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e _
    have h := mem_commutantOf_iff.mp hβ e⁻¹
    calc σ e * (σ g * β) * σ e⁻¹
      _ = σ e * σ g * (β * σ e⁻¹) := by simp only [mul_assoc]
      _ = σ e * σ g * (σ e⁻¹ * β) := by rw [h]
      _ = σ e * σ g * σ e⁻¹ * β := by rw [← mul_assoc]
      _ = σ (e * g) * σ e⁻¹ * β := by rw [← map_mul]
      _ = σ (e * g * e⁻¹) * β := by rw [← map_mul]
  -- The full conjugation sum evaluates to `(Σ_e λ([e,g])) • σ g`.
  rw [hsum, conj_sum_eq σ hsc hcomm g, smul_mul_assoc,
    sum_commChar_eq_zero σ hsc hfaith hcomm hg, zero_smul, smul_zero]

end Work.HallHigman.GLCore
