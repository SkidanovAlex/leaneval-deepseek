import Mathlib
import Submission.Work.EKLRelCross.LeafCtor

namespace Work.EKLRelCross

/-- If almost every `x` has trivial `U`-stabiliser then almost every `x` is *pair-free* for the
action of `U`: `u₁ • x = u₂ • x` forces `u₁ = u₂`.  Indeed the hypothesis applied to
`u₂⁻¹ * u₁ ∈ U` gives `u₂⁻¹ * u₁ = 1`. -/
theorem ae_pairfree_of_ae_free {U : Subgroup Work.EKLContract.SL3}
    {μ : MeasureTheory.Measure Work.EKLContract.X3}
    (hfree : ∀ᵐ x ∂μ, ∀ u ∈ U, u • x = x → u = 1) :
    ∀ᵐ x ∂μ, ∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ • x = u₂ • x → u₁ = u₂ := by
  filter_upwards [hfree] with x hx u₁ hu₁ u₂ hu₂ h
  have hw : u₂⁻¹ * u₁ ∈ U := U.mul_mem (U.inv_mem hu₂) hu₁
  have h1 : (u₂⁻¹ * u₁) • x = x := by
    rw [mul_smul, h, ← mul_smul, inv_mul_cancel, one_smul]
  have h2 : u₂⁻¹ * u₁ = 1 := hx (u₂⁻¹ * u₁) hw h1
  exact (inv_mul_eq_one.mp h2).symm

end Work.EKLRelCross
