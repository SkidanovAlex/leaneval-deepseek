import Mathlib
import Submission.Work.LT.lr_class_ops

namespace Work.LT

/-- The two off-diagonal blocks of `classOpA` are adjoints of each other: `⟨v, ROp A u⟩ = ⟨u, POp A v⟩`
where `POp A w g = (∑ i, w (A i * g))/Δ` and `ROp A w g = (∑ i, w ((A i)⁻¹ * g))/Δ`. -/
theorem lr_class_ROp_swap {G : Type} [Group G] [Fintype G] {Δ : ℕ} (A : Fin Δ → G)
    (u v : G → ℝ) :
    ∑ g, v g * ROp A u g = ∑ g, u g * POp A v g := by
  -- For each `i` the substitution `g ↦ A i * g` turns `∑ g, u g * v (A i * g)` into
  -- `∑ g, u ((A i)⁻¹ * g) * v g`, i.e. `∑ g, v g * u ((A i)⁻¹ * g)`.
  have key : ∀ i : Fin Δ, ∑ g, u g * v (A i * g) = ∑ g, v g * u ((A i)⁻¹ * g) := by
    intro i
    have h := Equiv.sum_comp (Equiv.mulLeft (A i)) (fun g => u ((A i)⁻¹ * g) * v g)
    simp only [Equiv.coe_mulLeft, inv_mul_cancel_left] at h
    rw [h]
    exact Finset.sum_congr rfl (fun g _ => by ring)
  -- Pull the factor `1/Δ` out of the inner sums on both sides.
  have hL : (∑ g, v g * ROp A u g) = (∑ g, ∑ i, v g * u ((A i)⁻¹ * g)) / (Δ : ℝ) := by
    simp only [ROp]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro g _
    rw [← mul_div_assoc, Finset.mul_sum]
  have hR : (∑ g, u g * POp A v g) = (∑ g, ∑ i, u g * v (A i * g)) / (Δ : ℝ) := by
    simp only [POp]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro g _
    rw [← mul_div_assoc, Finset.mul_sum]
  rw [hL, hR]
  congr 1
  -- Exchange the two summations and apply `key` indexwise.
  rw [Finset.sum_comm (f := fun g i => v g * u ((A i)⁻¹ * g))]
  rw [Finset.sum_comm (f := fun g i => u g * v (A i * g))]
  exact Finset.sum_congr rfl (fun i _ => (key i).symm)

end Work.LT
