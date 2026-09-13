import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.Real.Basic

namespace Commons.Algebra.AddSubgroup

open Finset BigOperators Classical

/-- For a finite additive commutative group `G`, an additive subgroup `H ≤ G` and any `φ : G → ℝ`,
`∑_g ∑_{h ∈ H} φ (g + h) = #H · ∑_g φ g`. -/
theorem sum_sum_add_eq {G : Type*} [AddCommGroup G] [Fintype G] (H : AddSubgroup G)
    (φ : G → ℝ) :
    (∑ g : G, ∑ h : H, φ (g + h)) = (Nat.card H : ℝ) * ∑ g : G, φ g := by
  classical
  rw [Finset.sum_comm]
  have hinner : ∀ h : H, (∑ g : G, φ (g + (h : G))) = ∑ g : G, φ g := by
    intro h
    have hcomp := Equiv.sum_comp (Equiv.addRight (h : G)) φ
    simpa using hcomp
  rw [Finset.sum_congr rfl (fun h _ => hinner h)]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]

end Commons.Algebra.AddSubgroup