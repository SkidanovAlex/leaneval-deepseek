import Mathlib
import Submission.Work.BW.logHeight_prod_zpow_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Deviation form of the subadditivity bound for `logHeight₁` over a product with integer
exponents.  If the exponents `t k * s i - s k * t i` deviate from zero only by a multiple of
`|t k|` controlled by the coefficients `c j`, the height of the resulting product is bounded
by `|t k|` times the corresponding weighted sum of the heights of the factors. -/
theorem logHeight_prod_zpow_deviation_le {K : Type*} [Field K] [NumberField K] {m : ℕ}
    (α : Fin m → K) (t s : Fin m → ℤ) (k : Fin m) (c : Fin m → ℝ)
    (hdev : ∀ j : Fin m, j ≠ k →
      |((t k : ℤ) : ℝ) * (s j : ℝ) - (s k : ℝ) * ((t j : ℤ) : ℝ)| ≤ |((t k : ℤ) : ℝ)| * c j) :
    Height.logHeight₁ (∏ i, α i ^ (t k * s i - s k * t i : ℤ)) ≤
      |((t k : ℤ) : ℝ)| * ∑ j ∈ Finset.univ.erase k, c j * Height.logHeight₁ (α j) := by
  refine (logHeight_prod_zpow_le α (fun i => t k * s i - s k * t i)).trans ?_
  have hk : ((t k * s k - s k * t k).natAbs : ℝ) * Height.logHeight₁ (α k) = 0 := by
    have : t k * s k - s k * t k = 0 := by ring
    rw [this]; simp
  calc ∑ i, ((t k * s i - s k * t i).natAbs : ℝ) * Height.logHeight₁ (α i)
      = ∑ j ∈ Finset.univ.erase k,
          ((t k * s j - s k * t j).natAbs : ℝ) * Height.logHeight₁ (α j) :=
        (Finset.sum_erase (s := Finset.univ) (a := k) hk).symm
    _ ≤ ∑ j ∈ Finset.univ.erase k, (|((t k : ℤ) : ℝ)| * c j) * Height.logHeight₁ (α j) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjne : j ≠ k := (Finset.mem_erase.mp hj).1
        apply mul_le_mul_of_nonneg_right _ (Height.zero_le_logHeight₁ (α j))
        have hcast : ((t k * s j - s k * t j : ℤ) : ℝ)
            = ((t k : ℤ) : ℝ) * (s j : ℝ) - (s k : ℝ) * ((t j : ℤ) : ℝ) := by
          push_cast; ring
        rw [Nat.cast_natAbs, Int.cast_abs, hcast]
        exact hdev j hjne
    _ = |((t k : ℤ) : ℝ)| * ∑ j ∈ Finset.univ.erase k, c j * Height.logHeight₁ (α j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring

end Work.BW
