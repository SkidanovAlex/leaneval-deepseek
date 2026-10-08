import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.CharCore

/-- A rational number which is integral over `ℤ` is an integer; consequently
`n / d` integral over `ℤ` forces `d ∣ n`. -/
theorem dvd_of_isIntegral_rat {n d : ℕ} (hd : 0 < d) (h : IsIntegral ℤ ((n : ℚ) / (d : ℚ))) : d ∣ n := by
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (R := ℤ) (K := ℚ) h
  have hy' : (y : ℚ) = (n : ℚ) / (d : ℚ) := hy
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have h1 : (y : ℚ) * (d : ℚ) = (n : ℚ) := by
    rw [hy']
    exact div_mul_cancel₀ _ hd'
  have h2 : y * (d : ℤ) = (n : ℤ) := by
    have : ((y * (d : ℤ) : ℤ) : ℚ) = ((n : ℤ) : ℚ) := by
      push_cast
      exact h1
    exact_mod_cast this
  refine Int.natCast_dvd_natCast.mp ⟨y, ?_⟩
  rw [← h2, mul_comm]

end Work.CharCore
