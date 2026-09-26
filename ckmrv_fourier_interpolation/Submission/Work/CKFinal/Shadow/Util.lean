import Mathlib

/-! Helpers for the "smooth shadow" of the CKMRV Theorem 3.1 adapter chain. -/

open scoped ContDiff

namespace Work.CKFinal.Shadow

/-- `↑n ≤ ∞` for `n : ℕ∞`. -/
theorem coe_le_smooth {n : ℕ∞} : ((n : ℕ∞ω)) ≤ (∞ : ℕ∞ω) := WithTop.coe_le_coe.mpr le_top

/-- `↑n ≤ ∞` for `n : ℕ`. -/
theorem natCast_le_smooth {n : ℕ} : ((n : ℕ∞ω)) ≤ (∞ : ℕ∞ω) := WithTop.coe_le_coe.mpr le_top

end Work.CKFinal.Shadow
