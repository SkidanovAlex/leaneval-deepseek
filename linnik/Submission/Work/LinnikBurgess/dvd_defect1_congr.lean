import Mathlib
import Submission.Work.LinnikBurgess.defect1_mul_Uval

namespace Work.LinnikBurgess

/-- Congruence form of the first defect identity from `defect1_mul_Uval`: since in `ZMod (p^e)` the
product `D₁(y) · U(y)` equals the Wronskian `N(y)`, the integer representative of `D₁(y)` satisfies
`D₁(y) · U(y) ≡ N(y) (mod p^e)`. -/
theorem dvd_defect1_congr {p e : ℕ} [Fact p.Prime] (a b : Fin 3 → ℕ) {y : ℕ}
    (hy : UnitAt p y a b) :
    ((p : ℤ) ^ e) ∣ (defect1 p e a b y).val * (Uval y a b : ℤ) - (critN a b).eval (y : ℤ) := by
  have hpm : ((p : ℤ) ^ e) = ((p ^ e : ℕ) : ℤ) := by push_cast; ring
  -- It suffices to show the integer difference vanishes in `ZMod (p^e)`.
  have key : (((defect1 p e a b y).val * (Uval y a b : ℤ) - (critN a b).eval (y : ℤ) : ℤ)
      : ZMod (p ^ e)) = 0 := by
    have h := defect1_mul_Uval (p := p) (e := e) a b hy
    push_cast
    rw [ZMod.natCast_zmod_val, h]
    ring
  rw [hpm, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact key

end Work.LinnikBurgess
