import Mathlib
import Submission.Work.LinnikBurgess.defect2_mul_Uval_sq

namespace Work.LinnikBurgess

/-- Congruence form of the second defect identity from `defect2_mul_Uval_sq`: in `ZMod (p^e)` the
product `D₂(y) · U(y)²` equals `-N'(y)·U(y) + N(y)·W(y)`, so the integer representative of `D₂(y)`
satisfies
`D₂(y) · U(y)² + N'(y)·U(y) - N(y)·W(y) ≡ 0 (mod p^e)`. -/
theorem dvd_defect2_congr {p e : ℕ} [Fact p.Prime] (a b : Fin 3 → ℕ) {y : ℕ}
    (hy : UnitAt p y a b) :
    ((p : ℤ) ^ e) ∣ (defect2 p e a b y).val * (Uval y a b : ℤ) ^ 2
      + (critN a b).derivative.eval (y : ℤ) * (Uval y a b : ℤ)
      - (critN a b).eval (y : ℤ) * (Wval y a b : ℤ) := by
  have hpm : ((p : ℤ) ^ e) = ((p ^ e : ℕ) : ℤ) := by push_cast; ring
  -- It suffices to show the integer expression vanishes in `ZMod (p^e)`.
  have key : ((((defect2 p e a b y).val * (Uval y a b : ℤ) ^ 2
      + (critN a b).derivative.eval (y : ℤ) * (Uval y a b : ℤ)
      - (critN a b).eval (y : ℤ) * (Wval y a b : ℤ) : ℤ)) : ZMod (p ^ e)) = 0 := by
    have h := defect2_mul_Uval_sq (p := p) (e := e) a b hy
    push_cast
    rw [ZMod.natCast_zmod_val, h]
    ring
  rw [hpm, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact key

end Work.LinnikBurgess
