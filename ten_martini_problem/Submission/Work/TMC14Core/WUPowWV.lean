import Mathlib
import Submission.Work.TMC14Core.Weyl

/-!
# TMC14Core: `U Vᵃ = ωᵃ Vᵃ U`

`U = wU q k` and `V = wV p q θ` satisfy the Weyl relation `U V = ω V U` with
`ω = om p q` (`wU_mul_wV`).  Here we integrate it: for every `a : ℕ`,
`U V^a = ω^a • (V^a U)`, and, multiplying on the right by an arbitrary
`Z : Matrix (Fin q) (Fin q) ℂ`,

`U (V^a Z) = ω^a • (V^a (U Z))`.
-/

open Matrix

noncomputable section

namespace Work.TMC14Core

/-- `U V^a = ω^a • (V^a U)`: the integrated Weyl relation. -/
theorem wU_mul_wV_pow (p : ℤ) (q : ℕ) (θ k : ℝ) (a : ℕ) :
    wU q k * (wV p q θ) ^ a = (om p q) ^ a • ((wV p q θ) ^ a * wU q k) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ, ← mul_assoc, ih, smul_mul_assoc, mul_assoc, wU_mul_wV,
      mul_smul_comm, smul_smul, ← pow_succ, ← mul_assoc, ← pow_succ]

theorem WUPowWV (p : ℤ) (q : ℕ) (θ k : ℝ) (a : ℕ) (Z : Matrix (Fin q) (Fin q) ℂ) :
    wU q k * ((wV p q θ) ^ a * Z) =
      (om p q) ^ a • ((wV p q θ) ^ a * (wU q k * Z)) := by
  rw [← mul_assoc, wU_mul_wV_pow, smul_mul_assoc, mul_assoc]

end Work.TMC14Core
