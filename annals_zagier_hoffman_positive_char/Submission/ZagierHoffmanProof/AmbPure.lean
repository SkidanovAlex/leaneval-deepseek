import Submission.ZagierHoffmanProof.AmbInf
import Submission.ZagierHoffmanProof.StepL199
import Submission.ZagierHoffmanProof.StepL195

/-!
# The pure case of the power sums, transferred to `Ambient F`

For `1 ≤ n ≤ q` the Thakur power sum `P_d(n) = ∑_{a monic, deg a = d} a^{-n}` is the `n`-th power
of `P_d(1)` (`StepL199.P_eq_pow_of_le_card`), and `P_d(1) = (∏_{i<d}(X - X^{q^{i+1}}))⁻¹`
(`StepL195.Hsum_closed` + `P_eq_coe_Hsum`).  Transferring along `ambInfHom` gives the **pure case**
of the bridge (4.2) in the ambient world:

  `ambInfHom (P_d(n)) = (∏_{i<d}(θ - θ^{q^{i+1}}))^{-n}`   (`1 ≤ n ≤ q`).
-/

set_option autoImplicit false
open Polynomial
open scoped WithZero Topology RatFunc.CompletionAtInfty

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The image of the Anderson–Thakur factor `X - X^{q^e}` in `Ambient F` is `θ - θ^{q^e}`. -/
theorem ambKEquiv_Afac (e : ℕ) :
    ((ambKEquiv F (Afac F e) : ↥(ambK F)) : Ambient F)
      = (ambTheta F) - (ambTheta F) ^ ((Nat.card F) ^ e) := by
  rw [Afac]
  rw [show ((X - X ^ ((Nat.card F) ^ e) : F[X]) : RatFunc F)
      = algebraMap (Polynomial F) (RatFunc F) (X - X ^ ((Nat.card F) ^ e) : F[X]) from rfl]
  rw [show (ambKEquiv F) (algebraMap (Polynomial F) (RatFunc F)
      (X - X ^ ((Nat.card F) ^ e) : F[X])) = ambKPolyHom F (X - X ^ ((Nat.card F) ^ e) : F[X])
    from ambKHom_algebraMap F _]
  rw [ambKPolyHom_apply, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_pow,
    Polynomial.eval₂_X]

/-- **The pure case at `n = 1`**, in the ambient world. -/
theorem ambInfHom_P_one (d : ℕ) :
    ambInfHom F (P F d oneExp)
      = ∏ i ∈ Finset.range d, (((ambKEquiv F (Afac F (i + 1)) : ↥(ambK F)) : Ambient F))⁻¹ := by
  rw [P_eq_coe_Hsum F d oneExp, ambInfHom_coe]
  rw [show ((oneExp : ℕ)) = 1 from rfl]
  rw [Hsum_closed F d]
  rw [map_prod]
  exact Finset.prod_congr rfl fun i _ => by
    rw [map_inv₀]
    rfl

/-- ★★ **The pure case** `1 ≤ n ≤ q`: `ambInfHom (P_d(n)) = (ambInfHom (P_d(1)))^n`. -/
theorem ambInfHom_P (d : ℕ) (n : ℕ+) (hn : (n : ℕ) ≤ Nat.card F) :
    ambInfHom F (P F d n) = (ambInfHom F (P F d oneExp)) ^ (n : ℕ) := by
  rw [P_eq_pow_of_le_card F d n hn, map_pow]

end ZagierHoffmanPositiveChar
