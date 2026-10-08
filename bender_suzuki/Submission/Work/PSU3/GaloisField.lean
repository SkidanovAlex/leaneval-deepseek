/-
# The Frobenius involution of `GaloisField 2 (2n)`

The field `E = GF(q²)`, `q = 2ⁿ`, of the model is `GaloisField 2 (2*n)`, and the
distinguished involution is the `q`-power Frobenius `x ↦ x^q`, i.e. the `n`-th
iterate of the `2`-power Frobenius.  This file installs it as the
`FrobeniusInvolution` instance used by `Work.PSU3.SZ` and the matrix model.
-/
import Submission.Work.PSU3.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.PSU3

/-- The `n`-fold iterate of the `2`-power Frobenius on `GF(2^(2n))` is an
involution (it is the `2ⁿ`-power Frobenius, and `x^(2^(2n)) = x`). -/
theorem iterateFrobenius_galoisField_invol (n : ℕ) (x : GaloisField 2 (2 * n)) :
    iterateFrobenius (GaloisField 2 (2 * n)) 2 n
      (iterateFrobenius (GaloisField 2 (2 * n)) 2 n x) = x := by
  cases n with
  | zero => simp [iterateFrobenius_eq_pow]
  | succ k =>
  haveI : Fintype (GaloisField 2 (2 * (k + 1))) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 (2 * (k + 1))) = 2 ^ (2 * (k + 1)) := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 (2 * (k + 1)) (by omega)
  have hf : frobenius (GaloisField 2 (2 * (k + 1))) 2 ^ (2 * (k + 1)) = 1 :=
    FiniteField.frobenius_pow hcard
  have h2 : (iterateFrobenius (GaloisField 2 (2 * (k + 1))) 2 (k + 1)) ^ 2 = 1 := by
    rw [iterateFrobenius_eq_pow, ← pow_mul, show (k + 1) * 2 = 2 * (k + 1) by ring]
    exact hf
  have h3 := congrFun (congrArg
    (fun f : GaloisField 2 (2 * (k + 1)) →+* GaloisField 2 (2 * (k + 1)) => ⇑f) h2) x
  simpa [RingHom.mul_def] using h3

/-- The distinguished involution `x ↦ x^(2ⁿ)` of `GaloisField 2 (2n)`. -/
noncomputable instance galoisFieldFrobInv (n : ℕ) :
    FrobeniusInvolution (GaloisField 2 (2 * n)) where
  σ := iterateFrobenius (GaloisField 2 (2 * n)) 2 n
  σ_invol := iterateFrobenius_galoisField_invol n

end Work.PSU3
