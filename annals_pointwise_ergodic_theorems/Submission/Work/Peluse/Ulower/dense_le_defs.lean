/-
# The pair-sum form of Peluse's level-two box-norm power

`pairSum f A C` is the `x`-sum of Peluse's level-two box sum, with the two *outer* index ranges
equal to `A` and the *inner* index range equal to `C`:

`pairSum f A C = ∑_{a,b ∈ A} ∑_x ‖∑_{k ∈ C} f (x + a + k) · conj (f (x + b + k))‖²`.

For a finitely supported `f` the level-two box-norm power is
`‖f‖^{4}_{□²_Q(S)} = |S|⁻¹ · |Q|⁻⁴ · pairSum f Q Q` (`boxNormPow_two_eq_pairSum`), and the point
of the definition is that the *swap* `pairSum f A C = pairSum f C A` is an identity (the reordering
of the quadruple sum), which lets one move the direction set between the outer and the inner role.

## Main definitions

* `Work.Peluse.Ulower.pairSum`
-/
import Mathlib
import Submission.Work.Peluse.BoxNormDilation.boxNormPow_two_eq

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

/-- The `x`-sum of Peluse's level-two box sum, with the outer index range `A` (used twice) and the
inner index range `C`:

`pairSum f A C = ∑_{a,b ∈ A} ∑_x ‖∑_{k ∈ C} f (x + a + k) · conj (f (x + b + k))‖²`. -/
def pairSum (f : ℤ → ℂ) (A C : Finset ℤ) : ℝ :=
  ∑ a ∈ A, ∑ b ∈ A, ∑' x : ℤ, ‖∑ k ∈ C, f (x + a + k) * star (f (x + b + k))‖ ^ 2

lemma pairSum_nonneg (f : ℤ → ℂ) (A C : Finset ℤ) : 0 ≤ pairSum f A C :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => tsum_nonneg fun _ => by positivity

/-- The level-two box-norm power of a finitely supported function, in terms of `pairSum`. -/
lemma boxNormPow_two_eq_pairSum {Q S : Finset ℤ} {f : ℤ → ℂ} (hf : FinSuppZ f) :
    boxNormPow 2 (fun _ : Fin 2 => Q) S f
      = ((S.card : ℝ))⁻¹ * ((Q.card : ℝ))⁻¹ ^ 4 * pairSum f Q Q := by
  rw [BoxNormDilation.boxNormPow_two_eq Q S hf]
  rfl

end

end Work.Peluse.Ulower
