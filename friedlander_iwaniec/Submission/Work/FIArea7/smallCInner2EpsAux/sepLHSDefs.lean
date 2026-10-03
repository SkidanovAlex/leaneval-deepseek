import Mathlib
import Submission.Work.FIArea7.smallCInner2EpsAux.defs

set_option autoImplicit false

namespace Work.FIArea7.smallCInner2EpsAux

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The indicator, as a complex number, of the condition that all prime factors of `n` are `≤ z`
(i.e. that `n` is `z`-smooth). -/
def smoothInd (z n : ℕ) : ℂ := if (∀ p : ℕ, p.Prime → p ∣ n → p ≤ z) then (1 : ℂ) else 0

/-- The coefficient attached to one of the three factors `d, m, n` of a *FI* §24 separation
triple: the coprimality indicator `(c, ·) = 1`, the `z`-smoothness indicator, the sieve factor
`nspInd` and the Möbius function.  On a separation triple `d·m·n` the product
`cCoeff Pa c z d * cCoeff Pa c z m * cCoeff Pa c z n` is `μ(d·m·n)·nspInd(d·m·n)·1[(c,dmn)=1]`
times the `z`-smoothness indicator. -/
def cCoeff (Pa : Work.FITop.Params) (c z : ℕ) (n : ℕ) : ℂ :=
  (if Nat.Coprime c n then (1 : ℂ) else 0) * smoothInd z n
    * Work.FIArea7.nspInd Pa n * ((ArithmeticFunction.moebius n : ℤ) : ℂ)

lemma norm_smoothInd_le_one (z n : ℕ) : ‖smoothInd z n‖ ≤ 1 := by
  unfold smoothInd
  split <;> simp

lemma norm_moebius_le_one (n : ℕ) : ‖(((ArithmeticFunction.moebius n : ℤ)) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast, ← Int.cast_abs]
  have h := ArithmeticFunction.abs_moebius_le_one (n := n)
  exact_mod_cast h

lemma norm_cCoeff_le_one (Pa : Work.FITop.Params) (c z n : ℕ) : ‖cCoeff Pa c z n‖ ≤ 1 := by
  rw [cCoeff]
  have h1 : ‖(if Nat.Coprime c n then (1 : ℂ) else 0)‖ ≤ 1 := by split <;> simp
  have h2 : ‖smoothInd z n‖ ≤ 1 := norm_smoothInd_le_one z n
  have h3 : ‖Work.FIArea7.nspInd Pa n‖ ≤ 1 := Work.FIArea7.norm_nspInd_le_one Pa n
  have h4 : ‖(((ArithmeticFunction.moebius n : ℤ)) : ℂ)‖ ≤ 1 := norm_moebius_le_one n
  calc ‖(if Nat.Coprime c n then (1 : ℂ) else 0) * smoothInd z n
        * Work.FIArea7.nspInd Pa n * ((ArithmeticFunction.moebius n : ℤ) : ℂ)‖
      = ‖(if Nat.Coprime c n then (1 : ℂ) else 0)‖ * ‖smoothInd z n‖
        * ‖Work.FIArea7.nspInd Pa n‖ * ‖(((ArithmeticFunction.moebius n : ℤ)) : ℂ)‖ := by
        rw [norm_mul, norm_mul, norm_mul]
    _ ≤ 1 * 1 * 1 * 1 := by
        gcongr
    _ = 1 := by norm_num

/-- The indicator of a proposition, as a complex number.  Bundled as a definition so that
statements using it do not have to carry a `Decidable` instance. -/
def ind (p : Prop) : ℂ := if p then 1 else 0

@[simp] lemma ind_pos {p : Prop} (h : p) : ind p = 1 := by
  unfold ind; rw [if_pos h]

@[simp] lemma ind_neg {p : Prop} (h : ¬p) : ind p = 0 := by
  unfold ind; rw [if_neg h]

lemma ind_and (p q : Prop) : ind (p ∧ q) = ind p * ind q := by
  unfold ind
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

lemma ind_mul (p q : Prop) : ind p * ind q = ind (p ∧ q) := (ind_and p q).symm

lemma norm_ind_le_one (p : Prop) : ‖ind p‖ ≤ 1 := by
  unfold ind; split <;> simp

lemma norm_ind_eq (p : Prop) : ‖ind p‖ = ind p := by
  unfold ind; split <;> simp


lemma ind_mul_eq (p : Prop) (x : ℂ) : ind p * x = if p then x else 0 := by
  unfold ind
  by_cases h : p <;> simp [h]

lemma ind_and_and (p q r : Prop) : ind (p ∧ q ∧ r) = ind p * ind q * ind r := by
  rw [ind_and, ind_and]; ring

lemma ind_and_and_and (p q r s : Prop) : ind (p ∧ q ∧ r ∧ s) = ind p * ind q * ind r * ind s := by
  rw [ind_and, ind_and, ind_and]; ring


end

end Work.FIArea7.smallCInner2EpsAux
