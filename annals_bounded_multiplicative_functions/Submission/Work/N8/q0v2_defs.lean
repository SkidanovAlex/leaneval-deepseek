import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Denominators of the coefficients of a polynomial (N8, arithmetic core of Step 6)

For the arithmetic core of the "`q₀ ≪ 1`" step (`Work.N8.q0_arith_v2`) we need the notion of the
*denominator* of the coefficient `γ.coeff m` of a real polynomial: the least `β ≥ 1` with
`β * γ.coeff m ∈ ℤ`.

* `IsDenom γ m β` : `β ≥ 1` and `β * γ.coeff m` is an integer;
* `denom γ m` : the least such `β` (junk value `1` if there is none);
* `denom_spec`, `denom_le` : its two defining properties.
-/

namespace Work.N8

open Polynomial

/-- `β` is a denominator of the `m`-th coefficient of `γ`: `1 ≤ β` and `β * γ.coeff m ∈ ℤ`. -/
def IsDenom (γ : Polynomial ℝ) (m : ℕ) (β : ℕ) : Prop :=
  1 ≤ β ∧ ∃ a : ℤ, (a : ℝ) = (β : ℝ) * γ.coeff m

open Classical in
/-- The least denominator of the coefficient `γ.coeff m`, or the junk value `1` if no
denominator exists. -/
noncomputable def denom (γ : Polynomial ℝ) (m : ℕ) : ℕ :=
  if h : ∃ β, IsDenom γ m β then Nat.find h else 1

theorem denom_spec {γ : Polynomial ℝ} {m : ℕ} (h : ∃ β, IsDenom γ m β) :
    IsDenom γ m (denom γ m) := by
  classical
  rw [denom, dite_eq_left h]
  exact Nat.find_spec h

theorem denom_le {γ : Polynomial ℝ} {m : ℕ} (h : ∃ β, IsDenom γ m β) {β : ℕ}
    (hβ : IsDenom γ m β) : denom γ m ≤ β := by
  classical
  rw [denom, dite_eq_left h]
  exact Nat.find_min' h hβ

theorem one_le_denom {γ : Polynomial ℝ} {m : ℕ} (h : ∃ β, IsDenom γ m β) :
    1 ≤ denom γ m := (denom_spec h).1

end Work.N8
