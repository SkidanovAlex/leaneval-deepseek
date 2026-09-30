import Mathlib
import Submission.Work.N8.q0v2_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The least denominator divides every denominator (N8)

`Work.N8.IsDenom γ m β` says `β ≥ 1` and `β * γ.coeff m ∈ ℤ`.  The set of such `β` is closed
under `gcd`: if `β₁ c ∈ ℤ` and `β₂ c ∈ ℤ` then Bézout gives `gcd β₁ β₂ · c ∈ ℤ` as well
(`Nat.gcd_eq_gcd_ab`).  Consequently the least denominator `Work.N8.denom γ m` divides every
denominator `β'`: apply `denom_le` to `gcd (denom γ m) β'`, which `gcd`-closure makes a
denominator, to get `denom γ m ≤ gcd (denom γ m) β'`, while `gcd` is always `≤ denom γ m`.
-/

namespace Work.N8

open Polynomial

/-- The set of denominators of the coefficient `γ.coeff m` is closed under `gcd`: a Bézout
combination of two integral multiples of `γ.coeff m` is again an integral multiple. -/
theorem isDenom_gcd {γ : Polynomial ℝ} {m β₁ β₂ : ℕ}
    (h₁ : IsDenom γ m β₁) (h₂ : IsDenom γ m β₂) : IsDenom γ m (Nat.gcd β₁ β₂) := by
  obtain ⟨h1, a, ha⟩ := h₁
  obtain ⟨h2, b, hb⟩ := h₂
  have hpos : 0 < Nat.gcd β₁ β₂ := Nat.gcd_pos_of_pos_left β₂ (by omega)
  refine ⟨hpos, Nat.gcdA β₁ β₂ * a + Nat.gcdB β₁ β₂ * b, ?_⟩
  have hbez := Nat.gcd_eq_gcd_ab β₁ β₂
  have hbezR : ((Nat.gcd β₁ β₂ : ℕ) : ℝ)
      = (β₁ : ℝ) * (Nat.gcdA β₁ β₂ : ℝ) + (β₂ : ℝ) * (Nat.gcdB β₁ β₂ : ℝ) := by
    exact_mod_cast hbez
  push_cast
  rw [ha, hb, hbezR]
  ring

theorem denom_dvd_of_isDenom {γ : Polynomial ℝ} {m : ℕ}
    (h : ∃ β : ℕ, Work.N8.IsDenom γ m β) {β' : ℕ} (h' : Work.N8.IsDenom γ m β') :
    Work.N8.denom γ m ∣ β' := by
  have hd := Work.N8.denom_spec h
  have hg := isDenom_gcd hd h'
  have hle : Work.N8.denom γ m ≤ Nat.gcd (Work.N8.denom γ m) β' := Work.N8.denom_le h hg
  have hge : Nat.gcd (Work.N8.denom γ m) β' ≤ Work.N8.denom γ m :=
    Nat.gcd_le_left β' (by have := hd.1; omega)
  have heq : Nat.gcd (Work.N8.denom γ m) β' = Work.N8.denom γ m := le_antisymm hge hle
  rw [← heq]
  exact Nat.gcd_dvd_right _ _

end Work.N8
