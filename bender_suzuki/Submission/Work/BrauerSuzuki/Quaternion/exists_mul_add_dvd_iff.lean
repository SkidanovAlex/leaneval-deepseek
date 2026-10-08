import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.Quaternion

set_option linter.style.haveILetI false

/-- For `0 < n`, the congruence `n ∣ a * k + b` is solvable in `k : ℕ` if and only if
`gcd a n ∣ b`. The forward direction is immediate since `gcd a n` divides both `a` and `n`;
for the converse one divides everything by `g = gcd a n`, reducing to the case where `a` is
coprime to `n`, i.e. `a` is a unit of `ZMod n`. -/
theorem exists_mul_add_dvd_iff {n a b : ℕ} (hn : 0 < n) :
    (∃ k : ℕ, n ∣ a * k + b) ↔ Nat.gcd a n ∣ b := by
  constructor
  · rintro ⟨k, hk⟩
    exact (Nat.dvd_add_iff_right ((Nat.gcd_dvd_left a n).trans (dvd_mul_right a k))).mpr
      ((Nat.gcd_dvd_right a n).trans hk)
  · intro hb
    -- Divide by `g = gcd a n`: `a = g * A`, `n = g * N`, `b = g * B` with `A` coprime to `N`.
    set g := Nat.gcd a n with hg
    set N := n / g with hN
    set A := a / g with hA
    set B := b / g with hB
    have hgpos : 0 < g := by rw [hg]; exact Nat.gcd_pos_of_pos_right a hn
    have hcop : Nat.Coprime A N := by
      rw [hA, hN, hg]
      exact Nat.coprime_div_gcd_div_gcd hgpos
    have hNne : N ≠ 0 := by
      rw [hN, hg]
      intro h
      have hnt := Nat.mul_div_cancel' (Nat.gcd_dvd_right a n)
      rw [h, mul_zero] at hnt
      omega
    haveI : NeZero N := ⟨hNne⟩
    have hav : g * A = a := by rw [hA, hg, Nat.mul_div_cancel' (Nat.gcd_dvd_left a n)]
    have hnv : g * N = n := by rw [hN, hg, Nat.mul_div_cancel' (Nat.gcd_dvd_right a n)]
    have hbv : g * B = b := by rw [hB, hg, Nat.mul_div_cancel' hb]
    -- `A` is a unit of `ZMod N`; solve `A * x + B = 0` there and lift `x` back to `ℕ`.
    have hunit : IsUnit (A : ZMod N) := (ZMod.isUnit_iff_coprime A N).mpr hcop
    let x : ZMod N := (A : ZMod N)⁻¹ * (-(B : ZMod N))
    have hx : (A : ZMod N) * (x.val : ZMod N) + (B : ZMod N) = 0 := by
      rw [ZMod.natCast_zmod_val x]
      show (A : ZMod N) * ((A : ZMod N)⁻¹ * -(B : ZMod N)) + (B : ZMod N) = 0
      rw [← mul_assoc, ZMod.mul_inv_of_unit (A : ZMod N) hunit, one_mul]
      simp
    have hdiv : N ∣ A * x.val + B :=
      (ZMod.natCast_eq_zero_iff (A * x.val + B) N).mp (by push_cast; exact hx)
    obtain ⟨t, ht⟩ := hdiv
    have key : a * x.val + b = g * (A * x.val + B) := by
      rw [← hav, ← hbv]; ring
    refine ⟨x.val, t, ?_⟩
    rw [key, ht, ← hnv]
    ring

end Work.BrauerSuzuki.Quaternion
