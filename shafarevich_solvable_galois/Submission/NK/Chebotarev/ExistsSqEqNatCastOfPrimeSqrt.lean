import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.Chebotarev

open Nat in
/-- If every prime dividing `M` has a square root in the field `F`, then `M` itself
has a square root in `F`.  Indeed `M = (M / p) * p` and by strong induction
`M / p` is a square, so `M` is the product of two squares. -/
theorem ExistsSqEqNatCastOfPrimeSqrt {F : Type*} [Field F] (M : ℕ)
    (h : ∀ p : ℕ, Nat.Prime p → p ∣ M → ∃ x : F, x ^ 2 = (p : F)) :
    ∃ y : F, y ^ 2 = (M : F) := by
  suffices ∀ M : ℕ, (∀ p : ℕ, Nat.Prime p → p ∣ M → ∃ x : F, x ^ 2 = (p : F)) →
      ∃ y : F, y ^ 2 = (M : F) from this M h
  intro M
  refine Nat.strong_induction_on M fun M ih => ?_
  intro hM
  rcases Nat.eq_zero_or_pos M with h0 | hpos
  · exact ⟨0, by rw [h0]; simp⟩
  rcases lt_or_ge M 2 with hlt | hge
  · have hM1 : M = 1 := by omega
    exact ⟨1, by rw [hM1]; simp⟩
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (by omega : M ≠ 1)
  obtain ⟨y, hy⟩ := hM p hp hpdvd
  set k := M / p with hk
  have hMk : M = p * k := by rw [hk]; exact (Nat.mul_div_cancel' hpdvd).symm
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkp
    · rw [hMk, hk0, mul_zero] at hge; omega
    · exact hkp
  have hklt : k < M := by nlinarith [hp.two_le, hkpos]
  obtain ⟨x, hx⟩ := ih k hklt fun q hq hqdvd => hM q hq (dvd_trans hqdvd ⟨p, by rw [mul_comm, hMk]⟩)
  exact ⟨y * x, by rw [mul_pow, hy, hx, hMk, Nat.cast_mul]⟩

end NK.Chebotarev
