import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageA

/-- If `y * y = 0` in a commutative ring, the binomial expansion of `(1 + y) ^ n`
degenerates after the linear term: `(1 + y) ^ n = 1 + n * y`. -/
lemma pow_one_add_of_sq_eq_zero {R : Type*} [CommRing R] {y : R} (hy : y * y = 0) :
    ∀ n : ℕ, (1 + y) ^ n = 1 + (n : R) * y := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, Nat.cast_succ]
    ring_nf
    rw [show y ^ 2 = 0 by rw [pow_two]; exact hy]
    ring

theorem geom_sum_modEq_prime_sq {A p : ℕ} (hA : 2 ≤ A) (hp : p.Prime) (hp2 : p ≠ 2)
    (hdiv : p ∣ A - 1) :
    Nat.ModEq (p ^ 2) (∑ i ∈ Finset.range p, A ^ i) p := by
  obtain ⟨t, ht⟩ := hdiv
  have hAeq : A = p * t + 1 := by omega
  have hpodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  have h2dvd : 2 ∣ p - 1 := by
    have : Odd p := Nat.odd_iff.mpr hpodd
    obtain ⟨k, hk⟩ := this
    exact ⟨k, by omega⟩
  have hdiv2 : p * (p - 1) / 2 = p * ((p - 1) / 2) := Nat.mul_div_assoc p h2dvd
  apply (ZMod.natCast_eq_natCast_iff _ _ (p ^ 2)).mp
  simp only [Nat.cast_sum, Nat.cast_pow]
  have hAc : (A : ZMod (p ^ 2)) = 1 + (p : ZMod (p ^ 2)) * (t : ZMod (p ^ 2)) := by
    rw [hAeq]; push_cast; ring
  rw [hAc]
  have hy : ((p : ZMod (p ^ 2)) * (t : ZMod (p ^ 2))) * ((p : ZMod (p ^ 2)) * (t : ZMod (p ^ 2))) = 0 := by
    have hpp : ((p : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))) = 0 := by
      rw [← pow_two, ← Nat.cast_pow, ZMod.natCast_self]
    calc ((p:ZMod (p ^ 2)) * (t:ZMod (p ^ 2))) * ((p:ZMod (p ^ 2)) * (t:ZMod (p ^ 2)))
        = ((p:ZMod (p ^ 2)) * (p:ZMod (p ^ 2))) * ((t:ZMod (p ^ 2)) * (t:ZMod (p ^ 2))) := by ring
      _ = 0 := by rw [hpp, zero_mul]
  rw [Finset.sum_congr rfl (fun x _ => pow_one_add_of_sq_eq_zero hy x)]
  rw [Finset.sum_add_distrib]
  have hsum1 : (∑ x ∈ Finset.range p, (1 : ZMod (p ^ 2))) = (p : ZMod (p ^ 2)) := by
    rw [Finset.sum_const, Finset.card_range]
    simp
  have hsumid : (∑ x ∈ Finset.range p, (x : ZMod (p ^ 2))) = ((p * (p - 1) / 2 : ℕ) : ZMod (p ^ 2)) := by
    rw [← Nat.cast_sum, Finset.sum_range_id]
  rw [hsum1, ← Finset.sum_mul, hsumid]
  have hzero : ((p * (p - 1) / 2 : ℕ) : ZMod (p ^ 2)) * ((p : ZMod (p ^ 2)) * (t : ZMod (p ^ 2))) = 0 := by
    rw [hdiv2]
    have hcast : (((p * ((p - 1) / 2)) : ℕ) : ZMod (p ^ 2)) = (p : ZMod (p ^ 2)) * (((p - 1) / 2 : ℕ) : ZMod (p ^ 2)) := by
      push_cast; ring
    rw [hcast]
    have hpp : ((p : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))) = 0 := by
      rw [← pow_two, ← Nat.cast_pow, ZMod.natCast_self]
    calc ((p:ZMod (p ^ 2)) * (((p-1)/2 : ℕ) : ZMod (p ^ 2))) * ((p:ZMod (p ^ 2)) * (t:ZMod (p ^ 2)))
        = ((p:ZMod (p ^ 2)) * (p:ZMod (p ^ 2))) * ((((p-1)/2 : ℕ) : ZMod (p ^ 2)) * (t:ZMod (p ^ 2))) := by ring
      _ = 0 := by rw [hpp, zero_mul]
  rw [hzero, add_zero]

end Work.PSU3.StageA
