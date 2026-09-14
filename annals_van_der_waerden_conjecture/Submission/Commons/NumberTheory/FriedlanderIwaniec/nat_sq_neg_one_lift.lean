import Mathlib

namespace Commons.NumberTheory.FriedlanderIwaniec

/-- Hensel lifting of a square root of `-1`: if `x` is a root of `X² + 1` modulo `p ^ e`
for an odd prime `p` (i.e. `p ^ e ∣ x² + 1`), then there is a lift `y` of `x` modulo
`p ^ e` which is a root modulo `p ^ (e+1)`. -/
lemma nat_sq_neg_one_lift {p e : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) (he : 1 ≤ e)
    {x : ℕ} (hx : x < p ^ e) (hroot : p ^ e ∣ x ^ 2 + 1) :
    ∃ y : ℕ, y < p ^ (e + 1) ∧ y % p ^ e = x ∧ p ^ (e + 1) ∣ y ^ 2 + 1 := by
  rcases hroot with ⟨a, ha⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  -- `p` divides `p ^ e` since `e ≥ 1`, hence `p ∣ x ^ 2 + 1`
  have hp_pe : p ∣ p ^ e := by
    refine ⟨p ^ (e - 1), ?_⟩
    rw [← pow_succ', Nat.sub_add_cancel he]
  have hpdvd1 : p ∣ x ^ 2 + 1 := dvd_trans hp_pe ⟨a, ha⟩
  -- so `x` is a root of `X² + 1` modulo `p`
  have hx2 : (x : ZMod p) ^ 2 + 1 = 0 := by
    have hcast : ((x ^ 2 + 1 : ℕ) : ZMod p) = 0 :=
      (CharP.cast_eq_zero_iff (ZMod p) p (x ^ 2 + 1)).mpr hpdvd1
    push_cast at hcast
    simpa using hcast
  -- hence `x` is invertible mod `p`
  have hxne : (x : ZMod p) ≠ 0 := by
    intro h
    rw [h] at hx2
    simp at hx2
  -- and `2` is invertible mod `p` as `p ≠ 2`
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hp2 : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
    rcases (Nat.dvd_prime Nat.prime_two).mp hp2 with h1 | h2
    · exact hp.ne_one h1
    · exact hpodd h2
  have h2xne : (2 * (x : ZMod p)) ≠ 0 := mul_ne_zero h2 hxne
  -- solve `2 * x * t ≡ -a (mod p)` for `t`
  let tbar : ZMod p := -(a : ZMod p) * (2 * (x : ZMod p))⁻¹
  let t : ℕ := tbar.val
  have htval : (t : ZMod p) = tbar := ZMod.natCast_zmod_val tbar
  have htlt : t < p := ZMod.val_lt tbar
  have hcong : ((a + 2 * x * t : ℕ) : ZMod p) = 0 := by
    have hcancel : (2 * (x : ZMod p)) * (2 * (x : ZMod p))⁻¹ = 1 := mul_inv_cancel₀ h2xne
    have hA : (2 * (x : ZMod p)) * tbar = -(a : ZMod p) := by
      calc (2 * (x : ZMod p)) * tbar
          = -(a : ZMod p) * ((2 * (x : ZMod p)) * (2 * (x : ZMod p))⁻¹) := by
              simp only [tbar]; ring
        _ = -(a : ZMod p) * 1 := by rw [hcancel]
        _ = -(a : ZMod p) := by ring
    calc ((a + 2 * x * t : ℕ) : ZMod p)
        = (a : ZMod p) + 2 * (x : ZMod p) * (t : ZMod p) := by push_cast; ring
      _ = (a : ZMod p) + 2 * (x : ZMod p) * tbar := by rw [htval]
      _ = (a : ZMod p) + (-(a : ZMod p)) := by rw [hA]
      _ = 0 := by ring
  have hpdvd : p ∣ a + 2 * x * t :=
    (CharP.cast_eq_zero_iff (ZMod p) p (a + 2 * x * t)).mp hcong
  rcases hpdvd with ⟨c, hc⟩
  -- the lift is `y = x + t * p ^ e`
  refine ⟨x + t * p ^ e, ?_, ?_, ?_⟩
  · -- bound
    have hxle : x + 1 ≤ p ^ e := hx
    have htle : t + 1 ≤ p := htlt
    have h3 : (t + 1) * p ^ e ≤ p * p ^ e := Nat.mul_le_mul_right (p ^ e) htle
    have h4 : x + t * p ^ e + 1 ≤ p ^ e + t * p ^ e := by
      calc x + t * p ^ e + 1 = (x + 1) + t * p ^ e := by ring
        _ ≤ p ^ e + t * p ^ e := by linarith
    have h5 : p ^ e + t * p ^ e ≤ p * p ^ e := by
      calc p ^ e + t * p ^ e = (t + 1) * p ^ e := by ring
        _ ≤ p * p ^ e := h3
    have h6 : x + t * p ^ e + 1 ≤ p * p ^ e := le_trans h4 h5
    have h7 : x + t * p ^ e < p * p ^ e := h6
    rw [mul_comm p (p ^ e), ← pow_succ] at h7
    exact h7
  · -- reduction mod `p ^ e`
    rw [mul_comm t (p ^ e), Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
  · -- the lift is a root modulo `p ^ (e+1)`
    refine ⟨c + t ^ 2 * p ^ (e - 1), ?_⟩
    have hP1 : p ^ (e + 1) = p ^ e * p := by rw [pow_succ]
    have hQ : p ^ e = p ^ (e - 1) * p := by
      conv_lhs => rw [← Nat.sub_add_cancel he]
      rw [pow_succ]
    have step1 :
        (x + t * p ^ e) ^ 2 + 1 = p ^ e * (a + 2 * x * t) + t ^ 2 * (p ^ e) ^ 2 := by
      have h : (x + t * p ^ e) ^ 2 + 1
          = (x ^ 2 + 1) + (2 * x * t) * p ^ e + t ^ 2 * (p ^ e) ^ 2 := by ring
      rw [h, ha]
      ring
    have step2 :
        p ^ (e + 1) * (c + t ^ 2 * p ^ (e - 1)) = p ^ e * (p * c) + t ^ 2 * (p ^ e) ^ 2 := by
      rw [hP1, hQ]
      ring
    rw [step1, hc, ← step2]

end Commons.NumberTheory.FriedlanderIwaniec
