import Mathlib

/-!
# Cross-congruence with a loss of `v_p(6)` (`critN_crossCong_delta`)

This is the arithmetic core used in the Burgess-route computation of
`Work.LinnikBurgess.critN_tripleVanish_content`: three residues
`(A1, A2, A3)` and `(B1, B2, B3)` are compared through the three "cross"
Plücker-type congruences

* `p^k ∣ A2 B3 - A3 B2`,
* `p^k ∣ 2 (A1 B3 - A3 B1)`,
* `p^k ∣ 2 ((A1 B2 - A2 B1) - 3 (A3 - B3))`,

with `B3` a `p`-adic unit.  The conclusion is that the two triples agree
coordinate-wise modulo `p ^ (k - v_p(6))`.

The two occurrences of the factor `2` cost a power `v_p(2)` of `p`, and the
correction term `3 (A3 - B3)` costs a further `v_p(3)`; altogether the loss is
exactly `v_p(2) + v_p(3) = v_p(6)`.  Concretely, the argument produces

* `p ^ (k - v_p 2) ∣ A1 B2 - A2 B1` (factors of `2` removed from `h0`, `h1`),
* `p ^ (k - v_p 2) ∣ A1 B3 - A3 B1` (factor of `2` removed from `h1`),
* `p ^ (k - v_p 2) ∣ 3 (A3 - B3)` (subtracting the previous two from `h2`),

whence `p ^ (k - v_p 6) ∣ A3 - B3`, and finally the two expansion identities

* `B3 (A2 - B2) = (A2 B3 - A3 B2) + B2 (A3 - B3)`,
* `B3 (A1 - B1) = (A1 B3 - A3 B1) + B1 (A3 - B3)`

transfer the divisibility, using `p ∤ B3`, to `A2 - B2` and `A1 - B1`.
-/

namespace Work.LinnikBurgess

/-- **Removal of a factor `c ≠ 0`.**  If `p ^ a ∣ c * D` then
`p ^ (a - v_p c) ∣ D`; the `p`-adic valuation lost is exactly `v_p(c)`. -/
private lemma int_dvd_of_dvd_mul_left {p a : ℕ} [Fact p.Prime] {c D : ℤ} (hc : c ≠ 0)
    (h : ((p ^ a : ℕ) : ℤ) ∣ c * D) :
    ((p ^ (a - padicValNat p c.natAbs) : ℕ) : ℤ) ∣ D := by
  by_cases hD : D = 0
  · subst hD; exact dvd_zero _
  · have hn : D.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hD
    have hm : c.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hc
    have h' : p ^ a ∣ c.natAbs * D.natAbs := by
      have := (Int.natAbs_dvd_natAbs).mpr h
      simpa [Int.natAbs_mul, Int.natAbs_natCast] using this
    have h3 : a ≤ padicValNat p (c.natAbs * D.natAbs) :=
      (padicValNat_dvd_iff_le (mul_ne_zero hm hn)).mp h'
    have h4 : padicValNat p (c.natAbs * D.natAbs)
        = padicValNat p c.natAbs + padicValNat p D.natAbs := padicValNat.mul hm hn
    have h5 : a - padicValNat p c.natAbs ≤ padicValNat p D.natAbs := by omega
    have h6 : p ^ (a - padicValNat p c.natAbs) ∣ D.natAbs :=
      (padicValNat_dvd_iff_le hn).mpr h5
    exact (Int.natAbs_dvd_natAbs).mp (by simpa [Int.natAbs_natCast] using h6)

/-- Monotonicity of `p`-power divisibility, transported to `ℤ`. -/
private lemma pow_dvd_pow_cast {p a b : ℕ} (h : a ≤ b) :
    ((p ^ a : ℕ) : ℤ) ∣ ((p ^ b : ℕ) : ℤ) :=
  Int.natCast_dvd_natCast.mpr (pow_dvd_pow p h)

theorem critN_crossCong_delta {p k : ℕ} [Fact p.Prime] {A1 A2 A3 B1 B2 B3 : ℤ}
    (hB3 : ¬ (p : ℤ) ∣ B3)
    (h0 : ((p ^ k : ℕ) : ℤ) ∣ A2 * B3 - A3 * B2)
    (h1 : ((p ^ k : ℕ) : ℤ) ∣ 2 * (A1 * B3 - A3 * B1))
    (h2 : ((p ^ k : ℕ) : ℤ) ∣ 2 * ((A1 * B2 - A2 * B1) - 3 * (A3 - B3))) :
    ((p ^ (k - padicValNat p 6) : ℕ) : ℤ) ∣ A1 - B1
    ∧ ((p ^ (k - padicValNat p 6) : ℕ) : ℤ) ∣ A2 - B2
    ∧ ((p ^ (k - padicValNat p 6) : ℕ) : ℤ) ∣ A3 - B3 := by
  have hB3ne : B3 ≠ 0 := by rintro rfl; exact hB3 (dvd_zero _)
  have hB3val : padicValNat p B3.natAbs = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro h
    exact hB3 ((Int.natAbs_dvd_natAbs).mp (by simpa using h))
  have hv6 : padicValNat p 6 = padicValNat p 2 + padicValNat p 3 := by
    have := padicValNat.mul (p := p) (a := 2) (b := 3) (by norm_num) (by norm_num)
    simpa using this
  have he : k - padicValNat p 2 - padicValNat p 3 = k - padicValNat p 6 := by
    rw [hv6, Nat.sub_sub]
  have hle_e_k : k - padicValNat p 6 ≤ k := Nat.sub_le _ _
  have hle_e_E2 : k - padicValNat p 6 ≤ k - padicValNat p 2 :=
    Nat.sub_le_sub_left (by rw [hv6]; exact Nat.le_add_right _ _) k
  -- `p ^ k ∣ 2 * B2 * (A1 B3 - A3 B1)` from `h1`
  have hA : ((p ^ k : ℕ) : ℤ) ∣ 2 * B2 * (A1 * B3 - A3 * B1) := by
    have heq : 2 * B2 * (A1 * B3 - A3 * B1) = B2 * (2 * (A1 * B3 - A3 * B1)) := by ring
    rw [heq]; exact dvd_mul_of_dvd_right h1 B2
  -- `p ^ k ∣ 2 * B1 * (A2 B3 - A3 B2)` from `h0`
  have hB : ((p ^ k : ℕ) : ℤ) ∣ 2 * B1 * (A2 * B3 - A3 * B2) :=
    dvd_mul_of_dvd_right h0 (2 * B1)
  -- `p ^ k ∣ 2 * B3 * (A1 B2 - A2 B1)`: subtract the two `2`-free combinations
  have hcomb : ((p ^ k : ℕ) : ℤ) ∣ 2 * B3 * (A1 * B2 - A2 * B1) := by
    have hsub := dvd_sub hA hB
    have heq : 2 * B3 * (A1 * B2 - A2 * B1)
        = 2 * B2 * (A1 * B3 - A3 * B1) - 2 * B1 * (A2 * B3 - A3 * B2) := by ring
    rw [heq]; exact hsub
  -- remove the factor `2` and then the unit `B3`: `p ^ (k - v_p 2) ∣ A1 B2 - A2 B1`
  have hiv : ((p ^ (k - padicValNat p 2) : ℕ) : ℤ) ∣ A1 * B2 - A2 * B1 := by
    have h1' : ((p ^ (k - padicValNat p 2) : ℕ) : ℤ) ∣ B3 * (A1 * B2 - A2 * B1) := by
      have heq : (2 : ℤ) * (B3 * (A1 * B2 - A2 * B1)) = 2 * B3 * (A1 * B2 - A2 * B1) := by
        ring
      have hin : ((p ^ k : ℕ) : ℤ) ∣ (2 : ℤ) * (B3 * (A1 * B2 - A2 * B1)) := by
        rw [heq]; exact hcomb
      have := int_dvd_of_dvd_mul_left (a := k) (c := (2 : ℤ))
        (D := B3 * (A1 * B2 - A2 * B1)) (by norm_num) hin
      simpa using this
    have := int_dvd_of_dvd_mul_left (a := k - padicValNat p 2) (c := B3)
      (D := A1 * B2 - A2 * B1) hB3ne h1'
    simpa [hB3val] using this
  -- remove the factor `2` from `h2`
  have h2rm : ((p ^ (k - padicValNat p 2) : ℕ) : ℤ)
      ∣ (A1 * B2 - A2 * B1) - 3 * (A3 - B3) := by
    have := int_dvd_of_dvd_mul_left (a := k) (c := (2 : ℤ))
      (D := (A1 * B2 - A2 * B1) - 3 * (A3 - B3)) (by norm_num) h2
    simpa using this
  -- subtract: `p ^ (k - v_p 2) ∣ 3 * (A3 - B3)`
  have h3rm : ((p ^ (k - padicValNat p 2) : ℕ) : ℤ) ∣ 3 * (A3 - B3) := by
    have h' : ((p ^ (k - padicValNat p 2) : ℕ) : ℤ) ∣ - (3 * (A3 - B3)) := by
      have hsub := dvd_sub h2rm hiv
      have heq : - (3 * (A3 - B3))
          = ((A1 * B2 - A2 * B1) - 3 * (A3 - B3)) - (A1 * B2 - A2 * B1) := by ring
      rw [heq]; exact hsub
    exact (dvd_neg).mp h'
  -- remove the factor `3`: `p ^ (k - v_p 6) ∣ A3 - B3`
  have hd3 : ((p ^ (k - padicValNat p 6) : ℕ) : ℤ) ∣ A3 - B3 := by
    have := int_dvd_of_dvd_mul_left (a := k - padicValNat p 2) (c := (3 : ℤ))
      (D := A3 - B3) (by norm_num) h3rm
    simpa [he] using this
  -- expansion identity `B3 (A2 - B2) = (A2 B3 - A3 B2) + B2 (A3 - B3)`
  have hd2 : ((p ^ (k - padicValNat p 6) : ℕ) : ℤ) ∣ A2 - B2 := by
    have hk : ((p ^ (k - padicValNat p 6) : ℕ) : ℤ) ∣ A2 * B3 - A3 * B2 :=
      (pow_dvd_pow_cast hle_e_k).trans h0
    have hb : ((p ^ (k - padicValNat p 6) : ℕ) : ℤ) ∣ B2 * (A3 - B3) :=
      dvd_mul_of_dvd_right hd3 B2
    have hsum := dvd_add hk hb
    have heq : B3 * (A2 - B2) = (A2 * B3 - A3 * B2) + B2 * (A3 - B3) := by ring
    have hin : ((p ^ (k - padicValNat p 6) : ℕ) : ℤ) ∣ B3 * (A2 - B2) := by
      rw [heq]; exact hsum
    have := int_dvd_of_dvd_mul_left (a := k - padicValNat p 6) (c := B3) (D := A2 - B2)
      hB3ne hin
    simpa [hB3val] using this
  -- remove the factor `2` from `h1`: `p ^ (k - v_p 2) ∣ A1 B3 - A3 B1`
  have hX : ((p ^ (k - padicValNat p 2) : ℕ) : ℤ) ∣ A1 * B3 - A3 * B1 := by
    have := int_dvd_of_dvd_mul_left (a := k) (c := (2 : ℤ))
      (D := A1 * B3 - A3 * B1) (by norm_num) h1
    simpa using this
  -- expansion identity `B3 (A1 - B1) = (A1 B3 - A3 B1) + B1 (A3 - B3)`
  have hd1 : ((p ^ (k - padicValNat p 6) : ℕ) : ℤ) ∣ A1 - B1 := by
    have h1' : ((p ^ (k - padicValNat p 6) : ℕ) : ℤ) ∣ A1 * B3 - A3 * B1 :=
      (pow_dvd_pow_cast hle_e_E2).trans hX
    have hb : ((p ^ (k - padicValNat p 6) : ℕ) : ℤ) ∣ B1 * (A3 - B3) :=
      dvd_mul_of_dvd_right hd3 B1
    have hsum := dvd_add h1' hb
    have heq : B3 * (A1 - B1) = (A1 * B3 - A3 * B1) + B1 * (A3 - B3) := by ring
    have hin : ((p ^ (k - padicValNat p 6) : ℕ) : ℤ) ∣ B3 * (A1 - B1) := by
      rw [heq]; exact hsum
    have := int_dvd_of_dvd_mul_left (a := k - padicValNat p 6) (c := B3) (D := A1 - B1)
      hB3ne hin
    simpa [hB3val] using this
  exact ⟨hd1, hd2, hd3⟩

end Work.LinnikBurgess
