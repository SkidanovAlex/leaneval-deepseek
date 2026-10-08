import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PGroup

/-- For any integer `a` and `n : ℕ`, `(a - 1)^2` divides `a^n - (1 + n(a-1))`;
i.e. `a^n ≡ 1 + n(a-1)  (mod (a-1)^2)`. -/
lemma geom_term_dvd (a : ℤ) (n : ℕ) :
    (a - 1) ^ 2 ∣ a ^ n - (1 + (n : ℤ) * (a - 1)) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hsum : a ^ (n + 1) - (1 + ((n + 1 : ℕ) : ℤ) * (a - 1))
        = a * (a ^ n - (1 + (n : ℤ) * (a - 1))) + (n : ℤ) * (a - 1) ^ 2 := by
      push_cast; ring
    rw [hsum]
    apply dvd_add
    · obtain ⟨c, hc⟩ := ih; exact ⟨a * c, by rw [hc]; ring⟩
    · exact ⟨(n : ℤ), by ring⟩

/-- For an odd number `q`, `q` divides `∑_{i<q} i = q(q-1)/2`. -/
lemma dvd_sum_range_id_of_odd {q : ℕ} (hodd : Odd q) :
    (q : ℤ) ∣ ∑ i ∈ Finset.range q, (i : ℤ) := by
  obtain ⟨k, hk⟩ := hodd
  have h2 : 2 ∣ q - 1 := ⟨k, by omega⟩
  have hid : ∑ i ∈ Finset.range q, (i : ℤ) = ((q * ((q - 1) / 2) : ℕ) : ℤ) := by
    rw [← Nat.cast_sum, Finset.sum_range_id, Nat.mul_div_assoc q h2]
  rw [hid, Nat.cast_mul]
  exact dvd_mul_right _ _

lemma geom_sum_sq_not_dvd {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {a : ℤ}
    (ha : (q : ℤ) ∣ a - 1) :
    ¬ ((q : ℤ) ^ 2 ∣ ∑ i ∈ Finset.range q, a ^ i) := by
  intro hdiv
  obtain ⟨b, hb⟩ := ha
  have hodd : Odd q := hq.odd_of_ne_two hq2
  -- `(q:ℤ)^2 ∣ (a-1)^2`
  have hq2dvd : (q : ℤ) ^ 2 ∣ (a - 1) ^ 2 := ⟨b ^ 2, by rw [hb]; ring⟩
  -- each term satisfies `a^i ≡ 1 + i(a-1)  (mod q^2)`
  have hterm : ∀ i ∈ Finset.range q,
      (q : ℤ) ^ 2 ∣ a ^ i - (1 + (i : ℤ) * (a - 1)) := by
    intro i _
    exact dvd_trans hq2dvd (geom_term_dvd a i)
  have hsum : (q : ℤ) ^ 2 ∣
      ∑ i ∈ Finset.range q, (a ^ i - (1 + (i : ℤ) * (a - 1))) :=
    Finset.dvd_sum hterm
  rw [Finset.sum_sub_distrib] at hsum
  -- the linear part sums to `q + (a-1) * ∑ i`
  have hS1 : (∑ i ∈ Finset.range q, (1 + (i : ℤ) * (a - 1))) - (q : ℤ)
      = (a - 1) * (∑ i ∈ Finset.range q, (i : ℤ)) := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    ring
  obtain ⟨Y, hY⟩ := dvd_sum_range_id_of_odd hodd
  have hmul : (∑ i ∈ Finset.range q, (1 + (i : ℤ) * (a - 1))) - (q : ℤ)
      = (q : ℤ) ^ 2 * (b * Y) := by
    rw [hS1, hY, hb]; ring
  have hS1q : (q : ℤ) ^ 2 ∣
      (∑ i ∈ Finset.range q, (1 + (i : ℤ) * (a - 1))) - (q : ℤ) :=
    ⟨b * Y, hmul⟩
  -- therefore `q^2 ∣ S - q`
  have hSq : (q : ℤ) ^ 2 ∣ (∑ i ∈ Finset.range q, a ^ i) - (q : ℤ) := by
    have hh : (∑ i ∈ Finset.range q, a ^ i) - (q : ℤ)
        = ((∑ i ∈ Finset.range q, a ^ i)
            - (∑ i ∈ Finset.range q, (1 + (i : ℤ) * (a - 1))))
          + ((∑ i ∈ Finset.range q, (1 + (i : ℤ) * (a - 1))) - (q : ℤ)) := by
      ring
    rw [hh]
    exact dvd_add hsum hS1q
  -- combine with the assumed divisibility to force `q^2 ∣ q`, impossible
  have hqq : (q : ℤ) ^ 2 ∣ (q : ℤ) := by
    have := dvd_sub hdiv hSq
    simpa using this
  have hle : (q : ℤ) ^ 2 ≤ (q : ℤ) := Int.le_of_dvd (by exact_mod_cast hq.pos) hqq
  have h2q : (2 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq.two_le
  nlinarith [hle, h2q]

end Work.PGroup
