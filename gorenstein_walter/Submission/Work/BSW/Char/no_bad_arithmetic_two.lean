/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW, `Work.BSW.Char`)

# The "no bad arithmetic" contract, `dᵢ ≥ 2` version

The counting argument of Bender's §2 (in the Bender–Suzuki–Walter strategy towards
Gorenstein–Walter) rules out a numerical configuration of a hypothetical group: an integer
`n ≥ 5` with `n ≡ 1 (mod 4)` and `3 ∣ n`, three degrees `dᵢ ≥ 2` and signs `eᵢ = ±1` with

`1 + e1/d1 + e2/d2 + e3/d3 = 8/(3n)`   and   `1 + d1² + d2² + d3² ≤ 12n`.

The companion `Work.BSW.Char.no_bad_arithmetic` disposes of all configurations with
`dᵢ ≥ 3`.  Here we treat the remaining case, where one of the `dᵢ` equals `2`.

The mathematical content of the extra case is the following clean argument.  If some `dᵢ = 2`,
say `d = 2` at one position and `x, y` at the other two, then `3n` is odd, so
`gcd (3n - 16) (6n) = 1`.  The sign patterns that are not immediately impossible by a size
bound (`1 + ea/2 + eb/x + ec/y > 1/2 > 8/(3n)` when `ea = 1`, and `1/2 + 1/x + 1/y > 1/2`
when `ea = eb = ec = 1`) rearrange the equation to either

`1/x + 1/y = (3n-16)/(6n)`   or   `±(1/x - 1/y) = (3n-16)/(6n)`,

whence clearing denominators gives `(3n-16)·x·y = 6n·(x ± y)`.  Since `gcd (3n-16) (6n) = 1`
this forces `6n ∣ x·y`, so `x·y ≥ 6n`.  But `x·y ≤ (x² + y²)/2 ≤ (12n - 5)/2 < 6n` because
`x² + y² + 5 ≤ 12n`.  Contradiction.
-/
import Mathlib
import Submission.Work.BSW.Char.no_bad_arithmetic

namespace Work.BSW.Char

/-- `e ^ 2 = 1` in `ℤ` forces `e = 1` or `e = -1`. -/
lemma nbt_int_sq_eq_one {e : ℤ} (h : e ^ 2 = 1) : e = 1 ∨ e = -1 := by
  have h2 : (e - 1) * (e + 1) = 0 := by ring_nf; nlinarith [h]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · left; linarith
  · right; linarith

/-- For odd `n ≥ 9`, the number `3n - 16` is coprime to `6n`. -/
lemma nbt_coprime_6n_3n16 (n : ℕ) (hn : 9 ≤ n) (hodd : n % 2 = 1) :
    Nat.Coprime (3 * n - 16) (6 * n) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  set g := Nat.gcd (3 * n - 16) (6 * n) with hg
  -- Every common divisor divides `6n - 2 * (3n - 16) = 32`.
  have hg32 : g ∣ 32 := by
    have h1 : g ∣ 3 * n - 16 := Nat.gcd_dvd_left _ _
    have h2 : g ∣ 6 * n := Nat.gcd_dvd_right _ _
    obtain ⟨m, hm⟩ := h1
    have h3 : g ∣ 2 * (3 * n - 16) := ⟨2 * m, by rw [hm]; ring⟩
    have h4 : g ∣ 6 * n - 2 * (3 * n - 16) := Nat.dvd_sub h2 h3
    have h5 : 6 * n - 2 * (3 * n - 16) = 32 := by omega
    rwa [h5] at h4
  have hgpow : g ∣ 2 ^ 5 := by
    have : (2 : ℕ) ^ 5 = 32 := by norm_num
    rw [this]; exact hg32
  obtain ⟨k, _, hkg⟩ := (Nat.dvd_prime_pow (p := 2) (m := 5) Nat.prime_two).mp hgpow
  -- ... and every common divisor is odd, since it divides `3n - 16` and `n` is odd.
  have hk0 : k = 0 := by
    by_contra hk
    have hk1 : 1 ≤ k := by omega
    have hdvd : (2 : ℕ) ∣ 2 ^ k := pow_dvd_pow 2 hk1
    have h2g : (2 : ℕ) ∣ g := by rw [hkg]; exact hdvd
    have : (2 : ℕ) ∣ 3 * n - 16 := dvd_trans h2g (Nat.gcd_dvd_left _ _)
    omega
  rw [hkg, hk0]; norm_num

/-- If `6n ∣ x·y`, `x² + y² + 5 ≤ 12n` and `x, y ≥ 1`, we reach a contradiction: `x·y ≥ 6n`
while `2·(x·y) ≤ x² + y² ≤ 12n - 5`. -/
lemma nbt_no_sixn_dvd (n x y : ℕ) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hdvd : (6 * n) ∣ x * y) (hineq : x ^ 2 + y ^ 2 + 5 ≤ 12 * n) : False := by
  have hpos : 0 < x * y := Nat.mul_pos (by omega) (by omega)
  have hge : 6 * n ≤ x * y := Nat.le_of_dvd hpos hdvd
  have hxy : 2 * (x * y) ≤ x ^ 2 + y ^ 2 := by nlinarith [sq_nonneg (x - y : ℤ)]
  omega

/-- If `1/x + 1/y = (3n-16)/(6n)` then `6n ∣ x·y`. -/
lemma nbt_sixn_dvd_of_sum (n x y : ℕ) (hn : 9 ≤ n) (hodd : n % 2 = 1)
    (hx : 0 < x) (hy : 0 < y)
    (h : (1 : ℚ) / (x : ℚ) + (1 : ℚ) / (y : ℚ) = (3 * (n : ℚ) - 16) / (6 * (n : ℚ))) :
    (6 * n) ∣ x * y := by
  have h16 : 16 ≤ 3 * n := by omega
  have keyQ : (((3 * n - 16) * (x * y) : ℕ) : ℚ) = (((6 * n) * (x + y) : ℕ) : ℚ) := by
    push_cast [Nat.cast_sub h16]
    field_simp at h ⊢
    linarith
  have keyN : (3 * n - 16) * (x * y) = (6 * n) * (x + y) := by exact_mod_cast keyQ
  have hdvd : (6 * n) ∣ (3 * n - 16) * (x * y) := ⟨x + y, keyN⟩
  exact Nat.Coprime.dvd_of_dvd_mul_left (nbt_coprime_6n_3n16 n hn hodd).symm hdvd

/-- If `1/x - 1/y = (3n-16)/(6n)` then `6n ∣ x·y`. -/
lemma nbt_sixn_dvd_of_sub (n x y : ℕ) (hn : 9 ≤ n) (hodd : n % 2 = 1)
    (hx : 0 < x) (hy : 0 < y)
    (h : (1 : ℚ) / (x : ℚ) - (1 : ℚ) / (y : ℚ) = (3 * (n : ℚ) - 16) / (6 * (n : ℚ))) :
    (6 * n) ∣ x * y := by
  have h16 : 16 < 3 * n := by omega
  have hnq : (9 : ℚ) ≤ (n : ℚ) := by exact_mod_cast (by omega : 9 ≤ n)
  have hpos : 0 < (3 * (n : ℚ) - 16) / (6 * (n : ℚ)) :=
    div_pos (by linarith) (by positivity)
  have hlt : (1 : ℚ) / (y : ℚ) < 1 / (x : ℚ) := by linarith [h, hpos]
  -- ... hence `1/y < 1/x`, i.e. `x < y`.
  have hxy : x < y := by
    by_contra hle
    push Not at hle
    have hle' : (1 : ℚ) / (x : ℚ) ≤ 1 / (y : ℚ) :=
      one_div_le_one_div_of_le (by positivity : (0 : ℚ) < (y : ℚ)) (by exact_mod_cast hle)
    linarith [hlt, hle']
  have h16' : 16 ≤ 3 * n := by omega
  have keyQ : (((3 * n - 16) * (x * y) : ℕ) : ℚ) = (((6 * n) * (y - x) : ℕ) : ℚ) := by
    push_cast [Nat.cast_sub h16', Nat.cast_sub (le_of_lt hxy)]
    field_simp at h ⊢
    linarith
  have keyN : (3 * n - 16) * (x * y) = (6 * n) * (y - x) := by exact_mod_cast keyQ
  have hdvd : (6 * n) ∣ (3 * n - 16) * (x * y) := ⟨y - x, keyN⟩
  exact Nat.Coprime.dvd_of_dvd_mul_left (nbt_coprime_6n_3n16 n hn hodd).symm hdvd

/-- The `d = 2` case of `no_bad_arithmetic_two`: at the position where the degree is `2`, the
two remaining degrees `x, y ≥ 2` cannot make the equation `1 + ea/2 + eb/x + ec/y = 8/(3n)`
hold together with `x² + y² + 5 ≤ 12n`. -/
lemma nbt_two_case (n x y z : ℕ) (hz : z = 2) (hn : 5 ≤ n) (hmod4 : n % 4 = 1)
    (h3dvd : 3 ∣ n) (hx : 2 ≤ x) (hy : 2 ≤ y) (ea eb ec : ℤ)
    (hea : ea ^ 2 = 1) (heb : eb ^ 2 = 1) (hec : ec ^ 2 = 1)
    (heq : (1 : ℚ) + (ea : ℚ) / (z : ℚ) + (eb : ℚ) / (x : ℚ) + (ec : ℚ) / (y : ℚ)
        = 8 / (3 * (n : ℚ)))
    (hineq : x ^ 2 + y ^ 2 + 5 ≤ 12 * n) : False := by
  have hn9 : 9 ≤ n := by omega
  have hodd : n % 2 = 1 := by omega
  have h12x : (1 : ℚ) / (x : ℚ) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num); exact_mod_cast hx
  have h12y : (1 : ℚ) / (y : ℚ) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num); exact_mod_cast hy
  have hpx : (0 : ℚ) < 1 / (x : ℚ) := by rw [one_div_pos]; exact_mod_cast (by omega : 0 < x)
  have hpy : (0 : ℚ) < 1 / (y : ℚ) := by rw [one_div_pos]; exact_mod_cast (by omega : 0 < y)
  have hnq : (9 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn9
  have hlt : 8 / (3 * (n : ℚ)) < 1 / 2 := by
    rw [div_lt_iff₀ (by positivity : (0 : ℚ) < 3 * (n : ℚ))]
    nlinarith
  rw [hz] at heq
  have h86 : (1 : ℚ) / 2 - 8 / (3 * (n : ℚ)) = (3 * (n : ℚ) - 16) / (6 * (n : ℚ)) := by
    field_simp; ring
  rcases nbt_int_sq_eq_one hea with h1 | h1 <;>
    rcases nbt_int_sq_eq_one heb with h2 | h2 <;>
    rcases nbt_int_sq_eq_one hec with h3 | h3
  · rw [h1, h2, h3] at heq
    push_cast at heq
    try simp only [neg_div] at heq
    linarith [heq, hpx, hpy, hlt]
  · rw [h1, h2, h3] at heq
    push_cast at heq
    try simp only [neg_div] at heq
    linarith [heq, hpx, h12y, hlt]
  · rw [h1, h2, h3] at heq
    push_cast at heq
    try simp only [neg_div] at heq
    linarith [heq, h12x, hpy, hlt]
  · rw [h1, h2, h3] at heq
    push_cast at heq
    try simp only [neg_div] at heq
    linarith [heq, h12x, h12y, hlt]
  · rw [h1, h2, h3] at heq
    push_cast at heq
    try simp only [neg_div] at heq
    linarith [heq, hpx, hpy, hlt]
  · -- `ea = -1`, `eb = 1`, `ec = -1`
    rw [h1, h2, h3] at heq
    push_cast at heq
    try simp only [neg_div] at heq
    have hsub : (1 : ℚ) / (y : ℚ) - (1 : ℚ) / (x : ℚ)
        = (3 * (n : ℚ) - 16) / (6 * (n : ℚ)) := by linarith [heq, h86]
    have hd := nbt_sixn_dvd_of_sub n y x hn9 hodd (by omega) (by omega) hsub
    exact nbt_no_sixn_dvd n x y (by omega) (by omega)
      (by simpa [Nat.mul_comm] using hd) hineq
  · -- `ea = -1`, `eb = -1`, `ec = 1`
    rw [h1, h2, h3] at heq
    push_cast at heq
    try simp only [neg_div] at heq
    have hsub : (1 : ℚ) / (x : ℚ) - (1 : ℚ) / (y : ℚ)
        = (3 * (n : ℚ) - 16) / (6 * (n : ℚ)) := by linarith [heq, h86]
    exact nbt_no_sixn_dvd n x y (by omega) (by omega)
      (nbt_sixn_dvd_of_sub n x y hn9 hodd (by omega) (by omega) hsub) hineq
  · -- `ea = eb = ec = -1`
    rw [h1, h2, h3] at heq
    push_cast at heq
    try simp only [neg_div] at heq
    have hsum : (1 : ℚ) / (x : ℚ) + (1 : ℚ) / (y : ℚ)
        = (3 * (n : ℚ) - 16) / (6 * (n : ℚ)) := by linarith [heq, h86]
    exact nbt_no_sixn_dvd n x y (by omega) (by omega)
      (nbt_sixn_dvd_of_sum n x y hn9 hodd (by omega) (by omega) hsum) hineq

theorem no_bad_arithmetic_two (n : ℕ) (hn : 5 ≤ n) (hmod4 : n % 4 = 1) :
    ¬ (3 ∣ n ∧ ∃ d1 d2 d3 : ℕ, 2 ≤ d1 ∧ 2 ≤ d2 ∧ 2 ≤ d3 ∧ ∃ e1 e2 e3 : ℤ,
        e1 ^ 2 = 1 ∧ e2 ^ 2 = 1 ∧ e3 ^ 2 = 1 ∧
        (1 : ℚ) + e1 / (d1 : ℚ) + e2 / (d2 : ℚ) + e3 / (d3 : ℚ) = 8 / (3 * (n : ℚ)) ∧
        1 + d1 ^ 2 + d2 ^ 2 + d3 ^ 2 ≤ 12 * n) := by
  rintro ⟨h3dvd, d1, d2, d3, hd1, hd2, hd3, e1, e2, e3, he1, he2, he3, heq, hineq⟩
  by_cases h3 : 3 ≤ d1 ∧ 3 ≤ d2 ∧ 3 ≤ d3
  · -- all three degrees are `≥ 3`: the companion lemma applies verbatim
    exact no_bad_arithmetic n hn hmod4
      ⟨h3dvd, d1, d2, d3, h3.1, h3.2.1, h3.2.2, e1, e2, e3, he1, he2, he3, heq, hineq⟩
  · -- some degree is `2` (it is `≥ 2` and not `≥ 3`); split on which one
    have hsome : d1 = 2 ∨ d2 = 2 ∨ d3 = 2 := by
      have key : ∀ d : ℕ, 2 ≤ d → d ≠ 2 → 3 ≤ d := by
        intro d hd hne; omega
      by_cases h1 : d1 = 2
      · exact Or.inl h1
      · by_cases h2 : d2 = 2
        · exact Or.inr (Or.inl h2)
        · by_cases h3' : d3 = 2
          · exact Or.inr (Or.inr h3')
          · exact absurd ⟨key d1 hd1 h1, ⟨key d2 hd2 h2, key d3 hd3 h3'⟩⟩ h3
    rcases hsome with h | h | h
    · refine nbt_two_case n d2 d3 d1 h hn hmod4 h3dvd hd2 hd3 e1 e2 e3
        he1 he2 he3 ?_ ?_
      · exact heq
      · nlinarith [hineq, h]
    · refine nbt_two_case n d1 d3 d2 h hn hmod4 h3dvd hd1 hd3 e2 e1 e3
        he2 he1 he3 ?_ ?_
      · linarith [heq]
      · nlinarith [hineq, h]
    · refine nbt_two_case n d1 d2 d3 h hn hmod4 h3dvd hd1 hd2 e3 e1 e2
        he3 he1 he2 ?_ ?_
      · linarith [heq]
      · nlinarith [hineq, h]

end Work.BSW.Char
