import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea2

/-- For `m ≠ 0` divisible by `4`, the `d` with `1 ≤ d ≤ m/4 + 1` and `4d ∣ m` are exactly the
divisors of `m/4`. -/
private lemma filter_Icc_four_dvd_eq_divisors {m : ℕ} (hm : m ≠ 0) (h4 : 4 ∣ m) :
    (Finset.Icc 1 (m / 4 + 1)).filter (fun d => 4 * d ∣ m) = (m / 4).divisors := by
  have hpos : 0 < m := Nat.pos_of_ne_zero hm
  have h4m : 4 ≤ m := Nat.le_of_dvd hpos h4
  have hnpos : 0 < m / 4 := Nat.div_pos h4m (by norm_num)
  ext d
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨h1, h2⟩, hd⟩
    exact ⟨(Nat.dvd_div_iff_mul_dvd h4).mpr hd, ne_of_gt hnpos⟩
  · rintro ⟨hdvd, -⟩
    have h1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd hnpos
    have h2 : d ≤ m / 4 := Nat.le_of_dvd hnpos hdvd
    exact ⟨⟨h1, by omega⟩, (Nat.dvd_div_iff_mul_dvd h4).mp hdvd⟩

/-- For `a ≡ 1 (mod 8)`, the Jacobi symbol `(a / 2^β)` is `1` for every `β`. -/
private lemma jacobiSym_two_pow_eq_one {a : ℕ} (ha8 : a % 8 = 1) (β : ℕ) :
    jacobiSym (a : ℤ) (2 ^ β) = 1 := by
  have ha2 : a % 2 = 1 := by omega
  have hne : ((a : ℤ) : ZMod 2) ≠ 0 := by
    intro h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    have h2 : (2 : ℕ) ∣ a := by exact_mod_cast h
    omega
  have hleg : legendreSym 2 (a : ℤ) = 1 := by
    rw [legendreSym, quadraticChar_eq_one_of_char_two (by rw [ZMod.ringChar_zmod_n]) hne]
  rw [jacobiSym.pow_right, ← jacobiSym.legendreSym.to_jacobiSym, hleg, one_pow]

/-- `Σ_{β=0}^{ν-2} φ(2^β)/2^β = ν/2` for `ν ≥ 2`. -/
private lemma sum_totient_two_pow_div {ν : ℕ} (hν : 2 ≤ ν) :
    ∑ β ∈ Finset.range (ν - 1), ((Nat.totient (2 ^ β) : ℝ) / ((2 ^ β : ℕ) : ℝ)) = (ν : ℝ) / 2 := by
  have hν1 : ν - 1 = (ν - 2) + 1 := by omega
  rw [hν1, Finset.sum_range_succ']
  have h0 : (Nat.totient (2 ^ 0) : ℝ) / ((2 ^ 0 : ℕ) : ℝ) = 1 := by norm_num [Nat.totient_one]
  have hterm : ∀ β : ℕ, (Nat.totient (2 ^ (β + 1)) : ℝ) / ((2 ^ (β + 1) : ℕ) : ℝ) = 1 / 2 := by
    intro β
    rw [Nat.totient_prime_pow_succ Nat.prime_two β]
    simp only [Nat.reduceSub, mul_one]
    push_cast
    rw [pow_succ]
    field_simp
  rw [h0, Finset.sum_congr rfl (fun β _ => hterm β), Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  have hcast : ((ν - 2 : ℕ) : ℝ) = (ν : ℝ) - 2 := by
    rw [Nat.cast_sub hν]; norm_num
  rw [hcast]; ring

/-- The divisors of a product of coprime naturals split as a double sum. -/
private lemma sum_divisors_mul_pointwise {m n : ℕ} (h : m.Coprime n) (f : ℕ → ℝ) :
    ∑ d ∈ (m * n).divisors, f d = ∑ a ∈ m.divisors, ∑ b ∈ n.divisors, f (a * b) := by
  rw [h.divisors_mul, Finset.sum_map]
  change ∑ x ∈ (m.divisors ×ˢ n.divisors).attach,
      f ((↑x : ℕ × ℕ).1 * (↑x : ℕ × ℕ).2) = _
  rw [Finset.sum_attach (s := m.divisors ×ˢ n.divisors) (f := fun p => f (p.1 * p.2))]
  rw [Finset.sum_product]

/-- The divisors of `2^k` are the `2^β` with `0 ≤ β ≤ k`. -/
private lemma sum_divisors_two_pow (k : ℕ) (g : ℕ → ℝ) :
    ∑ x ∈ (2 ^ k).divisors, g x = ∑ x ∈ Finset.range (k + 1), g (2 ^ x) := by
  rw [Nat.divisors_prime_pow Nat.prime_two k, Finset.sum_map]
  rfl

/-- Regrouping identity of (*FI* Lemma 8.4, (8.14)–(8.16)): with `m = 2^ν m'`, `m'` odd, `ν ≥ 2`,
and `a ≡ 1 (mod 8)`,
`2 Σ_{4d ∣ m} (φ(d)/d)(a/d) = ν Σ_{d ∣ m'} (φ(d)/d)(a/d)`.
Indeed the divisors `d` of `m` with `4d ∣ m` are the `2^β d'` with `0 ≤ β ≤ ν-2` and
`d' ∣ m'`; `φ` and the Jacobi symbol are multiplicative, `(a/2^β) = 1` for `a ≡ 1 (mod 8)`
(`jacobiSym_two_pow_eq_one`), and `Σ_{β=0}^{ν-2} φ(2^β)/2^β = ν/2`
(`sum_totient_two_pow_div`). -/
lemma two_mul_sum_four_dvd_eq {m a ν m' : ℕ}
    (hm : m = 2 ^ ν * m') (hm'odd : Odd m') (hν : 2 ≤ ν) (ha8 : a % 8 = 1) :
    2 * (∑ d ∈ (Finset.Icc 1 (m / 4 + 1)).filter (fun d => 4 * d ∣ m),
        ((Nat.totient d : ℝ) / (d : ℝ)) * (jacobiSym (a : ℤ) d : ℝ))
      = (ν : ℝ) * ∑ d ∈ m'.divisors,
        ((Nat.totient d : ℝ) / (d : ℝ)) * (jacobiSym (a : ℤ) d : ℝ) := by
  have hm'ne : m' ≠ 0 := by
    rintro h; rw [h] at hm'odd; obtain ⟨t, ht⟩ := hm'odd; omega
  have hmne : m ≠ 0 := by
    rw [hm]; exact mul_ne_zero (pow_ne_zero ν (by norm_num)) hm'ne
  set k := ν - 2 with hkdef
  have hk : 2 ^ ν = 4 * 2 ^ k := by
    have h2 : 2 + k = ν := by omega
    rw [← h2, pow_add]; norm_num
  have hm_eq : m = 4 * (2 ^ k * m') := by rw [hm, hk]; ring
  have h4 : 4 ∣ m := ⟨2 ^ k * m', hm_eq⟩
  have hmd : m / 4 = 2 ^ k * m' := by
    rw [hm_eq]; exact Nat.mul_div_right (2 ^ k * m') (by norm_num)
  rw [filter_Icc_four_dvd_eq_divisors hmne h4, hmd]
  have hcop : (2 ^ k).Coprime m' := (Nat.coprime_two_left.mpr hm'odd).pow_left k
  rw [sum_divisors_mul_pointwise hcop]
  rw [sum_divisors_two_pow]
  -- `hterm`: the summand factorises.
  have hterm : ∀ b d' : ℕ, d' ∈ m'.divisors →
      ((Nat.totient (2 ^ b * d') : ℝ) / ((2 ^ b * d' : ℕ) : ℝ)) *
          (jacobiSym (a : ℤ) (2 ^ b * d') : ℝ)
        = (((Nat.totient (2 ^ b) : ℝ) / ((2 ^ b : ℕ) : ℝ))) *
          (((Nat.totient d' : ℝ) / (d' : ℝ)) * (jacobiSym (a : ℤ) d' : ℝ)) := by
    intro b d' hd'
    obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hd'
    have hd'odd : Odd d' := Odd.of_dvd_nat hm'odd hdvd
    have hd'ne : d' ≠ 0 := ne_of_gt (Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hm'ne))
    haveI : NeZero (2 ^ b) := ⟨pow_ne_zero b (by norm_num)⟩
    haveI : NeZero d' := ⟨hd'ne⟩
    have hcop2 : (2 ^ b).Coprime d' := (Nat.coprime_two_left.mpr hd'odd).pow_left b
    rw [Nat.totient_mul hcop2, jacobiSym.mul_right, jacobiSym_two_pow_eq_one ha8 b, one_mul]
    push_cast
    ring
  have hstep : (∑ b ∈ Finset.range (k + 1), ∑ d' ∈ m'.divisors,
        ((Nat.totient (2 ^ b * d') : ℝ) / ((2 ^ b * d' : ℕ) : ℝ)) *
          (jacobiSym (a : ℤ) (2 ^ b * d') : ℝ))
      = (∑ b ∈ Finset.range (k + 1), ∑ d' ∈ m'.divisors,
        (((Nat.totient (2 ^ b) : ℝ) / ((2 ^ b : ℕ) : ℝ))) *
          (((Nat.totient d' : ℝ) / (d' : ℝ)) * (jacobiSym (a : ℤ) d' : ℝ))) := by
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro d' hd'
    exact hterm b d' hd'
  rw [hstep]
  have hprod : (∑ b ∈ Finset.range (k + 1), ∑ d' ∈ m'.divisors,
        (((Nat.totient (2 ^ b) : ℝ) / ((2 ^ b : ℕ) : ℝ))) *
          (((Nat.totient d' : ℝ) / (d' : ℝ)) * (jacobiSym (a : ℤ) d' : ℝ)))
      = (∑ b ∈ Finset.range (k + 1), ((Nat.totient (2 ^ b) : ℝ) / ((2 ^ b : ℕ) : ℝ))) *
          (∑ d' ∈ m'.divisors,
            ((Nat.totient d' : ℝ) / (d' : ℝ)) * (jacobiSym (a : ℤ) d' : ℝ)) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro b _
    rw [Finset.mul_sum]
  rw [hprod]
  have hg : (∑ b ∈ Finset.range (k + 1), ((Nat.totient (2 ^ b) : ℝ) / ((2 ^ b : ℕ) : ℝ)))
      = (ν : ℝ) / 2 := by
    have hk1 : k + 1 = ν - 1 := by omega
    rw [hk1]
    exact sum_totient_two_pow_div hν
  rw [hg]; ring

end Work.FIArea2
