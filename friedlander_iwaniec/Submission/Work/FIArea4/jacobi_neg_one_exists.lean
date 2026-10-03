/-
# A nontrivial value of the Jacobi-symbol character `u ↦ J(n | u)`

For `n ≥ 1` which is not a perfect square, the Jacobi symbol `J(n | ·)`, restricted to odd `u`
coprime to `n`, is a non-principal Dirichlet character: we produce an odd `u` with `J(n | u) = -1`.

The proof splits off the exact power of two: `n = 2 ^ s * m` with `m` odd.

* If `m` is not a perfect square, an odd `u` with `J(m | u) = -1`, `u ≡ 1 (mod 8)` is produced by
  `odd_jacobiSym_neg_one` (which uses the prime case `prime_jacobiSym_neg_one` and the CRT glue
  `crt_jacobiSym_neg_one`); since `u ≡ 1 (mod 8)` we have `J(2 ^ s | u) = χ₈(u) ^ s = 1`, hence
  `J(n | u) = J(2 ^ s | u) * J(m | u) = -1`.
* If `m = k ^ 2` (so `k` is odd), the non-squareness of `n` forces `s` odd, and `u = 1 + 4 k`
  satisfies `u ≡ 5 (mod 8)`, so `J(2 ^ s | u) = χ₈(u) ^ s = (-1) ^ s = -1`, while
  `J(m | u) = J(k | u) ^ 2 = 1` because `gcd (k, u) = 1`.
-/
import Mathlib
import Submission.Work.FIArea4.exists_prime_factorization_odd
import Submission.Work.FIArea4.prime_jacobiSym_neg_one

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea4

/-- **CRT glue.** If `a` and `b` are odd, coprime and nonzero, `u₀` is odd with `u₀ ≡ 1 (mod 8)`
and `J(a | u₀) = -1`, then there is `u` which is odd, `≡ 1 (mod 8)`, coprime to `a * b`, satisfies
`J(a | u) = -1` and `J(b | u) = 1`, and hence `J(a * b | u) = -1`.

Take `u` with `u ≡ u₀ (mod a)` and `u ≡ 1 (mod 8*b)` (`Nat.chineseRemainder`, moduli coprime since
`a` is odd and coprime to `b`).  Then `u ≡ u₀ (mod 4)`, so `u ≡ u₀ (mod 4*a)` and
`J(a | u) = J(a | u₀) = -1` because `J(a | ·)` depends only on the argument mod `4*a`
(`jacobiSym.mod_right`); while `u ≡ 1 (mod 8*b)` gives `J(b | u) = J(b | 1) = 1`. -/
lemma crt_jacobiSym_neg_one {a b u₀ : ℕ} (hb : b ≠ 0) (haodd : Odd a)
    (hcop : a.Coprime b) (hu₀ : Odd u₀) (hu₀8 : u₀ % 8 = 1)
    (hJ : jacobiSym (a : ℤ) u₀ = -1) :
    ∃ u : ℕ, Odd u ∧ u % 8 = 1 ∧ Nat.Coprime u (a * b) ∧ jacobiSym ((a * b : ℕ) : ℤ) u = -1 := by
  have hu₀ne : u₀ ≠ 0 := by rintro rfl; obtain ⟨k, hk⟩ := hu₀; omega
  -- the moduli `a` and `8 * b` are coprime
  have hcop8 : a.Coprime (8 * b) := by
    have h2 : a.Coprime 8 := by
      have h : a.Coprime (2 ^ 3) := ((Nat.coprime_two_right.mpr haodd)).pow_right 3
      simpa using h
    exact h2.mul_right hcop
  obtain ⟨u, hu₁, hu₂⟩ := Nat.chineseRemainder hcop8 u₀ 1
  have hmod8b : u % (8 * b) = 1 := by
    have h' : u % (8 * b) = 1 % (8 * b) := hu₂
    rwa [Nat.mod_eq_of_lt (by omega : 1 < 8 * b)] at h'
  have hu8 : u % 8 = 1 := by
    calc u % 8 = u % (8 * b) % 8 := (Nat.mod_mod_of_dvd u (dvd_mul_right 8 b)).symm
      _ = 1 % 8 := by rw [hmod8b]
      _ = 1 := by norm_num
  have huodd : Odd u := by rw [Nat.odd_iff]; omega
  have hune : u ≠ 0 := by rintro rfl; simp at hu8
  -- `u ≡ u₀` modulo `4 * a`
  have hmod4a : u % (4 * a) = u₀ % (4 * a) := by
    have h4a : Nat.Coprime 4 a := by
      have h : a.Coprime (2 ^ 2) := (Nat.coprime_two_right.mpr haodd).pow_right 2
      exact h.symm
    have hmod4 : u % 4 = u₀ % 4 := by omega
    exact (Nat.modEq_and_modEq_iff_modEq_mul h4a).mp ⟨hmod4, hu₁⟩
  have hJa : jacobiSym (a : ℤ) u = -1 := by
    have hstep : jacobiSym (a : ℤ) u₀ = jacobiSym (a : ℤ) (u₀ % (4 * a)) := by
      rw [jacobiSym.mod_right (a : ℤ) hu₀, Int.natAbs_natCast]
    calc jacobiSym (a : ℤ) u = jacobiSym (a : ℤ) (u % (4 * a)) := by
          rw [jacobiSym.mod_right (a : ℤ) huodd, Int.natAbs_natCast]
      _ = jacobiSym (a : ℤ) (u₀ % (4 * a)) := by rw [hmod4a]
      _ = jacobiSym (a : ℤ) u₀ := hstep.symm
      _ = -1 := hJ
  have hJb : jacobiSym (b : ℤ) u = 1 := by
    have hmod4b : u % (4 * b) = 1 := by
      have h4bdvd : 4 * b ∣ 8 * b := ⟨2, by ring⟩
      have h' := Nat.mod_mod_of_dvd u h4bdvd
      rw [hmod8b, Nat.mod_eq_of_lt (by omega : 1 < 4 * b)] at h'
      exact h'.symm
    calc jacobiSym (b : ℤ) u = jacobiSym (b : ℤ) (u % (4 * b)) := by
          rw [jacobiSym.mod_right (b : ℤ) huodd, Int.natAbs_natCast]
      _ = jacobiSym (b : ℤ) 1 := by rw [hmod4b]
      _ = 1 := jacobiSym.one_right _
  have hJab : jacobiSym ((a * b : ℕ) : ℤ) u = -1 := by
    rw [Nat.cast_mul, jacobiSym.mul_left, hJa, hJb]
    norm_num
  have hua : Nat.Coprime a u := by
    have hne : (a : ℤ).gcd (u : ℤ) = 1 := by
      by_contra hcon
      have h0 : jacobiSym (a : ℤ) u = 0 := jacobiSym.eq_zero_iff.mpr ⟨hune, hcon⟩
      rw [hJa] at h0; norm_num at h0
    rwa [Int.gcd_natCast_natCast] at hne
  have hub : Nat.Coprime b u := by
    have hne : (b : ℤ).gcd (u : ℤ) = 1 := by
      by_contra hcon
      have h0 : jacobiSym (b : ℤ) u = 0 := jacobiSym.eq_zero_iff.mpr ⟨hune, hcon⟩
      rw [hJb] at h0; norm_num at h0
    rwa [Int.gcd_natCast_natCast] at hne
  exact ⟨u, huodd, hu8, (hua.mul_left hub).symm, hJab⟩

/-- **The odd case.** For odd `m ≥ 1` which is not a perfect square there is an odd `u` with
`u ≡ 1 (mod 8)`, `gcd (u, m) = 1` and `J(m | u) = -1`.

Let `p` be a prime occurring in `m` to an odd power (`exists_prime_factorization_odd`) and write
`m = p ^ e * b` with `b = m / p ^ e` (so `p ∤ b`, `gcd (p ^ e, b) = 1`, and both factors are odd).
Choose `u₀` with `J(p | u₀) = -1` and `u₀ ≡ 1 (mod 8)` (`prime_jacobiSym_neg_one`); then
`J(p ^ e | u₀) = J(p | u₀) ^ e = -1` as `e` is odd, and `crt_jacobiSym_neg_one` combines
`a = p ^ e` with `b`. -/
lemma odd_jacobiSym_neg_one (m : ℕ) (hodd : Odd m) (hnsq : ∀ k : ℕ, m ≠ k ^ 2) :
    ∃ u : ℕ, Odd u ∧ u % 8 = 1 ∧ Nat.Coprime u m ∧ jacobiSym (m : ℤ) u = -1 := by
  have hm0 : m ≠ 0 := by rintro rfl; obtain ⟨k, hk⟩ := hodd; omega
  obtain ⟨p, hp, hpe⟩ := exists_prime_factorization_odd m hm0 hnsq
  have hdecomp : p ^ m.factorization p * (m / p ^ m.factorization p) = m :=
    Nat.ordProj_mul_ordCompl_eq_self m p
  have hbnd : ¬ p ∣ m / p ^ m.factorization p := Nat.not_dvd_ordCompl hp hm0
  have he1 : 1 ≤ m.factorization p := by obtain ⟨t, ht⟩ := hpe; omega
  have hpdvd : p ∣ m := by
    have hpa : p ∣ p ^ m.factorization p := by
      have h := pow_dvd_pow p he1
      simpa using h
    exact hpa.trans ⟨_, hdecomp.symm⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr hpdvd)
  obtain ⟨u₀, hu₀odd, hu₀8, -, hJu₀⟩ := prime_jacobiSym_neg_one p hp hp2
  have haodd : Odd (p ^ m.factorization p) := (hp.odd_of_ne_two hp2).pow
  have hb0 : m / p ^ m.factorization p ≠ 0 := by
    rintro h0
    rw [h0, mul_zero] at hdecomp
    exact hm0 hdecomp.symm
  have hcop : (p ^ m.factorization p).Coprime (m / p ^ m.factorization p) :=
    (Nat.Prime.coprime_pow_of_not_dvd hp hbnd).symm
  have hJa₀ : jacobiSym ((p ^ m.factorization p : ℕ) : ℤ) u₀ = -1 := by
    have hcast : ((p ^ m.factorization p : ℕ) : ℤ) = (p : ℤ) ^ (m.factorization p) := by
      push_cast; ring
    rw [hcast, jacobiSym.pow_left, hJu₀, hpe.neg_one_pow]
  obtain ⟨u, huodd, hu8, hucop, hJab⟩ :=
    crt_jacobiSym_neg_one hb0 haodd hcop hu₀odd hu₀8 hJa₀
  refine ⟨u, huodd, hu8, ?_, ?_⟩
  · rwa [hdecomp] at hucop
  · rwa [hdecomp] at hJab

/-- If `n ≥ 1` is not a perfect square, there is an odd `u` coprime to `n` with `jacobiSym n u = -1`
(`J(n | u) = -1`). Equivalently: the Jacobi-symbol character `u ↦ J(n | u)` (on odd `u`) is not the
principal character. Proof sketch: `J(n|u) = ∏_{p} J(p|u)^{v_p(n)}`; if some odd prime `p` occurs to
an odd power in `n`, take `u ≡ 1 mod 8·(n/p^{v_p n})` and `u ≡` a quadratic non-residue mod `p`
(CRT), then `J(n|u) = -1`; if every odd prime occurs to an even power then `n = 2^s · m^2` with `s`
odd (as `n` is no square), and `u ≡ 5 mod 8`, `u ≡ 1 mod m` gives `J(n|u) = χ₈(u) = -1`. -/
theorem jacobi_neg_one_exists (n : ℕ) (hn : 1 ≤ n)
    (hnsq : ∀ k : ℕ, n ≠ k ^ 2) :
    ∃ u : ℕ, Odd u ∧ Nat.Coprime u n ∧ jacobiSym (n : ℤ) u = -1 := by
  have hn0 : n ≠ 0 := by omega
  -- split off the exact power of two: `n = 2 ^ s * m` with `m` odd
  obtain ⟨s, m, hm2, hneq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 2 (by norm_num)
  have hm0 : m ≠ 0 := by rintro rfl; rw [mul_zero] at hneq; omega
  have hmodd : Odd m := Nat.not_even_iff_odd.mp (by rwa [even_iff_two_dvd])
  by_cases hmsq : ∃ k, m = k ^ 2
  · -- `m = k ^ 2`; then `s` is odd and `u = 1 + 4 * k` works
    obtain ⟨k, hk⟩ := hmsq
    have hkodd : Odd k := by
      by_contra hk'
      obtain ⟨t, ht⟩ := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hk')
      have h2m : 2 ∣ m := by
        rw [hk, ht]
        exact ⟨2 * t ^ 2, by ring⟩
      exact Nat.not_even_iff_odd.mpr hmodd (even_iff_two_dvd.mpr h2m)
    have hsodd : Odd s := by
      by_contra hs'
      obtain ⟨t, ht⟩ := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hs')
      refine hnsq (2 ^ t * k) ?_
      rw [hneq, hk, ht]
      rw [show (2 : ℕ) ^ (2 * t) = (2 ^ t) ^ 2 by rw [← pow_mul, mul_comm]]
      ring
    have huodd : Odd (1 + 4 * k) := by
      rw [Nat.odd_iff]
      obtain ⟨t, ht⟩ := hkodd
      omega
    have hcop2 : Nat.Coprime (1 + 4 * k) 2 := Nat.coprime_two_right.mpr huodd
    have hk1 : (1 + 4 * k).Coprime k := by
      have h : k.gcd (1 + 4 * k) = 1 := by
        rw [show 1 + 4 * k = 1 + k * 4 by ring, Nat.gcd_add_mul_left_right, Nat.gcd_one_right]
      rwa [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm]
    have hucop : Nat.Coprime (1 + 4 * k) n := by
      have h : Nat.Coprime (1 + 4 * k) (2 ^ s * k ^ 2) :=
        (hcop2.pow_right s).mul_right (hk1.pow_right 2)
      rwa [← hk, ← hneq] at h
    have hu85 : (1 + 4 * k) % 8 = 5 := by
      obtain ⟨t, ht⟩ := hkodd
      rw [ht]
      omega
    have hchi : jacobiSym (2 : ℤ) (1 + 4 * k) = -1 := by
      rw [jacobiSym.at_two huodd, ZMod.χ₈_nat_eq_if_mod_eight]
      rw [if_neg (by omega), if_neg (by omega)]
    have hsq : jacobiSym ((k : ℤ)) (1 + 4 * k) ^ 2 = 1 := by
      apply jacobiSym.sq_one
      rw [Int.gcd_natCast_natCast, Nat.coprime_iff_gcd_eq_one.mp hk1.symm]
    have hJn : jacobiSym (n : ℤ) (1 + 4 * k) = -1 := by
      calc jacobiSym (n : ℤ) (1 + 4 * k)
          = jacobiSym ((2 ^ s * k ^ 2 : ℕ) : ℤ) (1 + 4 * k) := by rw [hneq, hk]
        _ = jacobiSym (((2 : ℤ) ^ s * (k : ℤ) ^ 2)) (1 + 4 * k) := by push_cast; ring
        _ = jacobiSym ((2 : ℤ) ^ s) (1 + 4 * k) * jacobiSym ((k : ℤ) ^ 2) (1 + 4 * k) := by
              rw [jacobiSym.mul_left]
        _ = (-1) * 1 := by
              rw [jacobiSym.pow_left, jacobiSym.pow_left, hchi, hsq, hsodd.neg_one_pow]
        _ = -1 := by norm_num
    exact ⟨1 + 4 * k, huodd, hucop, hJn⟩
  · -- `m` is not a square: use the odd case and multiply by the two-part
    have hnsqm : ∀ k : ℕ, m ≠ k ^ 2 := fun k hk => hmsq ⟨k, hk⟩
    obtain ⟨u, huodd, hu8, hucop, hJm⟩ := odd_jacobiSym_neg_one m hmodd hnsqm
    refine ⟨u, huodd, ?_, ?_⟩
    · have hcop2 : Nat.Coprime u 2 := Nat.coprime_two_right.mpr huodd
      have h : Nat.Coprime u (2 ^ s * m) := (hcop2.pow_right s).mul_right hucop
      rwa [← hneq] at h
    · have hchi : jacobiSym (2 : ℤ) u = 1 := by
        rw [jacobiSym.at_two huodd, ZMod.χ₈_nat_eq_if_mod_eight]
        rw [if_neg (by omega), if_pos (by omega)]
      have h2s : jacobiSym ((2 : ℤ) ^ s) u = 1 := by
        rw [jacobiSym.pow_left, hchi, one_pow]
      calc jacobiSym (n : ℤ) u
          = jacobiSym ((2 ^ s * m : ℕ) : ℤ) u := by rw [hneq]
        _ = jacobiSym (((2 : ℤ) ^ s * (m : ℤ))) u := by push_cast; ring
        _ = jacobiSym ((2 : ℤ) ^ s) u * jacobiSym (m : ℤ) u := by rw [jacobiSym.mul_left]
        _ = 1 * (-1) := by rw [h2s, hJm]
        _ = -1 := by norm_num

end Work.FIArea4
