/-
# A unit on which the Jacobi symbol `J(4n | ·)` takes the value `-1`

If the odd part `m = oddPart n` of `n ≥ 1` is not a perfect square, the Jacobi symbol
`a ↦ J(4n | a)` is a non-principal character of the units modulo `16n`, so there is a unit `x`
with `J(4n | x) = -1`.  This is the pointwise form of FI (11.16) used to see that the bottom
symbol character has conductor `> 1` (`Submission/Work/FIArea4/exists_bottom_sym_char.lean`).

The proof is constructive.  Let `m = oddPart n` (odd, not a square) and
`k = sqfreeKernel m`, `s = sqPart m`, so that `m = k · s²` with `k` squarefree and `k ≠ 1`.
Pick a prime `p ∣ k`; since `k` is squarefree, `v_p(k) = 1`, hence `v_p(m) = 1 + 2 v_p(s)` is odd.
Write `m = p ^ e · M1` with `e = v_p(m)` and `M1 = m / p ^ e` the `p`-free part.  Choose a
quadratic non-residue `v` mod `p` and let `x` be the Chinese-remainder solution of

  `x ≡ 1 (mod 8 · M1)`,  `x ≡ v (mod p)`.

Then `x` is odd, `gcd(x, m) = 1`, `J(p | x) = -1` (quadratic reciprocity plus `x ≡ 1 mod 8`),
and `J(M1 | x) = 1` (reciprocity plus `x ≡ 1 mod M1`).  Hence

  `J(m | x) = J(p^e | x) · J(M1 | x) = J(p | x)^e = (-1)^e = -1`

because `e` is odd.  Finally `J(4n | x) = J(2 | x)^{a+2} · J(m | x) = 1 · (-1) = -1` since
`n = 2^a · m` and `J(2 | x) = χ₈(x) = 1` for `x ≡ 1 mod 8`.
-/
import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea4.SqfreeKernel
import Submission.Work.FIArea4.sqfree_kernel
import Submission.Work.FIArea4.Assembly
import Submission.Work.FIArea4.JacobiChar

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea4

open Work.FIPlan

noncomputable section

/-! ### Elementary congruences for the Jacobi symbol -/

/-- If `M` is odd, `x ≡ 1 (mod 8)` and `x ≡ 1 (mod M)`, then `J(M | x) = 1`.
By quadratic reciprocity `J(M | x) = (-1)^{(M/2)(x/2)} J(x | M)`; the sign is `1` because
`x ≡ 1 (mod 8)` makes `x / 2` even, and `J(x | M) = J(1 | M) = 1`. -/
lemma jacobiSym_eq_one_of_modEq_one (M x : ℕ) (hM : Odd M) (hx8 : x % 8 = 1)
    (hxM : x ≡ 1 [MOD M]) : jacobiSym (M : ℤ) x = 1 := by
  have hxodd : Odd x := by rw [Nat.odd_iff]; omega
  have hxhalf : Even (x / 2) := by
    have hx : x = 8 * (x / 8) + 1 := by have := Nat.div_add_mod x 8; omega
    rw [hx, show (8 * (x / 8) + 1) / 2 = 4 * (x / 8) by omega]
    exact ⟨2 * (x / 8), by ring⟩
  rw [jacobiSym.quadratic_reciprocity hM hxodd]
  have hpow : (-1 : ℤ) ^ (M / 2 * (x / 2)) = 1 := by
    apply Even.neg_one_pow
    obtain ⟨t, ht⟩ := hxhalf
    rw [ht]; exact ⟨M / 2 * t, by ring⟩
  rw [hpow, one_mul]
  have hmod : ((x : ℤ) % (M : ℤ)) = ((1 : ℤ) % (M : ℤ)) := by
    have h : ((x % M : ℕ) : ℤ) = ((1 % M : ℕ) : ℤ) := by rw [hxM]
    rwa [Int.natCast_emod, Int.natCast_emod] at h
  rw [jacobiSym.mod_left' hmod, jacobiSym.one_left]

/-- If `p` is odd, `x ≡ 1 (mod 8)`, `x ≡ v (mod p)` and `J(v | p) = -1`, then `J(p | x) = -1`.
Again quadratic reciprocity: the sign is `1` since `x / 2` is even, and `J(x | p) = J(v | p)`. -/
lemma jacobiSym_eq_neg_one_of_prime_modEq (p x v : ℕ) (hpodd : Odd p) (hx8 : x % 8 = 1)
    (hxv : x ≡ v [MOD p]) (hv : jacobiSym (v : ℤ) p = -1) : jacobiSym (p : ℤ) x = -1 := by
  have hxodd : Odd x := by rw [Nat.odd_iff]; omega
  have hxhalf : Even (x / 2) := by
    have hx : x = 8 * (x / 8) + 1 := by have := Nat.div_add_mod x 8; omega
    rw [hx, show (8 * (x / 8) + 1) / 2 = 4 * (x / 8) by omega]
    exact ⟨2 * (x / 8), by ring⟩
  rw [jacobiSym.quadratic_reciprocity hpodd hxodd]
  have hpow : (-1 : ℤ) ^ (p / 2 * (x / 2)) = 1 := by
    apply Even.neg_one_pow
    obtain ⟨t, ht⟩ := hxhalf
    rw [ht]; exact ⟨p / 2 * t, by ring⟩
  rw [hpow, one_mul]
  have hmod : ((x : ℤ) % (p : ℤ)) = ((v : ℤ) % (p : ℤ)) := by
    have h : ((x % p : ℕ) : ℤ) = ((v % p : ℕ) : ℤ) := by rw [hxv]
    rwa [Int.natCast_emod, Int.natCast_emod] at h
  rw [jacobiSym.mod_left' hmod, hv]

/-! ### A prime occurring to an odd power -/

/-- If `m ≥ 1` is not a perfect square, some prime occurs to an odd power in `m`.
Writing `m = k · s ^ 2` with `k = sqfreeKernel m` squarefree and `k ≠ 1`, a prime `p ∣ k` satisfies
`m.factorization p = k.factorization p + 2 * s.factorization p = 1 + 2 * s.factorization p`. -/
lemma exists_prime_odd_factorization (m : ℕ) (hm : 1 ≤ m) (hns : ∀ k, m ≠ k^2) :
    ∃ p : ℕ, Nat.Prime p ∧ p ∣ m ∧ Odd (m.factorization p) := by
  have hm0 : m ≠ 0 := by omega
  obtain ⟨hksq_dvd, hmax, hmul, hk_dvd, hk_sqf⟩ := sqfree_kernel m hm0
  set k := Work.FIArea4.sqfreeKernel m with hk
  set s := Work.FIArea4.sqPart m with hs
  have hs1 : 1 ≤ s := hmax 1 (by simp)
  have hs0 : s ≠ 0 := by omega
  have hk0 : k ≠ 0 := by
    intro h
    rw [h, zero_mul] at hmul
    omega
  have hk_ne_one : k ≠ 1 := by
    intro h1
    exact hns s (by rw [← hmul, h1, one_mul])
  obtain ⟨p, hp, hpk⟩ := Nat.exists_prime_and_dvd hk_ne_one
  have hk_fact : k.factorization p = 1 := by
    have h1 : 1 ≤ k.factorization p := (Nat.Prime.dvd_iff_one_le_factorization hp hk0).mp hpk
    have h2 : k.factorization p ≤ 1 := (Nat.squarefree_iff_factorization_le_one hk0).mp hk_sqf p
    omega
  have hm_fact : m.factorization p = 1 + 2 * s.factorization p := by
    have h : m.factorization = k.factorization + (s^2).factorization := by
      rw [← hmul]
      exact Nat.factorization_mul hk0 (pow_ne_zero 2 hs0)
    have h2 : (s^2).factorization p = 2 * s.factorization p := by
      rw [Nat.factorization_pow]
      simp [Finsupp.smul_apply]
    calc m.factorization p = (k.factorization + (s^2).factorization) p := by rw [h]
      _ = k.factorization p + (s^2).factorization p := rfl
      _ = 1 + 2 * s.factorization p := by rw [hk_fact, h2]
  exact ⟨p, hp, hpk.trans hk_dvd, ⟨s.factorization p, by rw [hm_fact]; ring⟩⟩

/-! ### The main construction -/

/-- For odd `m ≥ 1` that is not a perfect square there is `x ≡ 1 (mod 8)`, coprime to `m`, with
`J(m | x) = -1`. -/
lemma exists_odd_jacobi_neg_one (m : ℕ) (hm : 1 ≤ m) (hmodd : Odd m)
    (hns : ∀ k : ℕ, m ≠ k ^ 2) :
    ∃ x : ℕ, x % 8 = 1 ∧ Nat.Coprime x m ∧ jacobiSym (m : ℤ) x = -1 := by
  have hm0 : m ≠ 0 := by omega
  obtain ⟨p, hp, hpm, hodd_e⟩ := exists_prime_odd_factorization m hm hns
  have hpodd : Odd p := hmodd.of_dvd_nat hpm
  have hp_ne_two : p ≠ 2 := by
    intro h; rw [h] at hpodd
    rw [Nat.odd_iff] at hpodd; omega
  set e := m.factorization p with he
  set M1 := m / p ^ e with hM1
  have hm_eq : p ^ e * M1 = m := Nat.ordProj_mul_ordCompl_eq_self m p
  have hM1_dvd : M1 ∣ m := Nat.ordCompl_dvd m p
  have hM1_odd : Odd M1 := hmodd.of_dvd_nat hM1_dvd
  have hM1_pos : 0 < M1 := Nat.ordCompl_pos p hm0
  have hcop_pM1 : p.Coprime M1 := Nat.coprime_ordCompl hp hm0
  have : Fact p.Prime := ⟨hp⟩
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp_ne_two
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' (F := ZMod p) hF
  set v : ℕ := (a : ZMod p).val with hv
  have hv_cast : ((v : ℕ) : ZMod p) = (a : ZMod p) := by rw [hv]; exact ZMod.natCast_zmod_val _
  have hJp : jacobiSym (v : ℤ) p = -1 := by
    have hleg : legendreSym p (v : ℤ) = -1 := by
      show quadraticChar (ZMod p) ((v : ℤ) : ZMod p) = -1
      rw [Int.cast_natCast, hv_cast]; exact ha
    rwa [jacobiSym.legendreSym.to_jacobiSym p (v : ℤ)] at hleg
  have hv_ne : v ≠ 0 := by
    rw [hv]
    exact (ZMod.val_ne_zero _).mpr a.isUnit.ne_zero
  have hvlt : v < p := by rw [hv]; exact ZMod.val_lt _
  have hpv : ¬ p ∣ v := fun h => hv_ne (Nat.eq_zero_of_dvd_of_lt h hvlt)
  have h8p : Nat.Coprime 8 p := by
    have h2p : Nat.Coprime 2 p := Nat.coprime_two_left.mpr hpodd
    have hh : Nat.Coprime (2^3) p := h2p.pow_left 3
    simpa using hh
  have hcop : Nat.Coprime (8 * M1) p := h8p.mul_left hcop_pM1.symm
  obtain ⟨x, hx1, hx2⟩ := Nat.chineseRemainder hcop 1 v
  have hx8 : x % 8 = 1 := by
    have h : x ≡ 1 [MOD 8] := Nat.ModEq.of_dvd (dvd_mul_right 8 M1) hx1
    rw [Nat.ModEq] at h; simpa using h
  have hxM1 : x ≡ 1 [MOD M1] := Nat.ModEq.of_dvd (dvd_mul_left M1 8) hx1
  have hcopx8M1 : Nat.Coprime x (8 * M1) := by
    have hxmod : (x : ZMod (8*M1)) = 1 := by
      rw [show (1 : ZMod (8*M1)) = ((1:ℕ) : ZMod (8*M1)) from by simp]
      exact (ZMod.natCast_eq_natCast_iff x 1 (8*M1)).mpr hx1
    exact (ZMod.isUnit_iff_coprime x (8*M1)).mp (by rw [hxmod]; exact isUnit_one)
  have hcopxM1 : Nat.Coprime x M1 := hcopx8M1.coprime_dvd_right (dvd_mul_left M1 8)
  have hcopxp : Nat.Coprime x p := by
    have hpx : ¬ p ∣ x := by
      intro h
      apply hpv
      have hmod : v % p = 0 := by
        have h2 : v ≡ 0 [MOD p] :=
          hx2.symm.trans (by rw [Nat.ModEq]; exact Nat.mod_eq_zero_of_dvd h)
        rw [Nat.ModEq] at h2; simpa using h2
      exact Nat.dvd_of_mod_eq_zero hmod
    exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpx).symm
  have hcopxm : Nat.Coprime x m := by
    have h : Nat.Coprime x (p^e * M1) := (hcopxp.pow_right e).mul_right hcopxM1
    rwa [hm_eq] at h
  have hJp_den : jacobiSym (p : ℤ) x = -1 := jacobiSym_eq_neg_one_of_prime_modEq p x v hpodd hx8 hx2 hJp
  have hJM1 : jacobiSym (M1 : ℤ) x = 1 := jacobiSym_eq_one_of_modEq_one M1 x hM1_odd hx8 hxM1
  have hm_cast : (m : ℤ) = (p : ℤ)^e * (M1 : ℤ) := by
    rw [← hm_eq]; push_cast; ring
  refine ⟨x, hx8, hcopxm, ?_⟩
  calc jacobiSym (m:ℤ) x = jacobiSym ((p:ℤ)^e * (M1:ℤ)) x := by rw [hm_cast]
    _ = jacobiSym ((p:ℤ)^e) x * jacobiSym (M1:ℤ) x := by rw [jacobiSym.mul_left]
    _ = jacobiSym (p:ℤ) x ^ e * jacobiSym (M1:ℤ) x := by rw [jacobiSym.pow_left]
    _ = -1 := by rw [hJp_den, hJM1, hodd_e.neg_one_pow, mul_one]

/-! ### The target statement -/

theorem exists_unit_jacobi_neg_one (n : ℕ) (hn : 1 ≤ n)
    (hns : ∀ k : ℕ, Work.FIPlan.oddPart n ≠ k ^ 2) :
    ∃ x : ℕ, x.gcd (16 * n) = 1 ∧ jacobiSym (4 * n : ℤ) x = -1 := by
  have hn0 : n ≠ 0 := by omega
  set m := Work.FIPlan.oddPart n with hmdef
  have hmm : 1 ≤ m := by rw [hmdef]; exact oddPart_pos hn0
  have hmodd : Odd m := by rw [hmdef]; exact oddPart_odd hn0
  have hnsm : ∀ k, m ≠ k^2 := fun k => by rw [hmdef]; exact hns k
  obtain ⟨x, hx8, hxcop, hxJ⟩ := exists_odd_jacobi_neg_one m hmm hmodd hnsm
  set a := n.factorization 2 with ha
  have hna : 2 ^ a * m = n := by
    rw [ha, hmdef]; exact oddPart_mul_two_pow n
  have hxodd : Odd x := by rw [Nat.odd_iff]; omega
  have h16n : 16 * n = 2 ^ (a + 4) * m := by
    rw [← hna]
    rw [show (16:ℕ) = 2^4 from by norm_num, pow_add]
    ring
  have hcop2 : Nat.Coprime x (2 ^ (a + 4)) :=
    (Nat.coprime_two_right.mpr hxodd).pow_right _
  have hcop16n : Nat.Coprime x (16 * n) := by
    rw [h16n]
    exact hcop2.mul_right hxcop
  have hJ2 : jacobiSym (2 : ℤ) x = 1 := by
    rw [jacobiSym.at_two hxodd, ZMod.χ₈_nat_eq_if_mod_eight]
    have h2 : x % 2 ≠ 0 := by omega
    rw [if_neg h2, if_pos (by omega)]
  have h4nZ : (4 * n : ℤ) = (2:ℤ)^(a + 2) * (m:ℤ) := by
    rw [← hna]
    push_cast
    rw [show (4:ℤ) = 2^2 from by norm_num, pow_add]
    ring
  have hJ4n : jacobiSym (4 * n : ℤ) x = -1 := by
    calc jacobiSym (4 * n : ℤ) x
        = jacobiSym ((2:ℤ)^(a + 2) * (m:ℤ)) x := by rw [h4nZ]
      _ = jacobiSym ((2:ℤ)^(a + 2)) x * jacobiSym (m:ℤ) x := by rw [jacobiSym.mul_left]
      _ = jacobiSym (2:ℤ) x ^ (a + 2) * jacobiSym (m:ℤ) x := by rw [jacobiSym.pow_left]
      _ = -1 := by rw [hJ2, hxJ, one_pow, one_mul]
  exact ⟨x, hcop16n, hJ4n⟩

end

end Work.FIArea4
