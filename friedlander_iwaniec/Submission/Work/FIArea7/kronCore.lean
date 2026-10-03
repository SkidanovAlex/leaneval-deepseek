import Mathlib
import Submission.Work.FIArea7.KronTwoAux
import Submission.Work.FIArea7.KronTwo

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea7

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `J(a | 2) = 1` for odd `a`: the Legendre symbol at the prime `2` is trivial (`2` is a square
modulo `2`), which is exactly the reason Mathlib's `jacobiSym a b` for `b = 2` is useless and the
Kronecker symbol needs the explicit `kronTwo` factor. -/
lemma jacobiSym_two_right_of_odd {a : ℤ} (ha : Odd a) : jacobiSym a 2 = 1 := by
  rw [← jacobiSym.legendreSym.to_jacobiSym 2 a]
  show quadraticChar (ZMod 2) ((a : ℤ) : ZMod 2) = 1
  refine quadraticChar_eq_one_of_char_two ?_ ?_
  · exact ZMod.ringChar_zmod_n 2
  · intro h0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
    obtain ⟨k, hk⟩ := h0
    obtain ⟨m, hm⟩ := ha
    omega

/-- For odd `u₁, u₂`: `(u₁u₂)/2 = 2·(u₁/2)·(u₂/2) + u₁/2 + u₂/2`. -/
lemma mul_div_two_odd {u1 u2 : ℕ} (hu1 : Odd u1) (hu2 : Odd u2) :
    (u1 * u2) / 2 = 2 * (u1 / 2) * (u2 / 2) + u1 / 2 + u2 / 2 := by
  obtain ⟨p, hp⟩ := hu1
  obtain ⟨q, hq⟩ := hu2
  rw [hp, hq]
  rw [show (2 * p + 1) * (2 * q + 1) = 2 * (2 * p * q + p + q) + 1 by ring]
  rw [show (2 * p + 1) / 2 = p by omega, show (2 * q + 1) / 2 = q by omega]
  omega

/-- The parity computation behind the `2`-adic correction: if `p ≡ q (mod 2)` then
`(2pq + p + q)·m + p + q·p` is even.  (With `p = u₁/2`, `q = u₂/2`, `m = ν₂(|Δ|)/2` this is the
evenness of the total `(-1)`-exponent of the identity `Kron = (s₁|u₁)(s₂|u₂)`.) -/
lemma even_two_adic_exp (p q m : ℕ) (h : p % 2 = q % 2) :
    Even ((2 * p * q + p + q) * m + p + q * p) := by
  rcases Nat.mod_two_eq_zero_or_one p with hp | hp
  · have hq : q % 2 = 0 := h ▸ hp
    have hpe : Even p := Nat.even_iff.mpr hp
    have hqe : Even q := Nat.even_iff.mpr hq
    have h1 : Even (2 * p * q + p + q) := by
      have h2 : Even (2 * p * q) := by simp [show 2 * p * q = 2 * (p * q) by ring]
      exact (h2.add hpe).add hqe
    exact ((h1.mul_right m).add hpe).add (hqe.mul_right p)
  · have hq : q % 2 = 1 := h ▸ hp
    have hpo : Odd p := Nat.odd_iff.mpr hp
    have hqo : Odd q := Nat.odd_iff.mpr hq
    have h1 : Even (2 * p * q + p + q) := by
      have h2 : Even (2 * p * q) := by simp [show 2 * p * q = 2 * (p * q) by ring]
      exact Odd.add_odd (Even.add_odd h2 hpo) hqo
    exact Odd.add_odd (Even.add_odd (h1.mul_right m) hpo) (Odd.mul hqo hpo)

/-- **The arithmetic core of *FI* Lemma 17.1, positive-`Δ` form.** For odd coprime `u₁ u₂` with
`u₁ ≡ u₂ (mod 4)` and `Δ = u₁s₂ − u₂s₁ > 0`,

  `(u₁u₂ | Δ)·χ₂(u₁u₂)^{ν₂(Δ)} = (s₁|u₁)(s₂|u₂)`.

This is the Kronecker-symbol reciprocity computation of *FI* (17.6): writing `Δ = 2^ν n` with `n`
odd, `(u₁u₂ | Δ) = (u₁u₂ | n)` (the Legendre symbol at `2` is trivial), reciprocity gives
`(u₁u₂ | n) = (−1)^{(u₁u₂/2)(n/2)}(n | u₁u₂)`, and `(n | uᵢ)` is recovered from
`(Δ | uᵢ) = (2 | uᵢ)^ν (n | uᵢ)` together with `Δ ≡ −u₂s₁ (mod u₁)`, `Δ ≡ u₁s₂ (mod u₂)` and
`χ₂ = (·|2) = (2|·)`.  The `2`-adic factor `χ₂(u₁)^ν χ₂(u₂)^ν χ₂(u₁u₂)^ν` is `1` because `χ₂` is
multiplicative and `±1`, and the remaining sign
`(−1)^{(u₁u₂/2)(n/2)+(u₁/2)+(u₂/2)(u₁/2)}` is trivial because `u₁ ≡ u₂ (mod 4)` forces
`u₁/2 ≡ u₂/2 (mod 2)` (and hence `u₁u₂ ≡ 1 (mod 4)`). -/
lemma kronCore_pos {u1 u2 : ℕ} {s1 s2 : ℤ}
    (hu1 : Odd u1) (hu2 : Odd u2) (h12 : u1.Coprime u2)
    (h4 : (u1 : ℤ) ≡ (u2 : ℤ) [ZMOD 4])
    (hΔ : 0 < (u1 : ℤ) * s2 - (u2 : ℤ) * s1) :
    jacobiSym (((u1 * u2 : ℕ) : ℤ)) (((u1 : ℤ) * s2 - (u2 : ℤ) * s1).natAbs)
        * Work.FIArea7.kronTwo (((u1 * u2 : ℕ) : ℤ))
            ^ ((((u1 : ℤ) * s2 - (u2 : ℤ) * s1).natAbs).factorization 2)
      = jacobiSym s1 u1 * jacobiSym s2 u2 := by
  set Δ : ℤ := (u1 : ℤ) * s2 - (u2 : ℤ) * s1 with hΔdef
  set D : ℕ := Δ.natAbs with hDdef
  set ν : ℕ := D.factorization 2 with hνdef
  set n : ℕ := D / 2 ^ ν with hndef
  have hΔpos : 0 < Δ := by rw [hΔdef]; exact hΔ
  have hDne : D ≠ 0 := (Int.natAbs_pos.mpr (ne_of_gt hΔpos)).ne'
  have hDΔ : (D : ℤ) = Δ := by
    rw [hDdef]; exact Int.natAbs_of_nonneg (le_of_lt hΔpos)
  have h2dvd : 2 ^ ν ∣ D := by
    rw [hνdef]
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hDne).mpr le_rfl
  have hDsplit : 2 ^ ν * n = D := by
    rw [hndef]; exact Nat.mul_div_cancel' h2dvd
  have hdivne : n ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hDne) h2dvd) (by positivity)).ne'
  have hfacn : n.factorization 2 = 0 := by
    rw [hndef, Nat.factorization_div h2dvd, Finsupp.tsub_apply,
      Nat.factorization_pow_self Nat.prime_two, ← hνdef]
    exact tsub_self ν
  have hnodd : Odd n := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    intro hcon
    have h1 := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hdivne).mp hcon
    rw [hfacn] at h1
    omega
  have hu1z : Odd ((u1 : ℤ)) := by exact_mod_cast hu1
  have hu2z : Odd ((u2 : ℤ)) := by exact_mod_cast hu2
  have haodd : Odd (u1 * u2) := hu1.mul hu2
  have haz : Odd (((u1 * u2 : ℕ) : ℤ)) := by exact_mod_cast haodd
  -- the `2`-part of the denominator does not contribute to `jacobiSym`
  have hJn : jacobiSym (((u1 * u2 : ℕ) : ℤ)) D
      = jacobiSym (((u1 * u2 : ℕ) : ℤ)) n := by
    rw [← hDsplit, jacobiSym.mul_right' _ (pow_ne_zero ν (by norm_num)) hdivne,
      jacobiSym.pow_right, jacobiSym_two_right_of_odd haz, one_pow, one_mul]
  -- quadratic reciprocity for the odd parts
  have hrec : jacobiSym (((u1 * u2 : ℕ) : ℤ)) n
      = (-1) ^ ((u1 * u2) / 2 * (n / 2)) * jacobiSym ((n : ℤ)) (u1 * u2) :=
    jacobiSym.quadratic_reciprocity haodd hnodd
  have hmul : jacobiSym ((n : ℤ)) (u1 * u2)
      = jacobiSym ((n : ℤ)) u1 * jacobiSym ((n : ℤ)) u2 :=
    jacobiSym.mul_right' _ hu1.pos.ne' hu2.pos.ne'
  have hD1 : jacobiSym ((D : ℤ)) u1
      = kronTwo ((u1 : ℤ)) ^ ν * jacobiSym ((n : ℤ)) u1 := by
    rw [← hDsplit]
    push_cast
    rw [jacobiSym.mul_left, jacobiSym.pow_left, jacobiSym.at_two hu1, kronTwo_eq_chi8 (u1 : ℤ)]
    congr 1
  have hflip1 : jacobiSym ((n : ℤ)) u1
      = kronTwo ((u1 : ℤ)) ^ ν * jacobiSym ((D : ℤ)) u1 := by
    have hk : kronTwo ((u1 : ℤ)) ^ ν * kronTwo ((u1 : ℤ)) ^ ν = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, kronTwo_sq_of_odd hu1z, one_pow]
    calc jacobiSym ((n : ℤ)) u1
        = 1 * jacobiSym ((n : ℤ)) u1 := (one_mul _).symm
      _ = (kronTwo ((u1 : ℤ)) ^ ν * kronTwo ((u1 : ℤ)) ^ ν)
            * jacobiSym ((n : ℤ)) u1 := by rw [hk]
      _ = kronTwo ((u1 : ℤ)) ^ ν
            * (kronTwo ((u1 : ℤ)) ^ ν * jacobiSym ((n : ℤ)) u1) := by ring
      _ = kronTwo ((u1 : ℤ)) ^ ν * jacobiSym ((D : ℤ)) u1 := by rw [← hD1]
  have hDexp1 : jacobiSym ((D : ℤ)) u1
      = ZMod.χ₄ (u1 : ZMod 4) * jacobiSym ((u2 : ℤ)) u1 * jacobiSym s1 u1 := by
    have hc : (D : ℤ) ≡ -((u2 : ℤ) * s1) [ZMOD (u1 : ℤ)] := by
      rw [Int.modEq_iff_dvd]
      refine ⟨-s2, ?_⟩
      rw [hDΔ, hΔdef]; ring
    rw [jacobiSym.mod_left' hc.eq]
    rw [show -((u2 : ℤ) * s1) = (-1) * (u2 : ℤ) * s1 by ring]
    rw [jacobiSym.mul_left, jacobiSym.mul_left, jacobiSym.at_neg_one hu1]
  have hD2 : jacobiSym ((D : ℤ)) u2
      = kronTwo ((u2 : ℤ)) ^ ν * jacobiSym ((n : ℤ)) u2 := by
    rw [← hDsplit]
    push_cast
    rw [jacobiSym.mul_left, jacobiSym.pow_left, jacobiSym.at_two hu2, kronTwo_eq_chi8 (u2 : ℤ)]
    congr 1
  have hflip2 : jacobiSym ((n : ℤ)) u2
      = kronTwo ((u2 : ℤ)) ^ ν * jacobiSym ((D : ℤ)) u2 := by
    have hk : kronTwo ((u2 : ℤ)) ^ ν * kronTwo ((u2 : ℤ)) ^ ν = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, kronTwo_sq_of_odd hu2z, one_pow]
    calc jacobiSym ((n : ℤ)) u2
        = 1 * jacobiSym ((n : ℤ)) u2 := (one_mul _).symm
      _ = (kronTwo ((u2 : ℤ)) ^ ν * kronTwo ((u2 : ℤ)) ^ ν)
            * jacobiSym ((n : ℤ)) u2 := by rw [hk]
      _ = kronTwo ((u2 : ℤ)) ^ ν
            * (kronTwo ((u2 : ℤ)) ^ ν * jacobiSym ((n : ℤ)) u2) := by ring
      _ = kronTwo ((u2 : ℤ)) ^ ν * jacobiSym ((D : ℤ)) u2 := by rw [← hD2]
  have hDexp2 : jacobiSym ((D : ℤ)) u2
      = jacobiSym ((u1 : ℤ)) u2 * jacobiSym s2 u2 := by
    have hc : (D : ℤ) ≡ (u1 : ℤ) * s2 [ZMOD (u2 : ℤ)] := by
      rw [Int.modEq_iff_dvd]
      refine ⟨s1, ?_⟩
      rw [hDΔ, hΔdef]; ring
    rw [jacobiSym.mod_left' hc.eq, jacobiSym.mul_left]
  have hrec2 : jacobiSym ((u2 : ℤ)) u1
      = (-1) ^ (u2 / 2 * (u1 / 2)) * jacobiSym ((u1 : ℤ)) u2 :=
    jacobiSym.quadratic_reciprocity hu2 hu1
  have hK2 : jacobiSym ((u1 : ℤ)) u2 * jacobiSym ((u1 : ℤ)) u2 = 1 := by
    have hg : ((u1 : ℤ)).gcd (↑u2) = 1 := by
      rw [Int.gcd_natCast_natCast]; exact h12
    have hh := jacobiSym.sq_one hg
    rwa [sq] at hh
  have hchi : kronTwo ((u1 : ℤ)) ^ ν * kronTwo ((u2 : ℤ)) ^ ν
      * kronTwo (((u1 * u2 : ℕ) : ℤ)) ^ ν = 1 := by
    have hχa : kronTwo (((u1 * u2 : ℕ) : ℤ))
        = kronTwo ((u1 : ℤ)) * kronTwo ((u2 : ℤ)) := by
      rw [show (((u1 * u2 : ℕ) : ℤ)) = (u1 : ℤ) * (u2 : ℤ) by push_cast; ring, kronTwo_mul]
    rw [hχa, ← mul_pow, ← pow_add, ← two_mul, pow_mul, mul_pow,
      kronTwo_sq_of_odd hu1z, kronTwo_sq_of_odd hu2z, one_mul, one_pow]
  have hpq : u1 / 2 % 2 = u2 / 2 % 2 := by
    have h4' : u1 % 4 = u2 % 4 := Int.natCast_modEq_iff.mp h4
    omega
  have hsign : (-1 : ℤ) ^ ((u1 * u2) / 2 * (n / 2)) * ZMod.χ₄ (u1 : ZMod 4)
      * (-1 : ℤ) ^ (u2 / 2 * (u1 / 2)) = 1 := by
    rw [ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp hu1), ← pow_add, ← pow_add]
    refine Even.neg_one_pow ?_
    rw [mul_div_two_odd hu1 hu2]
    exact even_two_adic_exp (u1 / 2) (u2 / 2) (n / 2) hpq
  calc
    jacobiSym (((u1 * u2 : ℕ) : ℤ)) D * kronTwo (((u1 * u2 : ℕ) : ℤ)) ^ ν
        = jacobiSym (((u1 * u2 : ℕ) : ℤ)) n
            * kronTwo (((u1 * u2 : ℕ) : ℤ)) ^ ν := by rw [hJn]
    _ = ((-1) ^ ((u1 * u2) / 2 * (n / 2)) * jacobiSym ((n : ℤ)) (u1 * u2))
          * kronTwo (((u1 * u2 : ℕ) : ℤ)) ^ ν := by rw [hrec]
    _ = ((-1) ^ ((u1 * u2) / 2 * (n / 2))
            * (jacobiSym ((n : ℤ)) u1 * jacobiSym ((n : ℤ)) u2))
          * kronTwo (((u1 * u2 : ℕ) : ℤ)) ^ ν := by rw [hmul]
    _ = ((-1) ^ ((u1 * u2) / 2 * (n / 2))
            * ((kronTwo ((u1 : ℤ)) ^ ν * jacobiSym ((D : ℤ)) u1)
               * (kronTwo ((u2 : ℤ)) ^ ν * jacobiSym ((D : ℤ)) u2)))
          * kronTwo (((u1 * u2 : ℕ) : ℤ)) ^ ν := by rw [hflip1, hflip2]
    _ = ((-1) ^ ((u1 * u2) / 2 * (n / 2))
            * ((kronTwo ((u1 : ℤ)) ^ ν
                * (ZMod.χ₄ (u1 : ZMod 4) * jacobiSym ((u2 : ℤ)) u1 * jacobiSym s1 u1))
               * (kronTwo ((u2 : ℤ)) ^ ν
                * (jacobiSym ((u1 : ℤ)) u2 * jacobiSym s2 u2))))
          * kronTwo (((u1 * u2 : ℕ) : ℤ)) ^ ν := by rw [hDexp1, hDexp2]
    _ = jacobiSym s1 u1 * jacobiSym s2 u2 := by
      rw [hrec2]
      have hmain : (-1) ^ ((u1 * u2) / 2 * (n / 2))
            * ((kronTwo ((u1 : ℤ)) ^ ν
                * (ZMod.χ₄ (u1 : ZMod 4)
                    * ((-1) ^ (u2 / 2 * (u1 / 2)) * jacobiSym ((u1 : ℤ)) u2)
                    * jacobiSym s1 u1))
               * (kronTwo ((u2 : ℤ)) ^ ν
                * (jacobiSym ((u1 : ℤ)) u2 * jacobiSym s2 u2)))
          * kronTwo (((u1 * u2 : ℕ) : ℤ)) ^ ν
          = ((-1) ^ ((u1 * u2) / 2 * (n / 2)) * ZMod.χ₄ (u1 : ZMod 4)
              * (-1) ^ (u2 / 2 * (u1 / 2)))
            * (kronTwo ((u1 : ℤ)) ^ ν * kronTwo ((u2 : ℤ)) ^ ν
                * kronTwo (((u1 * u2 : ℕ) : ℤ)) ^ ν)
            * (jacobiSym ((u1 : ℤ)) u2 * jacobiSym ((u1 : ℤ)) u2)
            * (jacobiSym s1 u1 * jacobiSym s2 u2) := by ring
      rw [hmain, hsign, hchi, hK2]
      ring

/-- **The arithmetic core of *FI* Lemma 17.1 in the Kronecker convention.**
For odd coprime `u₁ u₂ : ℕ` and even `s₁ s₂ : ℤ` with `(uᵢ,sᵢ) = 1` and `u₁ ≡ u₂ (mod 4)`, the
Kronecker symbol `(u₁u₂ | |u₁s₂ − u₂s₁|) = jacobiSym · χ₂^{ν₂}` equals the product of the two
rational Jacobi symbols `(s₁|u₁)(s₂|u₂)`.  Equivalently `jacobiSym (u₁u₂) |Δ'| = χ₂(u₁u₂)^{ν} ·
(s₁|u₁)(s₂|u₂)`.  The hypothesis `u₁ ≡ u₂ (mod 4)` is all that is needed: the `z₁ ≡ z₂ (mod 8)`
hypothesis that the source's (17.5) carries is absorbed here by the `χ₂`-factor.
(`χ₂ = Work.FIArea7.kronTwo = ZMod.χ₈ = (2|·)`.) -/
theorem kronCore {u1 u2 : ℕ} {s1 s2 : ℤ}
    (hu1 : Odd u1) (hu2 : Odd u2) (hs1 : Even s1) (hs2 : Even s2)
    (h12 : u1.Coprime u2) (hcs1 : u1.Coprime s1.natAbs) (hcs2 : u2.Coprime s2.natAbs)
    (h4 : (u1 : ℤ) ≡ (u2 : ℤ) [ZMOD 4])
    (hD : (u1 : ℤ) * s2 - (u2 : ℤ) * s1 ≠ 0) :
    jacobiSym (((u1 * u2 : ℕ) : ℤ)) (((u1 : ℤ) * s2 - (u2 : ℤ) * s1).natAbs)
        * Work.FIArea7.kronTwo (((u1 * u2 : ℕ) : ℤ))
            ^ ((((u1 : ℤ) * s2 - (u2 : ℤ) * s1).natAbs).factorization 2)
      = jacobiSym s1 u1 * jacobiSym s2 u2 := by
  rcases lt_trichotomy ((u1 : ℤ) * s2 - (u2 : ℤ) * s1) 0 with hlt | heq | hgt
  · -- `Δ < 0`: exchange the two pairs, which replaces `Δ` by `-Δ`
    have hpos : 0 < (u2 : ℤ) * s1 - (u1 : ℤ) * s2 := by linarith
    have h := kronCore_pos (u1 := u2) (u2 := u1) (s1 := s2) (s2 := s1)
      hu2 hu1 h12.symm h4.symm hpos
    rw [show ((u2 * u1 : ℕ) : ℤ) = ((u1 * u2 : ℕ) : ℤ) by rw [Nat.mul_comm]] at h
    rw [show ((u2 : ℤ) * s1 - (u1 : ℤ) * s2).natAbs
          = ((u1 : ℤ) * s2 - (u2 : ℤ) * s1).natAbs by
        rw [show (u2 : ℤ) * s1 - (u1 : ℤ) * s2
              = -((u1 : ℤ) * s2 - (u2 : ℤ) * s1) by ring, Int.natAbs_neg]] at h
    rw [mul_comm (jacobiSym s2 u2) (jacobiSym s1 u1)] at h
    exact h
  · exact absurd heq hD
  · exact kronCore_pos hu1 hu2 h12 h4 hgt

end Work.FIArea7
