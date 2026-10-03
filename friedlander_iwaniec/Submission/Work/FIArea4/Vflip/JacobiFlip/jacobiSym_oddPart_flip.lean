import Mathlib
import Submission.Work.FIArea4.A4varbounds
import Submission.Work.FIArea4.Assembly
import Submission.Work.FIPlan.Interface

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The reciprocity "flip" of the Jacobi symbol `(r | d')` (FI §12)

For two coprime odd moduli `r₁, r₂` congruent modulo `8`, and pairs `(rᵢ, sᵢ) = 1`, the product
`(r₁ | d')(r₂ | d')` of Jacobi symbols attached to the odd part `d' = oddPart d` of a modulus `d`
is completely determined by the complementary divisor `k / d` of `k = |r₁ s₂ − r₂ s₁|`:

`(r₁ | d')(r₂ | d') = (s₁ | r₁)(s₂ | r₂) (r₁ | (k/d)')(r₂ | (k/d)')`.

This is the identity underlying the paper's change of variables `d ↦ q = k/(dm)` in §12.
-/

namespace Work.FIArea4.Vflip.JacobiFlip

open Work.FIArea4

/-! ### Elementary facts about the quadratic characters `χ₄`, `χ₈` -/

/-- `χ₄ n` has square one for odd `n`. -/
lemma chi4_mul_self {n : ℕ} (hn : Odd n) : ZMod.χ₄ n * ZMod.χ₄ n = 1 := by
  rw [ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp hn), ← pow_two, ← pow_mul, mul_comm, pow_mul,
    neg_one_sq, one_pow]

/-- `χ₈ n` has square one for odd `n`. -/
lemma chi8_mul_self {n : ℕ} (hn : Odd n) : ZMod.χ₈ n * ZMod.χ₈ n = 1 := by
  rw [ZMod.χ₈_nat_eq_if_mod_eight]
  have h2 : ¬ (n % 2 = 0) := by rw [Nat.odd_iff.mp hn]; norm_num
  rw [if_neg h2]
  split <;> norm_num

/-- `χ₄ (r₁) = χ₄ (r₂)` when `r₁ ≡ r₂ (mod 8)`. -/
lemma chi4_nat_eq_of_mod_eight {r1 r2 : ℕ} (h8 : r1 % 8 = r2 % 8) :
    ZMod.χ₄ r1 = ZMod.χ₄ r2 := by
  have h84 : r1 % 4 = r2 % 4 := by omega
  rw [ZMod.χ₄_nat_mod_four r1, ZMod.χ₄_nat_mod_four r2, h84]

/-- `χ₈ (r₁) = χ₈ (r₂)` when `r₁ ≡ r₂ (mod 8)`. -/
lemma chi8_nat_eq_of_mod_eight {r1 r2 : ℕ} (h8 : r1 % 8 = r2 % 8) :
    ZMod.χ₈ r1 = ZMod.χ₈ r2 := by
  rw [ZMod.χ₈_nat_mod_eight r1, ZMod.χ₈_nat_mod_eight r2, h8]

/-! ### Reciprocity signs -/

/-- For coprime odd `r₁ ≡ r₂ (mod 8)` and odd `K`, the product of the two reciprocity signs in
`(rᵢ | K) = qrSign(K, rᵢ)(K | rᵢ)` equals one. -/
lemma qrSign_prod_eq_one {r1 r2 K : ℕ} (h1 : Odd r1) (h2 : Odd r2) (hK : Odd K)
    (h8 : r1 % 8 = r2 % 8) : qrSign K r1 * qrSign K r2 = 1 := by
  have hchi4 := chi4_nat_eq_of_mod_eight h8
  rw [qrSign.symm hK h1, qrSign.symm hK h2]
  show jacobiSym (ZMod.χ₄ r1) K * jacobiSym (ZMod.χ₄ r2) K = 1
  rw [← jacobiSym.mul_left, ← hchi4, chi4_mul_self h1, jacobiSym.one_left]

/-- For odd `r₁ ≡ r₂ (mod 8)`, the reciprocity sign `qrSign r₁ r₂` equals `χ₄ r₁`. -/
lemma qrSign_eq_chi4 {r1 r2 : ℕ} (h1 : Odd r1) (h2 : Odd r2) (h8 : r1 % 8 = r2 % 8) :
    qrSign r1 r2 = ZMod.χ₄ r1 := by
  have hchi4 := chi4_nat_eq_of_mod_eight h8
  have hc : ZMod.χ₄ r1 = 1 ∨ ZMod.χ₄ r1 = -1 := by
    rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp h1) with h | h
    · left; exact ZMod.χ₄_nat_one_mod_four h
    · right; exact ZMod.χ₄_nat_three_mod_four h
  rcases hc with h | h
  · rw [qrSign, h, jacobiSym.one_left]
  · rw [qrSign, h, jacobiSym.at_neg_one h2, ← hchi4, h]

/-- For coprime odd `r₁, r₂`: `(r₂ | r₁)(r₁ | r₂) = qrSign r₁ r₂`. -/
lemma jacobiSym_mul_recip_eq_qrSign {r1 r2 : ℕ} (h1 : Odd r1) (h2 : Odd r2)
    (hcop : Nat.Coprime r1 r2) :
    jacobiSym (r2 : ℤ) r1 * jacobiSym (r1 : ℤ) r2 = qrSign r1 r2 := by
  have h := jacobiSym.quadratic_reciprocity' h1 h2
  rw [← qrSign.symm h1 h2] at h
  have hsq : jacobiSym (r2 : ℤ) r1 ^ 2 = 1 := by
    refine jacobiSym.sq_one ?_
    rw [Int.gcd_natCast_natCast]
    exact hcop.symm.gcd_eq_one
  calc jacobiSym (r2 : ℤ) r1 * jacobiSym (r1 : ℤ) r2
      = jacobiSym (r2 : ℤ) r1 * (qrSign r1 r2 * jacobiSym (r2 : ℤ) r1) := by rw [h]
    _ = qrSign r1 r2 * jacobiSym (r2 : ℤ) r1 ^ 2 := by ring
    _ = qrSign r1 r2 := by rw [hsq]; ring

/-! ### `r` is coprime to `|r₁ s₂ − r₂ s₁|` -/

/-- Passage from `Int.gcd` to a `Nat.Coprime` statement about `natAbs`. -/
lemma coprime_natAbs_of_gcd {x : ℕ} {a : ℤ} (h : (x : ℤ).gcd a = 1) : Nat.Coprime x a.natAbs := by
  rw [Nat.coprime_iff_gcd_eq_one]
  have hconv : x.gcd a.natAbs = (x : ℤ).gcd a := by
    rw [← Int.gcd_natCast_natCast, Int.gcd_eq_natAbs, Int.gcd_eq_natAbs]
    simp [Int.natAbs_abs]
  rw [hconv]
  exact h

/-- `(r₁, r₁ s₂ − r₂ s₁) = 1` when `r₁` is coprime to `r₂` and to `s₁`. -/
lemma gcd_r1_cross {r1 r2 s1 s2 : ℕ} (hcop : Nat.Coprime r1 r2) (hs1 : Nat.Coprime s1 r1) :
    (r1 : ℤ).gcd ((r1 : ℤ) * (s2 : ℤ) - (r2 : ℤ) * (s1 : ℤ)) = 1 := by
  have hc : Nat.Coprime r1 (r2 * s1) := hcop.mul_right hs1.symm
  have hava : (r1 : ℤ) * (s2 : ℤ) - (r2 : ℤ) * (s1 : ℤ)
      = -((r2 : ℤ) * (s1 : ℤ)) + (r1 : ℤ) * (s2 : ℤ) := by ring
  rw [hava, Int.gcd_add_mul_left_right]
  rw [show -((r2 : ℤ) * (s1 : ℤ)) = -((r2 * s1 : ℕ) : ℤ) by push_cast; ring]
  rw [show (r1 : ℤ).gcd (-(((r2 * s1 : ℕ)) : ℤ)) = (r1 : ℤ).gcd (((r2 * s1 : ℕ)) : ℤ) by
        rw [Int.gcd_eq_natAbs, Int.gcd_eq_natAbs]; simp]
  rw [Int.gcd_natCast_natCast]
  exact hc.gcd_eq_one

/-- `(r₂, r₁ s₂ − r₂ s₁) = 1` when `r₂` is coprime to `r₁` and to `s₂`. -/
lemma gcd_r2_cross {r1 r2 s1 s2 : ℕ} (hcop : Nat.Coprime r1 r2) (hs2 : Nat.Coprime s2 r2) :
    (r2 : ℤ).gcd ((r1 : ℤ) * (s2 : ℤ) - (r2 : ℤ) * (s1 : ℤ)) = 1 := by
  have hc : Nat.Coprime r2 (r1 * s2) := hcop.symm.mul_right hs2.symm
  have hava : (r1 : ℤ) * (s2 : ℤ) - (r2 : ℤ) * (s1 : ℤ)
      = ((r1 : ℤ) * (s2 : ℤ)) + (r2 : ℤ) * (-(s1 : ℤ)) := by ring
  rw [hava, Int.gcd_add_mul_left_right]
  rw [show ((r1 : ℤ) * (s2 : ℤ)) = ((r1 * s2 : ℕ) : ℤ) by push_cast; ring]
  rw [Int.gcd_natCast_natCast]
  exact hc.gcd_eq_one

/-! ### The core reciprocity identity -/

/-- **Core identity.**  For coprime odd `r₁ ≡ r₂ (mod 8)` and `(rᵢ, sᵢ) = 1`, and
`K = oddPart |r₁ s₂ − r₂ s₁|`:
`(r₁ | K)(r₂ | K) = (s₁ | r₁)(s₂ | r₂)`. -/
lemma flip_core {r1 r2 s1 s2 k : ℕ} (h1 : Odd r1) (h2 : Odd r2) (hcop : Nat.Coprime r1 r2)
    (h8 : r1 % 8 = r2 % 8) (hkpos : 0 < k)
    (hka : k = ((r1 : ℤ) * (s2 : ℤ) - (r2 : ℤ) * (s1 : ℤ)).natAbs) :
    jacobiSym (r1 : ℤ) (Work.FIPlan.oddPart k) * jacobiSym (r2 : ℤ) (Work.FIPlan.oddPart k)
      = jacobiSym (s1 : ℤ) r1 * jacobiSym (s2 : ℤ) r2 := by
  set K : ℕ := Work.FIPlan.oddPart k with hK
  have hKodd : Odd K := by rw [hK]; exact Work.FIArea4.oddPart_odd hkpos.ne'
  have hchi4 := chi4_nat_eq_of_mod_eight h8
  -- Step A: `(rᵢ | K) = qrSign K rᵢ * (K | rᵢ)`, and the signs multiply to one.
  have hA : jacobiSym (r1 : ℤ) K * jacobiSym (r2 : ℤ) K
      = jacobiSym (K : ℤ) r1 * jacobiSym (K : ℤ) r2 := by
    rw [jacobiSym.quadratic_reciprocity' h1 hKodd, jacobiSym.quadratic_reciprocity' h2 hKodd]
    rw [show qrSign K r1 * jacobiSym (↑K) r1 * (qrSign K r2 * jacobiSym (↑K) r2)
        = (qrSign K r1 * qrSign K r2) * (jacobiSym (↑K) r1 * jacobiSym (↑K) r2) from by ring,
        qrSign_prod_eq_one h1 h2 hKodd h8, one_mul]
  -- Step B: only the odd part of `k = 2 ^ v * K` matters; the `χ₈`-factors cancel.
  have hB : jacobiSym (K : ℤ) r1 * jacobiSym (K : ℤ) r2
      = jacobiSym (k : ℤ) r1 * jacobiSym (k : ℤ) r2 := by
    have h1' : 2 ^ (k.factorization 2) * K = k := by
      rw [hK]; exact Work.FIArea4.oddPart_mul_two_pow k
    have hkv : (k : ℤ) = (2 : ℤ) ^ (k.factorization 2) * (K : ℤ) := by
      have hh : (k : ℤ) = ((2 ^ (k.factorization 2) * K : ℕ) : ℤ) := by rw [h1']
      rw [hh]; push_cast; ring
    have e1 : jacobiSym (k : ℤ) r1
        = (ZMod.χ₈ r1) ^ (k.factorization 2) * jacobiSym (K : ℤ) r1 := by
      rw [hkv, jacobiSym.mul_left, jacobiSym.pow_left, jacobiSym.at_two h1]
    have e2 : jacobiSym (k : ℤ) r2
        = (ZMod.χ₈ r2) ^ (k.factorization 2) * jacobiSym (K : ℤ) r2 := by
      rw [hkv, jacobiSym.mul_left, jacobiSym.pow_left, jacobiSym.at_two h2]
    have hc8 : (ZMod.χ₈ r1) ^ (k.factorization 2) * (ZMod.χ₈ r2) ^ (k.factorization 2) = 1 := by
      rw [← chi8_nat_eq_of_mod_eight h8, ← pow_add,
        show k.factorization 2 + k.factorization 2 = 2 * k.factorization 2 from by ring,
        pow_mul, pow_two, chi8_mul_self h1, one_pow]
    rw [e1, e2]
    rw [show (ZMod.χ₈ r1) ^ (k.factorization 2) * jacobiSym (↑K) r1 *
          ((ZMod.χ₈ r2) ^ (k.factorization 2) * jacobiSym (↑K) r2)
        = ((ZMod.χ₈ r1) ^ (k.factorization 2) * (ZMod.χ₈ r2) ^ (k.factorization 2))
          * (jacobiSym (↑K) r1 * jacobiSym (↑K) r2) from by ring_nf, hc8, one_mul]
  -- Step C: replacing `k` by the signed integer `r₁ s₂ − r₂ s₁` costs at most `χ₄`-factors.
  have hC : jacobiSym (k : ℤ) r1 * jacobiSym (k : ℤ) r2
      = jacobiSym ((r1 : ℤ) * (s2 : ℤ) - (r2 : ℤ) * (s1 : ℤ)) r1
        * jacobiSym ((r1 : ℤ) * (s2 : ℤ) - (r2 : ℤ) * (s1 : ℤ)) r2 := by
    set a : ℤ := (r1 : ℤ) * (s2 : ℤ) - (r2 : ℤ) * (s1 : ℤ) with ha
    have hak : a.natAbs = k := by rw [ha]; exact hka.symm
    rw [← hak]
    rcases Int.natAbs_eq a with h | h
    · have h1' : (↑a.natAbs : ℤ) = a := h.symm
      rw [h1']
    · have h2' : (↑a.natAbs : ℤ) = -a := by conv_rhs => rw [h]; ring
      rw [h2', show -a = (-1) * a by ring, jacobiSym.mul_left, jacobiSym.mul_left,
        jacobiSym.at_neg_one h1, jacobiSym.at_neg_one h2]
      rw [show ZMod.χ₄ r1 * jacobiSym a r1 * (ZMod.χ₄ r2 * jacobiSym a r2)
          = (ZMod.χ₄ r1 * ZMod.χ₄ r2) * (jacobiSym a r1 * jacobiSym a r2) from by ring,
          ← hchi4, chi4_mul_self h1, one_mul]
  -- Step D: the reciprocity law applied to `(r₁ s₂ − r₂ s₁ | rᵢ)`.
  have hD : jacobiSym ((r1 : ℤ) * (s2 : ℤ) - (r2 : ℤ) * (s1 : ℤ)) r1 *
        jacobiSym ((r1 : ℤ) * (s2 : ℤ) - (r2 : ℤ) * (s1 : ℤ)) r2
      = jacobiSym (s1 : ℤ) r1 * jacobiSym (s2 : ℤ) r2 := by
    have ha1 : jacobiSym ((r1 : ℤ) * (s2 : ℤ) - (r2 : ℤ) * (s1 : ℤ)) r1
        = ZMod.χ₄ r1 * jacobiSym (r2 : ℤ) r1 * jacobiSym (s1 : ℤ) r1 := by
      have hmod : ((r1 : ℤ) * (s2 : ℤ) - (r2 : ℤ) * (s1 : ℤ)) % (r1 : ℤ)
          = (-((r2 : ℤ) * (s1 : ℤ))) % (r1 : ℤ) := by
        have he : (r1 : ℤ) * (s2 : ℤ) - (r2 : ℤ) * (s1 : ℤ)
            = (-((r2 : ℤ) * (s1 : ℤ))) + r1 * s2 := by ring
        rw [he, Int.add_mul_emod_self_left]
      rw [jacobiSym.mod_left, hmod, ← jacobiSym.mod_left]
      rw [show (-((r2 : ℤ) * (s1 : ℤ))) = (-1) * ((r2 : ℤ) * (s1 : ℤ)) by ring,
        jacobiSym.mul_left, jacobiSym.mul_left, jacobiSym.at_neg_one h1]
      ring
    have ha2 : jacobiSym ((r1 : ℤ) * (s2 : ℤ) - (r2 : ℤ) * (s1 : ℤ)) r2
        = jacobiSym (r1 : ℤ) r2 * jacobiSym (s2 : ℤ) r2 := by
      have hmod : ((r1 : ℤ) * (s2 : ℤ) - (r2 : ℤ) * (s1 : ℤ)) % (r2 : ℤ)
          = ((r1 : ℤ) * (s2 : ℤ)) % (r2 : ℤ) := by
        have he : (r1 : ℤ) * (s2 : ℤ) - (r2 : ℤ) * (s1 : ℤ)
            = ((r1 : ℤ) * (s2 : ℤ)) + r2 * (-(s1 : ℤ)) := by ring
        rw [he, Int.add_mul_emod_self_left]
      rw [jacobiSym.mod_left, hmod, ← jacobiSym.mod_left, jacobiSym.mul_left]
    rw [ha1, ha2]
    rw [show ZMod.χ₄ r1 * jacobiSym (↑r2) r1 * jacobiSym (↑s1) r1 *
          (jacobiSym (↑r1) r2 * jacobiSym (↑s2) r2)
        = (ZMod.χ₄ r1 * (jacobiSym (↑r2) r1 * jacobiSym (↑r1) r2))
          * (jacobiSym (↑s1) r1 * jacobiSym (↑s2) r2) from by ring,
        jacobiSym_mul_recip_eq_qrSign h1 h2 hcop, qrSign_eq_chi4 h1 h2 h8,
        chi4_mul_self h1, one_mul]
  rw [hA, hB, hC, hD]

/-- **The reciprocity flip of the Jacobi symbol `(r | d')` (FI §12).** -/
theorem jacobiSym_oddPart_flip {r1 r2 s1 s2 d : ℕ} (h1 : Odd r1) (h2 : Odd r2)
    (hcop : Nat.Coprime r1 r2) (h8 : r1 % 8 = r2 % 8)
    (hs1 : Nat.Coprime s1 r1) (hs2 : Nat.Coprime s2 r2)
    (hd : 0 < d) (hdvd : d ∣ ((r1 : ℤ) * (s2 : ℤ) - (r2 : ℤ) * (s1 : ℤ)).natAbs) :
    jacobiSym (r1 : ℤ) (Work.FIPlan.oddPart d) * jacobiSym (r2 : ℤ) (Work.FIPlan.oddPart d)
      = jacobiSym (s1 : ℤ) r1 * jacobiSym (s2 : ℤ) r2
        * (jacobiSym (r1 : ℤ) (Work.FIPlan.oddPart (((r1 : ℤ) * (s2 : ℤ) - (r2 : ℤ) * (s1 : ℤ)).natAbs / d))
           * jacobiSym (r2 : ℤ) (Work.FIPlan.oddPart (((r1 : ℤ) * (s2 : ℤ) - (r2 : ℤ) * (s1 : ℤ)).natAbs / d))) := by
  set a : ℤ := (r1 : ℤ) * (s2 : ℤ) - (r2 : ℤ) * (s1 : ℤ) with ha
  set k : ℕ := a.natAbs with hk
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- degenerate case `|r₁ s₂ − r₂ s₁| = 0`: then `r₁ = r₂ = 1`
    have ha0 : a = 0 := by
      have h : a.natAbs = 0 := by rw [← hk]; exact hk0
      exact Int.natAbs_eq_zero.mp h
    have hnat : r1 * s2 = r2 * s1 := by
      have h : (r1 : ℤ) * (s2 : ℤ) - (r2 : ℤ) * (s1 : ℤ) = 0 := by rw [← ha]; exact ha0
      have h' : (r1 : ℤ) * (s2 : ℤ) = (r2 : ℤ) * (s1 : ℤ) := by linarith
      exact_mod_cast h'
    have hr1 : r1 = 1 := by
      have hdvd1 : r1 ∣ s1 * r2 := ⟨s2, by rw [mul_comm s1 r2]; exact hnat.symm⟩
      have hs1dvd : r1 ∣ s1 := hcop.dvd_of_dvd_mul_right hdvd1
      have : r1 ∣ s1.gcd r1 := Nat.dvd_gcd hs1dvd (dvd_refl r1)
      rw [hs1.gcd_eq_one] at this
      exact Nat.dvd_one.mp this
    have hr2 : r2 = 1 := by
      have hdvd2 : r2 ∣ s2 * r1 := ⟨s1, by rw [mul_comm s2 r1]; exact hnat⟩
      have hs2dvd : r2 ∣ s2 := hcop.symm.dvd_of_dvd_mul_right hdvd2
      have : r2 ∣ s2.gcd r2 := Nat.dvd_gcd hs2dvd (dvd_refl r2)
      rw [hs2.gcd_eq_one] at this
      exact Nat.dvd_one.mp this
    rw [hr1, hr2]
    simp [jacobiSym.one_left, jacobiSym.one_right]
  · -- main case `|r₁ s₂ − r₂ s₁| > 0`
    have hdvd' : d ∣ k := hdvd
    have hcore : jacobiSym (r1 : ℤ) (Work.FIPlan.oddPart k) * jacobiSym (r2 : ℤ) (Work.FIPlan.oddPart k)
        = jacobiSym (s1 : ℤ) r1 * jacobiSym (s2 : ℤ) r2 :=
      flip_core h1 h2 hcop h8 hkpos (by rw [hk, ha])
    have hd1ne : Work.FIPlan.oddPart d ≠ 0 :=
      (Work.FIArea4.oddPart_pos hd.ne').ne'
    have hqpos : 0 < k / d := Nat.div_pos (Nat.le_of_dvd hkpos hdvd') hd
    have hd2ne : Work.FIPlan.oddPart (k / d) ≠ 0 :=
      (Work.FIArea4.oddPart_pos hqpos.ne').ne'
    have hK : Work.FIPlan.oddPart k = Work.FIPlan.oddPart d * Work.FIPlan.oddPart (k / d) := by
      have hmul : Work.FIPlan.oddPart (d * (k / d))
          = Work.FIPlan.oddPart d * Work.FIPlan.oddPart (k / d) := Nat.ordCompl_mul d (k / d) 2
      rw [Nat.mul_div_cancel' hdvd'] at hmul
      exact hmul
    have hP1 : jacobiSym (r1 : ℤ) (Work.FIPlan.oddPart d) * jacobiSym (r1 : ℤ) (Work.FIPlan.oddPart (k / d))
        = jacobiSym (r1 : ℤ) (Work.FIPlan.oddPart k) := by
      rw [← jacobiSym.mul_right' (r1 : ℤ) hd1ne hd2ne, ← hK]
    have hP2 : jacobiSym (r2 : ℤ) (Work.FIPlan.oddPart d) * jacobiSym (r2 : ℤ) (Work.FIPlan.oddPart (k / d))
        = jacobiSym (r2 : ℤ) (Work.FIPlan.oddPart k) := by
      rw [← jacobiSym.mul_right' (r2 : ℤ) hd1ne hd2ne, ← hK]
    have hPQ : (jacobiSym (r1 : ℤ) (Work.FIPlan.oddPart d) * jacobiSym (r2 : ℤ) (Work.FIPlan.oddPart d))
          * (jacobiSym (r1 : ℤ) (Work.FIPlan.oddPart (k / d)) * jacobiSym (r2 : ℤ) (Work.FIPlan.oddPart (k / d)))
        = jacobiSym (s1 : ℤ) r1 * jacobiSym (s2 : ℤ) r2 := by
      rw [show (jacobiSym (r1 : ℤ) (Work.FIPlan.oddPart d) * jacobiSym (r2 : ℤ) (Work.FIPlan.oddPart d))
            * (jacobiSym (r1 : ℤ) (Work.FIPlan.oddPart (k / d)) * jacobiSym (r2 : ℤ) (Work.FIPlan.oddPart (k / d)))
          = (jacobiSym (r1 : ℤ) (Work.FIPlan.oddPart d) * jacobiSym (r1 : ℤ) (Work.FIPlan.oddPart (k / d)))
            * (jacobiSym (r2 : ℤ) (Work.FIPlan.oddPart d) * jacobiSym (r2 : ℤ) (Work.FIPlan.oddPart (k / d))) from by ring,
        hP1, hP2, hcore]
    have hcr1 : Nat.Coprime r1 k := by
      rw [hk, ha]; exact coprime_natAbs_of_gcd (gcd_r1_cross hcop hs1)
    have hcr2 : Nat.Coprime r2 k := by
      rw [hk, ha]; exact coprime_natAbs_of_gcd (gcd_r2_cross hcop hs2)
    have hd2dvd : Work.FIPlan.oddPart (k / d) ∣ k :=
      (Work.FIArea4.oddPart_dvd (k / d)).trans (Nat.div_dvd_of_dvd hdvd')
    have hQ2 : (jacobiSym (r1 : ℤ) (Work.FIPlan.oddPart (k / d))
          * jacobiSym (r2 : ℤ) (Work.FIPlan.oddPart (k / d)))
        * (jacobiSym (r1 : ℤ) (Work.FIPlan.oddPart (k / d))
          * jacobiSym (r2 : ℤ) (Work.FIPlan.oddPart (k / d))) = 1 := by
      have hs1' : jacobiSym (r1 : ℤ) (Work.FIPlan.oddPart (k / d)) ^ 2 = 1 := by
        refine jacobiSym.sq_one ?_
        rw [Int.gcd_natCast_natCast]
        exact (hcr1.coprime_dvd_right hd2dvd).gcd_eq_one
      have hs2' : jacobiSym (r2 : ℤ) (Work.FIPlan.oddPart (k / d)) ^ 2 = 1 := by
        refine jacobiSym.sq_one ?_
        rw [Int.gcd_natCast_natCast]
        exact (hcr2.coprime_dvd_right hd2dvd).gcd_eq_one
      rw [show (jacobiSym (r1 : ℤ) (Work.FIPlan.oddPart (k / d))
            * jacobiSym (r2 : ℤ) (Work.FIPlan.oddPart (k / d)))
          * (jacobiSym (r1 : ℤ) (Work.FIPlan.oddPart (k / d))
            * jacobiSym (r2 : ℤ) (Work.FIPlan.oddPart (k / d)))
          = jacobiSym (r1 : ℤ) (Work.FIPlan.oddPart (k / d)) ^ 2
            * jacobiSym (r2 : ℤ) (Work.FIPlan.oddPart (k / d)) ^ 2 from by ring,
        hs1', hs2', mul_one]
    calc jacobiSym (r1 : ℤ) (Work.FIPlan.oddPart d) * jacobiSym (r2 : ℤ) (Work.FIPlan.oddPart d)
        = (jacobiSym (r1 : ℤ) (Work.FIPlan.oddPart d) * jacobiSym (r2 : ℤ) (Work.FIPlan.oddPart d))
            * 1 := by ring
      _ = (jacobiSym (r1 : ℤ) (Work.FIPlan.oddPart d) * jacobiSym (r2 : ℤ) (Work.FIPlan.oddPart d))
            * ((jacobiSym (r1 : ℤ) (Work.FIPlan.oddPart (k / d))
                * jacobiSym (r2 : ℤ) (Work.FIPlan.oddPart (k / d)))
              * (jacobiSym (r1 : ℤ) (Work.FIPlan.oddPart (k / d))
                * jacobiSym (r2 : ℤ) (Work.FIPlan.oddPart (k / d)))) := by rw [hQ2]
      _ = ((jacobiSym (r1 : ℤ) (Work.FIPlan.oddPart d) * jacobiSym (r2 : ℤ) (Work.FIPlan.oddPart d))
            * (jacobiSym (r1 : ℤ) (Work.FIPlan.oddPart (k / d))
              * jacobiSym (r2 : ℤ) (Work.FIPlan.oddPart (k / d))))
            * (jacobiSym (r1 : ℤ) (Work.FIPlan.oddPart (k / d))
              * jacobiSym (r2 : ℤ) (Work.FIPlan.oddPart (k / d))) := by ring
      _ = (jacobiSym (s1 : ℤ) r1 * jacobiSym (s2 : ℤ) r2)
            * (jacobiSym (r1 : ℤ) (Work.FIPlan.oddPart (k / d))
              * jacobiSym (r2 : ℤ) (Work.FIPlan.oddPart (k / d))) := by rw [hPQ]

end Work.FIArea4.Vflip.JacobiFlip
