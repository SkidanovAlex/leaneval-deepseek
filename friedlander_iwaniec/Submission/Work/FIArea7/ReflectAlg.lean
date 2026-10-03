/-
# `Submission.Work.FIArea7.ReflectAlg` — the elementary algebra of the *FI* §17 reflection

Area 7 (`Work.FITop3.Area7`, *FI* §§17, 19–26) reflects the large-moduli cut of (10.17) into the
complementary divisors `e = |∆|/(4d) < X` of (17.1) and then inserts Lemma 17.1 ((17.5)) to
produce the twisted coefficient `β'` of (17.8)/(17.14).  Two purely algebraic steps occur there,
and this file isolates them:

* **the square-factor rule for `jacobiSym`**: `(a | 4e²) = 1` for odd `a` coprime to `e`, hence
  `(a | m/(4e)) = (a | m·e)` whenever `4e ∣ m`.  This is what lets the reflected symbol
  `(z₂/z₁ | |∆|/(4e))` be rewritten as `(z₂/z₁ | |∆|)·(z₂/z₁ | e)` — the factorisation behind
  (17.8)/(17.9).  (Mathlib's `jacobiSym a b` is the product of `legendreSym p a` over the prime
  factors of `b`, i.e. the paper's convention (8.15), so an even modulus is harmless as long as
  the *odd* part is a square; here the odd part is `e²`.)

* **the algebra of the Jacobi–Kubota symbol**: `[z] = i^{(r-1)/2}(s/|r|)` is `∈ {±1, ±i}`, so
  `star ([z]) = [z]⁻¹`, and
  `[z₁]·conj([z₂]) = i^{(r₁-1)/2 - (r₂-1)/2}·(s₁/|r₁|)(s₂/|r₂|)`.
  Under the paper's hypothesis (17.3) `z₁ ≡ z₂ (mod 8)` the power of `i` is `1` and the identity
  becomes `β'_{z₁}·conj(β'_{z₂}) = (z₂/z₁ | |∆|)·β_{z₁}conj(β_{z₂})`, which is exactly the step
  ("here we could introduce the factor `i^{(r-1)/2}` because `r₁ ≡ r₂ (mod 8)`") that inserts
  (17.5) into (17.1).  For a pair with only `z₁ ≡ z₂ (mod 4)` — which is all the frozen
  `Work.FITop3.IsBetaCoeff` forces (see `NOTES.md` §1) — the power of `i` is `±1` and must be
  carried as an explicit per-pair sign; `jksym_mul_star` states the general form, from which
  either case follows.

All statements are elementary; nothing here mentions `β` or `Params`.
-/
import Mathlib
import Submission.Work.FIArea7.FIsymbols

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The square-factor rule for `jacobiSym` -/

/-- `gcd (2 : ℤ) a = 1` for odd `a`. -/
lemma gcd_two_eq_one_of_odd (a : ℤ) (ha : Odd a) : a.gcd (2 : ℤ) = 1 := by
  rw [Int.gcd_def]
  have h1 : Nat.gcd a.natAbs 2 ∣ 2 := Nat.gcd_dvd_right _ _
  have h2 : Nat.gcd a.natAbs 2 ∣ a.natAbs := Nat.gcd_dvd_left _ _
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
  · exact h
  · exfalso
    have hdvd : 2 ∣ a.natAbs := h ▸ h2
    obtain ⟨k, hk⟩ := ha.natAbs
    obtain ⟨j, hj⟩ := hdvd
    omega

/-- `(a | 4) = 1` for odd `a` (`4 = 2²`, and `(a|2)² = 1`). -/
lemma jacobiSym_odd_four (a : ℤ) (ha : Odd a) : jacobiSym a 4 = 1 := by
  have h2 : jacobiSym a 2 ^ 2 = 1 := jacobiSym.sq_one (gcd_two_eq_one_of_odd a ha)
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [h4, jacobiSym.pow_right]
  exact h2

/-- **The square-factor rule**: `(a | 4e²) = 1` for odd `a` coprime to `e ≠ 0`. -/
lemma jacobiSym_four_sq (a : ℤ) (e : ℕ) (ha : Odd a) (he : a.gcd e = 1) (he0 : e ≠ 0) :
    jacobiSym a (4 * e ^ 2) = 1 := by
  haveI : NeZero (e ^ 2) := ⟨pow_ne_zero 2 he0⟩
  rw [jacobiSym.mul_right, jacobiSym_odd_four a ha, jacobiSym.pow_right, jacobiSym.sq_one he]
  norm_num

/-- **The reflected symbol.**  If `4e ∣ m`, `e ≠ 0`, `a` odd and coprime to `e`, then the symbol
of the complementary modulus `m/(4e)` equals the symbol of the product `m·e`.  This is the
identity `(a | m/(4e)) = (a | m)·(a | e)` of (17.8)/(17.9) (it uses `m·e = (m/(4e))·4e²`). -/
lemma jacobiSym_eq_of_four_dvd {a : ℤ} {m e : ℕ} (hm : 0 < m) (ha : Odd a) (he : a.gcd e = 1)
    (he0 : e ≠ 0) (hme : 4 * e ∣ m) : jacobiSym a (m / (4 * e)) = jacobiSym a (m * e) := by
  have hd : m = (m / (4 * e)) * (4 * e) := (Nat.div_mul_cancel hme).symm
  have hpos : 0 < m / (4 * e) := by
    rcases Nat.eq_zero_or_pos (m / (4 * e)) with h | h
    · rw [h, zero_mul] at hd; omega
    · exact h
  haveI : NeZero (m / (4 * e)) := ⟨Nat.pos_iff_ne_zero.mp hpos⟩
  haveI : NeZero (4 * e ^ 2) := ⟨by positivity⟩
  have key : m * e = (m / (4 * e)) * (4 * e ^ 2) := by
    conv_lhs => rw [hd]
    ring
  rw [key, jacobiSym.mul_right, jacobiSym_four_sq a e ha he he0, mul_one]

/-- **The mixed-sign correction of Lemma 17.1.**  *FI* (17.4) assumes `0 < r₁r₂`; for a pair with
`r₁r₂ < 0` (possible when the polar box (5.12) straddles `arg = ±π/2`) the reciprocity bookkeeping
inside the proof of (17.5) — the paper passes to `|rᵢ|` as the lower entry of the Jacobi symbols,
while `(a|b)(b|a) = (-1)^{(a-1)(b-1)/4}(a,b)_∞` is stated for *signed* `a, b` — produces one extra
sign.  Verified exhaustively (203214 admissible pairs, both signs of `r₁r₂` **and** of `∆`): it is

  `1` if `r₁r₂ > 0`,  and  `sign(r₁)·sign(∆(z₁,z₂))` if `r₁r₂ < 0`,

i.e. `1` unless `r₁r₂ < 0` and `r₁`, `∆` have *opposite* signs, in which case it is `-1`.
(Equivalently `-1` exactly when one of `r₁, r₂` is negative and `∆` has the sign of that one.)
It is *not* a function of the residue classes mod 8 of `(r₁,r₂)`.
-/
def reflSign (z1 z2 : GaussianInt) : ℤ :=
  if 0 < z1.re * z2.re then 1
  else if (0 < z1.re ∧ 0 < Work.FIPlan.Delta z1 z2)
      ∨ (z1.re < 0 ∧ Work.FIPlan.Delta z1 z2 < 0) then 1
  else -1

/-- The rational factor `(s/|r|)` of `[z]` is real, hence fixed by conjugation. -/
lemma jkcoeff_conj (z : GaussianInt) : star (JKCoeff z) = JKCoeff z := by
  rw [JKCoeff]; simp

/-- `conj (i^k) = i^{-k}` (`i` lies on the unit circle). -/
lemma star_I_zpow (k : ℤ) : star (Complex.I ^ k) = Complex.I ^ (-k) := by
  rw [Complex.star_def, map_zpow₀]
  have h : (starRingEnd ℂ) Complex.I = Complex.I⁻¹ := by
    rw [Complex.inv_I]; simp
  rw [h, zpow_neg, ← inv_zpow]

/-- `conj [z] = i^{-(r-1)/2}(s/|r|)`. -/
lemma star_JKSym (z : GaussianInt) :
    star (JKSym z) = Complex.I ^ (-((z.re - 1) / 2 : ℤ)) * JKCoeff z := by
  rw [JKSym, star_mul', jkcoeff_conj, star_I_zpow]

/-- **The product law of the Jacobi–Kubota symbol**:
`[z₁]·conj([z₂]) = i^{(r₁-1)/2 - (r₂-1)/2}(s₁/|r₁|)(s₂/|r₂|)`.  Under (17.3)
(`z₁ ≡ z₂ (mod 8)`) the power of `i` is `1` (`I_zpow_eq_one_of_four_dvd`), which is the paper's
step "we could introduce the factor `i^{(r-1)/2}` because `r₁ ≡ r₂ (mod 8)`". -/
lemma jksym_mul_star (z1 z2 : GaussianInt) :
    JKSym z1 * star (JKSym z2)
      = Complex.I ^ (((z1.re - 1) / 2 : ℤ) - ((z2.re - 1) / 2 : ℤ))
        * (JKCoeff z1 * JKCoeff z2) := by
  have hexp : ((z1.re - 1) / 2 : ℤ) + (-((z2.re - 1) / 2 : ℤ))
      = ((z1.re - 1) / 2 : ℤ) - ((z2.re - 1) / 2 : ℤ) := by ring
  rw [star_JKSym, JKSym,
    show Complex.I ^ ((z1.re - 1) / 2 : ℤ) * JKCoeff z1
        * (Complex.I ^ (-((z2.re - 1) / 2 : ℤ)) * JKCoeff z2)
      = (Complex.I ^ ((z1.re - 1) / 2 : ℤ)
         * Complex.I ^ (-((z2.re - 1) / 2 : ℤ))) * (JKCoeff z1 * JKCoeff z2) by ring,
    ← zpow_add₀ Complex.I_ne_zero, hexp]

/-- `i^k = 1` for `4 ∣ k`. -/
lemma I_zpow_eq_one_of_four_dvd {k : ℤ} (h : (4 : ℤ) ∣ k) : Complex.I ^ k = 1 := by
  rw [Complex.I_zpow_eq_zpow_mod, Int.emod_eq_zero_of_dvd h]
  simp

end

end Work.FIArea7
