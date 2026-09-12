/-
Local re-provision of the small shared-commons lemmas used by the χ₂ theory,
placed OUTSIDE Submission/Commons so that the fixed Solution/Challenge files
never import the `Mathlib` bundle (whose global notations would make the
challenge statements ambiguous).  Content mirrors the (read-only) commons
modules Submission.Commons.NumberTheory.* exactly.
-/
import Mathlib.Tactic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
set_option autoImplicit false


namespace Commons.NumberTheory.Int

set_option autoImplicit false
/-- The absolute value of an odd integer is an odd natural number. -/
theorem odd_natAbs {x : ℤ} (h : ¬ 2 ∣ x) : Odd x.natAbs := by
  rw [← Nat.not_even_iff_odd]
  rw [even_iff_two_dvd]
  intro hd
  apply h
  exact (Int.natAbs_dvd_natAbs.mp hd)

end Commons.NumberTheory.Int

set_option autoImplicit false

namespace Commons.NumberTheory.Int

/-- If two integers are each coprime to x, so is their product. -/
theorem gcd_mul_left_of_coprime {y₁ y₂ x : ℤ} (h₁ : y₁.gcd x = 1) (h₂ : y₂.gcd x = 1) :
    (y₁ * y₂).gcd x = 1 := by
  rw [Int.gcd_eq_natAbs, Int.natAbs_mul]
  exact Nat.coprime_iff_gcd_eq_one.mp
    (Nat.Coprime.mul_left
      (Nat.coprime_iff_gcd_eq_one.mpr (by simpa [Int.gcd_eq_natAbs] using h₁))
      (Nat.coprime_iff_gcd_eq_one.mpr (by simpa [Int.gcd_eq_natAbs] using h₂)))

end Commons.NumberTheory.Int

set_option autoImplicit false

namespace Commons.NumberTheory.Int

/-- The absolute value of an integer ≡ 5 mod 8 is ≡ 3 or 5 mod 8. -/
theorem natAbs_mod8_of_mod8_five {o : ℤ} (h : o % 8 = 5) : o.natAbs % 8 = 3 ∨ o.natAbs % 8 = 5 := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg o
  · -- o = ↑n (nonnegative), so natAbs = n
    simp
    have hm : (n : ℤ) % 8 = ((n % 8 : ℕ) : ℤ) := (Int.natCast_emod n 8).symm
    have hnat : ((n % 8 : ℕ) : ℤ) = 5 := by omega
    right
    exact_mod_cast hnat
  · -- o = -↑n, so natAbs = n
    simp
    have hneg := Int.neg_emod (a := (n : ℤ)) (b := (8 : ℤ))
    by_cases hdvd : (8 : ℤ) ∣ (n : ℤ)
    · have hz : (-(n : ℤ)) % 8 = 0 := by simp [hdvd]
      have hz5 : (5 : ℤ) = 0 := by rw [← h, hz]
      omega
    · have hlin : (8 : ℤ) - (n : ℤ) % 8 = 5 := by
        have hneg' : (-(n : ℤ)) % 8 = (8 : ℤ) - (n : ℤ) % 8 := by
          simpa [hdvd] using hneg
        rw [← hneg']
        exact h
      have hm : (n : ℤ) % 8 = ((n % 8 : ℕ) : ℤ) := (Int.natCast_emod n 8).symm
      have hnat : ((n % 8 : ℕ) : ℤ) = 3 := by omega
      left
      exact_mod_cast hnat

end Commons.NumberTheory.Int

set_option autoImplicit false

namespace Commons.NumberTheory.Int

/-- Coprimality of y and x is equivalent to coprimality of y and |x|. -/
theorem gcd_natAbs_iff {x y : ℤ} : y.gcd x = 1 ↔ y.gcd x.natAbs = 1 := by
  constructor
  · intro h
    rw [Int.gcd_eq_natAbs] at h
    rw [Int.gcd_eq_natAbs]
    rw [Int.natAbs_natCast]
    exact h
  · intro h
    rw [Int.gcd_eq_natAbs] at h
    rw [Int.natAbs_natCast] at h
    rw [Int.gcd_eq_natAbs]
    exact h

end Commons.NumberTheory.Int

set_option autoImplicit false

namespace Commons.NumberTheory.Int

/-- An integer that is 1 mod 4 is 1 mod 2. -/
theorem emod_two_of_four_one {x : ℤ} (h : x % 4 = 1) : x % 2 = 1 := by
  omega

end Commons.NumberTheory.Int

set_option autoImplicit false

namespace Commons.NumberTheory.Int

/-- If an integer is 1 mod 2 then its absolute value is an odd natural. -/
theorem natAbs_odd_of_emod_two {x : ℤ} (h : x % 2 = 1) : Odd x.natAbs := by
  apply odd_natAbs
  intro hdvd
  have hx0 : x % 2 = 0 := Int.emod_eq_zero_of_dvd hdvd
  omega

end Commons.NumberTheory.Int

set_option autoImplicit false
open scoped NumberTheorySymbols

namespace Commons.NumberTheory.JacobiSymbol

/-- The Jacobi symbol only depends on the absolute value of the numerator when
the (odd) denominator is ≡ 1 mod 4. -/
theorem abs_eq_one_mod_four {a : ℤ} {b : ℕ} (hb : b % 4 = 1) :
    jacobiSym a b = jacobiSym a.natAbs b := by
  have hodd : Odd b := Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_one hb)
  rcases lt_or_ge a 0 with ha | ha
  · have h0 : 0 ≤ -a := by omega
    have hnat : (a.natAbs : ℤ) = -a := by
      calc
        (a.natAbs : ℤ) = ((-a).natAbs : ℤ) := by rw [Int.natAbs_neg]
        _ = -a := Int.natAbs_of_nonneg h0
    rw [hnat]
    rw [jacobiSym.neg (a := a) hodd]
    rw [ZMod.χ₄_nat_one_mod_four hb, one_mul]
  · have hnat : (a.natAbs : ℤ) = a := Int.natAbs_of_nonneg ha
    rw [hnat]

end Commons.NumberTheory.JacobiSymbol

set_option autoImplicit false
open scoped NumberTheorySymbols

namespace Commons.NumberTheory.JacobiSymbol

/-- The Jacobi symbol ignores the sign of the numerator when the (odd)
denominator is ≡ 1 mod 4. -/
theorem neg_eq_one_mod_four {a : ℤ} {b : ℕ} (hb : b % 4 = 1) :
    jacobiSym (-a) b = jacobiSym a b := by
  rw [jacobiSym.neg a (Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_one hb))]
  rw [ZMod.χ₄_nat_one_mod_four hb, one_mul]

end Commons.NumberTheory.JacobiSymbol

set_option autoImplicit false
open scoped NumberTheorySymbols

namespace Commons.NumberTheory.JacobiSymbol

/-- The Jacobi symbol (2 | n) is −1 when n ≡ 3 or 5 mod 8. -/
theorem two_neg_of_mod8_three_five {n : ℕ} (h : n % 8 = 3 ∨ n % 8 = 5) :
    jacobiSym 2 n = -1 := by
  rcases h with h3 | h5
  · have hodd : Odd n := by
      rw [Nat.odd_iff]
      omega
    rw [jacobiSym.at_two hodd]
    rw [ZMod.χ₈_nat_mod_eight n, h3]
    rfl
  · have hodd : Odd n := by
      rw [Nat.odd_iff]
      omega
    rw [jacobiSym.at_two hodd]
    rw [ZMod.χ₈_nat_mod_eight n, h5]
    rfl

end Commons.NumberTheory.JacobiSymbol

set_option autoImplicit false
open scoped NumberTheorySymbols

namespace Commons.NumberTheory.JacobiSymbol

/-- A positive integer that is 1 mod 4 has absolute value 1 mod 4. -/
lemma natAbs_mod_four_eq_one_of_pos {o : ℤ} (h : o % 4 = 1) (ho : 0 < o) :
    o.natAbs % 4 = 1 := by
  have hcast : (o.natAbs : ℤ) = o := Int.natAbs_of_nonneg (le_of_lt ho)
  have h2 : (o.natAbs : ℤ) % 4 = 1 := by rw [hcast, h]
  have h3 : (o.natAbs % 4 : ℤ) = 1 := (Int.natCast_emod o.natAbs 4).trans h2
  exact Int.ofNat.inj h3

/-- An integer that is 1 mod 4 has odd absolute value. -/
lemma odd_natAbs_of_mod_four_eq_one {o : ℤ} (h : o % 4 = 1) : Odd o.natAbs := by
  exact Commons.NumberTheory.Int.natAbs_odd_of_emod_two
    (Commons.NumberTheory.Int.emod_two_of_four_one h)

/-- For two (possibly negative) integers both ≡ 1 mod 4, at least one of which
is positive, the Jacobi symbols with each other's absolute values as
denominators agree: J(o₂ | |o₁|) = J(o₁ | |o₂|). -/
theorem odd_odd_symm {o₁ o₂ : ℤ} (h₁ : o₁ % 4 = 1) (h₂ : o₂ % 4 = 1)
    (hpos : 0 < o₁ ∨ 0 < o₂) :
    jacobiSym o₂ o₁.natAbs = jacobiSym o₁ o₂.natAbs := by
  rcases hpos with ho₁ | ho₂
  · -- o₁ positive: strip the sign from the numerator of the left symbol
    -- (its denominator |o₁| ≡ 1 mod 4), and replace o₁ by its absolute value
    -- in the right symbol; then use quadratic reciprocity.
    have hm₁ : o₁.natAbs % 4 = 1 := natAbs_mod_four_eq_one_of_pos h₁ ho₁
    have hm₂odd : Odd o₂.natAbs := odd_natAbs_of_mod_four_eq_one h₂
    conv_lhs => rw [abs_eq_one_mod_four (a := o₂) (b := o₁.natAbs) hm₁]
    conv_rhs => rw [← Int.natAbs_of_nonneg (le_of_lt ho₁)]
    exact (jacobiSym.quadratic_reciprocity_one_mod_four (a := o₁.natAbs)
      (b := o₂.natAbs) hm₁ hm₂odd).symm
  · -- o₂ positive: the symmetric argument.
    have hm₂ : o₂.natAbs % 4 = 1 := natAbs_mod_four_eq_one_of_pos h₂ ho₂
    have hm₁odd : Odd o₁.natAbs := odd_natAbs_of_mod_four_eq_one h₁
    conv_lhs => rw [← Int.natAbs_of_nonneg (le_of_lt ho₂)]
    conv_rhs => rw [abs_eq_one_mod_four (a := o₁) (b := o₂.natAbs) hm₂]
    exact jacobiSym.quadratic_reciprocity_one_mod_four (a := o₂.natAbs)
      (b := o₁.natAbs) hm₂ hm₁odd

end Commons.NumberTheory.JacobiSymbol

set_option autoImplicit false
open scoped NumberTheorySymbols

namespace Commons.NumberTheory.JacobiSymbol

/-- If `o % 4 = 1` and `o < 0`, then the absolute value of `o` is `3 mod 4`. -/
lemma natAbs_mod_four_eq_three_of_neg {o : ℤ} (h : o % 4 = 1) (ho : o < 0) :
    o.natAbs % 4 = 3 := by
  have hneg : (-o) % 4 = 3 := by omega
  have h0 : 0 ≤ -o := by omega
  have hcast : (o.natAbs : ℤ) = -o := by
    calc
      (o.natAbs : ℤ) = ((-o).natAbs : ℤ) := by rw [Int.natAbs_neg]
      _ = -o := Int.natAbs_of_nonneg h0
  have h2 : (o.natAbs : ℤ) % 4 = 3 := by rw [hcast, hneg]
  have h3 : ((o.natAbs % 4 : ℕ) : ℤ) = 3 := by
    simpa using (Int.natCast_emod o.natAbs 4).trans h2
  exact Int.ofNat.inj h3

/-- Jacobi reciprocity variant: for o ≡ 1 mod 4 (any sign) and odd positive
m, J(o | m) = J(m | |o|). -/
theorem mixed_recip {o : ℤ} {m : ℕ} (ho4 : o % 4 = 1) (hmodd : Odd m) :
    jacobiSym o m = jacobiSym m o.natAbs := by
  have hodd_o : Odd o.natAbs := by
    exact Commons.NumberTheory.Int.natAbs_odd_of_emod_two
      (Commons.NumberTheory.Int.emod_two_of_four_one ho4)
  rcases lt_or_ge o 0 with ho_neg | ho_nonneg
  · -- case o < 0: o = -|o|, and J(-n | m) = χ₄ m * J(n | m)
    have hnat : (o.natAbs : ℤ) = -o := by
      have h0 : 0 ≤ -o := by omega
      calc
        (o.natAbs : ℤ) = ((-o).natAbs : ℤ) := by rw [Int.natAbs_neg]
        _ = -o := Int.natAbs_of_nonneg h0
    have ho_eq : o = -((o.natAbs : ℤ)) := by
      rw [hnat]
      omega
    conv_lhs => rw [ho_eq]
    -- goal: J(-|o| | m) = J(m | |o|)
    rw [jacobiSym.neg (a := (o.natAbs : ℤ)) hmodd]
    -- goal: χ₄ m * J(|o| | m) = J(m | |o|)
    rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hmodd) with hm1 | hm3
    · -- m ≡ 1 mod 4
      rw [ZMod.χ₄_nat_one_mod_four hm1, one_mul]
      exact (jacobiSym.quadratic_reciprocity_one_mod_four (a := m) (b := o.natAbs)
        hm1 hodd_o).symm
    · -- m ≡ 3 mod 4, and |o| ≡ 3 mod 4 as well
      have hn3 : o.natAbs % 4 = 3 := natAbs_mod_four_eq_three_of_neg ho4 ho_neg
      rw [ZMod.χ₄_nat_three_mod_four hm3]
      rw [jacobiSym.quadratic_reciprocity_three_mod_four (a := o.natAbs) (b := m) hn3 hm3]
      ring
  · -- case o ≥ 0, then o = |o| and |o| ≡ 1 mod 4
    have ho_pos : 0 < o := by omega
    have hn1 : o.natAbs % 4 = 1 := natAbs_mod_four_eq_one_of_pos ho4 ho_pos
    have ho_eq : o = (o.natAbs : ℤ) := (Int.natAbs_of_nonneg ho_nonneg).symm
    conv_lhs => rw [ho_eq]
    exact jacobiSym.quadratic_reciprocity_one_mod_four (a := o.natAbs) (b := m) hn1 hmodd

end Commons.NumberTheory.JacobiSymbol

namespace Commons.NumberTheory.Nat

/-- If `a` and `b` are coprime and `a * b` is the square of `c`, then `a` is a square. -/
private lemma isSquare_left_of_coprime_mul_sq {a b c : ℕ} (hcop : Nat.Coprime a b)
    (h : a * b = c ^ 2) (ha : a ≠ 0) (hb : b ≠ 0) : IsSquare a := by
  have hprod_ne : a * b ≠ 0 := Nat.mul_ne_zero ha hb
  have hc : c ≠ 0 := by
    intro hc0
    exact hprod_ne (by simpa [hc0] using h)
  -- factorizations of both sides of `a * b = c ^ 2`
  have hfac : a.factorization + b.factorization = c.factorization + c.factorization := by
    rw [← Nat.factorization_mul ha hb, h, pow_two, Nat.factorization_mul hc hc]
  -- coprimality says: for every prime-power counter p the two exponents cannot both be nonzero
  have hmin : ∀ p : ℕ, min (a.factorization p) (b.factorization p) = 0 := by
    intro p
    have hfac0 : a.factorization ⊓ b.factorization = (0 : ℕ →₀ ℕ) := by
      calc
        a.factorization ⊓ b.factorization = (a.gcd b).factorization :=
          (Nat.factorization_gcd ha hb).symm
        _ = (1 : ℕ).factorization := by rw [hcop.gcd_eq_one]
        _ = 0 := by simp
    have h := congrArg (fun f : ℕ →₀ ℕ => f p) hfac0
    simpa using h
  -- `a = gcd a c ^ 2` by comparing prime factorizations
  have hgcdsq : a = (a.gcd c) * (a.gcd c) := by
    apply Nat.eq_of_factorization_eq ha
    · exact mul_ne_zero (Nat.gcd_ne_zero_left ha) (Nat.gcd_ne_zero_left ha)
    intro p
    have hxeq : (a.gcd c).factorization p = min (a.factorization p) (c.factorization p) := by
      have h := congrArg (fun f : ℕ →₀ ℕ => f p) (Nat.factorization_gcd ha hc)
      simpa using h
    have hsum : a.factorization p + b.factorization p = c.factorization p + c.factorization p := by
      simpa [Finsupp.add_apply] using congrArg (fun f : ℕ →₀ ℕ => f p) hfac
    calc
      a.factorization p = 2 * (a.gcd c).factorization p := by
        by_cases hea0 : a.factorization p = 0
        · have hmin0 : min (a.factorization p) (c.factorization p) = 0 := by
            rw [hea0]
            exact Nat.min_eq_left (Nat.zero_le (c.factorization p))
          have hx0 : (a.gcd c).factorization p = 0 := by rw [hxeq, hmin0]
          omega
        · have heb0 : b.factorization p = 0 := by
            rcases (Nat.min_eq_zero_iff.mp (hmin p)) with h | h
            · exact False.elim (hea0 h)
            · exact h
          have hea2 : a.factorization p = c.factorization p + c.factorization p := by omega
          have hle : c.factorization p ≤ a.factorization p := by omega
          have hxc : (a.gcd c).factorization p = c.factorization p := by
            rw [hxeq, Nat.min_eq_right hle]
          omega
      _ = ((a.gcd c) * (a.gcd c)).factorization p := by
        rw [Nat.factorization_mul (Nat.gcd_ne_zero_left ha) (Nat.gcd_ne_zero_left ha),
          Finsupp.add_apply]
        omega
  exact ⟨a.gcd c, hgcdsq⟩

/-- If `a` and `b` are coprime and `a * b` is the square of `c`, then `b` is a square. -/
private lemma isSquare_right_of_coprime_mul_sq {a b c : ℕ} (hcop : Nat.Coprime a b)
    (h : a * b = c ^ 2) (ha : a ≠ 0) (hb : b ≠ 0) : IsSquare b := by
  have hcop' : Nat.Coprime b a := hcop.symm
  have h' : b * a = c ^ 2 := by
    calc
      b * a = a * b := by rw [mul_comm]
      _ = c ^ 2 := h
  exact isSquare_left_of_coprime_mul_sq hcop' h' hb ha

theorem coprime_isSquare_mul {a b : ℕ} (hcop : Nat.Coprime a b) (hsq : IsSquare (a * b)) :
    IsSquare a ∧ IsSquare b := by
  rcases eq_or_ne a 0 with rfl | ha
  · have hb1 : b = 1 := by
      have hg := hcop.gcd_eq_one
      simpa using hg
    subst b
    exact ⟨⟨0, by norm_num⟩, ⟨1, by norm_num⟩⟩
  · rcases eq_or_ne b 0 with rfl | hb
    · have ha1 : a = 1 := by
        have hg := hcop.gcd_eq_one
        simpa using hg
      subst a
      exact ⟨⟨1, by norm_num⟩, ⟨0, by norm_num⟩⟩
    · rcases hsq.exists_sq with ⟨c, hc⟩
      exact ⟨isSquare_left_of_coprime_mul_sq hcop hc ha hb,
        isSquare_right_of_coprime_mul_sq hcop hc ha hb⟩

end Commons.NumberTheory.Nat

namespace Commons.NumberTheory.Nat

theorem odd_sq_mod_eight {n : ℕ} (hn : Odd n) : n ^ 2 % 8 = 1 := by
  rcases hn with ⟨k, hk⟩
  subst n
  have hEven : Even (k * (k + 1)) := Nat.even_mul_succ_self k
  rcases hEven with ⟨m, hm⟩
  have hm2 : 4 * k ^ 2 + 4 * k + 1 = 8 * m + 1 := by
    nlinarith [hm]
  calc
    (2 * k + 1) ^ 2 % 8 = (4 * k ^ 2 + 4 * k + 1) % 8 := by ring_nf
    _ = (8 * m + 1) % 8 := by rw [hm2]
    _ = 1 := by
      rw [Nat.mul_add_mod]

end Commons.NumberTheory.Nat

namespace Commons.NumberTheory.Nat

theorem sq_dvd_sq {a b : ℕ} (h : a ^ 2 ∣ b ^ 2) : a ∣ b := by
  by_cases hb : b = 0
  · subst b
    exact dvd_zero a
  · have ha : a ≠ 0 := by
      intro ha0
      subst a
      have h0 : 0 ∣ b ^ 2 := by simpa using h
      have hb2 : b ^ 2 = 0 := zero_dvd_iff.mp h0
      have : b = 0 := (mul_self_eq_zero.mp (by simpa [pow_two] using hb2))
      exact hb this
    have hfac : (a ^ 2).factorization ≤ (b ^ 2).factorization :=
      (Nat.factorization_le_iff_dvd (pow_ne_zero 2 ha) (pow_ne_zero 2 hb)).mpr h
    have hpoint : ∀ p : ℕ, a.factorization p ≤ b.factorization p := by
      intro p
      have hpq : (a ^ 2).factorization p ≤ (b ^ 2).factorization p := hfac p
      have hpq' : 2 * a.factorization p ≤ 2 * b.factorization p := by
        simpa [Nat.factorization_pow] using hpq
      omega
    have hfac_le : a.factorization ≤ b.factorization := by
      rw [Finsupp.le_def]
      exact hpoint
    exact (Nat.factorization_le_iff_dvd ha hb).mp hfac_le

end Commons.NumberTheory.Nat
