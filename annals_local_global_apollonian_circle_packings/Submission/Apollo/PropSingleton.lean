/-
The quadratic-form "one square class" lemma (the core of the paper's
Proposition "singleton" / the well-definedness of χ₂ per circle).

For a binary quadratic form f(x,y) = Ax²+Bxy+Cy² of discriminant
B²-4AC = -4a² (the discriminant of the form attached to a circle of
curvature a), and for an odd divisor m of a, every value c ≡ f(x,y) (mod m)
that is coprime to m has the same Kronecker symbol against m:
ksym c m = ksym (4A) m, provided A is coprime to m.  The point is the exact
identity 4A·f(x,y) = (2Ax+By)² + 4a²y² (from the discriminant), which makes
4Ac congruent to a square modulo m; multiplying out with multiplicativity of
ksym in the numerator gives (4A|m)(c|m) = (square|m) = 1, and since both
factors are ±1 the symbol of c is the fixed value (4A|m).  This is used
(after Sarnak's parametrization of the tangent partners of a circle by the
values of such a form) to show that all coprime tangent partners of a circle
give one χ₂ value: the partner values lie in a single square coset modulo
the curvature.
-/
import Submission.Apollo.KsymTool
import Submission.Apollo.OneStep
import Submission.Apollo.CLocal
import Submission.Apollo.CLocal
import Mathlib.Tactic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
set_option autoImplicit false
open scoped NumberTheorySymbols

namespace Apollo



lemma prime_eq_two_of_dvd_two (p : ℕ) (pp : p.Prime) (h : p ∣ 2) : p = 2 := by
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h
  have hge : 2 ≤ p := pp.two_le
  omega

lemma prime_two_of_dvd_four (p : ℕ) (pp : p.Prime) (h : p ∣ 4) : p = 2 := by
  have h' : p ∣ 2 * 2 := by simpa using h
  rcases (Nat.Prime.dvd_mul pp).mp h' with h2 | h2
  all_goals exact prime_eq_two_of_dvd_two p pp h2

/-- s² - 4A f(x,y) = (B²-4AC)y². -/
lemma form_discr_ident (A B C x y : ℤ) :
    (2 * A * x + B * y) ^ 2 - 4 * A * (A * x ^ 2 + B * x * y + C * y ^ 2)
      = (B ^ 2 - 4 * A * C) * y ^ 2 := by
  ring


lemma gcd_four_of_odd (m : ℕ) (hodd : Odd m) : (4 : ℤ).gcd m = 1 := by
  rw [Int.gcd_eq_natAbs]
  norm_num
  rw [Nat.gcd_comm]
  have hm2 : ¬ 2 ∣ m := fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
  by_contra h
  rcases Nat.exists_prime_and_dvd h with ⟨p, pp, hpg⟩
  have hpd4 : p ∣ 4 := dvd_trans hpg (Nat.gcd_dvd_right m 4)
  have hp2 : p = 2 := prime_two_of_dvd_four p pp hpd4
  have hpm : p ∣ m := dvd_trans hpg (Nat.gcd_dvd_left m 4)
  rw [hp2] at hpm
  exact hm2 hpm

/-- product coprime at a ℕ modulus. -/
lemma gcd_mul_nat {x y : ℤ} {m : ℕ} (hx : x.gcd m = 1) (hy : y.gcd m = 1) :
    (x * y).gcd m = 1 := by
  rw [Int.gcd_eq_natAbs] at hx hy ⊢
  rw [Int.natAbs_mul]
  exact Nat.Coprime.mul_left (Nat.coprime_iff_gcd_eq_one.mpr (by simpa using hx))
    (Nat.coprime_iff_gcd_eq_one.mpr (by simpa using hy))

/-- Prop-singleton core: for a form f(x,y) = Ax²+Bxy+Cy² of discriminant
-4a², modulo an odd divisor m of a, the coprime values lie in one square
class: ksym c m = ksym (4A) m whenever c ≡ f(x,y) (mod m), gcd(c,m)=1 and
gcd(A,m)=1. -/
theorem form_coset (a A B C : ℤ) (m : ℕ) (hoddm : Odd m)
    (hAm : (m : ℤ) ∣ a) (hgA : A.gcd m = 1)
    (hD : B ^ 2 - 4 * A * C = -4 * a ^ 2)
    (x y c : ℤ) (hdiv : (m : ℤ) ∣ c - (A * x ^ 2 + B * x * y + C * y ^ 2))
    (hgc : c.gcd m = 1) :
    ksym c m = ksym (4 * A) m := by
  let f := A * x ^ 2 + B * x * y + C * y ^ 2
  let s := 2 * A * x + B * y
  have hm : ¬ Even m ∨ 4 ∣ m := Or.inl (Nat.not_even_iff_odd.mpr hoddm)
  have hg4 : (4 : ℤ).gcd m = 1 := gcd_four_of_odd m hoddm
  have hg4A : (4 * A).gcd m = 1 := gcd_mul_nat hg4 hgA
  have hg4Ac : (4 * A * c).gcd m = 1 := gcd_mul_nat hg4A hgc
  -- the congruence 4Ac ≡ s² (mod m):
  have hdifs : (m : ℤ) ∣ 4 * A * c - s ^ 2 := by
    have hident : 4 * A * c - s ^ 2 = 4 * A * (c - (A * x ^ 2 + B * x * y + C * y ^ 2)) + 4 * a ^ 2 * y ^ 2 := by
      dsimp [f, s]
      nlinarith [form_discr_ident A B C x y, hD]
    rw [hident]
    rcases hdiv with ⟨t1, ht1⟩
    rcases hAm with ⟨t2, ht2⟩
    refine ⟨4 * A * t1 + 4 * (m : ℤ) * (t2 ^ 2) * y ^ 2, ?_⟩
    rw [ht1, ht2]
    ring
  -- s is coprime to m:
  have hgs : s.gcd m = 1 := by
    by_contra h
    rcases Nat.exists_prime_and_dvd h with ⟨p, pp, hpd⟩
    have hpm : p ∣ m := by
      rw [Int.gcd_eq_natAbs] at hpd
      exact dvd_trans hpd (Nat.gcd_dvd_right s.natAbs m)
    have hps : p ∣ s.natAbs := by
      rw [Int.gcd_eq_natAbs] at hpd
      exact dvd_trans hpd (Nat.gcd_dvd_left s.natAbs m)
    have hpodd : p ≠ 2 := by
      intro hp2
      subst p
      exact (Nat.not_even_iff_odd.mpr hoddm) (even_iff_two_dvd.mpr hpm)
    have hpz : (p : ℤ) ∣ s := Int.natCast_dvd.mpr hps
    have hpmz : (p : ℤ) ∣ m := Int.natCast_dvd.mpr hpm
    have hpdifs : (p : ℤ) ∣ 4 * A * c - s ^ 2 := dvd_trans hpmz hdifs
    have hpsq : (p : ℤ) ∣ s ^ 2 := by
      rw [pow_two]
      exact dvd_mul_of_dvd_right hpz s
    have hsum : (p : ℤ) ∣ (4 * A * c - s ^ 2) + s ^ 2 := dvd_add hpdifs hpsq
    have hp4Ac : (p : ℤ) ∣ 4 * A * c := by simpa using hsum
    have hpz2 : p ∣ (4 * A * c).natAbs := Int.natCast_dvd.mp hp4Ac
    have hgcd1 : p ∣ Nat.gcd (4 * A * c).natAbs m := Nat.dvd_gcd hpz2 hpm
    have hg' : Nat.gcd (4 * A * c).natAbs m = 1 := by
      rw [Int.gcd_eq_natAbs] at hg4Ac
      rw [Int.natAbs_natCast] at hg4Ac
      exact hg4Ac
    have : p ∣ 1 := by rwa [hg'] at hgcd1
    exact pp.not_dvd_one this
  -- the symbol computation:
  have hnum : ksym (4 * A * c) m = ksym (s ^ 2) m := by
    apply ksym_numred (4 * A * c) (s ^ 2) m hm hg4Ac
    · -- gcd(s², m) = 1
      rw [pow_two]
      exact gcd_mul_nat hgs hgs
    · exact hdifs
  have hmul := ksym_mul_left (4 * A) c m
  have hsq1 : ksym (s ^ 2) m = 1 := ksym_sq_coprime s m hgs
  have hprod : ksym (4 * A) m * ksym c m = 1 := by
    rw [← hmul]
    rw [hnum]
    exact hsq1
  have h1v : ksym (4 * A) m = 1 ∨ ksym (4 * A) m = -1 := ksym_eq_one_or_neg_one hg4A
  have h2v : ksym c m = 1 ∨ ksym c m = -1 := ksym_eq_one_or_neg_one hgc
  rcases h1v with h1a | h1a
  · rcases h2v with h2a | h2a
    · rw [h1a, h2a]
    · exfalso
      rw [h1a, h2a] at hprod
      norm_num at hprod
  · rcases h2v with h2a | h2a
    · exfalso
      rw [h1a, h2a] at hprod
      norm_num at hprod
    · rw [h1a, h2a]


/-- Two coprime values that are both congruent to (possibly different) form
values modulo m have the same symbol: all properly represented coprime
values of the form lie in one square class. -/
theorem form_coset_pair (a A B C : ℤ) (m : ℕ) (hoddm : Odd m)
    (hAm : (m : ℤ) ∣ a) (hgA : A.gcd m = 1)
    (hD : B ^ 2 - 4 * A * C = -4 * a ^ 2)
    (c₁ x₁ y₁ c₂ x₂ y₂ : ℤ)
    (hdiv₁ : (m : ℤ) ∣ c₁ - (A * x₁ ^ 2 + B * x₁ * y₁ + C * y₁ ^ 2))
    (hdiv₂ : (m : ℤ) ∣ c₂ - (A * x₂ ^ 2 + B * x₂ * y₂ + C * y₂ ^ 2))
    (hgc₁ : c₁.gcd m = 1) (hgc₂ : c₂.gcd m = 1) :
    ksym c₁ m = ksym c₂ m := by
  have h₁ := form_coset a A B C m hoddm hAm hgA hD x₁ y₁ c₁ hdiv₁ hgc₁
  have h₂ := form_coset a A B C m hoddm hAm hgA hD x₂ y₂ c₂ hdiv₂ hgc₂
  rw [h₁, h₂]

theorem form_pair_square_zmod₀ (p : ℕ) (pp : p.Prime) (hpodd : p ≠ 2)
    (A₁ B₁ C₁ : ZMod p) (hB : B₁ ^ 2 = 4 * A₁ * C₁)
    (x₁ y₁ x₂ y₂ : ZMod p) :
    ∃ u : ZMod p,
      (A₁ * x₁ ^ 2 + B₁ * x₁ * y₁ + C₁ * y₁ ^ 2) *
          (A₁ * x₂ ^ 2 + B₁ * x₂ * y₂ + C₁ * y₂ ^ 2) = u ^ 2 := by
  haveI : Fact p.Prime := ⟨pp⟩
  by_cases hA : A₁ = 0
  · have hB₁ : B₁ = 0 := by
      have hb : B₁ ^ 2 = 0 := by rw [hB, hA]; ring
      exact sq_eq_zero_iff.mp hb
    refine ⟨C₁ * y₁ * y₂, ?_⟩
    rw [hA, hB₁]
    ring
  · have h4 : (4 : ZMod p) ≠ 0 := by
      by_contra hz
      have hd : p ∣ (4 : ℕ) := (ZMod.natCast_eq_zero_iff 4 p).1 hz
      have h22 : p ∣ 2 * 2 := by simpa [show (4 : ℕ) = 2 * 2 by norm_num] using hd
      have hp2 : p = 2 := by
        have hge : 2 ≤ p := pp.two_le
        rcases (Nat.Prime.dvd_mul pp).1 h22 with h2 | h2
        all_goals
          · have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2
            omega
      exact hpodd hp2
    have h4A : 4 * A₁ ≠ 0 := mul_ne_zero h4 hA
    let f₁ : ZMod p := A₁ * x₁ ^ 2 + B₁ * x₁ * y₁ + C₁ * y₁ ^ 2
    let f₂ : ZMod p := A₁ * x₂ ^ 2 + B₁ * x₂ * y₂ + C₁ * y₂ ^ 2
    let s₁ : ZMod p := 2 * A₁ * x₁ + B₁ * y₁
    let s₂ : ZMod p := 2 * A₁ * x₂ + B₁ * y₂
    have hsq₁ : 4 * A₁ * f₁ = s₁ ^ 2 := by
      dsimp [f₁, s₁]
      ring_nf
      rw [hB]
      ring
    have hsq₂ : 4 * A₁ * f₂ = s₂ ^ 2 := by
      dsimp [f₂, s₂]
      ring_nf
      rw [hB]
      ring
    have hmul : (4 * A₁) ^ 2 * (f₁ * f₂) = (s₁ * s₂) ^ 2 := by
      calc
        (4 * A₁) ^ 2 * (f₁ * f₂) = (4 * A₁ * f₁) * (4 * A₁ * f₂) := by ring
        _ = s₁ ^ 2 * s₂ ^ 2 := by rw [hsq₁, hsq₂]
        _ = (s₁ * s₂) ^ 2 := by ring
    refine ⟨(4 * A₁)⁻¹ * (s₁ * s₂), ?_⟩
    calc
      (A₁ * x₁ ^ 2 + B₁ * x₁ * y₁ + C₁ * y₁ ^ 2) * (A₁ * x₂ ^ 2 + B₁ * x₂ * y₂ + C₁ * y₂ ^ 2) = f₁ * f₂ := by
        dsimp [f₁, f₂]
      _ = ((4 * A₁)⁻¹ * (s₁ * s₂)) ^ 2 := by
        calc
          f₁ * f₂ = (4 * A₁)⁻¹ ^ 2 * ((4 * A₁) ^ 2 * (f₁ * f₂)) := by
            field_simp [h4A]
          _ = (4 * A₁)⁻¹ ^ 2 * (s₁ * s₂) ^ 2 := by rw [hmul]
          _ = ((4 * A₁)⁻¹ * (s₁ * s₂)) ^ 2 := by ring

/-- ℤ-level wrapper: for odd prime p | a, products of two values of a form of
discriminant -4a² are squares mod p. -/
theorem form_pair_square_zmod (A B C a x₁ y₁ x₂ y₂ : ℤ) (p : ℕ) (pp : p.Prime)
    (hpodd : p ≠ 2) (hpa : (a : ZMod p) = 0) (hD : B ^ 2 - 4 * A * C = -4 * a ^ 2) :
    ∃ u : ZMod p,
      (((A * x₁ ^ 2 + B * x₁ * y₁ + C * y₁ ^ 2) * (A * x₂ ^ 2 + B * x₂ * y₂ + C * y₂ ^ 2) : ℤ)
        : ZMod p) = u ^ 2 := by
  have hB : (B : ZMod p) ^ 2 = 4 * (A : ZMod p) * (C : ZMod p) := by
    have h := congrArg (fun t : ℤ => (t : ZMod p)) hD
    push_cast at h
    rw [hpa] at h
    norm_num at h
    exact sub_eq_zero.mp h
  rcases (form_pair_square_zmod₀ p pp hpodd (A : ZMod p) (B : ZMod p) (C : ZMod p)
    hB (x₁ : ZMod p) (y₁ : ZMod p) (x₂ : ZMod p) (y₂ : ZMod p)) with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  push_cast
  exact hu

/-- an integer that is a nonzero square mod the odd prime p has Jacobi symbol 1. -/
lemma jacobiSym_eq_one_of_square (a : ℤ) (p : ℕ) (pp : p.Prime)
    (hne : (a : ZMod p) ≠ 0) (hsq : ∃ u : ZMod p, (a : ZMod p) = u ^ 2) :
    jacobiSym a p = 1 := by
  haveI : Fact p.Prime := ⟨pp⟩
  have hsq' : IsSquare (a : ZMod p) := by
    rcases hsq with ⟨u, hu⟩
    exact ⟨u, by rw [← pow_two]; exact hu⟩
  have hl : legendreSym p a = 1 := by
    rw [legendreSym]
    exact (quadraticChar_one_iff_isSquare hne).2 hsq'
  exact (jacobiSym.legendreSym.to_jacobiSym p a).symm.trans hl
end Apollo
