/-
Partner consistency for an odd coordinate: in a Descartes quadruple, if x is
an odd coordinate and y₁, y₂ are coprime partners of x (in the same
quadruple), then pairChi x y₁ = pairChi x y₂.

The bridge: for each odd prime p | x the reduced Descartes equation makes
y₁·y₂ a square mod p, hence jacobiSym (y₁·y₂) p = 1, and therefore
J(y₁·y₂ | |x|) = 1, forcing J(y₁ ||x|) = J(y₂ ||x|).
-/
import Submission.Apollo.Consistency
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

/-- Jacobi symbol equal to 1 when all its prime factors give symbol ≠ −1. -/
lemma jacobiSym_eq_one_of_prime_symbols {a : ℤ} {n : ℕ}
    (hg : a.gcd n = 1) (h : ∀ p : ℕ, p.Prime → p ∣ n → jacobiSym a p ≠ -1) :
    jacobiSym a n = 1 := by
  have hne : jacobiSym a n ≠ -1 := by
    intro hn
    rcases jacobiSym.eq_neg_one_at_prime_divisor_of_eq_neg_one hn with ⟨p, pp, pd, hpj⟩
    exact h p pp pd hpj
  rcases jacobiSym.eq_one_or_neg_one hg with h1 | hneg
  · exact h1
  · exact False.elim (hne hneg)

/-- if p divides the absolute value of x then x vanishes mod p. -/
lemma cast_zmod_eq_zero_of_natAbs_dvd {x : ℤ} {p : ℕ} (h : p ∣ x.natAbs) : (x : ZMod p) = 0 := by
  have hcast : (x.natAbs : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff x.natAbs p).2 h
  rcases Int.natAbs_eq x with hx | hx
  · rw [hx]; simpa using hcast
  · rw [hx]; simpa using hcast

/-- Integer Descartes equation reduces to the Descartes equation mod p when a
coordinate is 0 mod p. -/
lemma descartes_partners_zmod (p : ℕ) (a b c d : ℤ)
    (h : (a + b + c + d) ^ 2 = 2 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2))
    (hx : (a : ZMod p) = 0) :
    ((b + c + d : ZMod p) ^ 2) = 2 * ((b : ZMod p) ^ 2 + (c : ZMod p) ^ 2 + (d : ZMod p) ^ 2) := by
  have hz := congrArg (fun t : ℤ => (t : ZMod p)) h
  push_cast at hz
  rw [hx] at hz
  simpa [add_assoc, add_comm, add_left_comm] using hz

/-- A prime divisor of |x| for odd x is odd. -/
lemma prime_of_natAbs_dvd_ne_two {x : ℤ} (hxodd : ¬ 2 ∣ x) {p : ℕ}
    (pp : p.Prime) (pd : p ∣ x.natAbs) : p ≠ 2 := by
  intro hp2
  subst p
  have hoddn : Odd x.natAbs := Commons.NumberTheory.Int.odd_natAbs hxodd
  have hne : ¬ Even x.natAbs := Nat.not_even_iff_odd.mpr hoddn
  exact hne (even_iff_two_dvd.mpr pd)

/-- an integer coprime to x is nonzero mod every prime divisor p of |x|. -/
lemma zmod_ne_zero_of_gcd_one_of_dvd {x y : ℤ} {p : ℕ}
    (hg : y.gcd x = 1) (pd : p ∣ x.natAbs) (pp : p.Prime) : (y : ZMod p) ≠ 0 := by
  intro hz
  have hd1 : (p : ℤ) ∣ y := (ZMod.intCast_zmod_eq_zero_iff_dvd y p).1 hz
  -- p | y as naturals
  have hnat : p ∣ y.natAbs := by
    rcases Int.natAbs_eq y with hy | hy
    · rw [hy] at hd1
      -- (p:ℤ) ∣ ↑y.natAbs → p | y.natAbs
      exact Int.natCast_dvd_natCast.mp hd1
    · rw [hy] at hd1
      -- (p : ℤ) ∣ -↑y.natAbs → p | y.natAbs
      exact Int.natCast_dvd_natCast.mp (Int.dvd_neg.mp hd1)
  -- gcd y.natAbs x.natAbs = 1 from hg:
  have hg' : y.natAbs.gcd x.natAbs = 1 := by
    simpa [Int.gcd_def] using hg
  have hp1 : p ∣ y.natAbs.gcd x.natAbs := Nat.dvd_gcd hnat pd
  have hp1' : p ∣ 1 := by rwa [hg'] at hp1
  have hp_eq : p = 1 := Nat.dvd_one.mp hp1'
  have htwo : 2 ≤ p := pp.two_le
  omega  -- p prime → p ≥ 2, contradiction with p = 1

/-- Main: odd coordinate x, coprime partners y₁, y₂ in the same Descartes
quadruple give equal χ₂. -/
lemma pairChi_partner_consistency_odd {x y₁ y₂ z : ℤ}
    (hD : (x + y₁ + y₂ + z) ^ 2 = 2 * (x ^ 2 + y₁ ^ 2 + y₂ ^ 2 + z ^ 2))
    (hxodd : ¬ 2 ∣ x) (hg₁ : y₁.gcd x = 1) (hg₂ : y₂.gcd x = 1) :
    pairChi x y₁ = pairChi x y₂ := by
  have hnodd : Odd x.natAbs := Commons.NumberTheory.Int.odd_natAbs hxodd
  unfold pairChi
  rw [ksym_odd y₁ hnodd, ksym_odd y₂ hnodd]
  -- gcds with the denominator:
  have hg₁n : y₁.gcd x.natAbs = 1 := by
    rw [Int.gcd_eq_natAbs] at hg₁ ⊢
    rw [Int.natAbs_natCast]
    exact hg₁
  have hg₂n : y₂.gcd x.natAbs = 1 := by
    rw [Int.gcd_eq_natAbs] at hg₂ ⊢
    rw [Int.natAbs_natCast]
    exact hg₂
  -- J(y₁ y₂ | |x|) = 1
  have hprod : jacobiSym (y₁ * y₂) x.natAbs = 1 := by
    apply jacobiSym_eq_one_of_prime_symbols
    · have hgprod : (y₁ * y₂).gcd x = 1 := Commons.NumberTheory.Int.gcd_mul_left_of_coprime hg₁ hg₂
      rw [Int.gcd_eq_natAbs] at hgprod ⊢
      rw [Int.natAbs_natCast]
      exact hgprod
    · intro p pp pd
      haveI : Fact (Nat.Prime p) := ⟨pp⟩
      have hpodd : p ≠ 2 := prime_of_natAbs_dvd_ne_two hxodd pp pd
      have hx0 : (x : ZMod p) = 0 := cast_zmod_eq_zero_of_natAbs_dvd pd
      have hz1 : (y₁ : ZMod p) ≠ 0 := zmod_ne_zero_of_gcd_one_of_dvd hg₁ pd pp
      have hz2 : (y₂ : ZMod p) ≠ 0 := zmod_ne_zero_of_gcd_one_of_dvd hg₂ pd pp
      have hred : ((y₁ + y₂ + z : ZMod p) ^ 2) =
          2 * ((y₁ : ZMod p) ^ 2 + (y₂ : ZMod p) ^ 2 + (z : ZMod p) ^ 2) :=
        descartes_partners_zmod p x y₁ y₂ z hD hx0
      have hsq : IsSquare ((y₁ * y₂ : ℤ) : ZMod p) := by
        have hsq' : IsSquare ((y₁ : ZMod p) * (y₂ : ZMod p)) :=
          descartes_pair_square_zmod (p := p) hpodd (x := (y₁ : ZMod p)) (y := (y₂ : ZMod p))
            (z := (z : ZMod p)) hred
        simpa using hsq'
      have hne : ((y₁ * y₂ : ℤ) : ZMod p) ≠ 0 := by
        simpa using (mul_ne_zero hz1 hz2 : (y₁ : ZMod p) * (y₂ : ZMod p) ≠ 0)
      have hjp : jacobiSym (y₁ * y₂) p = 1 := jacobiSym_eq_one_of_zmod_square hsq hne
      rw [hjp]
      norm_num
  -- J(y₁|n)·J(y₂|n) = 1, both ±1, hence equal
  have hmul : jacobiSym y₁ x.natAbs * jacobiSym y₂ x.natAbs = 1 := by
    rw [← jacobiSym.mul_left]
    exact hprod
  rcases jacobiSym.eq_one_or_neg_one hg₁n with ha1 | ha1
  · rw [ha1] at hmul
    have ha2 : jacobiSym y₂ x.natAbs = 1 := by simpa using hmul
    rw [ha1, ha2]
  · rw [ha1] at hmul
    have ha2 : jacobiSym y₂ x.natAbs = -1 := by omega
    rw [ha1, ha2]

end Apollo
