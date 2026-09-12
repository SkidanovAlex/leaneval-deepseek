/-
Even-coordinate partner consistency.  The additional 2-adic ingredient: two
odd partners of an even coordinate x in a Descartes quadruple (coprime to x)
must be congruent mod 8 for their (·|2)-factors to agree; in the Apollonian
packing of (−3,5,8,8) all odd coordinates are ≡ 5 mod 8, so that congruence
holds automatically (`Apollo.Mod24`).
-/
import Submission.Apollo.KR
import Submission.Apollo.Consistency
import Submission.Apollo.Partner
import Submission.Apollo.CLocal
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

open Commons.NumberTheory.Int

/-- 2 divides x whenever 2 divides |x|. -/
lemma even_dvd_of_natAbs_dvd {x : ℤ} (h : 2 ∣ x.natAbs) : 2 ∣ x := by
  rcases Int.natAbs_eq x with hx | hx
  · rw [hx]
    exact Int.natCast_dvd_natCast.mpr h
  · rw [hx]
    exact Int.dvd_neg.mpr (Int.natCast_dvd_natCast.mpr h)

/-- an integer coprime to an even x is odd. -/
lemma odd_mod_of_coprime_even {x y : ℤ} (hx : 2 ∣ x) (hg : y.gcd x = 1) : y % 2 = 1 := by
  have hx' : 2 ∣ x.natAbs := by
    rcases hx with ⟨t, ht⟩
    rw [ht]
    simp [Int.natAbs_mul]
  have hgx : y.gcd x.natAbs = 1 := (gcd_natAbs_iff.mp hg)
  have hg2 : y.gcd 2 = 1 := by
    rcases hx' with ⟨m, hm⟩
    apply Int.gcd_eq_one_of_gcd_mul_right_eq_one_right (m := m) (n := 2)
    rw [hm] at hgx
    simpa [Nat.cast_mul, mul_comm] using hgx
  exact emod_two_eq_one_of_gcd_two y hg2

/-- odd partners of an even x with the same residue mod 8 give equal (·|2). -/
lemma kronTwo_eq_of_odd_mod8 {y₁ y₂ : ℤ} (h₁ : y₁ % 2 = 1) (h₂ : y₂ % 2 = 1)
    (h8 : y₁ % 8 = y₂ % 8) : kronTwo y₁ = kronTwo y₂ := by
  unfold kronTwo
  rw [h₁, h₂]
  have hc : (y₁ % 8 = 1 ∨ y₁ % 8 = 7) ↔ (y₂ % 8 = 1 ∨ y₂ % 8 = 7) := by
    rw [h8]
  by_cases h : y₁ % 8 = 1 ∨ y₁ % 8 = 7 <;> simp [hc, h]

/-- gcd with a divisor: y coprime to x is coprime to any k | |x|. -/
lemma gcd_of_natAbs_dvd {x y : ℤ} {k : ℕ} (hg : y.gcd x = 1) (hk : k ∣ x.natAbs) :
    y.gcd k = 1 := by
  rw [Int.gcd_eq_natAbs] at hg ⊢
  rw [Int.natAbs_natCast]
  -- Nat.gcd y.natAbs k | Nat.gcd y.natAbs x.natAbs = 1
  have hd : Nat.gcd y.natAbs k ∣ Nat.gcd y.natAbs x.natAbs := by
    apply Nat.dvd_gcd
    · exact Nat.gcd_dvd_left y.natAbs k
    · exact dvd_trans (Nat.gcd_dvd_right y.natAbs k) hk
  exact Nat.dvd_one.mp (by simpa [hg] using hd)

/-- Jacobi-partner consistency for an odd denominator k | |x|. -/
lemma jacobiSym_partner_eq_odd {x y₁ y₂ z : ℤ}
    (hD : (x + y₁ + y₂ + z) ^ 2 = 2 * (x ^ 2 + y₁ ^ 2 + y₂ ^ 2 + z ^ 2))
    (hg₁ : y₁.gcd x = 1) (hg₂ : y₂.gcd x = 1)
    {k : ℕ} (hk : k ∣ x.natAbs) (hkodd : Odd k) :
    jacobiSym y₁ k = jacobiSym y₂ k := by
  have hg₁k : y₁.gcd k = 1 := gcd_of_natAbs_dvd hg₁ hk
  have hg₂k : y₂.gcd k = 1 := gcd_of_natAbs_dvd hg₂ hk
  have hprod : jacobiSym (y₁ * y₂) k = 1 := by
    apply jacobiSym_eq_one_of_prime_symbols
    · exact Commons.NumberTheory.Int.gcd_mul_left_of_coprime hg₁k hg₂k
    · intro p pp pd
      haveI : Fact (Nat.Prime p) := ⟨pp⟩
      have hpodd : p ≠ 2 := by
        intro hp2
        have h2dvd : 2 ∣ k := by
          rw [hp2] at pd
          simpa using pd
        have hne : ¬ Even k := Nat.not_even_iff_odd.mpr hkodd
        exact hne (even_iff_two_dvd.mpr h2dvd)
      have hpd' : p ∣ x.natAbs := dvd_trans pd hk
      have hx0 : (x : ZMod p) = 0 := cast_zmod_eq_zero_of_natAbs_dvd hpd'
      have hz1 : (y₁ : ZMod p) ≠ 0 := zmod_ne_zero_of_gcd_one_of_dvd hg₁ hpd' pp
      have hz2 : (y₂ : ZMod p) ≠ 0 := zmod_ne_zero_of_gcd_one_of_dvd hg₂ hpd' pp
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
  have hmul : jacobiSym y₁ k * jacobiSym y₂ k = 1 := by
    rw [← jacobiSym.mul_left]
    exact hprod
  rcases jacobiSym.eq_one_or_neg_one hg₁k with ha1 | ha1
  · rw [ha1] at hmul
    have ha2 : jacobiSym y₂ k = 1 := by simpa using hmul
    rw [ha1, ha2]
  · rw [ha1] at hmul
    have ha2 : jacobiSym y₂ k = -1 := by omega
    rw [ha1, ha2]

/-- Full Kronecker partner consistency (any parity of x), assuming the two
partners are congruent mod 8 (automatic when x is even, in the packing). -/
theorem ksym_partner_of_coprime {x y₁ y₂ z : ℤ}
    (hD : (x + y₁ + y₂ + z) ^ 2 = 2 * (x ^ 2 + y₁ ^ 2 + y₂ ^ 2 + z ^ 2))
    (hg₁ : y₁.gcd x = 1) (hg₂ : y₂.gcd x = 1) (h8 : y₁ % 8 = y₂ % 8)
    {k : ℕ} (hk : k ∣ x.natAbs) :
    ksym y₁ k = ksym y₂ k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk0 : k = 0
    · subst k; simp [ksym]
    · by_cases he : Even k
      · rcases he with ⟨c, hc⟩
        have hkform : k = 2 * c := by omega
        have hcpos : c ≠ 0 := by
          intro hc0; omega
        have hclt : c < k := by omega
        have hcdvd : c ∣ x.natAbs := by
          exact dvd_trans (⟨2, by rw [hkform]; omega⟩) hk
        have hxeven : 2 ∣ x := by
          apply even_dvd_of_natAbs_dvd
          exact dvd_trans ⟨c, hkform⟩ hk
        have hy1odd : y₁ % 2 = 1 := odd_mod_of_coprime_even hxeven hg₁
        have hy2odd : y₂ % 2 = 1 := odd_mod_of_coprime_even hxeven hg₂
        have hkron : kronTwo y₁ = kronTwo y₂ := kronTwo_eq_of_odd_mod8 hy1odd hy2odd h8
        have hc_eq : ksym y₁ c = ksym y₂ c := ih c hclt hcdvd
        calc
          ksym y₁ k = ksym y₁ c * kronTwo y₁ := by rw [hkform]; exact ksym_even_mul y₁ hcpos
          _ = ksym y₂ c * kronTwo y₂ := by rw [hc_eq, hkron]
          _ = ksym y₂ k := by rw [hkform]; exact (ksym_even_mul y₂ hcpos).symm
      · have hkodd : Odd k := Nat.not_even_iff_odd.mp he
        rw [ksym_odd y₁ hkodd, ksym_odd y₂ hkodd]
        exact jacobiSym_partner_eq_odd hD hg₁ hg₂ hk hkodd

/-- Partner consistency for χ₂ (hypothesis h8 automatic in the packing). -/
theorem pairChi_partner_consistency {x y₁ y₂ z : ℤ}
    (hD : (x + y₁ + y₂ + z) ^ 2 = 2 * (x ^ 2 + y₁ ^ 2 + y₂ ^ 2 + z ^ 2))
    (hg₁ : y₁.gcd x = 1) (hg₂ : y₂.gcd x = 1) (h8 : y₁ % 8 = y₂ % 8) :
    pairChi x y₁ = pairChi x y₂ := by
  unfold pairChi
  exact ksym_partner_of_coprime hD hg₁ hg₂ h8 (k := x.natAbs) (dvd_rfl)


/-- value of the reduction of x mod n is congruent to x mod n. -/
lemma val_modEq {x : ℤ} {n : ℕ} [NeZero n] : ((x : ZMod n).val : ℤ) ≡ x [ZMOD (n : ℤ)] := by
  have h := ZMod.natCast_zmod_val (n := n) (a := (x : ZMod n))
  have h2 : ((x : ZMod n).val : ℤ) ≡ (x : ℤ) [ZMOD (n : ℤ)] := by
    exact (ZMod.intCast_eq_intCast_iff ((x : ZMod n).val : ℤ) x n).mp (by simpa using h.symm)
  simpa [Int.modEq_comm] using h2

/-- x mod m equals the mod-m of the residue of x mod n, when m | n. -/
lemma val_emod_eq (x : ℤ) (n m : ℕ) (hmn : m ∣ n) [NeZero n] [NeZero m] :
    x % (m : ℤ) = ((x : ZMod n).val % m : ℕ) := by
  have hm : ((x : ZMod n).val : ℤ) ≡ x [ZMOD (m : ℤ)] :=
    Int.ModEq.of_dvd (by exact_mod_cast hmn) (val_modEq (x := x) (n := n))
  have hz : ((x : ZMod n).val : ℤ) % (m : ℤ) = x % (m : ℤ) := hm
  rw [← Int.natCast_emod (m := (x : ZMod n).val) (n := m)] at hz
  exact hz.symm

private lemma finA : ∀ t : ZMod 32, (4 * t).val % 4 = 0 := by native_decide
private lemma finB : ∀ t : ZMod 32, (2 * t + 1).val % 2 = 1 := by native_decide
private lemma fin_mod8 : ∀ (A B C D S : ZMod 32),
    A.val % 4 = 0 → D.val % 4 = 0 → B.val % 2 = 1 → C.val % 2 = 1 →
    S = A + B + C + D →
    S ^ 2 = 2 * (A ^ 2 + B ^ 2 + C ^ 2 + D ^ 2) →
    B.val % 8 = C.val % 8 := by native_decide

lemma mod4_cast {a : ℤ} (h : a % 4 = 0) : ∃ t : ZMod 32, (a : ZMod 32) = 4 * t := by
  have hd : (4 : ℤ) ∣ a := (Int.dvd_iff_emod_eq_zero (a := 4) (b := a)).2 h
  rcases hd with ⟨c, hc⟩
  refine ⟨(c : ZMod 32), ?_⟩
  rw [hc]
  norm_num [Int.cast_mul]

lemma odd_cast {b : ℤ} (h : b % 2 = 1) : ∃ t : ZMod 32, (b : ZMod 32) = 2 * t + 1 := by
  have hm : b ≡ (1 : ℤ) [ZMOD (2 : ℤ)] := by
    change b % (2 : ℤ) = (1 : ℤ) % (2 : ℤ)
    rw [h]
    norm_num
  have hd : (2 : ℤ) ∣ (1 : ℤ) - b := (Int.modEq_iff_dvd.mp hm)
  rcases hd with ⟨c, hc⟩
  refine ⟨(-c : ZMod 32), ?_⟩
  have hb : b = 2 * (-c) + 1 := by omega
  rw [hb]
  norm_num [Int.cast_mul, Int.cast_neg]

/-- The two odd partners b, c of an even coordinate a ≡ 0 mod 4 in a
Descartes quadruple are congruent mod 8. -/
lemma odd_partners_cong_mod8 {a b c d : ℤ}
    (hD : (a + b + c + d) ^ 2 = 2 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2))
    (ha : a % 4 = 0) (hb : b % 2 = 1) (hc : c % 2 = 1) (hd : d % 4 = 0) :
    b % 8 = c % 8 := by
  have hA : (a : ZMod 32).val % 4 = 0 := by
    rcases mod4_cast ha with ⟨t, ht⟩
    rw [ht]
    exact finA t
  have hDv : (d : ZMod 32).val % 4 = 0 := by
    rcases mod4_cast hd with ⟨t, ht⟩
    rw [ht]
    exact finA t
  have hB : (b : ZMod 32).val % 2 = 1 := by
    rcases odd_cast hb with ⟨t, ht⟩
    rw [ht]
    exact finB t
  have hC : (c : ZMod 32).val % 2 = 1 := by
    rcases odd_cast hc with ⟨t, ht⟩
    rw [ht]
    exact finB t
  let A : ZMod 32 := a
  let B : ZMod 32 := b
  let C : ZMod 32 := c
  let D : ZMod 32 := d
  let S : ZMod 32 := ((a + b + c + d : ℤ) : ZMod 32)
  have hS : S = A + B + C + D := by simp [A, B, C, D, S]
  have hz : S ^ 2 = 2 * (A ^ 2 + B ^ 2 + C ^ 2 + D ^ 2) := by
    have hc := congrArg (fun t : ℤ => (t : ZMod 32)) hD
    push_cast at hc
    simpa [A, B, C, D, S] using hc
  have hres := fin_mod8 A B C D S hA hDv hB hC hS hz
  calc
    b % 8 = ((b : ZMod 32).val % 8 : ℤ) := by
      simpa using (val_emod_eq b 32 8 (by norm_num))
    _ = ((c : ZMod 32).val % 8 : ℤ) := by
      simpa [B, C] using (congrArg (fun k : ℕ => (k : ℤ)) hres)
    _ = c % 8 := by
      symm
      simpa using (val_emod_eq c 32 8 (by norm_num))

end Apollo
