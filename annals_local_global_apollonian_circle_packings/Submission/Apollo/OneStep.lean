/-
The one-step S-mate identity for the partner-symbol theory.

If (a,b,c,d) is a Descartes quadruple of the packing and b' is the S-mate of b
across (a,c,d) (the value obtained by reflecting the coordinate of b), then
two coprime partners b, b' of the circle a give the same Kronecker symbol
value: `pairChi a b = pairChi a b'`.  Algebraically this rests on the
identity (a+b)(a+b') = 4a² + (c-d)², a consequence of the Descartes
equation: it makes (a+b)(a+b') congruent to the square (c-d)² modulo a.
Since b, b' are coprime to a (and therefore so are a+b, a+b' and c-d), the
Kronecker symbol of the product against |a| is 1, and the two factors, both
being ±1, are equal.

Also published here are the elementary facts used repeatedly by the χ₂
theory: |a| divides a, |a|² = a², |a| divides 4a², and the denominator |w i|
of an orbit value is never congruent to 2 mod 4 (odd or divisible by 4).
-/
import Submission.Apollo.Chi2
import Submission.Apollo.KsymTool
import Submission.Apollo.Parity
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
open scoped Pointwise
open LocalGlobalApollonianCirclePackings

namespace Apollo

/-- S-mate product identity: (a+b)(a+b') = 4a² + (c-d)² for b,b' the two
Descartes completions of (a,c,d). -/
lemma smate_product (a b c d b' : ℤ)
    (hD : (a + b + c + d) ^ 2 = 2 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2))
    (hb' : b + b' = 2 * (a + c + d)) :
    (a + b) * (a + b') = 4 * a ^ 2 + (c - d) ^ 2 := by
  have hb'form : b' = 2 * (a + c + d) - b := by linarith
  rw [hb'form]
  nlinarith

/-- gcd(a+b, a) = gcd(b, a). -/
lemma gcd_add_left (a b : ℤ) : (a + b).gcd a = b.gcd a := by
  rw [add_comm]
  exact Int.gcd_add_self_left a b

/-- from gcd(b, a) = 1, gcd(a+b, a) = 1. -/
lemma gcd_coprime_sum {a b : ℤ} (h : b.gcd a = 1) : (a + b).gcd a = 1 := by
  rw [gcd_add_left]
  exact h

/-- |a| divides a. -/
lemma natAbs_dvd_self (a : ℤ) : (a.natAbs : ℤ) ∣ a := by
  rcases Int.natAbs_eq a with h | h
  · rw [← h]
  · have hn : (a.natAbs : ℤ) = -a := by linarith
    rw [hn]
    refine ⟨-1, ?_⟩
    ring

/-- (a.natAbs)² = a² as integers. -/
lemma natAbs_sq (a : ℤ) : (a.natAbs : ℤ) ^ 2 = a ^ 2 := by
  rcases Int.natAbs_eq a with h | h
  · rw [← h]
  · have hn : (a.natAbs : ℤ) = -a := by linarith
    rw [hn]
    ring

/-- |a| divides 4a². -/
lemma natAbs_dvd_four_sq (a : ℤ) : (a.natAbs : ℤ) ∣ 4 * a ^ 2 := by
  refine ⟨4 * (a.natAbs : ℤ), ?_⟩
  rw [← natAbs_sq a]
  ring

/-- the denominators |w i| of orbit values are never ≡ 2 mod 4: they are odd
or divisible by 4 (odd values are ≡ 5 mod 8, even values ≡ 0 mod 4). -/
lemma denom_not_two_mod (w : Fin 4 → ℤ) (hw : w ∈ apOrbit) (i : Fin 4) :
    ¬ Even (w i).natAbs ∨ 4 ∣ (w i).natAbs := by
  by_cases he : 2 ∣ w i
  · right
    have hi : i = 2 ∨ i = 3 := by
      by_contra h
      have hi01 : i = 0 ∨ i = 1 := by
        fin_cases i
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exfalso; exact h (Or.inl rfl)
        · exfalso; exact h (Or.inr rfl)
      have : ¬ 2 ∣ w i := (coord_odd_iff w hw i).2 hi01
      exact this he
    have hz : w i % 4 = 0 := orbit_even_coord_eq_zero_mod4 w hw i hi
    have h4 : (4 : ℤ) ∣ w i := by
      rw [Int.dvd_iff_emod_eq_zero]
      exact hz
    rcases h4 with ⟨k, hk⟩
    refine ⟨k.natAbs, ?_⟩
    rw [hk]
    rw [Int.natAbs_mul]
    norm_num
  · left
    have hodd := Commons.NumberTheory.Int.odd_natAbs he
    exact Nat.not_even_iff_odd.mpr hodd

/-- The sum over the three coordinates different from j (given that the four
indices i, j, k, l are pairwise distinct). -/
lemma sum_excl_three (w : Fin 4 → ℤ) (i j k l : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    (∑ t : Fin 4, if t = j then 0 else w t) = w i + w k + w l := by
  fin_cases j <;> fin_cases i <;> fin_cases k <;> fin_cases l <;>
    simp [Fin.sum_univ_four] at hij hik hil hjk hjl hkl ⊢ <;> ring_nf

/-- One step of the ring around a circle: reflecting the coordinate of b
keeps the partner symbol of a fixed, provided both b and its S-mate are
coprime to a.  (`gen j • w` is the S-mate quadruple.) -/
theorem one_step (w : Fin 4 → ℤ) (hw : w ∈ apOrbit)
    {i j k l : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hb : (w j).gcd (w i) = 1) (hB : ((gen j • w) j).gcd (w i) = 1) :
    pairChi (w i) (w j) = pairChi (w i) ((gen j • w) j) := by
  let a := w i
  let b := w j
  let c := w k
  let d := w l
  let B := (gen j • w) j
  have hD : (a + b + c + d) ^ 2 = 2 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
    have h := descartes_fourterm w hw (i := i) (j := j) (k := k) (l := l)
      hij hik hil hjk hjl hkl
    simpa [a, b, c, d] using h
  have hu : (gen j • w) j = 2 * (w i + w k + w l) - w j := by
    rw [gen_smul_apply]
    simp
    rw [sum_excl_three w i j k l hij hik hil hjk hjl hkl]
    ring
  have hBsum : b + B = 2 * (a + c + d) := by
    change w j + (gen j • w) j = 2 * (w i + w k + w l)
    rw [hu]
    ring
  have hprod : (a + b) * (a + B) = 4 * a ^ 2 + (c - d) ^ 2 := smate_product a b c d B hD hBsum
  have h1 : (a + b).gcd a = 1 := gcd_coprime_sum (by simpa [a, b] using hb)
  have h2 : (a + B).gcd a = 1 := gcd_coprime_sum (by simpa [a, B] using hB)
  have hgcdcd : (c - d).gcd a = 1 := by
    by_contra hne
    rcases Nat.exists_prime_and_dvd hne with ⟨p, pp, hpd⟩
    have hpa : p ∣ a.natAbs := by
      rw [Int.gcd_eq_natAbs] at hpd
      exact dvd_trans hpd (Nat.gcd_dvd_right (c - d).natAbs a.natAbs)
    have hpc : p ∣ (c - d).natAbs := by
      rw [Int.gcd_eq_natAbs] at hpd
      exact dvd_trans hpd (Nat.gcd_dvd_left (c - d).natAbs a.natAbs)
    have hpaz : (p : ℤ) ∣ a := Int.natCast_dvd.mpr hpa
    have hpcz : (p : ℤ) ∣ c - d := Int.natCast_dvd.mpr hpc
    have h4a : (p : ℤ) ∣ 4 * a ^ 2 := by
      rcases hpaz with ⟨t, ht⟩
      refine ⟨4 * a * t, ?_⟩
      rw [ht]
      ring
    have hsq : (p : ℤ) ∣ (c - d) ^ 2 := by
      rw [pow_two]
      exact dvd_mul_of_dvd_right hpcz (c - d)
    have hdiv : (p : ℤ) ∣ (a + b) * (a + B) := by
      rw [hprod]
      exact dvd_add h4a hsq
    rcases Int.Prime.dvd_mul pp hdiv with hpb | hpB
    · have hpabz : (p : ℤ) ∣ a + b := Int.natCast_dvd.mpr hpb
      have hbpb : (p : ℤ) ∣ b := by
        have : (p : ℤ) ∣ (a + b) - a := dvd_sub hpabz hpaz
        simpa using this
      have hpb' : p ∣ b.natAbs := Int.natCast_dvd.mp hbpb
      have hp1 : (p : ℤ) ∣ (b.gcd a : ℤ) := by
        rw [Int.gcd_eq_natAbs]
        exact Int.natCast_dvd.mpr (Nat.dvd_gcd hpb' hpa)
      have hz : p ∣ (1 : ℕ) := by
        rw [hb] at hp1
        exact Int.natCast_dvd.mp hp1
      exact pp.not_dvd_one hz
    · have hpaBz : (p : ℤ) ∣ a + B := Int.natCast_dvd.mpr hpB
      have hBpb : (p : ℤ) ∣ B := by
        have : (p : ℤ) ∣ (a + B) - a := dvd_sub hpaBz hpaz
        simpa using this
      have hpB' : p ∣ B.natAbs := Int.natCast_dvd.mp hBpb
      have hp1 : (p : ℤ) ∣ (B.gcd a : ℤ) := by
        rw [Int.gcd_eq_natAbs]
        exact Int.natCast_dvd.mpr (Nat.dvd_gcd hpB' hpa)
      have hz : p ∣ (1 : ℕ) := by
        rw [hB] at hp1
        exact Int.natCast_dvd.mp hp1
      exact pp.not_dvd_one hz
  -- symbol comparisons:
  have hDm : ¬ Even a.natAbs ∨ 4 ∣ a.natAbs := by simpa [a] using denom_not_two_mod w hw i
  have habc : (a + b).gcd a.natAbs = 1 := (Commons.NumberTheory.Int.gcd_natAbs_iff (x := a) (y := a + b)).mp h1
  have hbc : b.gcd a.natAbs = 1 := (Commons.NumberTheory.Int.gcd_natAbs_iff (x := a) (y := b)).mp (by simpa [a, b] using hb)
  have hdiv1 : (a.natAbs : ℤ) ∣ (a + b) - b := by
    rw [show (a + b) - b = a by ring]
    exact natAbs_dvd_self a
  have hred1 : ksym (a + b) a.natAbs = ksym b a.natAbs :=
    ksym_numred (a + b) b a.natAbs hDm habc hbc hdiv1
  have hBc : (a + B).gcd a.natAbs = 1 := (Commons.NumberTheory.Int.gcd_natAbs_iff (x := a) (y := a + B)).mp h2
  have hBCc : B.gcd a.natAbs = 1 := (Commons.NumberTheory.Int.gcd_natAbs_iff (x := a) (y := B)).mp (by simpa [a, B] using hB)
  have hdiv2 : (a.natAbs : ℤ) ∣ (a + B) - B := by
    rw [show (a + B) - B = a by ring]
    exact natAbs_dvd_self a
  have hred2 : ksym (a + B) a.natAbs = ksym B a.natAbs :=
    ksym_numred (a + B) B a.natAbs hDm hBc hBCc hdiv2
  -- the product identity at the symbol level:
  have hcdsq : (c - d).gcd a.natAbs = 1 :=
    (Commons.NumberTheory.Int.gcd_natAbs_iff (x := a) (y := c - d)).mp hgcdcd
  have hcdsq2 : ((c - d) ^ 2).gcd a.natAbs = 1 := by
    rw [pow_two]
    exact Commons.NumberTheory.Int.gcd_mul_left_of_coprime hcdsq hcdsq
  have hprodgc : ((a + b) * (a + B)).gcd a.natAbs = 1 :=
    Commons.NumberTheory.Int.gcd_mul_left_of_coprime habc hBc
  have hdiv4 : (a.natAbs : ℤ) ∣ ((a + b) * (a + B)) - (c - d) ^ 2 := by
    rw [hprod]
    rw [show 4 * a ^ 2 + (c - d) ^ 2 - (c - d) ^ 2 = 4 * a ^ 2 by ring]
    exact natAbs_dvd_four_sq a
  have hnum : ksym ((a + b) * (a + B)) a.natAbs = ksym ((c - d) ^ 2) a.natAbs :=
    ksym_numred ((a + b) * (a + B)) ((c - d) ^ 2) a.natAbs hDm hprodgc hcdsq2 hdiv4
  have hmul := ksym_mul_left (a + b) (a + B) a.natAbs
  have hsqval : ksym ((c - d) ^ 2) a.natAbs = 1 := ksym_sq_coprime (c - d) a.natAbs hcdsq
  have hprodval : ksym (a + b) a.natAbs * ksym (a + B) a.natAbs = 1 := by
    rw [← hmul]
    rw [hnum]
    exact hsqval
  have h1v : ksym (a + b) a.natAbs = 1 ∨ ksym (a + b) a.natAbs = -1 :=
    ksym_eq_one_or_neg_one habc
  have h2v : ksym (a + B) a.natAbs = 1 ∨ ksym (a + B) a.natAbs = -1 :=
    ksym_eq_one_or_neg_one hBc
  have heq : ksym (a + b) a.natAbs = ksym (a + B) a.natAbs := by
    rcases h1v with h1a | h1a
    · rcases h2v with h2a | h2a
      · rw [h1a, h2a]
      · exfalso
        rw [h1a, h2a] at hprodval
        norm_num at hprodval
    · rcases h2v with h2a | h2a
      · exfalso
        rw [h1a, h2a] at hprodval
        norm_num at hprodval
      · rw [h1a, h2a]
  calc
    pairChi (w i) (w j) = pairChi a b := by simp [a, b]
    _ = ksym b a.natAbs := by rfl
    _ = ksym (a + b) a.natAbs := hred1.symm
    _ = ksym (a + B) a.natAbs := heq
    _ = ksym B a.natAbs := hred2
    _ = pairChi a B := by rfl
    _ = pairChi (w i) ((gen j • w) j) := by simp [a, B]

end Apollo
