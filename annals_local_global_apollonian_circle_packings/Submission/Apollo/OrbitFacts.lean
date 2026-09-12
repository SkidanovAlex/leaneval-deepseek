/-
Orbit facts needed by the coprime-path construction:
  * every Descartes quadruple in the Apollonian orbit of (-3,5,8,8) is
    primitive (its coordinates have gcd 1), since the orbit lies in the
    GL(4, ℤ)-action which preserves primitivity;
  * no orbit coordinate is 0: odd coordinates are ≡ 5 mod 8 (hence nonzero),
    and a Descartes quadruple (a, b, 0, c) with a, b ≡ 5 mod 8 and c even can
    never be primitive (from (a-b-c)² = 4bc the two "side" coordinates are
    coprime squares after dividing out their gcd — but a square ≡ 5 mod 8 is
    impossible, since odd squares are ≡ 1 mod 8).
-/
import Submission.Apollo.Crack
import Submission.Apollo.Occurrence
import Submission.Apollo.MoveStep
import Submission.Apollo.CLocal
import Submission.Apollo.CLocal
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

/-- the base quadruple is primitive. -/
lemma q0v_gcd_one : Finset.univ.gcd q0v = 1 := by
  decide

/-- the general-linear-group action on vectors preserves primitivity. -/
lemma gl_smul_gcd_one (g : GL (Fin 4) ℤ) (v : Fin 4 → ℤ)
    (hv : Finset.univ.gcd v = 1) : Finset.univ.gcd (g • v) = 1 := by
  have h := GeneralLinearGroupAction.smul_mem' g (by
    dsimp [GeneralLinearGroupAction]
    exact hv)
  dsimp [GeneralLinearGroupAction] at h
  exact h

/-- Every Descartes quadruple in the Apollonian orbit is primitive. -/
theorem apOrbit_gcd_one (w : Fin 4 → ℤ) (hw : w ∈ apOrbit) : Finset.univ.gcd w = 1 := by
  rcases hw with ⟨g, hg, rfl⟩
  exact gl_smul_gcd_one g q0v q0v_gcd_one

/-- an orbit coordinate with an odd index is nonzero (it is ≡ 5 mod 8). -/
theorem orbit_odd_coord_ne_zero (w : Fin 4 → ℤ) (hw : w ∈ apOrbit) (i : Fin 4)
    (hi : i = 0 ∨ i = 1) : w i ≠ 0 := by
  intro hz
  have h8 : w i % 8 = 5 := orbit_odd_coord_eq_five_mod8 w hw i hi
  rw [hz] at h8
  norm_num at h8

/-- Descartes quadruple (a,b,0,c) (a,b the odd ≡ 5 mod 8 coordinates, c even):
no such quadruple can be primitive.  `hprim` says: any natural divisor of all
of |a|,|b|,|c| is 1. -/
lemma descartes_zero_contra {a b c : ℤ}
    (ha : a % 8 = 5) (hb : b % 8 = 5) (hce : (2 : ℤ) ∣ c)
    (hD : (a + b + c) ^ 2 = 2 * (a ^ 2 + b ^ 2 + c ^ 2))
    (hprim : ∀ t : ℕ, t ∣ a.natAbs → t ∣ b.natAbs → t ∣ c.natAbs → t = 1) : False := by
  have hsq : (a - b - c) ^ 2 = 4 * b * c := by
    nlinarith [hD]
  have ha2 : a % 2 = 1 := by omega
  have hb2 : b % 2 = 1 := by omega
  have hab : (2 : ℤ) ∣ a - b := by
    have hm : a ≡ b [ZMOD (2 : ℤ)] := by
      rw [Int.ModEq]
      omega
    have hd : (2 : ℤ) ∣ b - a := Int.modEq_iff_dvd.mp hm
    simpa [neg_sub] using (Int.dvd_neg.mpr hd)
  have h2t : (2 : ℤ) ∣ a - b - c := by
    simpa [sub_eq_add_neg, add_assoc] using (Int.dvd_sub hab hce)
  rcases h2t with ⟨m, hm⟩
  have hbd : b * c = m ^ 2 := by
    have h4 : (2 * m) ^ 2 = 4 * b * c := by
      rw [← hm]
      exact hsq
    have h4' : 4 * m ^ 2 = 4 * (b * c) := by nlinarith [h4]
    nlinarith [h4']
  let B : ℕ := b.natAbs
  let C : ℕ := c.natAbs
  let M : ℕ := m.natAbs
  have hBC : B * C = M ^ 2 := by
    have h' := congrArg Int.natAbs hbd
    simpa [B, C, M, Int.natAbs_mul, Int.natAbs_pow] using h'
  let h : ℕ := Nat.gcd B C
  have hB : h ∣ B := Nat.gcd_dvd_left B C
  have hC : h ∣ C := Nat.gcd_dvd_right B C
  have h2div : h ^ 2 ∣ M ^ 2 := by
    rw [pow_two, pow_two]
    have hBCmm : B * C = M * M := by
      rw [pow_two] at hBC
      exact hBC
    have hh : h * h ∣ B * C := Nat.mul_dvd_mul hB hC
    rwa [hBCmm] at hh
  have hM : h ∣ M := Commons.NumberTheory.Nat.sq_dvd_sq h2div
  have hma : (h : ℤ) ∣ m := Int.natCast_dvd.mpr hM
  have h2ma : (h : ℤ) ∣ 2 * m := by
    simpa [mul_comm] using (dvd_mul_of_dvd_right hma 2)
  have hb' : (h : ℤ) ∣ b := Int.natCast_dvd.mpr hB
  have hc' : (h : ℤ) ∣ c := Int.natCast_dvd.mpr hC
  have ha' : (h : ℤ) ∣ a := by
    have hsum : (h : ℤ) ∣ 2 * m + b + c := by
      exact dvd_add (dvd_add h2ma hb') hc'
    have haeq : a = 2 * m + b + c := by omega
    rwa [← haeq] at hsum
  have hh : h = 1 := hprim h (Int.natCast_dvd.mp ha') (Int.natCast_dvd.mp hb') (Int.natCast_dvd.mp hc')
  have hh1 : h ∣ 1 := by
    rw [hh]
  have hcop : Nat.Coprime B C := by
    simpa [Nat.Coprime, h] using hh
  have hsqBC : IsSquare (B * C) := by
    refine ⟨M, ?_⟩
    have hsym := hBC.symm
    rw [pow_two] at hsym
    exact hsym.symm
  rcases Commons.NumberTheory.Nat.coprime_isSquare_mul hcop hsqBC with ⟨⟨u, hu⟩, _⟩
  have hBeq : u ^ 2 = B := by
    rw [pow_two]
    exact hu.symm
  have hBodd : Odd B := by
    exact Commons.NumberTheory.Int.odd_natAbs (odd_of_mod8_five hb)
  have hu_odd : Odd u := by
    by_contra huE
    have hEven : Even u := Nat.not_odd_iff_even.mp huE
    rcases hEven with ⟨k, hk⟩
    have hBe : Even B := by
      refine ⟨2 * k ^ 2, ?_⟩
      rw [← hBeq, hk]
      ring
    exact (Nat.not_even_iff_odd.mpr hBodd) hBe
  have hB1 : B % 8 = 1 := by
    rw [← hBeq]
    exact Commons.NumberTheory.Nat.odd_sq_mod_eight hu_odd
  rcases Commons.NumberTheory.Int.natAbs_mod8_of_mod8_five hb with h3 | h5
  · omega
  · omega

/-- primitive-instance for a zero at index 2: any t dividing |w0|,|w1|,|w3| is 1. -/
lemma gcd_one_of_divides2 {w : Fin 4 → ℤ} (hw : w ∈ apOrbit) (hzero : w 2 = 0)
    {t : ℕ} (ht0 : t ∣ (w 0).natAbs) (ht1 : t ∣ (w 1).natAbs) (ht3 : t ∣ (w 3).natAbs) : t = 1 := by
  have hg : (t : ℤ) ∣ Finset.univ.gcd w := by
    rw [Finset.dvd_gcd_iff]
    intro k hk
    fin_cases k
    · exact Int.natCast_dvd.mpr ht0
    · exact Int.natCast_dvd.mpr ht1
    · simpa [hzero]
    · exact Int.natCast_dvd.mpr ht3
  have hg1 : (t : ℤ) ∣ (1 : ℤ) := by rwa [apOrbit_gcd_one w hw] at hg
  exact Nat.dvd_one.mp (Int.natCast_dvd.mp hg1)

/-- primitive-instance for a zero at index 3. -/
lemma gcd_one_of_divides3 {w : Fin 4 → ℤ} (hw : w ∈ apOrbit) (hzero : w 3 = 0)
    {t : ℕ} (ht0 : t ∣ (w 0).natAbs) (ht1 : t ∣ (w 1).natAbs) (ht2 : t ∣ (w 2).natAbs) : t = 1 := by
  have hg : (t : ℤ) ∣ Finset.univ.gcd w := by
    rw [Finset.dvd_gcd_iff]
    intro k hk
    fin_cases k
    · exact Int.natCast_dvd.mpr ht0
    · exact Int.natCast_dvd.mpr ht1
    · exact Int.natCast_dvd.mpr ht2
    · simpa [hzero]
  have hg1 : (t : ℤ) ∣ (1 : ℤ) := by rwa [apOrbit_gcd_one w hw] at hg
  exact Nat.dvd_one.mp (Int.natCast_dvd.mp hg1)

/-- coordinate 2 of an orbit quadruple is never 0. -/
theorem orbit_two_ne_zero (w : Fin 4 → ℤ) (hw : w ∈ apOrbit) : w 2 ≠ 0 := by
  intro hzero
  have ha : (w 0) % 8 = 5 := orbit_odd_coord_eq_five_mod8 w hw 0 (Or.inl rfl)
  have hb : (w 1) % 8 = 5 := orbit_odd_coord_eq_five_mod8 w hw 1 (Or.inr rfl)
  have hce : (2 : ℤ) ∣ w 3 := orbit_even_three w hw
  have hD3 : (w 0 + w 1 + w 3) ^ 2 = 2 * ((w 0) ^ 2 + (w 1) ^ 2 + (w 3) ^ 2) := by
    have hD' := apOrbit_descarates w hw
    have hs1 : (∑ j : Fin 4, w j) = w 0 + w 1 + w 3 := by
      rw [Fin.sum_univ_four]
      simp [hzero]
    have hs2 : (∑ j : Fin 4, (w j) ^ 2) = (w 0) ^ 2 + (w 1) ^ 2 + (w 3) ^ 2 := by
      rw [Fin.sum_univ_four]
      simp [hzero]
    rw [hs1, hs2] at hD'
    exact hD'
  exact descartes_zero_contra ha hb hce hD3 (fun t ht0 ht1 ht3 => gcd_one_of_divides2 hw hzero ht0 ht1 ht3)

/-- coordinate 3 of an orbit quadruple is never 0. -/
theorem orbit_three_ne_zero (w : Fin 4 → ℤ) (hw : w ∈ apOrbit) : w 3 ≠ 0 := by
  intro hzero
  have ha : (w 0) % 8 = 5 := orbit_odd_coord_eq_five_mod8 w hw 0 (Or.inl rfl)
  have hb : (w 1) % 8 = 5 := orbit_odd_coord_eq_five_mod8 w hw 1 (Or.inr rfl)
  have hce : (2 : ℤ) ∣ w 2 := orbit_even_two w hw
  have hD3 : (w 0 + w 1 + w 2) ^ 2 = 2 * ((w 0) ^ 2 + (w 1) ^ 2 + (w 2) ^ 2) := by
    have hD' := apOrbit_descarates w hw
    have hs1 : (∑ j : Fin 4, w j) = w 0 + w 1 + w 2 := by
      rw [Fin.sum_univ_four]
      simp [hzero]
    have hs2 : (∑ j : Fin 4, (w j) ^ 2) = (w 0) ^ 2 + (w 1) ^ 2 + (w 2) ^ 2 := by
      rw [Fin.sum_univ_four]
      simp [hzero]
    rw [hs1, hs2] at hD'
    exact hD'
  exact descartes_zero_contra ha hb hce hD3 (fun t ht0 ht1 ht2 => gcd_one_of_divides3 hw hzero ht0 ht1 ht2)

/-- no coordinate of any Descartes quadruple in the Apollonian orbit of
(-3, 5, 8, 8) is 0. -/
theorem orbit_value_ne_zero (w : Fin 4 → ℤ) (hw : w ∈ apOrbit) (i : Fin 4) : w i ≠ 0 := by
  fin_cases i
  · exact orbit_odd_coord_ne_zero w hw 0 (Or.inl rfl)
  · exact orbit_odd_coord_ne_zero w hw 1 (Or.inr rfl)
  · exact orbit_two_ne_zero w hw
  · exact orbit_three_ne_zero w hw

end Apollo
