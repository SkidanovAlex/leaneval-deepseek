import Mathlib
import Submission.Work.HilbertSymbol.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

theorem padicVal_eq_zero_iff {p : ℕ} [Fact p.Prime] (a : ℚˣ) :
    padicVal p a = 0 ↔ ¬ (p : ℤ) ∣ (a : ℚ).num ∧ ¬ p ∣ (a : ℚ).den := by
  have hp1 : p ≠ 1 := (Fact.out : p.Prime).ne_one
  have hnum : (a : ℚ).num ≠ 0 := Rat.num_ne_zero.mpr a.ne_zero
  have hden : (a : ℚ).den ≠ 0 := Rat.den_nz _
  -- A prime cannot divide both the numerator and the denominator of a reduced fraction.
  have key : ∀ (hnum_dvd_int : (p : ℤ) ∣ (a : ℚ).num) (hden_dvd : p ∣ (a : ℚ).den),
      False := by
    intro hnum_dvd_int hden_dvd
    have hnum_dvd : p ∣ (a : ℚ).num.natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr hnum_dvd_int
      rwa [Int.natAbs_natCast] at this
    have hcop := (a : ℚ).reduced
    have h1 : p ∣ (a : ℚ).num.natAbs.gcd (a : ℚ).den := Nat.dvd_gcd hnum_dvd hden_dvd
    rw [Nat.coprime_iff_gcd_eq_one.mp hcop] at h1
    exact (Fact.out : p.Prime).not_dvd_one h1
  constructor
  · intro h
    rw [padicVal, padicValRat_def] at h
    have hAB : padicValInt p (a : ℚ).num = padicValNat p (a : ℚ).den := by
      exact_mod_cast (sub_eq_zero.mp h)
    constructor
    · intro hnum_dvd_int
      have hA : padicValInt p (a : ℚ).num ≠ 0 := by
        intro h0
        rcases (padicValInt.eq_zero_iff.mp h0) with h' | h' | h'
        · exact hp1 h'
        · exact hnum h'
        · exact h' hnum_dvd_int
      have hB : padicValNat p (a : ℚ).den ≠ 0 := by rw [← hAB]; exact hA
      have hden_dvd : p ∣ (a : ℚ).den := by
        by_contra hnd
        exact hB (padicValNat.eq_zero_of_not_dvd hnd)
      exact key hnum_dvd_int hden_dvd
    · intro hden_dvd
      have hB : padicValNat p (a : ℚ).den ≠ 0 := by
        intro h0
        rcases (padicValNat.eq_zero_iff.mp h0) with h' | h' | h'
        · exact hp1 h'
        · exact hden h'
        · exact h' hden_dvd
      have hA : padicValInt p (a : ℚ).num ≠ 0 := by rw [hAB]; exact hB
      have hnum_dvd_int : (p : ℤ) ∣ (a : ℚ).num := by
        by_contra hnd
        exact hA (padicValInt.eq_zero_of_not_dvd hnd)
      exact key hnum_dvd_int hden_dvd
  · rintro ⟨hnum_ndvd, hden_ndvd⟩
    rw [padicVal, padicValRat_def]
    have hA : padicValInt p (a : ℚ).num = 0 :=
      padicValInt.eq_zero_of_not_dvd hnum_ndvd
    have hB : padicValNat p (a : ℚ).den = 0 :=
      padicValNat.eq_zero_of_not_dvd hden_ndvd
    rw [hA, hB]
    simp

end Work.HilbertSymbol
