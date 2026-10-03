import Mathlib
import Submission.Work.FIArea4.S15pDngAux
import Submission.Work.FIArea7.ReSymbolTwist
import Submission.Work.FIArea4.A6psi.jacobiSym_gnorm_scalePt_eq_classFactor
import Submission.Work.FIArea4.A6psi.ratioSym_scalePt_eq_zero_of_not_coprime

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea4.A6psi

/-- Unit conditions on `w.re` and `w.im` coming from `(e·Re w, 2·Im w) = 1` and `(Re w, d') = 1`:
`Re w` is a unit modulo `4d'` and `Im w` is a unit modulo `e`. -/
lemma coprime_scalePt_units (e d' : ℕ) (w : GaussianInt)
    (hc : Nat.Coprime w.re.natAbs d')
    (hprim : Nat.Coprime ((e : ℤ) * w.re).natAbs (2 * w.im.natAbs)) :
    Nat.Coprime w.re.natAbs (4 * d') ∧ Nat.Coprime w.im.natAbs e := by
  have hprim' : Nat.Coprime (e * w.re.natAbs) (2 * w.im.natAbs) := by
    have h := hprim
    rwa [Int.natAbs_mul, Int.natAbs_natCast] at h
  constructor
  · have ha : Nat.Coprime (e * w.re.natAbs) 2 :=
      Nat.Coprime.coprime_dvd_right (dvd_mul_right 2 w.im.natAbs) hprim'
    have hre2 : Nat.Coprime w.re.natAbs 2 :=
      Nat.Coprime.coprime_dvd_left (dvd_mul_left w.re.natAbs e) ha
    have hre4 : Nat.Coprime w.re.natAbs 4 := by
      have h := Nat.Coprime.pow_right 2 hre2
      simpa using h
    exact Nat.Coprime.mul_right hre4 hc
  · have hse2 : Nat.Coprime e (2 * w.im.natAbs) :=
      Nat.Coprime.coprime_dvd_left (dvd_mul_right e w.re.natAbs) hprim'
    exact (Nat.Coprime.coprime_dvd_right (dvd_mul_left w.im.natAbs 2) hse2).symm

theorem ratioSym_scalePt_factor (e d' : ℕ) (he : 1 ≤ e) (hd' : 1 ≤ d') (w1 w2 : GaussianInt)
    (hc1 : Nat.Coprime w1.re.natAbs d') (hc2 : Nat.Coprime w2.re.natAbs d')
    (hprim : Nat.Coprime ((e : ℤ) * w1.re).natAbs (2 * w1.im.natAbs))
    (h4 : 4 * d' ∣ Work.FIPlan.absDelta w1 w2) :
    Work.FIArea7.ratioSym (Work.FIArea4.scalePt e w1) (Work.FIArea4.scalePt e w2) (e * d')
      = jacobiSym ((e : ℤ) ^ 2
          + ((((w1.im : ZMod (4 * d')) * ((w1.re : ZMod (4 * d')))⁻¹).val : ℤ)) ^ 2) d'
        * jacobiSym ((star (Work.FIArea4.scalePt e w1) * Work.FIArea4.scalePt e w2).re) (e * d') := by
  haveI : NeZero (e * d') := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  obtain ⟨hc, hs⟩ := coprime_scalePt_units e d' w1 hc1 hprim
  -- **(i)** the twist `(|z₁|² | e·d')` is the class factor `(e²+a²|d')`
  have hJ := jacobiSym_gnorm_scalePt_eq_classFactor e d' he hd' w1 hc hs
  by_cases hcop : Nat.Coprime (Work.FIPlan.gnorm (Work.FIArea4.scalePt e w1)) (e * d')
  · -- **(ii-A)** the `|z₁|²` is a unit, so `ratioSym` and `J(Re)` differ by it
    have htw := Work.FIArea7.jacobiSym_re_eq_ratioSym_mul (Work.FIArea4.scalePt e w1)
      (Work.FIArea4.scalePt e w2) (d := e * d') hcop
    have hsq : jacobiSym ((Work.FIPlan.gnorm (Work.FIArea4.scalePt e w1) : ℤ)) (e * d') ^ 2 = 1 := by
      apply jacobiSym.sq_one
      rw [Int.gcd_natCast_natCast]
      exact hcop
    have hsq' : jacobiSym ((Work.FIPlan.gnorm (Work.FIArea4.scalePt e w1) : ℤ)) (e * d')
        * jacobiSym ((Work.FIPlan.gnorm (Work.FIArea4.scalePt e w1) : ℤ)) (e * d') = 1 := by
      rw [← pow_two]; exact hsq
    have key : Work.FIArea7.ratioSym (Work.FIArea4.scalePt e w1) (Work.FIArea4.scalePt e w2)
          (e * d')
        = jacobiSym (star (Work.FIArea4.scalePt e w1) * Work.FIArea4.scalePt e w2).re (e * d')
          * jacobiSym ((Work.FIPlan.gnorm (Work.FIArea4.scalePt e w1) : ℤ)) (e * d') := by
      calc Work.FIArea7.ratioSym (Work.FIArea4.scalePt e w1) (Work.FIArea4.scalePt e w2) (e * d')
          = Work.FIArea7.ratioSym (Work.FIArea4.scalePt e w1) (Work.FIArea4.scalePt e w2)
                (e * d') * 1 := (mul_one _).symm
        _ = Work.FIArea7.ratioSym (Work.FIArea4.scalePt e w1) (Work.FIArea4.scalePt e w2)
                (e * d')
              * (jacobiSym ((Work.FIPlan.gnorm (Work.FIArea4.scalePt e w1) : ℤ)) (e * d')
                 * jacobiSym ((Work.FIPlan.gnorm (Work.FIArea4.scalePt e w1) : ℤ)) (e * d')) := by
              rw [hsq']
        _ = (Work.FIArea7.ratioSym (Work.FIArea4.scalePt e w1) (Work.FIArea4.scalePt e w2)
                (e * d')
              * jacobiSym ((Work.FIPlan.gnorm (Work.FIArea4.scalePt e w1) : ℤ)) (e * d'))
              * jacobiSym ((Work.FIPlan.gnorm (Work.FIArea4.scalePt e w1) : ℤ)) (e * d') := by
              ring
        _ = jacobiSym (star (Work.FIArea4.scalePt e w1) * Work.FIArea4.scalePt e w2).re (e * d')
              * jacobiSym ((Work.FIPlan.gnorm (Work.FIArea4.scalePt e w1) : ℤ)) (e * d') := by
              rw [htw.symm]
    rw [key, hJ]
    exact mul_comm _ _
  · -- **(ii-B)** `|z₁|²` is not a unit: both sides vanish
    have hL := ratioSym_scalePt_eq_zero_of_not_coprime e d' he hd' w1 w2 hc1 hprim h4 hcop
    have hzero : jacobiSym ((Work.FIPlan.gnorm (Work.FIArea4.scalePt e w1) : ℤ)) (e * d') = 0 := by
      rw [jacobiSym.eq_zero_iff_not_coprime]
      rw [Int.gcd_natCast_natCast]
      exact hcop
    rw [hL, ← hJ, hzero, zero_mul]

end Work.FIArea4.A6psi
