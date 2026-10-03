import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.VfdDefs
import Submission.Work.FIArea4.A4varbounds
import Submission.Work.FIArea4.Vflip.coprime_pair_iff_coprime_gcd

namespace Work.FIArea4.Vflip.Vfd

open Work.FIArea4.Vflip (pairC pairR pairAbs)

theorem coprime_pairR_oddPart_m {r1 s1 r2 s2 m q' : ℕ}
    (h1 : 0 < r1) (h2 : 0 < r2)
    (hcop1 : Nat.Coprime r1 (2*s1)) (hcop2 : Nat.Coprime r2 (2*s2))
    (hmc : m ∣ Work.FIArea4.Vflip.pairC r1 r2)
    (hcond : m*q' ∣ Work.FIArea4.Vflip.pairAbs r1 r2 s1 s2) :
    Nat.Coprime (Work.FIArea4.Vflip.pairR r1 r2) (Work.FIPlan.oddPart m)
      ∧ Nat.Coprime (Work.FIArea4.Vflip.pairR r2 r1) (Work.FIPlan.oddPart m) := by
  have hgpos : 0 < Nat.gcd r1 r2 := Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left r1 r2) h1
  have ho_dvd_m : Work.FIPlan.oddPart m ∣ m := by
    unfold Work.FIPlan.oddPart
    exact Nat.div_dvd_of_dvd (Nat.ordProj_dvd m 2)
  have ho_dvd_abs : Work.FIPlan.oddPart m ∣
      ((pairR r1 r2 : ℤ) * (s2 : ℤ) - (pairR r2 r1 : ℤ) * (s1 : ℤ)).natAbs := by
    have h : Work.FIPlan.oddPart m ∣ pairAbs r1 r2 s1 s2 :=
      dvd_trans (dvd_trans ho_dvd_m (dvd_mul_right m q')) hcond
    rwa [pairAbs] at h
  have hcopR : Nat.Coprime (pairR r1 r2) (pairR r2 r1) := by
    simp only [pairR, pairC, Nat.gcd_comm r2 r1]
    exact Nat.coprime_div_gcd_div_gcd hgpos
  have hcs1 : Nat.Coprime (pairR r1 r2) s1 := by
    have hr : pairR r1 r2 ∣ r1 := by
      simp only [pairR, pairC]
      exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left r1 r2)
    exact Nat.Coprime.coprime_dvd_right (dvd_mul_left s1 2)
      (Nat.Coprime.coprime_dvd_left hr hcop1)
  have hcs2 : Nat.Coprime (pairR r2 r1) s2 := by
    have hr : pairR r2 r1 ∣ r2 := by
      simp only [pairR, pairC]
      exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left r2 r1)
    exact Nat.Coprime.coprime_dvd_right (dvd_mul_left s2 2)
      (Nat.Coprime.coprime_dvd_left hr hcop2)
  refine ⟨?_, ?_⟩
  · have hdiv : Nat.gcd (pairR r1 r2) (Work.FIPlan.oddPart m) ∣ pairR r2 r1 :=
      Work.FIArea4.Vflip.gcd_dvd_of hcs1 ho_dvd_abs
    have h : Nat.gcd (pairR r1 r2) (Work.FIPlan.oddPart m)
        ∣ Nat.gcd (pairR r1 r2) (pairR r2 r1) :=
      Nat.dvd_gcd (Nat.gcd_dvd_left _ _) hdiv
    rw [Nat.coprime_iff_gcd_eq_one.mp hcopR] at h
    exact Nat.coprime_iff_gcd_eq_one.mpr (Nat.dvd_one.mp h)
  · have ho_dvd_abs' : Work.FIPlan.oddPart m ∣
        ((pairR r2 r1 : ℤ) * (s1 : ℤ) - (pairR r1 r2 : ℤ) * (s2 : ℤ)).natAbs := by
      have h : ((pairR r1 r2 : ℤ) * (s2 : ℤ) - (pairR r2 r1 : ℤ) * (s1 : ℤ))
          = -((pairR r2 r1 : ℤ) * (s1 : ℤ) - (pairR r1 r2 : ℤ) * (s2 : ℤ)) := by ring
      rw [h, Int.natAbs_neg] at ho_dvd_abs
      exact ho_dvd_abs
    have hdiv : Nat.gcd (pairR r2 r1) (Work.FIPlan.oddPart m) ∣ pairR r1 r2 :=
      Work.FIArea4.Vflip.gcd_dvd_of hcs2 ho_dvd_abs'
    have h : Nat.gcd (pairR r2 r1) (Work.FIPlan.oddPart m)
        ∣ Nat.gcd (pairR r2 r1) (pairR r1 r2) :=
      Nat.dvd_gcd (Nat.gcd_dvd_left _ _) hdiv
    rw [Nat.coprime_iff_gcd_eq_one.mp hcopR.symm] at h
    exact Nat.coprime_iff_gcd_eq_one.mpr (Nat.dvd_one.mp h)

end Work.FIArea4.Vflip.Vfd
