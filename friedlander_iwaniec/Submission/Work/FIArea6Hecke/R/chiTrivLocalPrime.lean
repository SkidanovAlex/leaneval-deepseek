import Mathlib
import Submission.Work.FIArea6Hecke.R.logDerivBoundAux
import Submission.Work.FIArea5.S16Hecke.heckeLam_localRec
import Submission.Work.FIArea5.S16Hecke.zfrAux
import Submission.Work.FIArea6Hecke.area5_6_of_S16Core
import Submission.Work.FIArea6Hecke.R.PrincipalCharAux
import Submission.Work.FIArea6Hecke.ZFRDefs
import Submission.Work.FIArea5.S16Hecke.heckeLam_prime_eq_zero_of_ne_one_mod_four
import Submission.Work.FIArea5.S16Hecke.splitPrimaryClass
import Submission.Work.FIArea5.S16Hecke.inertPrimaryClass

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open Work.FIPlan
open Work.FIArea5.S16Hecke
open Classical

attribute [local instance] Classical.propDecidable

open scoped BigOperators

noncomputable section

/-- `chiTriv d` is literally the principal strict character `principalStrict d`. -/
lemma chiTriv_eq_principalStrict (d : ℕ) :
    chiTriv d = Work.FIArea6Hecke.principalStrict d := by
  funext z
  by_cases h : Work.FIArea5.S16Hecke.IsUnitMod4d d z <;>
    simp [chiTriv, Work.FIArea6Hecke.principalStrict, h]

/-- For weight `0` the Größencharacter `ψ` (16.16) is the character itself. -/
lemma psi_zero (chi : GaussianInt → ℂ) (z : GaussianInt) :
    Work.FIArea5.S16Hecke.psi chi 0 z = chi z := by
  simp [Work.FIArea5.S16Hecke.psi]

/-- **Arithmetic input.**  If a Gaussian integer has norm `p ^ ν`, `ν > 0`, with `p` a rational
prime not dividing `4d`, then it is a unit modulo `4d` — equivalently, its norm is coprime to
`4d`. -/
lemma isUnitMod4d_of_gnorm_eq_prime_pow {d : ℕ} (hd : 1 ≤ d) {p : ℕ} (hp : p.Prime)
    (hpd : ¬ p ∣ 4 * d) {z : GaussianInt} {ν : ℕ} (hν : 0 < ν)
    (hgn : Work.FIPlan.gnorm z = p ^ ν) :
    Work.FIArea5.S16Hecke.IsUnitMod4d d z := by
  haveI : NeZero (4 * d) := ⟨by omega⟩
  rw [Work.FIArea6Hecke.GaussUnit.isUnitMod4d_iff_coprime (d := d) z, hgn]
  exact (Nat.coprime_pow_left_iff hν p (4 * d)).mpr (hp.coprime_iff_not_dvd.mpr hpd)

theorem chiTrivLocalPrime {d : ℕ} (hd : 1 ≤ d) {p : ℕ} (hp : p.Prime) (hpd : ¬ p ∣ 4 * d) :
    Work.FIArea5.S16Hecke.heckeLam (Work.FIArea6Hecke.R.chiTriv d) 0 p = 1 + Work.FIArea6Hecke.R.chi4fun p ∧
    Work.FIArea5.S16Hecke.heckeLam (Work.FIArea6Hecke.R.chiTriv d) 0 (p ^ 2) = 2 + Work.FIArea6Hecke.R.chi4fun p := by
  rw [chiTriv_eq_principalStrict d]
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hpd (dvd_mul_of_dvd_left (by norm_num : (2 : ℕ) ∣ 4) d)
  by_cases h1 : p % 4 = 1
  · -- split prime `p ≡ 1 (4)`
    obtain ⟨π, π', hπp, hπp', hgπ, hgπ', -, -, -, hclass⟩ := splitPrimaryClass p hp h1
    have hπu : Work.FIArea6Hecke.principalStrict d π = 1 :=
      Work.FIArea6Hecke.principalStrict_of_unit
        (isUnitMod4d_of_gnorm_eq_prime_pow hd hp hpd (z := π) (ν := 1) (by norm_num)
          (by simpa using hgπ))
    have hπ'u : Work.FIArea6Hecke.principalStrict d π' = 1 :=
      Work.FIArea6Hecke.principalStrict_of_unit
        (isUnitMod4d_of_gnorm_eq_prime_pow hd hp hpd (z := π') (ν := 1) (by norm_num)
          (by simpa using hgπ'))
    have hx : Work.FIArea5.S16Hecke.psi (Work.FIArea6Hecke.principalStrict d) 0 π = 1 := by
      rw [psi_zero]; exact hπu
    have hy : Work.FIArea5.S16Hecke.psi (Work.FIArea6Hecke.principalStrict d) 0 π' = 1 := by
      rw [psi_zero]; exact hπ'u
    have hchi : chi4fun p = 1 := chi4fun_eq_one_of_mod_four h1
    have hA1 := heckeLam_splitSum (Work.FIArea6Hecke.principalStrict d) 0 p hp.pos
      (Work.FIArea6Hecke.principalStrict_mul d) (Work.FIArea6Hecke.principalStrict_one d)
      π π' hπp hπp' hgπ hgπ' hclass 1
    have hA2 := heckeLam_splitSum (Work.FIArea6Hecke.principalStrict d) 0 p hp.pos
      (Work.FIArea6Hecke.principalStrict_mul d) (Work.FIArea6Hecke.principalStrict_one d)
      π π' hπp hπp' hgπ hgπ' hclass 2
    simp only [pow_one] at hA1
    constructor
    · rw [hchi, hA1, geo_one, hx, hy]
    · rw [hchi, hA2, geo_two, hx, hy]
      norm_num
  · -- inert prime `p ≡ 3 (4)`
    have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
    have h3 : p % 4 = 3 := (Nat.odd_mod_four_iff.mp hodd).resolve_left h1
    have hchi : chi4fun p = -1 := by
      rw [chi4fun_prime hp, if_neg hp2, if_neg h1]
    obtain ⟨hqp, -, hqgn, hclass⟩ := inertPrimaryClass p hp h3
    have hqu : Work.FIArea6Hecke.principalStrict d (-(p : GaussianInt)) = 1 :=
      Work.FIArea6Hecke.principalStrict_of_unit
        (isUnitMod4d_of_gnorm_eq_prime_pow hd hp hpd (z := -(p : GaussianInt)) (ν := 2)
          (by norm_num) (by rw [gnorm_neg_nat_prime]))
    have hqpsi : Work.FIArea5.S16Hecke.psi (Work.FIArea6Hecke.principalStrict d) 0
        (-(p : GaussianInt)) = 1 := by
      rw [psi_zero]; exact hqu
    have hz : Work.FIArea5.S16Hecke.heckeLam (Work.FIArea6Hecke.principalStrict d) 0 p = 0 :=
      heckeLam_prime_eq_zero_of_ne_one_mod_four hp h1
    have hA := heckeLam_inertSumEven (Work.FIArea6Hecke.principalStrict d) 0 p hp.pos
      (Work.FIArea6Hecke.principalStrict_mul d) (Work.FIArea6Hecke.principalStrict_one d)
      (-(p : GaussianInt)) hqp hqgn hclass 1
    simp only [mul_one] at hA
    constructor
    · rw [hchi, hz]; norm_num
    · rw [hchi, hA, pow_one, hqpsi]; norm_num

end

end Work.FIArea6Hecke.R
