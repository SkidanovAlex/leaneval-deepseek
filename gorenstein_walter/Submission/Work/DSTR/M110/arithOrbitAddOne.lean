import Mathlib
import Submission.Work.DSTR.M110.gcdPowAddOneDvd

namespace Work.DSTR.M110

/-- LTE for the `+`-case, expressed with `padicValNat`: for an odd prime `d` dividing `y + 1`,
the `d`-adic valuation of `y ^ d + 1` is one more than the `d`-adic valuation of `y + 1`.
This is the special case `x = y`, `z = 1`, `n = d` of `padicValNat.pow_add_pow`. -/
private lemma padicValNat_pow_self_add_one (y d : ℕ) (hd : d.Prime) (hdo : Odd d)
    (h : d ∣ y + 1) :
    padicValNat d (y ^ d + 1) = padicValNat d (y + 1) + 1 := by
  haveI : Fact d.Prime := ⟨hd⟩
  have hdy : ¬ d ∣ y := by
    intro hdy
    have h1 : d ∣ 1 := by
      have := Nat.dvd_sub h hdy
      rwa [show y + 1 - y = 1 by omega] at this
    exact hd.not_dvd_one h1
  have hkey : padicValNat d (y ^ d + 1 ^ d) = padicValNat d (y + 1) + padicValNat d d :=
    padicValNat.pow_add_pow (x := y) (y := 1) (n := d) hdo h hdy hdo
  rw [one_pow, padicValNat_self] at hkey
  exact hkey

/-- Fermat's little theorem in the form needed here: for prime `d`,
`d ∣ y ^ d + 1 ↔ d ∣ y + 1`. -/
private lemma dvd_pow_self_add_one_iff (y d : ℕ) (hd : d.Prime) :
    d ∣ y ^ d + 1 ↔ d ∣ y + 1 := by
  haveI : Fact d.Prime := ⟨hd⟩
  have hf : y ^ d ≡ y [MOD d] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    rw [ZMod.pow_card]
  have h1 : y ^ d + 1 ≡ y + 1 [MOD d] := hf.add_right 1
  simp only [← Nat.modEq_zero_iff_dvd]
  constructor
  · intro h; exact h1.symm.trans h
  · intro h; exact h1.trans h

/-- Elementary inequality: for `3 ≤ d` and `2 * d ≤ y + 1` we have `y ^ d + 1 > d * (y+1)^2`. -/
private lemma pow_add_one_gt_mul_sq (y d : ℕ) (hd : 3 ≤ d) (hy : 2 * d ≤ y + 1) :
    y ^ d + 1 > d * (y + 1) ^ 2 := by
  have hy5 : 5 ≤ y := by omega
  have hpow : y ^ 3 ≤ y ^ d := Nat.pow_le_pow_right (by omega : 1 ≤ y) hd
  have h2 : 2 * (d * (y + 1) ^ 2) ≤ (y + 1) ^ 3 := by
    calc 2 * (d * (y + 1) ^ 2) = (2 * d) * (y + 1) ^ 2 := by ring
      _ ≤ (y + 1) * (y + 1) ^ 2 := Nat.mul_le_mul_right _ hy
      _ = (y + 1) ^ 3 := by ring
  have h3 : (y + 1) ^ 3 < 2 * (y ^ 3 + 1) := by nlinarith [hy5, sq_nonneg (y : ℤ)]
  have key : d * (y + 1) ^ 2 < y ^ 3 + 1 := by omega
  omega

/-- **Arithmetic core.**  For an odd prime `d` and an odd number `A ≥ 3` we have
`(A^d + 1) / (A + 1) > d ^ v_d(A^d + 1)`.  The proof splits on whether `d ∣ A + 1`:
if not then `d ∤ A^d + 1` (Fermat) so the right hand side is `1`; if yes then LTE gives
`v_d(A^d+1) = v_d(A+1) + 1 ≤ log_d(d(A+1))` and `A^d + 1 > d (A+1)^2`. -/
private lemma div_pow_add_one_gt (A d : ℕ) (hd : d.Prime) (hdo : Odd d) (hAodd : Odd A)
    (hA : 3 ≤ A) :
    ((A) ^ d + 1) / (A + 1) > d ^ padicValNat d (A ^ d + 1) := by
  have hd3 : 3 ≤ d := by
    have h2 := hd.two_le
    have hod : Odd d := hdo
    rw [Nat.odd_iff] at hod
    omega
  have hAdvd : A + 1 ∣ A ^ d + 1 := by
    have := Odd.nat_add_dvd_pow_add_pow A 1 hdo
    simpa using this
  rw [gt_iff_lt, Nat.lt_div_iff_mul_lt' hAdvd]
  by_cases hcase : d ∣ A + 1
  · have hLTE := padicValNat_pow_self_add_one A d hd hdo hcase
    have htle : d ^ padicValNat d (A + 1) ≤ A + 1 :=
      Nat.le_of_dvd (by positivity) pow_padicValNat_dvd
    rw [hLTE, pow_succ]
    have hbound : d * (A + 1) ^ 2 < A ^ d + 1 :=
      pow_add_one_gt_mul_sq A d hd3 (by
        have h2dvd : 2 * d ∣ A + 1 :=
          Nat.Coprime.mul_dvd_of_dvd_of_dvd
            ((Nat.coprime_two_right.mpr hdo).symm)
            (even_iff_two_dvd.mp hAodd.add_one) hcase
        exact Nat.le_of_dvd (by positivity) h2dvd)
    calc (A + 1) * (d ^ padicValNat d (A + 1) * d)
        = d * ((A + 1) * d ^ padicValNat d (A + 1)) := by ring
      _ ≤ d * ((A + 1) * (A + 1)) :=
            Nat.mul_le_mul_left d (Nat.mul_le_mul_left (A + 1) htle)
      _ = d * (A + 1) ^ 2 := by ring
      _ < A ^ d + 1 := hbound
  · have hnd : ¬ d ∣ A ^ d + 1 := (dvd_pow_self_add_one_iff A d hd).not.mpr hcase
    rw [padicValNat.eq_zero_of_not_dvd hnd]
    simp only [pow_zero, mul_one]
    have hsq : A + 1 ≤ A ^ 2 := by nlinarith [hA]
    have h2 : A ^ 2 ≤ A ^ d := Nat.pow_le_pow_right (by omega) (by omega : 2 ≤ d)
    omega

theorem arithOrbitAddOne (p k i : ℕ) (hp : p.Prime) (hodd : Odd p) (h1 : 1 ≤ i) (h2 : i < k)
    (hrp : Nat.Prime (k / i.gcd k)) (hro : Odd (k / i.gcd k)) :
    (p ^ k + 1) / (p ^ k + 1).gcd (p ^ i - 1) >
        (k / i.gcd k) ^ ((p ^ k + 1).factorization (k / i.gcd k)) ∧
      (p ^ k + 1) / (p ^ k + 1).gcd (p ^ i + 1) >
        (k / i.gcd k) ^ ((p ^ k + 1).factorization (k / i.gcd k)) := by
  set g : ℕ := i.gcd k with hg
  set d : ℕ := k / g with hd
  have hro' : Odd (k / i.gcd k) := by rw [← hg, ← hd]; exact hro
  obtain ⟨hG1, hG2⟩ := gcdPowAddOneDvd p k i hro'
  rw [← hg] at hG1 hG2
  have hp3 : 3 ≤ p := by
    have h2' := hp.two_le
    have hod : Odd p := hodd
    rw [Nat.odd_iff] at hod
    omega
  have hgk : g ∣ k := by rw [hg]; exact Nat.gcd_dvd_right i k
  have hkgd : g * d = k := by rw [hd]; exact Nat.mul_div_cancel' hgk
  have hgpos : 0 < g := by rw [hg]; exact Nat.gcd_pos_of_pos_left k (by omega)
  have hpg3 : 3 ≤ p ^ g := le_trans hp3 (Nat.le_self_pow hgpos.ne' p)
  have hm_eq : p ^ k + 1 = (p ^ g) ^ d + 1 := by rw [← hkgd, Nat.pow_mul]
  have hfac : ((p ^ g) ^ d + 1).factorization d = padicValNat d ((p ^ g) ^ d + 1) :=
    Nat.factorization_def _ hrp
  have hcore := div_pow_add_one_gt (p ^ g) d hrp hro hodd.pow hpg3
  have hpipos : 0 < p ^ i - 1 := by
    have : 2 ≤ p ^ i := le_trans hp.two_le (Nat.le_self_pow (by omega : i ≠ 0) p)
    omega
  have hG1pos : 0 < (p ^ k + 1).gcd (p ^ i - 1) :=
    Nat.gcd_pos_of_pos_right _ hpipos
  have hG2pos : 0 < (p ^ k + 1).gcd (p ^ i + 1) :=
    Nat.gcd_pos_of_pos_right _ (by positivity)
  have hQ : d ^ ((p ^ k + 1).factorization d) < (p ^ k + 1) / (p ^ g + 1) := by
    rw [hm_eq, hfac]
    exact hcore
  refine ⟨?_, ?_⟩
  · have hle : (p ^ k + 1) / (p ^ g + 1) ≤ (p ^ k + 1) / ((p ^ k + 1).gcd (p ^ i - 1)) :=
      Nat.div_le_div_left (Nat.le_of_dvd (by positivity) hG1) hG1pos
    omega
  · have hle : (p ^ k + 1) / (p ^ g + 1) ≤ (p ^ k + 1) / ((p ^ k + 1).gcd (p ^ i + 1)) :=
      Nat.div_le_div_left (Nat.le_of_dvd (by positivity) hG2) hG2pos
    omega

end Work.DSTR.M110
