import Mathlib

namespace Work.DSTR.M110

/-- Arithmetic core (lifting-the-exponent in `Nat.factorization` language): for an odd prime `q`
and `2 ≤ x`, the largest power of `q` dividing `x ^ q - 1`, multiplied by `x - 1`, is still
strictly smaller than `x ^ q - 1`. -/
theorem factorizationPowMulLt {q x : ℕ} (hq : q.Prime) (hqodd : Odd q) (hx : 2 ≤ x) :
    q ^ ((x ^ q - 1).factorization q) * (x - 1) < x ^ q - 1 := by
  have hx1 : 1 ≤ x := by omega
  have hxd1 : x - 1 ≠ 0 := by omega
  have hxd1pos : 0 < x - 1 := by omega
  have hq2 : 2 ≤ q := hq.two_le
  have hq3 : 3 ≤ q := by
    obtain ⟨m, hm⟩ := hqodd
    omega
  by_cases hdvd : q ∣ x - 1
  · -- Case `q ∣ x - 1`: LTE gives `v_q(x^q - 1) = v_q(x - 1) + 1`.
    have hqnx : ¬ q ∣ x := by
      intro h
      have h1 : q ∣ x - (x - 1) := Nat.dvd_sub h hdvd
      have h2 : x - (x - 1) = 1 := by omega
      rw [h2] at h1
      exact hq.not_dvd_one h1
    have hFac : emultiplicity q (x - 1) = ((x - 1).factorization q : ℕ∞) := by
      rw [emultiplicity_eq_coe]
      refine ⟨?_, ?_⟩
      · exact (Nat.Prime.pow_dvd_iff_le_factorization hq hxd1).mpr le_rfl
      · intro h
        exact Nat.not_succ_le_self ((x - 1).factorization q)
          ((Nat.Prime.pow_dvd_iff_le_factorization hq hxd1).mp h)
    have hqq : emultiplicity q q = ((1 : ℕ) : ℕ∞) := by
      rw [emultiplicity_eq_coe]
      refine ⟨by simpa using (dvd_refl q), ?_⟩
      intro h
      have h2 : q * q ≤ q := by simpa [pow_two] using Nat.le_of_dvd hq.pos h
      have h3 : 2 * q ≤ q := le_trans (Nat.mul_le_mul_right q hq.two_le) h2
      omega
    have hlte := Nat.emultiplicity_pow_sub_pow (p := q) hq hqodd hdvd hqnx q
    rw [one_pow, hFac, hqq] at hlte
    have hlte' : emultiplicity q (x ^ q - 1) = (((x - 1).factorization q + 1 : ℕ) : ℕ∞) := by
      rw [hlte, Nat.cast_add, Nat.cast_one]
    have hne : x ^ q - 1 ≠ 0 := by
      have h2 : x ^ 1 ≤ x ^ q := Nat.pow_le_pow_right (by omega : 0 < x) hq.one_lt.le
      simp only [pow_one] at h2
      omega
    have hfac : (x ^ q - 1).factorization q = (x - 1).factorization q + 1 := by
      obtain ⟨h1, h2⟩ := emultiplicity_eq_coe.mp hlte'
      refine le_antisymm ?_ ?_
      · by_contra hlt
        rw [not_le] at hlt
        exact h2 ((Nat.Prime.pow_dvd_iff_le_factorization hq hne).mpr (Nat.succ_le_of_lt hlt))
      · exact (Nat.Prime.pow_dvd_iff_le_factorization hq hne).mp h1
    rw [hfac]
    have hs : q ^ ((x - 1).factorization q) ∣ x - 1 := by
      rw [Nat.factorization_def (x - 1) hq]
      exact pow_padicValNat_dvd
    have hsle : q ^ ((x - 1).factorization q) ≤ x - 1 := Nat.le_of_dvd hxd1pos hs
    have hqle : q ≤ x - 1 := Nat.le_of_dvd hxd1pos hdvd
    have key : q ^ ((x - 1).factorization q + 1) * (x - 1) ≤ (x - 1) ^ 3 := by
      calc q ^ ((x - 1).factorization q + 1) * (x - 1)
          = (q ^ ((x - 1).factorization q) * q) * (x - 1) := by rw [pow_succ]
        _ ≤ ((x - 1) * q) * (x - 1) :=
              Nat.mul_le_mul_right (x - 1) (Nat.mul_le_mul_right q hsle)
        _ ≤ ((x - 1) * (x - 1)) * (x - 1) :=
              Nat.mul_le_mul_right (x - 1) (Nat.mul_le_mul_left (x - 1) hqle)
        _ = (x - 1) ^ 3 := by ring
    have key2 : (x - 1) ^ 3 < x ^ 3 - 1 := by
      have hxx : x ^ 3 = (x - 1) ^ 3 + 3 * (x - 1) ^ 2 + 3 * (x - 1) + 1 := by
        conv_lhs => rw [← Nat.sub_add_cancel hx1]
        ring
      rw [hxx]
      omega
    have hx3q : x ^ 3 - 1 ≤ x ^ q - 1 :=
      Nat.sub_le_sub_right (Nat.pow_le_pow_right (by omega : 0 < x) hq3) 1
    exact lt_of_lt_of_le (lt_of_le_of_lt key key2) hx3q
  · -- Case `¬ q ∣ x - 1`: Fermat gives `v_q(x^q - 1) = 0`.
    have hxle : x ≤ x ^ q := by
      have h2 : x ^ 1 ≤ x ^ q := Nat.pow_le_pow_right (by omega : 0 < x) hq.one_lt.le
      simpa using h2
    have hferm : q ∣ x ^ q - x := by
      have h := Int.prime_dvd_pow_self_sub hq (x : ℤ)
      rw [← Int.natCast_pow, ← Int.natCast_sub hxle] at h
      exact Int.natCast_dvd_natCast.mp h
    have hndvd : ¬ q ∣ x ^ q - 1 := by
      intro hcon
      have h1 : q ∣ (x ^ q - 1) - (x ^ q - x) := Nat.dvd_sub hcon hferm
      have h2 : (x ^ q - 1) - (x ^ q - x) = x - 1 := by omega
      rw [h2] at h1
      exact hdvd h1
    have hfac0 : (x ^ q - 1).factorization q = 0 := by
      rw [Nat.factorization_eq_zero_iff]
      exact Or.inr (Or.inl hndvd)
    rw [hfac0, pow_zero, one_mul]
    have hlt : x < x ^ q := by
      simpa using Nat.pow_lt_pow_right (by omega : 1 < x) (by omega : 1 < q)
    omega

/-- For `1 ≤ k`, if `k / i.gcd k` is odd then the coprime part `p ^ i + 1` of `p ^ (2 * i) - 1`
meets `p ^ k - 1` only inside `p ^ (i.gcd k) - 1`. -/
theorem gcdPowSubOnePowAddOneDvd {p k i : ℕ} (hk : 1 ≤ k) (hodd : Odd (k / i.gcd k)) :
    (p ^ k - 1).gcd (p ^ i + 1) ∣ p ^ (i.gcd k) - 1 := by
  set e := i.gcd k with he
  have hke : e ∣ k := by rw [he]; exact Nat.gcd_dvd_right i k
  have hie : e ∣ i := by rw [he]; exact Nat.gcd_dvd_left i k
  have hepos : 0 < e := by
    rw [he]
    exact Nat.gcd_pos_of_pos_right i (by omega : 0 < k)
  have hdvd1 : p ^ i + 1 ∣ p ^ (2 * i) - 1 := by
    have h2 : p ^ (2 * i) = (p ^ i) ^ 2 := by rw [mul_comm 2 i, pow_mul]
    have h3 : (p ^ i) ^ 2 - 1 = (p ^ i + 1) * (p ^ i - 1) := by
      rw [← Nat.sq_sub_sq (p ^ i) 1, one_pow]
    rw [h2, h3]
    exact dvd_mul_right _ _
  have h1 : (p ^ k - 1).gcd (p ^ i + 1) ∣ (p ^ k - 1).gcd (p ^ (2 * i) - 1) :=
    Nat.dvd_gcd (Nat.gcd_dvd_left _ _) ((Nat.gcd_dvd_right _ _).trans hdvd1)
  have h2 : (p ^ k - 1).gcd (p ^ (2 * i) - 1) = p ^ (k.gcd (2 * i)) - 1 :=
    Nat.pow_sub_one_gcd_pow_sub_one p k (2 * i)
  have hcop : (k / e).Coprime (i / e) := by
    rw [Nat.coprime_iff_gcd_eq_one]
    have hstep : (k / e).gcd (i / e) * e = 1 * e := by
      rw [← Nat.gcd_mul_right (k / e) e (i / e), Nat.div_mul_cancel hke,
        Nat.div_mul_cancel hie, Nat.gcd_comm, one_mul]
    exact Nat.mul_right_cancel hepos hstep
  have hinner : (k / e).gcd (2 * (i / e)) = 1 :=
    Nat.Coprime.gcd_eq_one (hodd.coprime_two_right.mul_right hcop)
  have hkey : k.gcd (2 * i) = e := by
    have hp2 : e * (2 * (i / e)) = 2 * i := by
      calc e * (2 * (i / e)) = 2 * (e * (i / e)) := by ring
        _ = 2 * i := by rw [Nat.mul_div_cancel' hie]
    have hq' : e * (k / e) = k := Nat.mul_div_cancel' hke
    rw [← hq', ← hp2, Nat.gcd_mul_left, hinner, mul_one]
  rw [h2, hkey] at h1
  exact h1

theorem arithOrbitSubOne (p k i : ℕ) (hp : p.Prime) (hodd : Odd p) (h1 : 1 ≤ i) (h2 : i < k)
    (hrp : Nat.Prime (k / i.gcd k)) (hro : Odd (k / i.gcd k)) :
    (p ^ k - 1) / (p ^ k - 1).gcd (p ^ i - 1) >
        (k / i.gcd k) ^ ((p ^ k - 1).factorization (k / i.gcd k)) ∧
      (p ^ k - 1) / (p ^ k - 1).gcd (p ^ i + 1) >
        (k / i.gcd k) ^ ((p ^ k - 1).factorization (k / i.gcd k)) := by
  set d := i.gcd k with hd
  set q := k / d with hq
  set x := p ^ d with hx
  have hk1 : 1 ≤ k := by omega
  have hdk : d * q = k := by
    rw [hq, hd]
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_right i k)
  have hxq : x ^ q = p ^ k := by
    rw [hx, ← hdk, pow_mul]
  have hkp : 2 ≤ p := hp.two_le
  have hd0 : 0 < d := by
    rw [hd]
    exact Nat.gcd_pos_of_pos_left k (by omega : 0 < i)
  have hd1 : 1 ≤ d := by omega
  have hx2 : 2 ≤ x := by
    rw [hx]
    calc 2 ≤ p ^ 1 := by simpa using hkp
      _ ≤ p ^ d := Nat.pow_le_pow_right (by omega : 0 < p) hd1
  have hDpos : 0 < x - 1 := by omega
  have hkey : q ^ ((x ^ q - 1).factorization q) * (x - 1) < x ^ q - 1 :=
    factorizationPowMulLt hrp hro hx2
  have hstep : q ^ ((x ^ q - 1).factorization q) < (x ^ q - 1) / (x - 1) := by
    have hDvd : x - 1 ∣ x ^ q - 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      have h := Nat.pow_sub_one_mod_pow_sub_one x 1 q
      rw [pow_one, Nat.mod_one, pow_zero, tsub_self] at h
      exact h
    have hMD : (x ^ q - 1) / (x - 1) * (x - 1) = x ^ q - 1 := Nat.div_mul_cancel hDvd
    have h2' : q ^ ((x ^ q - 1).factorization q) * (x - 1)
        < (x ^ q - 1) / (x - 1) * (x - 1) := by
      rw [hMD]
      exact hkey
    exact (Nat.mul_lt_mul_right hDpos).mp h2'
  have hgoal1 : q ^ ((p ^ k - 1).factorization q) < (p ^ k - 1) / (x - 1) := by
    rw [← hxq]
    exact hstep
  have hgi : k.gcd i = d := by rw [Nat.gcd_comm, hd]
  have hg1 : (p ^ k - 1).gcd (p ^ i - 1) = x - 1 := by
    rw [Nat.pow_sub_one_gcd_pow_sub_one p k i, hgi, hx]
  have hg2dvd : (p ^ k - 1).gcd (p ^ i + 1) ∣ x - 1 := by
    have hh := gcdPowSubOnePowAddOneDvd (p := p) (k := k) (i := i) hk1 hro
    rw [hx, hd]
    exact hh
  have hg2pos : 0 < (p ^ k - 1).gcd (p ^ i + 1) := by
    have hN : 0 < p ^ k - 1 := by
      have hpk : 2 ≤ p ^ k := by
        calc 2 ≤ p ^ 1 := by simpa using hkp
          _ ≤ p ^ k := Nat.pow_le_pow_right (by omega : 0 < p) hk1
      omega
    exact Nat.gcd_pos_of_pos_left _ hN
  have hg2le : (p ^ k - 1).gcd (p ^ i + 1) ≤ x - 1 := Nat.le_of_dvd hDpos hg2dvd
  have hmono : (p ^ k - 1) / (x - 1) ≤ (p ^ k - 1) / (p ^ k - 1).gcd (p ^ i + 1) :=
    Nat.div_le_div_left hg2le hg2pos
  constructor
  · rw [hg1]
    exact hgoal1
  · exact lt_of_lt_of_le hgoal1 hmono

end Work.DSTR.M110
