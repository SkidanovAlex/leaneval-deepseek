import Mathlib
import Submission.Work.DSTR.M110.gcdPowAddOneDvd
import Submission.Work.DSTR.M110.powAddOneFactorizationOfDvd
import Submission.Work.DSTR.M110.powAddOneNotDvdOfNotDvdSucc
import Submission.Work.DSTR.M110.powAddOneQuotientGtMul
import Submission.Work.DSTR.M110.quotientPowAddOneOdd

/-!
# `Work.DSTR.M110.arithAddOneOddAux`

The "add one" arithmetic estimate of Gorenstein–Walter in its odd-part form.

Writing `g = gcd i k`, `q = k / g`, `A = p ^ g`, one has `p ^ k = A ^ q`, `p ^ i = A ^ (i / g)`, and
the goal is the pair of estimates

`m / gcd(m, p^i - 1) > q ^ (v_q m)`,  `m / gcd(m, p^i + 1) > q ^ (v_q m)`,

where `m` is the *odd part* of `p ^ k + 1 = A ^ q + 1`.

The proof is organized as follows.

* `addOneQuotientGtPowFactorization`: for odd `A ≥ 3` and an odd prime `q`, the cofactor
  `B = (A ^ q + 1) / (A + 1)` of `A + 1` in `A ^ q + 1` is strictly bigger than
  `q ^ (v_q (A ^ q + 1))`.
* `addOneOddPartDivGcdGe`: for odd `q` and any odd `d` dividing both `A + 1` and the odd part
  `m`, one has `m / d ≥ B`.
* Finally `d ∣ A + 1` for `d = gcd (m, p^i ∓ 1)`: this is `gcdPowAddOneDvd`, since
  `m ∣ p^k + 1` and `p^i ∓ 1` both divide, and `p ^ gcd i k + 1 = A + 1`.

The `q`-adic exponent appearing on the right is `v_q (A ^ q + 1) = v_q m` because `q` is odd.
-/

namespace Work.DSTR.M110

/-- **Crux arithmetic inequality.**  For odd `A ≥ 3` and an odd prime `q`, the cofactor
`(A ^ q + 1) / (A + 1)` of `A + 1` in `A ^ q + 1` is strictly larger than `q` to the
`q`-adic valuation of `A ^ q + 1`.

Either `q ∣ A + 1`, in which case LTE gives `v_q (A ^ q + 1) = v_q (A + 1) + 1 ≤ log_q (q (A+1))`
while the cofactor dominates `q (A + 1)`; or `q ∤ A + 1`, in which case Fermat forces
`q ∤ A ^ q + 1` and the estimate is `cofactor > 1 = q ^ 0`. -/
theorem addOneQuotientGtPowFactorization (A q : ℕ) (hA : Odd A) (hA3 : 3 ≤ A)
    (hq : q.Prime) (hqo : Odd q) :
    (A ^ q + 1) / (A + 1) > q ^ ((A ^ q + 1).factorization q) := by
  have hdiv : (A + 1) ∣ A ^ q + 1 := by
    simpa using Odd.nat_add_dvd_pow_add_pow A 1 hqo
  have hB1 : 1 < (A ^ q + 1) / (A + 1) := by
    have hAq : A < A ^ q := by
      have h := Nat.pow_lt_pow_right (show 1 < A by omega) hq.one_lt
      simpa using h
    have hQ : (A + 1) * ((A ^ q + 1) / (A + 1)) = A ^ q + 1 := Nat.mul_div_cancel' hdiv
    have h : (A + 1) * 1 < (A + 1) * ((A ^ q + 1) / (A + 1)) := by
      rw [mul_one, hQ]
      omega
    exact Nat.lt_of_mul_lt_mul_left h
  by_cases hdvd : q ∣ A + 1
  · have hfac := powAddOneFactorizationOfDvd A q hq hqo hdvd
    have hgt := powAddOneQuotientGtMul A q hA hA3 hq hqo hdvd
    have hle : q ^ ((A + 1).factorization q + 1) ≤ q * (A + 1) := by
      have h1 : q ^ ((A + 1).factorization q) ≤ A + 1 :=
        Nat.le_of_dvd (by omega) (Nat.ordProj_dvd (A + 1) q)
      calc q ^ ((A + 1).factorization q + 1)
          = q ^ ((A + 1).factorization q) * q := pow_succ _ _
        _ ≤ (A + 1) * q := Nat.mul_le_mul_right q h1
        _ = q * (A + 1) := by ring
    rw [hfac]
    linarith
  · have hnd := powAddOneNotDvdOfNotDvdSucc A q hq hdvd
    have hfac0 : (A ^ q + 1).factorization q = 0 := Nat.factorization_eq_zero_of_not_dvd hnd
    rw [hfac0, pow_zero]
    exact hB1

/-- **Lower bound for the odd part modulo a divisor of `A + 1`.**  For odd `q`, if `d` is an odd
divisor both of `A + 1` and of the odd part `m = (A ^ q + 1) / 2 ^ (v_2 (A ^ q + 1))`, then
`m / d` still dominates the cofactor `(A ^ q + 1) / (A + 1)`.

Indeed `m = oddpart (A + 1) * ((A ^ q + 1) / (A + 1))`, and an odd divisor of `A + 1` divides
`oddpart (A + 1)`. -/
theorem addOneOddPartDivGcdGe (A q d : ℕ) (hqo : Odd q) (hd1 : d ∣ A + 1) (hnd2 : ¬ 2 ∣ d)
    (hd3 : d ∣ (A ^ q + 1) / 2 ^ ((A ^ q + 1).factorization 2)) :
    (A ^ q + 1) / 2 ^ ((A ^ q + 1).factorization 2) / d ≥ (A ^ q + 1) / (A + 1) := by
  have hdvdq : (A + 1) ∣ A ^ q + 1 := by
    simpa using Odd.nat_add_dvd_pow_add_pow A 1 hqo
  set B := (A ^ q + 1) / (A + 1) with hB
  have hmulB : (A + 1) * B = A ^ q + 1 := Nat.mul_div_cancel' hdvdq
  have hBodd : Odd B := quotientPowAddOneOdd A q hqo
  have hBord : B / 2 ^ (B.factorization 2) = B := by
    rw [Nat.ordCompl_eq_self_iff_zero_or_not_dvd B (by norm_num : Nat.Prime 2)]
    right
    rw [← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.mpr hBodd
  have hdecomp : (A ^ q + 1) / 2 ^ ((A ^ q + 1).factorization 2) =
      ((A + 1) / 2 ^ ((A + 1).factorization 2)) * B := by
    rw [← hmulB, Nat.ordCompl_mul, hBord]
  have hA' : d ∣ (A + 1) / 2 ^ ((A + 1).factorization 2) :=
    Nat.dvd_ordCompl_of_dvd_not_dvd hd1 hnd2
  have hpos : 0 < (A + 1) / 2 ^ ((A + 1).factorization 2) := Nat.ordCompl_pos 2 (by omega)
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd1 (by omega)
  have hle : d ≤ (A + 1) / 2 ^ ((A + 1).factorization 2) := Nat.le_of_dvd hpos hA'
  have hdiv : (A ^ q + 1) / 2 ^ ((A ^ q + 1).factorization 2) /
      ((A + 1) / 2 ^ ((A + 1).factorization 2)) = (A ^ q + 1) / (A + 1) := by
    rw [hdecomp, hB]
    exact Nat.mul_div_cancel_left _ hpos
  calc (A ^ q + 1) / 2 ^ ((A ^ q + 1).factorization 2) / d
      ≥ (A ^ q + 1) / 2 ^ ((A ^ q + 1).factorization 2) /
          ((A + 1) / 2 ^ ((A + 1).factorization 2)) := Nat.div_le_div_left hle hdpos
    _ = (A ^ q + 1) / (A + 1) := hdiv

theorem arithAddOneOddAux (p k i : ℕ) (hp : p.Prime) (hodd : Odd p) (h1 : 1 ≤ i) (h2 : i < k)
    (hrp : Nat.Prime (k / i.gcd k)) (hro : Odd (k / i.gcd k)) :
    (let m := (p ^ k + 1) / 2 ^ ((p ^ k + 1).factorization 2)
     m / m.gcd (p ^ i - 1) > (k / i.gcd k) ^ (m.factorization (k / i.gcd k)) ∧
     m / m.gcd (p ^ i + 1) > (k / i.gcd k) ^ (m.factorization (k / i.gcd k))) := by
  set g := i.gcd k with hg
  set q := k / g with hq
  set A := p ^ g with hA
  have hgpos : 0 < g := by
    rw [hg]
    exact Nat.gcd_pos_of_pos_left k (by omega)
  have hAodd : Odd A := by
    rw [hA]
    exact hodd.pow
  have hp3 : 3 ≤ p := by
    have hpne : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_odd_iff_even.mpr (by norm_num : Even 2)) hodd
    have := hp.two_le
    omega
  have hA3 : 3 ≤ A := by
    rw [hA]
    calc 3 ≤ p := hp3
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ g := Nat.pow_le_pow_right hp.pos hgpos
  have hqprime : q.Prime := hrp
  have hqo : Odd q := hro
  have hq_ne_two : q ≠ 2 := by
    intro h
    rw [h] at hro
    rw [Nat.odd_iff] at hro
    omega
  have hmul : g * q = k := by
    rw [hq, hg]
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_right i k)
  have hmul_i : g * (i / g) = i := by
    rw [hg]
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_left i k)
  have hpoweq : p ^ k = A ^ q := by
    rw [← hmul, hA]
    exact pow_mul p g q
  have hpoweq_i : p ^ i = A ^ (i / g) := by
    nth_rewrite 1 [← hmul_i]
    rw [hA]
    exact pow_mul p g (i / g)
  have hNne : p ^ k + 1 ≠ 0 := by positivity
  dsimp only
  refine ⟨?_, ?_⟩
  · set M := (p ^ k + 1) / 2 ^ ((p ^ k + 1).factorization 2) with hM
    set d := M.gcd (p ^ i - 1) with hd
    have hdM : d ∣ M := by rw [hd]; exact Nat.gcd_dvd_left _ _
    have hdPi : d ∣ p ^ i - 1 := by rw [hd]; exact Nat.gcd_dvd_right _ _
    have hMN : M ∣ p ^ k + 1 := by rw [hM]; exact Nat.ordCompl_dvd _ _
    have hdA1 : d ∣ A + 1 := by
      have h := (Nat.dvd_gcd (hdM.trans hMN) hdPi).trans (gcdPowAddOneDvd p k i hro).1
      rw [← hg, ← hA] at h
      exact h
    have hnd2 : ¬ 2 ∣ d := by
      have hmodd : ¬ 2 ∣ M := by
        rw [hM]
        exact Nat.not_dvd_ordCompl (by norm_num) hNne
      intro h2
      exact hmodd (h2.trans hdM)
    have hAM : (A ^ q + 1) / 2 ^ ((A ^ q + 1).factorization 2) = M := by rw [hM, hpoweq]
    have hd3 : d ∣ (A ^ q + 1) / 2 ^ ((A ^ q + 1).factorization 2) := by
      rw [hAM]
      exact hdM
    have hfac : M.factorization q = (A ^ q + 1).factorization q := by
      rw [hM, hpoweq, Nat.factorization_ordCompl]
      exact Finsupp.erase_ne hq_ne_two
    have hMd : M / d = (A ^ q + 1) / 2 ^ ((A ^ q + 1).factorization 2) / d := by rw [hAM]
    have hlb := addOneOddPartDivGcdGe A q d hqo hdA1 hnd2 hd3
    have hcrux := addOneQuotientGtPowFactorization A q hAodd hA3 hqprime hqo
    rw [hfac, hMd]
    linarith
  · set M := (p ^ k + 1) / 2 ^ ((p ^ k + 1).factorization 2) with hM
    set d := M.gcd (p ^ i + 1) with hd
    have hdM : d ∣ M := by rw [hd]; exact Nat.gcd_dvd_left _ _
    have hdPi : d ∣ p ^ i + 1 := by rw [hd]; exact Nat.gcd_dvd_right _ _
    have hMN : M ∣ p ^ k + 1 := by rw [hM]; exact Nat.ordCompl_dvd _ _
    have hdA1 : d ∣ A + 1 := by
      have h := (Nat.dvd_gcd (hdM.trans hMN) hdPi).trans (gcdPowAddOneDvd p k i hro).2
      rw [← hg, ← hA] at h
      exact h
    have hnd2 : ¬ 2 ∣ d := by
      have hmodd : ¬ 2 ∣ M := by
        rw [hM]
        exact Nat.not_dvd_ordCompl (by norm_num) hNne
      intro h2
      exact hmodd (h2.trans hdM)
    have hAM : (A ^ q + 1) / 2 ^ ((A ^ q + 1).factorization 2) = M := by rw [hM, hpoweq]
    have hd3 : d ∣ (A ^ q + 1) / 2 ^ ((A ^ q + 1).factorization 2) := by
      rw [hAM]
      exact hdM
    have hfac : M.factorization q = (A ^ q + 1).factorization q := by
      rw [hM, hpoweq, Nat.factorization_ordCompl]
      exact Finsupp.erase_ne hq_ne_two
    have hMd : M / d = (A ^ q + 1) / 2 ^ ((A ^ q + 1).factorization 2) / d := by rw [hAM]
    have hlb := addOneOddPartDivGcdGe A q d hqo hdA1 hnd2 hd3
    have hcrux := addOneQuotientGtPowFactorization A q hAodd hA3 hqprime hqo
    rw [hfac, hMd]
    linarith

end Work.DSTR.M110
