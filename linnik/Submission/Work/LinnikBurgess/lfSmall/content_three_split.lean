import Mathlib
import Submission.Work.LinnikBurgess.lf_defs
import Submission.Work.LinnikBurgess.critN_ne_zero_of_unique
import Submission.Work.LinnikBurgess.critN_content_iff
import Submission.Work.LinnikBurgess.lfSmall.content_dvd_critN

/-!
# Splitting the content `contAB` against the 3-adic content of `critN`

For two triples `a b : Fin 3 → ℕ` let

* `contAB a b = gcd_k |e_k(a) - e_k(b)|` be the content of the pair, and
* `critN a b = f_a' f_b - f_a f_b'` the Wronskian of the two cubics `f_a = ∏_l (X + a_l)`.

Writing the expansion of the Wronskian (`critNcontent.critN_eq_expand`)
`critN = C(B₁-A₁)X⁴ + C(2(B₂-A₂))X³ + C(D₁B₂ - B₁D₂ - 3D₃)X² + …` with `Dᵢ = eᵢ(a) - eᵢ(b)`,
one gets for every `k ≥ 1` the two implications

* `3^k ∣ contAB a b → ∀ n, 3^k ∣ (critN a b).coeff n` (`dvd_coeff_critN_of_dvd_contAB`, valid for
  an arbitrary modulus), and
* `(∀ n, 3^k ∣ (critN a b).coeff n) → 3^(k-1) ∣ contAB a b` (`three_pow_pred_dvd_contAB`: the
  coefficients in degrees `4`, `3` give `3^k ∣ D₁, D₂` and the coefficient in degree `2` only
  gives `3^k ∣ 3·D₃`, i.e. `3^(k-1) ∣ D₃` — the single power of `3` lost, because `2` is invertible
  modulo `3` but `3` is not).

These two facts pin the 3-adic divisibility of all coefficients of `critN` between the `3`-adic
valuation `J` of `contAB` and `J + 1`.  Hence, given `3^J ∣ contAB` but `3^(J+1) ∤ contAB`, there is
an exact level `h ∈ {J, J+1}`: `3^h` divides every coefficient of `critN` but `3^(h+1)` does not.
-/

namespace Work.LinnikBurgess.lfSmall

open Classical
open Work.LinnikBurgess.critNcontent

/-- **The `p = 3` forward direction.**  If `3^k` (with `k ≥ 1`) divides every coefficient of the
Wronskian `critN a b`, then `3^(k-1)` divides the content `contAB a b`.

Degrees `4` and `3` of `critN_eq_expand` give `3^k ∣ e₁(a)-e₁(b)` and `3^k ∣ e₂(a)-e₂(b)`; degree
`2` reads `-A₂B₁ + A₁B₂ + 3(B₃-A₃) = D₁B₂ - D₂B₁ + 3(B₃-A₃)`, and the first two terms are divisible
by `3^k`, so `3^k ∣ 3(B₃-A₃)`, i.e. `3^(k-1) ∣ e₃(a)-e₃(b)`.  All three differences are then
divisible by `3^(k-1)`, hence so is their gcd `contAB a b`. -/
theorem three_pow_pred_dvd_contAB {a b : Fin 3 → ℕ} {k : ℕ} (hk : 1 ≤ k)
    (h : ∀ n : ℕ, ((3 ^ k : ℕ) : ℤ) ∣ (critN a b).coeff n) :
    (3 ^ (k - 1) : ℕ) ∣ contAB a b := by
  have h3k : ((3 ^ k : ℕ) : ℤ) = 3 * ((3 ^ (k - 1) : ℕ) : ℤ) := by
    have hk' : k = (k - 1) + 1 := (Nat.succ_pred_eq_of_pos (by omega)).symm
    rw [hk', pow_succ]
    push_cast
    ring
  have hpow_dvd : ((3 ^ (k - 1) : ℕ) : ℤ) ∣ ((3 ^ k : ℕ) : ℤ) := by
    rw [h3k]; exact dvd_mul_left _ _
  -- degree 4: `3^k ∣ e₁(a) - e₁(b)`
  have hD1 : ((3 ^ k : ℕ) : ℤ) ∣ esymm3 a 0 - esymm3 b 0 := by
    have hh := h 4
    rw [critN_eq_expand, coeff_four_exp] at hh
    have := (dvd_neg).mpr hh
    rwa [neg_sub] at this
  -- degree 3: `3^k ∣ 2 * (e₂(a) - e₂(b))` and `2` is invertible modulo `3^k`
  have hcop : IsCoprime ((3 ^ k : ℕ) : ℤ) (2 : ℤ) :=
    (Nat.isCoprime_iff_coprime).mpr (Nat.Coprime.pow_left k (by decide))
  have hD2 : ((3 ^ k : ℕ) : ℤ) ∣ esymm3 a 1 - esymm3 b 1 := by
    have hh := h 3
    rw [critN_eq_expand, coeff_three_exp] at hh
    have hh2 : ((3 ^ k : ℕ) : ℤ) ∣ esymm3 b 1 - esymm3 a 1 := hcop.dvd_of_dvd_mul_left hh
    have := (dvd_neg).mpr hh2
    rwa [neg_sub] at this
  -- degree 2: `3^k ∣ 3 * (e₃(b) - e₃(a))`
  have hD3 : ((3 ^ k : ℕ) : ℤ) ∣ 3 * (esymm3 b 2 - esymm3 a 2) := by
    have hh := h 2
    rw [critN_eq_expand, coeff_two_exp] at hh
    have hbase : ((3 ^ k : ℕ) : ℤ) ∣ (esymm3 a 0 - esymm3 b 0) * esymm3 b 1
        - (esymm3 a 1 - esymm3 b 1) * esymm3 b 0 :=
      dvd_sub (dvd_mul_of_dvd_left hD1 _) (dvd_mul_of_dvd_left hD2 _)
    have hdiff : -esymm3 a 1 * esymm3 b 0 + esymm3 a 0 * esymm3 b 1
          + 3 * (esymm3 b 2 - esymm3 a 2)
        - ((esymm3 a 0 - esymm3 b 0) * esymm3 b 1
            - (esymm3 a 1 - esymm3 b 1) * esymm3 b 0)
        = 3 * (esymm3 b 2 - esymm3 a 2) := by ring
    have := dvd_sub hh hbase
    rwa [hdiff] at this
  -- descend to `3^(k-1)` for each difference
  have hd1 : ((3 ^ (k - 1) : ℕ) : ℤ) ∣ esymm3 a 0 - esymm3 b 0 := dvd_trans hpow_dvd hD1
  have hd2 : ((3 ^ (k - 1) : ℕ) : ℤ) ∣ esymm3 a 1 - esymm3 b 1 := dvd_trans hpow_dvd hD2
  have hd3 : ((3 ^ (k - 1) : ℕ) : ℤ) ∣ esymm3 a 2 - esymm3 b 2 := by
    have hh : 3 * ((3 ^ (k - 1) : ℕ) : ℤ) ∣ 3 * (esymm3 b 2 - esymm3 a 2) := by
      rwa [← h3k]
    have hb : ((3 ^ (k - 1) : ℕ) : ℤ) ∣ esymm3 b 2 - esymm3 a 2 :=
      (mul_dvd_mul_iff_left (show (3 : ℤ) ≠ 0 by norm_num)).mp hh
    have := (dvd_neg).mpr hb
    rwa [neg_sub] at this
  -- combine through the gcd
  have hn1 : 3 ^ (k - 1) ∣ (esymm3 a 0 - esymm3 b 0).natAbs := by
    simpa using (Int.natAbs_dvd_natAbs).mpr hd1
  have hn2 : 3 ^ (k - 1) ∣ (esymm3 a 1 - esymm3 b 1).natAbs := by
    simpa using (Int.natAbs_dvd_natAbs).mpr hd2
  have hn3 : 3 ^ (k - 1) ∣ (esymm3 a 2 - esymm3 b 2).natAbs := by
    simpa using (Int.natAbs_dvd_natAbs).mpr hd3
  rw [contAB]
  exact Nat.dvd_gcd hn1 (Nat.dvd_gcd hn2 hn3)

/-- **Splitting the 3-adic level of `contAB` against the coefficients of `critN`.**

If `3^J` divides the content `contAB a b` (`J ≥ 1`) but `3^(J+1)` does not, then the exact level of
`3`-divisibility of the coefficient sequence of the Wronskian `critN a b` is `J` or `J+1`. -/
theorem content_three_split {a b : Fin 3 → ℕ} (i : Fin 6)
    (hi : ∀ j : Fin 6, j ≠ i → shift a b i ≠ shift a b j) {J : ℕ} (hJ1 : 1 ≤ J)
    (hJ : (3 ^ J : ℕ) ∣ contAB a b) (hJ' : ¬ (3 ^ (J + 1) : ℕ) ∣ contAB a b) :
    ∃ h : ℕ, 1 ≤ h ∧ h ≤ J + 1 ∧ (∀ n : ℕ, ((3 ^ h : ℕ) : ℤ) ∣ (critN a b).coeff n)
      ∧ (∃ n : ℕ, ¬ ((3 ^ (h + 1) : ℕ) : ℤ) ∣ (critN a b).coeff n) := by
  by_cases hcase : ∀ n : ℕ, ((3 ^ (J + 1) : ℕ) : ℤ) ∣ (critN a b).coeff n
  · -- `3^(J+1)` already divides every coefficient: the exact level is `J + 1`
    refine ⟨J + 1, by omega, by omega, hcase, ?_⟩
    have hnot : ¬ ∀ n : ℕ, ((3 ^ ((J + 1) + 1) : ℕ) : ℤ) ∣ (critN a b).coeff n := by
      intro hall
      have hdiv : (3 ^ (J + 1) : ℕ) ∣ contAB a b := by
        simpa using three_pow_pred_dvd_contAB (k := (J + 1) + 1) (by omega) hall
      exact hJ' hdiv
    simpa using not_forall.mp hnot
  · -- otherwise the exact level is `J`
    refine ⟨J, hJ1, by omega, dvd_coeff_critN_of_dvd_contAB (3 ^ J) a b hJ, ?_⟩
    simpa using not_forall.mp hcase

end Work.LinnikBurgess.lfSmall
