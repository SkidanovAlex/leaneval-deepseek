import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.P3.SummableVonMangoldtLogPow
import Submission.Work.ZeroFreeTables.P9.SigmaP3LChangeLevelAux
import Submission.Work.ZeroFreeTables.P9.norm_sigmaTerm_changeLevel_sub_le
import Submission.Work.ZeroFreeTables.P9.summable_sigmaTerm
import Submission.Work.ZeroFreeTables.P9.tsum_badTail_eq
import Submission.Work.ZeroFreeTables.P9.summable_vonMangoldt_primePow
import Submission.Work.ZeroFreeTables.Rep9.vonMangoldtComplCoprimeEqSum
import Submission.Work.ZeroFreeTables.Rep9.primePowSeriesLe_proof
import Submission.Work.ZeroFreeTables.Rep9.primeFactorSum_le_sqrt_log_proof

open scoped BigOperators
open ArithmeticFunction
noncomputable section

namespace Work.ZeroFreeTables.Rep9

/-- `log n ≥ 0` for a natural number `n`. -/
private lemma log_natCast_nonneg (n : ℕ) : 0 ≤ Real.log (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · exact Real.log_nonneg (by exact_mod_cast h)

/-- The smoothing weight `hbWL L a λ₁ n` is non-negative for `L > 0`, `a + λ₁ ≥ 0`. -/
private lemma hbWL_nonneg {L a lam₁ : ℝ} (hL : 0 < L) (hα : 0 ≤ a + lam₁) (n : ℕ) :
    0 ≤ Work.ZeroFreeTables.hbWL L a lam₁ n := by
  have hy : 0 ≤ Real.log (n : ℝ) / L := div_nonneg (log_natCast_nonneg n) hL.le
  have h2 : 0 ≤ (a + lam₁) ^ 2 * (Real.log (n : ℝ) / L) := mul_nonneg (pow_nonneg hα 2) hy
  have h3 : 0 ≤ (1 / 3) * (a + lam₁) ^ 3 * (Real.log (n : ℝ) / L) ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 3)) (pow_nonneg hy 2)
  unfold Work.ZeroFreeTables.hbWL
  linarith

/-- `∑_n Λ(n) (log n)^A n^{-σ}` converges absolutely for `σ > 1`. -/
private lemma summable_vonMangoldt_rpow_logpow {σ : ℝ} (hσ : 1 < σ) (A : ℕ) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ)
      * (Real.log (n : ℝ)) ^ A * (n : ℝ) ^ (-σ)) := by
  refine (Work.ZeroFreeTables.P3.SummableVonMangoldtLogPow (σ := σ) hσ A).congr (fun n => ?_)
  rw [div_eq_mul_inv, ← Real.rpow_neg (Nat.cast_nonneg n)]

/-- `∑_n Λ(n) n^{-σ} w(n)` converges absolutely for `σ > 1`. -/
private lemma summable_hbWL_tail {L a lam₁ σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)
      * Work.ZeroFreeTables.hbWL L a lam₁ n) := by
  have h0 := summable_vonMangoldt_rpow_logpow (σ := σ) hσ 0
  have h1 := summable_vonMangoldt_rpow_logpow (σ := σ) hσ 1
  have h2 := summable_vonMangoldt_rpow_logpow (σ := σ) hσ 2
  refine (((h0.mul_left (a + lam₁)).add (h1.mul_left ((a + lam₁) ^ 2 / L))).add
      (h2.mul_left ((1 / 3) * (a + lam₁) ^ 3 / L ^ 2))).congr (fun n => ?_)
  simp only [pow_one, pow_zero, mul_one]
  unfold Work.ZeroFreeTables.hbWL
  ring

/-- **The complementary (`gcd(n,q) > 1`) von Mangoldt tail is bounded by the prime-divisor
sum.**  For `σ > 1` and `j ≤ 2`,
`∑_n [gcd(n,q) > 1] Λ(n)(log n)^j / n^σ ≤ 12 ∑_{p ∣ q} (log p)^{j+1}/p`.

The summand vanishes unless `n` is a prime power `p^k` with `p ∣ q`; this is
`vonMangoldtComplCoprimeEqSum`, so the series splits over the finitely many primes `p ∣ q`,
where each prime tail is bounded by `primePowSeriesLe`. -/
theorem tail_le {q : ℕ} [NeZero q] {σ : ℝ} (hσ : 1 < σ) (j : ℕ) (hj : j ≤ 2) :
    (∑' n : ℕ, (if Nat.Coprime n q then (0:ℝ) else 1) * (ArithmeticFunction.vonMangoldt n : ℝ)
        * (n : ℝ) ^ (-σ) * (Real.log (n : ℝ)) ^ j)
      ≤ 12 * ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ (j + 1) / (p : ℝ) := by
  have hq : q ≠ 0 := NeZero.ne q
  have hpoint : ∀ n : ℕ,
      (if Nat.Coprime n q then (0:ℝ) else 1) * (ArithmeticFunction.vonMangoldt n : ℝ)
          * (n : ℝ) ^ (-σ) * (Real.log (n : ℝ)) ^ j
        = ∑ p ∈ q.primeFactors,
            (if IsPrimePow n ∧ n.minFac = p then (ArithmeticFunction.vonMangoldt n : ℝ)
              * (n : ℝ) ^ (-σ) * (Real.log (n : ℝ)) ^ j else (0:ℝ)) := by
    intro n
    rw [vonMangoldtComplCoprimeEqSum hq j n]
  calc (∑' n : ℕ, (if Nat.Coprime n q then (0:ℝ) else 1)
          * (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)
          * (Real.log (n : ℝ)) ^ j)
      = ∑' n : ℕ, ∑ p ∈ q.primeFactors,
          (if IsPrimePow n ∧ n.minFac = p then (ArithmeticFunction.vonMangoldt n : ℝ)
            * (n : ℝ) ^ (-σ) * (Real.log (n : ℝ)) ^ j else (0:ℝ)) := tsum_congr hpoint
    _ = ∑ p ∈ q.primeFactors, ∑' n : ℕ,
          (if IsPrimePow n ∧ n.minFac = p then (ArithmeticFunction.vonMangoldt n : ℝ)
            * (n : ℝ) ^ (-σ) * (Real.log (n : ℝ)) ^ j else (0:ℝ)) :=
        Summable.tsum_finsetSum
          (fun p hp => Work.ZeroFreeTables.P9.summable_vonMangoldt_primePow p
            (Nat.prime_of_mem_primeFactors hp) hσ j)
    _ ≤ ∑ p ∈ q.primeFactors, 12 * (Real.log (p : ℝ)) ^ (j + 1) / (p : ℝ) :=
        Finset.sum_le_sum (fun p hp =>
          primePowSeriesLe_proof p (Nat.prime_of_mem_primeFactors hp) hσ j hj)
    _ = 12 * ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ (j + 1) / (p : ℝ) := by
        rw [Finset.mul_sum]
        simp only [mul_div_assoc]

open Work.ZeroFreeTables.P9 in
/-- **The difference bound at a free positive scale.**  For `L > 0` and `Re s > 1` the
principal-character `Σ`-sums at level `q` and at level `1` differ by at most `L⁻¹` times the
prime-divisor tail
`12·(α·S₁ + (α²/L)·S₂ + (α³/L²)·S₃)`, `S_j = ∑_{p | q} (log p)^j/p`, `α = a + λ₁`. -/
theorem principalDiff_bound {q : ℕ} [NeZero q] {L : ℝ} (hL : 0 < L) {s : ℂ} (hs : 1 < s.re)
    {a lam₁ : ℝ} (ha : 0 < a) (hlam₁ : 0 ≤ lam₁) :
    |Work.ZeroFreeTables.SigmaP3L q L (1 : DirichletCharacter ℂ q) s a lam₁
        - Work.ZeroFreeTables.SigmaP3L 1 L 1 s a lam₁|
      ≤ (12 / L) * ((a + lam₁) * (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ))
        + ((a + lam₁) ^ 2 / L) * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ))
        + ((a + lam₁) ^ 3 / L ^ 2)
            * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ))) := by
  have hα : 0 ≤ a + lam₁ := by linarith
  have hone : DirichletCharacter.changeLevel (one_dvd q) (1 : DirichletCharacter ℂ 1)
      = (1 : DirichletCharacter ℂ q) := DirichletCharacter.changeLevel_one (one_dvd q)
  set χ' : DirichletCharacter ℂ q :=
    DirichletCharacter.changeLevel (one_dvd q) (1 : DirichletCharacter ℂ 1) with hχ'def
  have hFs : Summable (sigmaTerm q L χ' s a lam₁) :=
    summable_sigmaTerm L χ' a lam₁ hs ha hlam₁ hL
  have hGs : Summable (sigmaTerm 1 L (1 : DirichletCharacter ℂ 1) s a lam₁) :=
    summable_sigmaTerm L 1 a lam₁ hs ha hlam₁ hL
  have hdiff : (∑' n, sigmaTerm q L χ' s a lam₁ n)
      - (∑' n, sigmaTerm 1 L (1 : DirichletCharacter ℂ 1) s a lam₁ n)
      = ∑' n, (sigmaTerm q L χ' s a lam₁ n
          - sigmaTerm 1 L (1 : DirichletCharacter ℂ 1) s a lam₁ n) :=
    (Summable.tsum_sub hFs hGs).symm
  have hpt : ∀ n : ℕ,
      ‖sigmaTerm q L χ' s a lam₁ n
          - sigmaTerm 1 L (1 : DirichletCharacter ℂ 1) s a lam₁ n‖
      ≤ (if Nat.Coprime n q then (0:ℝ) else 1) * (ArithmeticFunction.vonMangoldt n : ℝ)
          * (n : ℝ) ^ (-s.re) * Work.ZeroFreeTables.hbWL L a lam₁ n := by
    intro n
    have h := norm_sigmaTerm_changeLevel_sub_le (one_dvd q) (1 : DirichletCharacter ℂ 1)
      L s a lam₁ ha hlam₁ hL n
    rw [← hχ'def] at h
    have hind : (if Nat.Coprime n 1 ∧ ¬ Nat.Coprime n q then (1:ℝ) else 0)
        ≤ (if Nat.Coprime n q then (0:ℝ) else 1) := by
      by_cases hc : Nat.Coprime n q
      · rw [if_neg (fun h : Nat.Coprime n 1 ∧ ¬ Nat.Coprime n q => h.2 hc), if_pos hc]
      · rw [if_neg hc, if_pos ⟨Nat.coprime_one_right n, hc⟩]
    have hw : 0 ≤ Work.ZeroFreeTables.hbWL L a lam₁ n := hbWL_nonneg hL hα n
    calc ‖sigmaTerm q L χ' s a lam₁ n
            - sigmaTerm 1 L (1 : DirichletCharacter ℂ 1) s a lam₁ n‖
        ≤ (if Nat.Coprime n 1 ∧ ¬ Nat.Coprime n q then (1:ℝ) else 0)
            * (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-s.re)
            * Work.ZeroFreeTables.hbWL L a lam₁ n := h
      _ ≤ (if Nat.Coprime n q then (0:ℝ) else 1) * (ArithmeticFunction.vonMangoldt n : ℝ)
            * (n : ℝ) ^ (-s.re) * Work.ZeroFreeTables.hbWL L a lam₁ n :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hind ArithmeticFunction.vonMangoldt_nonneg)
              (Real.rpow_nonneg (Nat.cast_nonneg n) _)) hw
  have hHsumm : Summable (fun n : ℕ => (if Nat.Coprime n q then (0:ℝ) else 1)
      * (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-s.re)
      * Work.ZeroFreeTables.hbWL L a lam₁ n) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
      (summable_hbWL_tail (L := L) (a := a) (lam₁ := lam₁) (σ := s.re) hs)
    · have hw := hbWL_nonneg hL hα n
      have h1 : (0:ℝ) ≤ (if Nat.Coprime n q then (0:ℝ) else 1) := by split <;> norm_num
      exact mul_nonneg (mul_nonneg (mul_nonneg h1 ArithmeticFunction.vonMangoldt_nonneg)
        (Real.rpow_nonneg (Nat.cast_nonneg n) _)) hw
    · have hw := hbWL_nonneg hL hα n
      have h1 : (if Nat.Coprime n q then (0:ℝ) else 1) ≤ 1 := by split <;> norm_num
      have h2 : (if Nat.Coprime n q then (0:ℝ) else 1) * (ArithmeticFunction.vonMangoldt n : ℝ)
          ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := by
        simpa using mul_le_mul_of_nonneg_right h1 ArithmeticFunction.vonMangoldt_nonneg
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (Nat.cast_nonneg n) _)) hw
  have hkey : ‖(∑' n, sigmaTerm q L χ' s a lam₁ n)
        - (∑' n, sigmaTerm 1 L (1 : DirichletCharacter ℂ 1) s a lam₁ n)‖
      ≤ 12 * (a + lam₁) * (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ))
        + 12 * ((a + lam₁) ^ 2 / L)
            * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ))
        + 4 * ((a + lam₁) ^ 3 / L ^ 2)
            * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ)) := by
    rw [hdiff]
    calc ‖∑' n, (sigmaTerm q L χ' s a lam₁ n
            - sigmaTerm 1 L (1 : DirichletCharacter ℂ 1) s a lam₁ n)‖
        ≤ ∑' n, ‖sigmaTerm q L χ' s a lam₁ n
            - sigmaTerm 1 L (1 : DirichletCharacter ℂ 1) s a lam₁ n‖ :=
          norm_tsum_le_tsum_norm ((hFs.sub hGs).norm)
      _ ≤ ∑' n, ((if Nat.Coprime n q then (0:ℝ) else 1)
            * (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-s.re)
            * Work.ZeroFreeTables.hbWL L a lam₁ n) :=
          Summable.tsum_le_tsum hpt ((hFs.sub hGs).norm) hHsumm
      _ = (a + lam₁) * (∑' n : ℕ, tailSummand q s.re 0 n)
            + ((a + lam₁) ^ 2 / L) * (∑' n : ℕ, tailSummand q s.re 1 n)
            + (1 / 3) * ((a + lam₁) ^ 3 / L ^ 2)
                * (∑' n : ℕ, tailSummand q s.re 2 n) :=
          tsum_badTail_eq q hs a lam₁ L
      _ ≤ 12 * (a + lam₁) * (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ))
            + 12 * ((a + lam₁) ^ 2 / L)
                * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ))
            + 4 * ((a + lam₁) ^ 3 / L ^ 2)
                * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ)) := by
        have hut0 : (∑' n : ℕ, tailSummand q s.re 0 n)
            = ∑' n : ℕ, (if Nat.Coprime n q then (0:ℝ) else 1)
                * (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-s.re)
                * (Real.log (n : ℝ)) ^ 0 := rfl
        have hut1 : (∑' n : ℕ, tailSummand q s.re 1 n)
            = ∑' n : ℕ, (if Nat.Coprime n q then (0:ℝ) else 1)
                * (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-s.re)
                * (Real.log (n : ℝ)) ^ 1 := rfl
        have hut2 : (∑' n : ℕ, tailSummand q s.re 2 n)
            = ∑' n : ℕ, (if Nat.Coprime n q then (0:ℝ) else 1)
                * (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-s.re)
                * (Real.log (n : ℝ)) ^ 2 := rfl
        have hT0 : (∑' n : ℕ, tailSummand q s.re 0 n)
            ≤ 12 * ∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ) := by
          rw [hut0]
          simpa using tail_le (q := q) hs 0 (by norm_num)
        have hT1 : (∑' n : ℕ, tailSummand q s.re 1 n)
            ≤ 12 * ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ) := by
          rw [hut1]
          simpa using tail_le (q := q) hs 1 (by norm_num)
        have hT2 : (∑' n : ℕ, tailSummand q s.re 2 n)
            ≤ 12 * ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ) := by
          rw [hut2]
          simpa using tail_le (q := q) hs 2 (by norm_num)
        have e0 := mul_le_mul_of_nonneg_left hT0 hα
        have e1 := mul_le_mul_of_nonneg_left hT1 (div_nonneg (pow_nonneg hα 2) hL.le)
        have e2 := mul_le_mul_of_nonneg_left hT2
          (by positivity : (0:ℝ) ≤ (1 / 3) * ((a + lam₁) ^ 3 / L ^ 2))
        linarith [e0, e1, e2]
  rw [SigmaP3L_eq_tsum_sigmaTerm, SigmaP3L_eq_tsum_sigmaTerm,
    show (1 : DirichletCharacter ℂ q) = χ' from hone.symm]
  rw [← mul_sub, abs_mul, abs_of_nonneg (inv_nonneg.mpr hL.le), ← Real.norm_eq_abs]
  refine le_trans (mul_le_mul_of_nonneg_left hkey (inv_nonneg.mpr hL.le)) ?_
  have hS3 : 0 ≤ ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ) :=
    Finset.sum_nonneg (fun p _ => div_nonneg (pow_nonneg (log_natCast_nonneg p) 3)
      (Nat.cast_nonneg p))
  have hc3 : 0 ≤ (a + lam₁) ^ 3 / L ^ 2 := div_nonneg (pow_nonneg hα 3) (sq_nonneg L)
  have hstep : (12 * (a + lam₁) * (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ))
      + 12 * ((a + lam₁) ^ 2 / L) * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ))
      + 4 * ((a + lam₁) ^ 3 / L ^ 2) * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ)))
      ≤ (12 * (a + lam₁) * (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ))
      + 12 * ((a + lam₁) ^ 2 / L) * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ))
      + 12 * ((a + lam₁) ^ 3 / L ^ 2)
          * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ))) := by
    linarith [mul_nonneg hc3 hS3]
  calc L⁻¹ * (12 * (a + lam₁) * (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ))
        + 12 * ((a + lam₁) ^ 2 / L) * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ))
        + 4 * ((a + lam₁) ^ 3 / L ^ 2) * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ)))
      ≤ L⁻¹ * (12 * (a + lam₁) * (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ))
        + 12 * ((a + lam₁) ^ 2 / L) * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ))
        + 12 * ((a + lam₁) ^ 3 / L ^ 2)
            * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ))) :=
        mul_le_mul_of_nonneg_left hstep (inv_nonneg.mpr hL.le)
    _ = (12 / L) * ((a + lam₁) * (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ))
        + ((a + lam₁) ^ 2 / L) * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ))
        + ((a + lam₁) ^ 3 / L ^ 2)
            * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ))) := by
        ring

/-- Algebraic rearrangement used at the end of `principalSigmaDiff`. -/
private lemma combine_eq {L : ℝ} (hL : L ≠ 0) (a Dm T : ℝ) :
    (12 / L) * ((a * (Dm * T)) + ((a ^ 2 / L) * (Dm * T)) + ((a ^ 3 / L ^ 2) * (Dm * T)))
      = (a / L) * (12 * Dm) * T * (1 + a / L + (a / L) ^ 2) := by
  field_simp

theorem principalSigmaDiff {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] {L lam₁ : ℝ}, 0 < L → Real.log (q:ℝ) ≤ L →
      0 ≤ lam₁ → lam₁ ≤ M → ∀ s : ℂ, s.re = 1 + a/L → |s.im| ≤ 5 →
        |Work.ZeroFreeTables.SigmaP3L q L (1 : DirichletCharacter ℂ q) s a lam₁
            - Work.ZeroFreeTables.SigmaP3L 1 L 1 s a lam₁|
          ≤ ((a + lam₁) / L) * C * (1 + Real.sqrt (Real.log q))
              * (1 + (a + lam₁) / L + ((a + lam₁) / L) ^ 2) := by
  obtain ⟨D1, hD1pos, hD1⟩ := primeFactorSum_le_sqrt_log_proof 1 (by norm_num)
  obtain ⟨D2, hD2pos, hD2⟩ := primeFactorSum_le_sqrt_log_proof 2 (by norm_num)
  obtain ⟨D3, hD3pos, hD3⟩ := primeFactorSum_le_sqrt_log_proof 3 (by norm_num)
  have hD12 : 0 < max D1 D2 := lt_of_lt_of_le hD1pos (le_max_left D1 D2)
  have hDmpos : 0 < max (max D1 D2) D3 := lt_of_lt_of_le hD12 (le_max_left (max D1 D2) D3)
  refine ⟨12 * max (max D1 D2) D3, mul_pos (by norm_num) hDmpos, ?_⟩
  intro q _ L lam₁ hL hlog hlam₁ hMle s hs him
  have hq1 : 1 ≤ q := by have := NeZero.ne q; omega
  have hTnn : 0 ≤ 1 + Real.sqrt (Real.log (q : ℝ)) := by
    have h : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq1)
    positivity
  have hsre : 1 < s.re := by
    rw [hs]
    have h : 0 < a / L := div_pos ha hL
    linarith
  have hα : 0 ≤ a + lam₁ := by linarith
  have hDm_le_1 : D1 ≤ max (max D1 D2) D3 :=
    le_trans (le_max_left D1 D2) (le_max_left (max D1 D2) D3)
  have hDm_le_2 : D2 ≤ max (max D1 D2) D3 :=
    le_trans (le_max_right D1 D2) (le_max_left (max D1 D2) D3)
  have hDm_le_3 : D3 ≤ max (max D1 D2) D3 := le_max_right (max D1 D2) D3
  have hkey := principalDiff_bound (q := q) hL hsre ha hlam₁
  have hS1 : (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ))
      ≤ max (max D1 D2) D3 * (1 + Real.sqrt (Real.log (q : ℝ))) := by
    have h := hD1 q hq1
    simp only [pow_one] at h
    exact h.trans (mul_le_mul_of_nonneg_right hDm_le_1 hTnn)
  have hS2 : (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ))
      ≤ max (max D1 D2) D3 * (1 + Real.sqrt (Real.log (q : ℝ))) :=
    (hD2 q hq1).trans (mul_le_mul_of_nonneg_right hDm_le_2 hTnn)
  have hS3 : (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ))
      ≤ max (max D1 D2) D3 * (1 + Real.sqrt (Real.log (q : ℝ))) :=
    (hD3 q hq1).trans (mul_le_mul_of_nonneg_right hDm_le_3 hTnn)
  have hA1 : (a + lam₁) * (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ))
      ≤ (a + lam₁) * (max (max D1 D2) D3 * (1 + Real.sqrt (Real.log (q : ℝ)))) :=
    mul_le_mul_of_nonneg_left hS1 hα
  have hA2 : ((a + lam₁) ^ 2 / L) * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ))
      ≤ ((a + lam₁) ^ 2 / L)
        * (max (max D1 D2) D3 * (1 + Real.sqrt (Real.log (q : ℝ)))) :=
    mul_le_mul_of_nonneg_left hS2 (by positivity)
  have hA3 : ((a + lam₁) ^ 3 / L ^ 2)
        * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ))
      ≤ ((a + lam₁) ^ 3 / L ^ 2)
        * (max (max D1 D2) D3 * (1 + Real.sqrt (Real.log (q : ℝ)))) :=
    mul_le_mul_of_nonneg_left hS3 (by positivity)
  have hsum : (a + lam₁) * (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ))
        + ((a + lam₁) ^ 2 / L) * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ))
        + ((a + lam₁) ^ 3 / L ^ 2)
            * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ))
      ≤ (a + lam₁) * (max (max D1 D2) D3 * (1 + Real.sqrt (Real.log (q : ℝ))))
        + ((a + lam₁) ^ 2 / L)
            * (max (max D1 D2) D3 * (1 + Real.sqrt (Real.log (q : ℝ))))
        + ((a + lam₁) ^ 3 / L ^ 2)
            * (max (max D1 D2) D3 * (1 + Real.sqrt (Real.log (q : ℝ)))) := by
    linarith [hA1, hA2, hA3]
  have hmain : |Work.ZeroFreeTables.SigmaP3L q L (1 : DirichletCharacter ℂ q) s a lam₁
        - Work.ZeroFreeTables.SigmaP3L 1 L 1 s a lam₁|
      ≤ (12 / L)
        * ((a + lam₁) * (max (max D1 D2) D3 * (1 + Real.sqrt (Real.log (q : ℝ))))
          + ((a + lam₁) ^ 2 / L)
              * (max (max D1 D2) D3 * (1 + Real.sqrt (Real.log (q : ℝ))))
          + ((a + lam₁) ^ 3 / L ^ 2)
              * (max (max D1 D2) D3 * (1 + Real.sqrt (Real.log (q : ℝ))))) :=
    hkey.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
  have heq := combine_eq (L := L) (ne_of_gt hL) (a + lam₁) (max (max D1 D2) D3)
    (1 + Real.sqrt (Real.log (q : ℝ)))
  rw [heq] at hmain
  exact hmain

end Work.ZeroFreeTables.Rep9
