import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.P9.SigmaP3LChangeLevelAux
import Submission.Work.ZeroFreeTables.P9.summable_sigmaTerm
import Submission.Work.ZeroFreeTables.P9.norm_sigmaTerm_changeLevel_sub_le
import Submission.Work.ZeroFreeTables.P9.tsum_badTail_eq
import Submission.Work.ZeroFreeTables.P9.vonMangoldt_coprime_compl_tail_le

open scoped BigOperators
noncomputable section

namespace Work.ZeroFreeTables.P9

open ArithmeticFunction

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

/-- The key estimate: the difference of the two `tsum`s is bounded by the prime-factor sum. -/
private lemma key_bound {N q : ℕ} [NeZero N] [NeZero q] (hNq : N ∣ q)
    (ψ : DirichletCharacter ℂ N) {L : ℝ} (hL : 1 ≤ L) {s : ℂ} (hs : 1 < s.re)
    {a lam₁ : ℝ} (ha : 0 < a) (hlam₁ : 0 ≤ lam₁) :
    ‖(∑' n : ℕ, sigmaTerm q L (DirichletCharacter.changeLevel hNq ψ) s a lam₁ n)
        - (∑' n : ℕ, sigmaTerm N L ψ s a lam₁ n)‖
      ≤ 12 * (a + lam₁) * (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ))
        + 12 * ((a + lam₁) ^ 2 / L) * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ))
        + 4 * ((a + lam₁) ^ 3 / L ^ 2) * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ)) := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hα : 0 ≤ a + lam₁ := by linarith
  set χ' : DirichletCharacter ℂ q := DirichletCharacter.changeLevel hNq ψ with hχ'def
  have hFs : Summable (sigmaTerm q L χ' s a lam₁) := summable_sigmaTerm L χ' a lam₁ hs ha hlam₁ hLpos
  have hGs : Summable (sigmaTerm N L ψ s a lam₁) := summable_sigmaTerm L ψ a lam₁ hs ha hlam₁ hLpos
  have hdiff : (∑' n, sigmaTerm q L χ' s a lam₁ n) - (∑' n, sigmaTerm N L ψ s a lam₁ n)
      = ∑' n, (sigmaTerm q L χ' s a lam₁ n - sigmaTerm N L ψ s a lam₁ n) :=
    (Summable.tsum_sub hFs hGs).symm
  have hpt : ∀ n : ℕ,
      ‖sigmaTerm q L χ' s a lam₁ n - sigmaTerm N L ψ s a lam₁ n‖
      ≤ (if Nat.Coprime n q then (0:ℝ) else 1) * (ArithmeticFunction.vonMangoldt n : ℝ)
          * (n : ℝ) ^ (-s.re) * Work.ZeroFreeTables.hbWL L a lam₁ n := by
    intro n
    have h := norm_sigmaTerm_changeLevel_sub_le hNq ψ L s a lam₁ ha hlam₁ hLpos n
    rw [← hχ'def] at h
    have hind : (if Nat.Coprime n N ∧ ¬ Nat.Coprime n q then (1:ℝ) else 0)
        ≤ (if Nat.Coprime n q then (0:ℝ) else 1) := by
      by_cases hc : Nat.Coprime n q
      · rw [if_neg (fun h : Nat.Coprime n N ∧ ¬ Nat.Coprime n q => h.2 hc), if_pos hc]
      · rw [if_neg hc]
        by_cases hN : Nat.Coprime n N
        · rw [if_pos (show Nat.Coprime n N ∧ ¬ Nat.Coprime n q from ⟨hN, hc⟩)]
        · rw [if_neg (show ¬(Nat.Coprime n N ∧ ¬ Nat.Coprime n q) from fun h => hN h.1)]
          norm_num
    have hw : 0 ≤ Work.ZeroFreeTables.hbWL L a lam₁ n := hbWL_nonneg hLpos hα n
    calc ‖sigmaTerm q L χ' s a lam₁ n - sigmaTerm N L ψ s a lam₁ n‖
        ≤ (if Nat.Coprime n N ∧ ¬ Nat.Coprime n q then (1:ℝ) else 0)
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
    · have hw := hbWL_nonneg hLpos hα n
      have h1 : (0:ℝ) ≤ (if Nat.Coprime n q then (0:ℝ) else 1) := by split <;> norm_num
      exact mul_nonneg (mul_nonneg (mul_nonneg h1 ArithmeticFunction.vonMangoldt_nonneg)
        (Real.rpow_nonneg (Nat.cast_nonneg n) _)) hw
    · have hw := hbWL_nonneg hLpos hα n
      have h1 : (if Nat.Coprime n q then (0:ℝ) else 1) ≤ 1 := by split <;> norm_num
      have h2 : (if Nat.Coprime n q then (0:ℝ) else 1) * (ArithmeticFunction.vonMangoldt n : ℝ)
          ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := by
        simpa using mul_le_mul_of_nonneg_right h1 ArithmeticFunction.vonMangoldt_nonneg
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (Nat.cast_nonneg n) _)) hw
  rw [hdiff]
  calc ‖∑' n, (sigmaTerm q L χ' s a lam₁ n - sigmaTerm N L ψ s a lam₁ n)‖
      ≤ ∑' n, ‖sigmaTerm q L χ' s a lam₁ n - sigmaTerm N L ψ s a lam₁ n‖ :=
        norm_tsum_le_tsum_norm ((hFs.sub hGs).norm)
    _ ≤ ∑' n, ((if Nat.Coprime n q then (0:ℝ) else 1) * (ArithmeticFunction.vonMangoldt n : ℝ)
          * (n : ℝ) ^ (-s.re) * Work.ZeroFreeTables.hbWL L a lam₁ n) :=
        Summable.tsum_le_tsum hpt ((hFs.sub hGs).norm) hHsumm
    _ = (a + lam₁) * (∑' n : ℕ, tailSummand q s.re 0 n)
          + ((a + lam₁) ^ 2 / L) * (∑' n : ℕ, tailSummand q s.re 1 n)
          + (1 / 3) * ((a + lam₁) ^ 3 / L ^ 2) * (∑' n : ℕ, tailSummand q s.re 2 n) :=
        tsum_badTail_eq q hs a lam₁ L
    _ ≤ 12 * (a + lam₁) * (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ))
          + 12 * ((a + lam₁) ^ 2 / L) * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ))
          + 4 * ((a + lam₁) ^ 3 / L ^ 2) * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ)) := by
      have hut : (∑' n : ℕ, tailSummand q s.re 0 n)
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
        rw [hut]
        simpa using vonMangoldt_coprime_compl_tail_le (q := q) hs 0 (by norm_num)
      have hT1 : (∑' n : ℕ, tailSummand q s.re 1 n)
          ≤ 12 * ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ) := by
        rw [hut1]
        simpa using vonMangoldt_coprime_compl_tail_le (q := q) hs 1 (by norm_num)
      have hT2 : (∑' n : ℕ, tailSummand q s.re 2 n)
          ≤ 12 * ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ) := by
        rw [hut2]
        simpa using vonMangoldt_coprime_compl_tail_le (q := q) hs 2 (by norm_num)
      have e0 := mul_le_mul_of_nonneg_left hT0 hα
      have e1 := mul_le_mul_of_nonneg_left hT1 (div_nonneg (pow_nonneg hα 2) hLpos.le)
      have e2 := mul_le_mul_of_nonneg_left hT2
        (by positivity : (0:ℝ) ≤ (1 / 3) * ((a + lam₁) ^ 3 / L ^ 2))
      linarith [e0, e1, e2]

/-- The prime-factor sums are non-negative. -/
private lemma primeFactorSum_nonneg (q : ℕ) (j : ℕ) :
    0 ≤ ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ j / (p : ℝ) :=
  Finset.sum_nonneg (fun p _ => div_nonneg (pow_nonneg (log_natCast_nonneg p) j)
    (Nat.cast_nonneg p))

theorem SigmaP3L_changeLevel_diff :
    ∃ C : ℝ, 0 < C ∧ ∀ {N q : ℕ} [NeZero N] [NeZero q] (hNq : N ∣ q) (ψ : DirichletCharacter ℂ N)
      {L : ℝ}, 1 ≤ L → ∀ {s : ℂ}, 1 < s.re → ∀ {a lam₁ : ℝ}, 0 < a → 0 ≤ lam₁ →
      |Work.ZeroFreeTables.SigmaP3L q L (DirichletCharacter.changeLevel hNq ψ) s a lam₁
        - Work.ZeroFreeTables.SigmaP3L N L ψ s a lam₁| ≤
      (C / L) * ((a + lam₁) * (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ))
        + ((a + lam₁) ^ 2 / L) * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ))
        + ((a + lam₁) ^ 3 / L ^ 2) * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ))) := by
  refine ⟨12, by norm_num, ?_⟩
  intro N q _ _ hNq ψ L hL s hs a lam₁ ha hlam₁
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hα : 0 ≤ a + lam₁ := by linarith
  set χ' : DirichletCharacter ℂ q := DirichletCharacter.changeLevel hNq ψ with hχ'def
  have hkey := key_bound hNq ψ hL hs ha hlam₁
  rw [← hχ'def] at hkey
  rw [SigmaP3L_eq_tsum_sigmaTerm, SigmaP3L_eq_tsum_sigmaTerm]
  rw [← mul_sub, abs_mul, abs_of_nonneg (inv_nonneg.mpr hLpos.le), ← Real.norm_eq_abs]
  refine le_trans (mul_le_mul_of_nonneg_left hkey (inv_nonneg.mpr hLpos.le)) ?_
  have hS3 : 0 ≤ ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ) :=
    primeFactorSum_nonneg q 3
  have hc3 : 0 ≤ (a + lam₁) ^ 3 / L ^ 2 := div_nonneg (pow_nonneg hα 3) (sq_nonneg L)
  have hstep : (12 * (a + lam₁) * (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ))
      + 12 * ((a + lam₁) ^ 2 / L) * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ))
      + 4 * ((a + lam₁) ^ 3 / L ^ 2) * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ)))
      ≤ (12 * (a + lam₁) * (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ))
      + 12 * ((a + lam₁) ^ 2 / L) * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ))
      + 12 * ((a + lam₁) ^ 3 / L ^ 2) * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ))) := by
    linarith [mul_nonneg hc3 hS3]
  calc L⁻¹ * (12 * (a + lam₁) * (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ))
        + 12 * ((a + lam₁) ^ 2 / L) * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ))
        + 4 * ((a + lam₁) ^ 3 / L ^ 2) * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ)))
      ≤ L⁻¹ * (12 * (a + lam₁) * (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ))
        + 12 * ((a + lam₁) ^ 2 / L) * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ))
        + 12 * ((a + lam₁) ^ 3 / L ^ 2) * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ))) :=
        mul_le_mul_of_nonneg_left hstep (inv_nonneg.mpr hLpos.le)
    _ = (12 / L) * ((a + lam₁) * (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ))
        + ((a + lam₁) ^ 2 / L) * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ))
        + ((a + lam₁) ^ 3 / L ^ 2) * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ))) := by
        ring

end Work.ZeroFreeTables.P9
