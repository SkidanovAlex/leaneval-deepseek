import Mathlib
import Submission.Work.FITop4.Defs4
import Submission.Work.FITop.AseqTauEightBound
import Submission.Work.FITop.AtilTauPowFourLe

namespace Work.FITop4.Red5

open Finset

/-- The `τ³`-weighted sum of the squarefree-supported sequence `ã = atilFIa` obeys the same
`Ã(x)(log x)^{2^17}` bound as the `τ⁴`-weighted sum: `τ³ ≤ τ⁴` termwise (as `τ` is a natural
cast, hence `= 0` or `≥ 1`), and `A(x) ≪ Ã(x)` by (9.12). -/
theorem AseqTauCubBound :
    ∃ C X₀ : ℕ, 0 < C ∧ ∀ y : ℕ, X₀ ≤ y →
      (∑ k ∈ Finset.Icc 1 y, Work.FITop.atilFIa k * ((k.divisors.card : ℝ) ^ 3))
        ≤ (C : ℝ) * Work.FITop.AcountAtil y * (Real.log (y : ℝ)) ^ (131072 : ℕ) := by
  classical
  obtain ⟨C4, hC4pos, X4, h4⟩ := Work.FITop.AtilTauPowFourLe
  obtain ⟨X1, hAtil⟩ := Submission.ASP.FI_Aseq_le_const_mul_Atil
  have hGpos : 0 < Submission.ASP.Gprod Submission.ASP.FIg := Submission.ASP.Gprod_FIg_pos
  set K : ℝ := 2 / Submission.ASP.Gprod Submission.ASP.FIg + 1 with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  refine ⟨⌈C4 * K⌉₊ + 1, max X4 (max X1 2), by positivity, ?_⟩
  intro y hy
  have hyX4 : X4 ≤ y := le_trans (le_max_left _ _) hy
  have hyX1 : X1 ≤ y := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hy)
  have hy2 : 2 ≤ y := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hy)
  have hy1 : 1 ≤ y := by omega
  have hyR1 : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy1
  have hlognn : 0 ≤ Real.log (y : ℝ) := Real.log_nonneg hyR1
  have hAcnn : 0 ≤ Work.FITop.AcountAtil y := by
    rw [Work.FITop.AcountAtil, Submission.ASP.Acount, Nat.floor_natCast]
    exact Finset.sum_nonneg (fun n _ => Work.FITop.atilFIa_nonneg n)
  have hAcge1 : (1 : ℝ) ≤ Work.FITop.AcountAtil y := by
    rw [Work.FITop.AcountAtil, Submission.ASP.Acount, Nat.floor_natCast]
    have hmem : (1 : ℕ) ∈ Finset.Icc 1 y := Finset.mem_Icc.mpr ⟨le_rfl, hy1⟩
    have hle : Work.FITop.atilFIa 1 ≤ ∑ n ∈ Finset.Icc 1 y, Work.FITop.atilFIa n :=
      Finset.single_le_sum (fun n _ => Work.FITop.atilFIa_nonneg n) hmem
    have hone : (1 : ℝ) ≤ Work.FITop.atilFIa 1 := by
      rw [Work.FITop.atilFIa, Submission.ASP.atil, Submission.ASP.FIa]
      have hmu : ((ArithmeticFunction.moebius 1 : ℝ)) ^ 2 = 1 := by
        norm_num [ArithmeticFunction.moebius_apply_one]
      rw [hmu, one_mul]
      exact_mod_cast Submission.ASP.an_one_pos'
    linarith
  -- ### Step 1: `τ³ ≤ τ⁴` termwise
  have hcub : (∑ k ∈ Finset.Icc 1 y, Work.FITop.atilFIa k * ((k.divisors.card : ℝ) ^ 3))
      ≤ ∑ k ∈ Finset.Icc 1 y, Work.FITop.atilFIa k * ((k.divisors.card : ℝ) ^ 4) := by
    refine Finset.sum_le_sum (fun k _ => ?_)
    have ha : 0 ≤ Work.FITop.atilFIa k := Work.FITop.atilFIa_nonneg k
    have ht : (k.divisors.card : ℝ) ^ 3 ≤ (k.divisors.card : ℝ) ^ 4 := by
      rcases Nat.eq_zero_or_pos k.divisors.card with h0 | hpos
      · rw [h0]; norm_num
      · have h1 : (1 : ℝ) ≤ (k.divisors.card : ℝ) := by exact_mod_cast hpos
        calc (k.divisors.card : ℝ) ^ 3 = (k.divisors.card : ℝ) ^ 3 * 1 := by ring
          _ ≤ (k.divisors.card : ℝ) ^ 3 * (k.divisors.card : ℝ) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = (k.divisors.card : ℝ) ^ 4 := by ring
    exact mul_le_mul_of_nonneg_left ht ha
  -- ### Step 2: the `τ⁴` bound
  have h4y : (∑ k ∈ Finset.Icc 1 y, Work.FITop.atilFIa k * ((k.divisors.card : ℝ) ^ 4))
      ≤ C4 * (Submission.Aseq y : ℝ) * (Real.log (y : ℝ)) ^ (131072 : ℕ) := by
    have h := h4 y hyX4
    have hexp : ((2 : ℕ) ^ 17) = 131072 := by norm_num
    simpa [hexp] using h
  -- ### Step 3: `A(x) ≪ Ã(x)` (9.12)
  have hAseq_le : (Submission.Aseq y : ℝ) ≤ K * Work.FITop.AcountAtil y := by
    have hAAtil : Work.FITop.AcountAtil y
        = Submission.ASP.Acount (Submission.ASP.atil Submission.ASP.FIa) (y : ℝ) := rfl
    have h := hAtil y hyX1
    rw [Submission.ASP.FI_Acount_eq] at h
    rw [← hAAtil] at h
    have h2 : (2 / Submission.ASP.Gprod Submission.ASP.FIg) * Work.FITop.AcountAtil y + 1
        ≤ K * Work.FITop.AcountAtil y := by
      rw [hKdef, add_mul, one_mul]
      linarith
    linarith [h]
  have hlogpow : 0 ≤ (Real.log (y : ℝ)) ^ (131072 : ℕ) := pow_nonneg hlognn _
  have hCK : C4 * K ≤ ((⌈C4 * K⌉₊ + 1 : ℕ) : ℝ) := by
    have h1 : C4 * K ≤ ((⌈C4 * K⌉₊ : ℕ) : ℝ) := Nat.le_ceil (C4 * K)
    push_cast
    linarith
  calc (∑ k ∈ Finset.Icc 1 y, Work.FITop.atilFIa k * ((k.divisors.card : ℝ) ^ 3))
      ≤ ∑ k ∈ Finset.Icc 1 y, Work.FITop.atilFIa k * ((k.divisors.card : ℝ) ^ 4) := hcub
    _ ≤ C4 * (Submission.Aseq y : ℝ) * (Real.log (y : ℝ)) ^ (131072 : ℕ) := h4y
    _ ≤ C4 * (K * Work.FITop.AcountAtil y) * (Real.log (y : ℝ)) ^ (131072 : ℕ) := by
        gcongr
    _ = (C4 * K) * Work.FITop.AcountAtil y * (Real.log (y : ℝ)) ^ (131072 : ℕ) := by ring
    _ ≤ ((⌈C4 * K⌉₊ + 1 : ℕ) : ℝ) * Work.FITop.AcountAtil y
          * (Real.log (y : ℝ)) ^ (131072 : ℕ) := by
        apply mul_le_mul_of_nonneg_right _ hlogpow
        exact mul_le_mul_of_nonneg_right hCK hAcnn

end Work.FITop4.Red5
