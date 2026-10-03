import Mathlib
import Submission.Work.FIChain.BpWinDefs
import Submission.Work.FITop.AtilInnerSumLeAd
import Submission.Work.FITop.SingleDvdTauSqLe
import Submission.Work.FIChain.rhoWindowC_param

namespace Work.FIChain

open Finset

attribute [local instance] Classical.propDecidable

/-! ### Scalar helpers: converting the saving `(log x)^{-2^26}` into a power saving

The main estimate below produces a saving `x^{-δ}` with `δ > 0`; the statement of
`singleDvd_atilc_le` asks for the stronger-looking `(log x)^{-2^26}`.  Since
`(log x)^{2^26} = o(x^δ)`, the power saving dominates it for all large `x`. -/

/-- `L ^ (-(2^26)) = (L ^ (2^26))⁻¹` (rpow exponent rewritten as a natural power). -/
private lemma rpow_neg_two_pow_26 {L : ℝ} (hL : 0 < L) :
    L ^ (-((2 : ℝ) ^ (26 : ℕ))) = (L ^ ((2 : ℕ) ^ 26))⁻¹ := by
  rw [show ((2 : ℝ) ^ (26 : ℕ)) = (((2 : ℕ) ^ 26 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_neg hL.le, Real.rpow_natCast]

/-- For every `δ > 0` and every large `x`, the power `x^{-δ}` is below `(log x)^{-2^26}`. -/
private lemma rpow_neg_le_log_rpow_neg_two_pow_26 {δ : ℝ} (hδ : 0 < δ) :
    ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      (x : ℝ) ^ (-δ) ≤ (Real.log (x : ℝ)) ^ (-((2 : ℝ) ^ (26 : ℕ))) := by
  obtain ⟨X, hX1, hX⟩ :=
    Commons.Analysis.ExpLog.const_mul_log_pow_le_rpow_threshold (K := 1) zero_le_one
      (n := (2 : ℕ) ^ 26) hδ
  refine ⟨max 2 (⌈X⌉₊ + 1), fun x hx => ?_⟩
  have hx2 : 2 ≤ x := le_trans (le_max_left _ _) hx
  have hxX : X ≤ (x : ℝ) := by
    have h1 : (⌈X⌉₊ + 1 : ℕ) ≤ x := le_trans (le_max_right _ _) hx
    have h2 : X ≤ ((⌈X⌉₊ : ℕ) : ℝ) := Nat.le_ceil X
    have h3 : ((⌈X⌉₊ + 1 : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast h1
    push_cast at h3
    linarith
  have hx0 : 0 < x := by omega
  have hxRpos : 0 < (x : ℝ) := by exact_mod_cast hx0
  have hx1 : 1 ≤ x := by omega
  have hxR1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
  have hxR2 : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx2
  have hlogpos : 0 < Real.log (x : ℝ) := Real.log_pos (by linarith)
  have hpow_le : (Real.log (x : ℝ)) ^ ((2 : ℕ) ^ 26) ≤ (x : ℝ) ^ δ := by
    have h := hX (x : ℝ) hxX
    simpa using h
  rw [Real.rpow_neg hxRpos.le, rpow_neg_two_pow_26 hlogpos]
  exact inv_anti₀ (pow_pos hlogpos _) hpow_le

/-- **The single-modulus slice of `ã`, with the saving `(log x)^{-2^26}`.**

For `b ≥ x^{1/4+ρ}` the multiples of `b` make up a proportion `≍ b^{-1}` of the mass of `ã`,
i.e. `Σ_{b ∣ n ≤ x} ã(n) ≪ Ã(x)/b`; together with `Ã(x) ≍ x^{3/4}` this is `≪ Ã(x) x^{-1/4-ρ}`,
and a power saving beats any power of `log`, giving the stated `(log x)^{-2^26}`.

The formal route is the already-proved pointwise congruence bound
`Ad_le_tau_sq_div_of_cubefree` (`A_b(x) ≤ C τ(b)²/b · A(x)` for cubefree `b` with `b² ≤ x`),
the divisor bound `τ(b)² ≤ C_ε b^{2ε}`, the domination `ã ≤ a` (`AtilInnerSumLeAd`), and
`A(x) ≪ Ã(x)`. -/
theorem singleDvd_atilc_le (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x → ∀ b : ℕ,
      (x : ℝ) ^ ((1 : ℝ) / 4 + ρ) ≤ (b : ℝ) → (b : ℝ) ≤ Real.sqrt (x : ℝ) →
      (∑ n ∈ (Finset.Icc 1 x).filter (fun n => b ∣ n), Work.FIChain.atilc n)
        ≤ C * Work.FIChain.AcountAtilC x * (Real.log (x : ℝ)) ^ (-((2 : ℝ) ^ (26 : ℕ))) := by
  classical
  -- the exponent `ε` of the divisor bound and the resulting power saving `δ`
  set ε : ℝ := ρ / (8 * (1 + ρ)) with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  have h2εlt : 2 * ε < 1 := by
    rw [hεdef, ← mul_div_assoc, div_lt_one (by positivity)]
    linarith
  set δ : ℝ := (1 - 2 * ε) * (1 / 4 + ρ) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact mul_pos (by linarith) (by linarith)
  -- the three inputs
  obtain ⟨Ca, hCapos, hAdle⟩ :=
    Commons.NumberTheory.FriedlanderIwaniec.Ad_le_tau_sq_div_of_cubefree
  obtain ⟨Cε, hCεpos, hCε⟩ :=
    Commons.NumberTheory.ArithmeticFunction.card_divisors_le_rpow ε hεpos
  obtain ⟨XK, hAseqK⟩ := Work.FITop.Aseq_le_const_mul_AcountAtil
  have hGpos : 0 < Submission.ASP.Gprod Submission.ASP.FIg := Submission.ASP.Gprod_FIg_pos
  set K : ℝ := 2 / Submission.ASP.Gprod Submission.ASP.FIg + 1 with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  set B : ℝ := Ca * Cε ^ 2 * K with hBdef
  have hBpos : 0 < B := by rw [hBdef]; positivity
  obtain ⟨Xlog, hXlog⟩ := rpow_neg_le_log_rpow_neg_two_pow_26 hδpos
  refine ⟨B, hBpos, max Xlog (max XK 3), ?_⟩
  intro x hx b hb_lo hb_hi
  have hxlog : Xlog ≤ x := le_trans (le_max_left _ _) hx
  have hxK : XK ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx3 : 3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hx0 : 0 < x := by omega
  have hxRpos : 0 < (x : ℝ) := by exact_mod_cast hx0
  have hx1 : 1 ≤ x := by omega
  have hxR1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
  have hx2 : 2 ≤ x := by omega
  have hxR2 : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx2
  have hlogpos : 0 < Real.log (x : ℝ) := Real.log_pos (by linarith)
  have hÃnn : (0 : ℝ) ≤ Work.FIChain.AcountAtilC x := Work.FITop.AcountAtil_nonneg' x
  have hlogδle : (x : ℝ) ^ (-δ) ≤ (Real.log (x : ℝ)) ^ (-((2 : ℝ) ^ (26 : ℕ))) :=
    hXlog x hxlog
  -- Step 1: the slice is dominated by the full congruence sum `A_b(x)`
  have hsum_le_Ad : (∑ n ∈ (Finset.Icc 1 x).filter (fun n => b ∣ n),
        Work.FIChain.atilc n) ≤ (Submission.Ad b x : ℝ) :=
    Work.FITop.AtilInnerSumLeAd b x
  by_cases hsf : Squarefree b
  · -- Step 2 (squarefree, hence cubefree `b`): the sharp congruence bound
    have hb1 : 1 ≤ b := by
      have h1 : (1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4 + ρ) := Real.one_le_rpow hxR1 (by linarith)
      have h2 : (1 : ℝ) ≤ (b : ℝ) := le_trans h1 hb_lo
      exact_mod_cast h2
    have hb0 : 0 < b := by omega
    have hbRpos : 0 < (b : ℝ) := by exact_mod_cast hb0
    have hbR0 : (0 : ℝ) ≤ (b : ℝ) := le_of_lt hbRpos
    have hbsq : b ^ 2 ≤ x := by
      have h1 : (b : ℝ) ^ 2 ≤ (Real.sqrt (x : ℝ)) ^ 2 := by
        nlinarith [hb_hi, Real.sqrt_nonneg (x : ℝ), hbR0]
      rw [Real.sq_sqrt (le_of_lt hxRpos)] at h1
      exact_mod_cast h1
    have hcb : ∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ b := by
      intro p hp hp3
      have hpp : p * p ∣ b := dvd_trans (show p * p ∣ p ^ 3 from ⟨p, by ring⟩) hp3
      exact (Nat.squarefree_iff_prime_squarefree.mp hsf) p hp hpp
    have hAdb : (Submission.Ad b x : ℝ)
        ≤ Ca * (((b.divisors.card : ℝ)) ^ 2 / (b : ℝ)) * (Submission.Aseq x : ℝ) :=
      hAdle b x hb1 hcb hbsq
    have hAseqK' : (Submission.Aseq x : ℝ) ≤ K * Work.FIChain.AcountAtilC x := by
      rw [hKdef]
      exact hAseqK x hxK
    -- the divisor bound turns `τ(b)²/b` into `C_ε² b^{2ε-1}`
    have htaub : ((b.divisors.card : ℝ)) ^ 2 / (b : ℝ) ≤ Cε ^ 2 * (b : ℝ) ^ (2 * ε - 1) := by
      have hcard := hCε b hb1
      have hsq : ((b.divisors.card : ℝ)) ^ 2 ≤ (Cε * (b : ℝ) ^ ε) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2
      have hexp : (Cε * (b : ℝ) ^ ε) ^ 2 = Cε ^ 2 * (b : ℝ) ^ (2 * ε) := by
        have h1 : ((b : ℝ) ^ ε) ^ 2 = (b : ℝ) ^ (2 * ε) := by
          rw [pow_two, ← Real.rpow_add hbRpos, show ε + ε = 2 * ε by ring]
        rw [mul_pow, h1]
      calc ((b.divisors.card : ℝ)) ^ 2 / (b : ℝ)
          ≤ (Cε ^ 2 * (b : ℝ) ^ (2 * ε)) / (b : ℝ) := by
            rw [← hexp]
            exact div_le_div_of_nonneg_right hsq hbR0
        _ = Cε ^ 2 * ((b : ℝ) ^ (2 * ε) / (b : ℝ)) := by ring
        _ = Cε ^ 2 * (b : ℝ) ^ (2 * ε - 1) := by
            rw [Real.rpow_sub hbRpos (2 * ε) 1, Real.rpow_one]
    -- the lower bound on `b` turns the exponent `2ε-1 < 0` into a gain `x^{-δ}`
    have hbp : (b : ℝ) ^ (2 * ε - 1) ≤ (x : ℝ) ^ (-δ) := by
      have h1 : (b : ℝ) ^ (2 * ε - 1) ≤ ((x : ℝ) ^ ((1 : ℝ) / 4 + ρ)) ^ (2 * ε - 1) :=
        Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hxRpos _) hb_lo (by linarith)
      have h2 : ((x : ℝ) ^ ((1 : ℝ) / 4 + ρ)) ^ (2 * ε - 1)
          = (x : ℝ) ^ (((1 : ℝ) / 4 + ρ) * (2 * ε - 1)) :=
        (Real.rpow_mul (le_of_lt hxRpos) ((1 : ℝ) / 4 + ρ) (2 * ε - 1)).symm
      rw [h2] at h1
      have h3 : ((1 : ℝ) / 4 + ρ) * (2 * ε - 1) = -δ := by rw [hδdef]; ring
      rwa [h3] at h1
    have hτb : ((b.divisors.card : ℝ)) ^ 2 / (b : ℝ) ≤ Cε ^ 2 * (x : ℝ) ^ (-δ) :=
      htaub.trans (mul_le_mul_of_nonneg_left hbp (by positivity))
    -- combine
    have hstep : (Submission.Ad b x : ℝ)
        ≤ Ca * (Cε ^ 2 * (x : ℝ) ^ (-δ)) * (K * Work.FIChain.AcountAtilC x) := by
      calc (Submission.Ad b x : ℝ)
          ≤ Ca * (((b.divisors.card : ℝ)) ^ 2 / (b : ℝ)) * (Submission.Aseq x : ℝ) := hAdb
        _ ≤ Ca * (Cε ^ 2 * (x : ℝ) ^ (-δ)) * (K * Work.FIChain.AcountAtilC x) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hτb (le_of_lt hCapos)) hAseqK'
              (Nat.cast_nonneg _)
              (mul_nonneg (le_of_lt hCapos)
                (mul_nonneg (by positivity) (Real.rpow_nonneg (le_of_lt hxRpos) _)))
    have hmain : (∑ n ∈ (Finset.Icc 1 x).filter (fun n => b ∣ n), Work.FIChain.atilc n)
        ≤ B * (x : ℝ) ^ (-δ) * Work.FIChain.AcountAtilC x := by
      calc (∑ n ∈ (Finset.Icc 1 x).filter (fun n => b ∣ n), Work.FIChain.atilc n)
          ≤ (Submission.Ad b x : ℝ) := hsum_le_Ad
        _ ≤ Ca * (Cε ^ 2 * (x : ℝ) ^ (-δ)) * (K * Work.FIChain.AcountAtilC x) := hstep
        _ = B * (x : ℝ) ^ (-δ) * Work.FIChain.AcountAtilC x := by rw [hBdef]; ring
    calc (∑ n ∈ (Finset.Icc 1 x).filter (fun n => b ∣ n), Work.FIChain.atilc n)
        ≤ B * (x : ℝ) ^ (-δ) * Work.FIChain.AcountAtilC x := hmain
      _ ≤ B * (Real.log (x : ℝ)) ^ (-((2 : ℝ) ^ (26 : ℕ))) * Work.FIChain.AcountAtilC x :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogδle (le_of_lt hBpos)) hÃnn
      _ = B * Work.FIChain.AcountAtilC x
            * (Real.log (x : ℝ)) ^ (-((2 : ℝ) ^ (26 : ℕ))) := by ring
  · -- Step 2 (non-squarefree `b`): every term of the slice vanishes
    have hzero : (∑ n ∈ (Finset.Icc 1 x).filter (fun n => b ∣ n), Work.FIChain.atilc n) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      rw [Finset.mem_filter] at hn
      have hnsf : ¬ Squarefree n := fun hsn => hsf (Squarefree.squarefree_of_dvd hn.2 hsn)
      exact Work.FITop.atilFIa_eq_zero_of_not_squarefree hnsf
    rw [hzero]
    exact mul_nonneg (mul_nonneg (le_of_lt hBpos) hÃnn)
      (Real.rpow_nonneg (le_of_lt hlogpos) _)

end Work.FIChain
