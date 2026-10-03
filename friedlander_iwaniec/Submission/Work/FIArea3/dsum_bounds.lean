/-
# `Submission.Work.FIArea3.dsum_bounds`

The three elementary divisor sums attached to the polar-box `τ`-average
(`Submission/Work/FIArea3/PairBracketDefs.lean`)

  `dsum1 K₁ K₂ = Σ_{d ≤ K₁} Σ_{e ≤ K₂} τ(d)⁹ τ(e)⁸ gcd(d,e)/(d e)`,
  `dsum2 K₁ K₂ = Σ_{d ≤ K₁} Σ_{e ≤ K₂} τ(d)⁹ τ(e)⁸ / √d`,
  `dsum3 K₁ K₂ = Σ_{d ≤ K₁} Σ_{e ≤ K₂} τ(d)⁹ τ(e)⁸`

are here bounded by explicit powers of `log`:

  `dsum1 ≤ C (log K₂+2)^{2⁹} (log K₁+2)^{2¹⁸}`,
  `dsum2 ≤ C √K₁ · K₂ (log K₁+2)^{2¹⁷} (log K₂+2)^{2⁸}`,
  `dsum3 ≤ C K₁ K₂ (log K₁+2)^{2⁹} (log K₂+2)^{2⁸}`.

The inputs are the two classical divisor-sum estimates `Work.FIArea2.sum_tau_pow_le`
(`Σ_{n ≤ X} τ(n)^k ≤ C X (log X+2)^{2^k}`) and `Work.FIArea2.sum_tau_pow_div_le`
(`Σ_{n ≤ X} τ(n)^k/n ≤ C (log X+2)^{2^k}`), the `√`-weighted companion proved below, and
`gcdTauSumLe` with `k = 8`:

  `Σ_{e ≤ K₂} τ(e)⁸ gcd(d,e)/e ≤ C (log K₂+2)^{2⁹} τ(d)⁹`.

For `dsum1` this gives the factor `τ(d)⁹ τ(d)⁹ = τ(d)^{18}`, whose `1/d`-weighted sum is bounded by
`sum_tau_pow_div_le` with `k = 18`, i.e. by `C (log K₁+2)^{2¹⁸} = C (log K₁+2)^{262144}` — exactly
the exponent in the statement.  For `dsum2`, `Σ_{d ≤ K₁} τ(d)⁹/√d ≤ √K₁ Σ_{d ≤ K₁} τ(d)⁹/d`
(pointwise `1/√d ≤ √K₁/d` when `d ≤ K₁`), giving `(log K₁+2)^{2⁹}` which is dominated by the
statement's `(log K₁+2)^{2¹⁷}` since the base is `≥ 1`.
-/
import Mathlib
import Submission.Work.FIArea3.PairBracketDefs
import Submission.Work.FIArea3.gcdTauSumLe
import Submission.Work.FIArea2.sum_tau_pow_le
import Submission.Work.FIArea2.sum_tau_pow_div_le

open Finset
open scoped BigOperators

namespace Work.FIArea3

noncomputable section

/-- `log X + 2 ≥ 1` for `X : ℕ` (in particular the base of every power below is at least `1`,
so raising the exponent only makes the bound larger). -/
private lemma log_base_one (X : ℕ) : (1 : ℝ) ≤ Real.log (X : ℝ) + 2 := by
  have := Real.log_natCast_nonneg X; linarith

/-- `log X + 2 ≥ 0`. -/
private lemma log_base_nonneg (X : ℕ) : (0 : ℝ) ≤ Real.log (X : ℝ) + 2 := by
  have := Real.log_natCast_nonneg X; linarith

/-- `Σ_{n ≤ X} τ(n)^k/√n ≤ C √X (log X + 2)^{2^k}`: the `√`-weighted companion of
`Work.FIArea2.sum_tau_pow_div_le`, from the pointwise `1/√n ≤ √X/n` valid for `1 ≤ n ≤ X`. -/
private lemma sum_tau_pow_div_sqrt_le (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ,
      (∑ n ∈ Finset.Icc 1 X, ((n.divisors.card : ℝ)) ^ k / Real.sqrt (n : ℝ))
        ≤ C * Real.sqrt (X : ℝ) * (Real.log (X : ℝ) + 2) ^ (2 ^ k) := by
  obtain ⟨C, hCpos, hC⟩ := Work.FIArea2.sum_tau_pow_div_le k
  refine ⟨C, hCpos, fun X => ?_⟩
  rcases Nat.eq_zero_or_pos X with hX | hX
  · subst hX; simp
  · have h1 : (∑ n ∈ Finset.Icc 1 X, ((n.divisors.card : ℝ)) ^ k / Real.sqrt (n : ℝ))
        ≤ Real.sqrt (X : ℝ) * (∑ n ∈ Finset.Icc 1 X, ((n.divisors.card : ℝ)) ^ k / (n:ℝ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun n hn => ?_
      obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
      have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
      have hs0 : (0:ℝ) < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hnpos
      have hsq : Real.sqrt (n:ℝ) ≤ Real.sqrt (X:ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hn2)
      have hτ : (0:ℝ) ≤ ((n.divisors.card : ℝ)) ^ k := pow_nonneg (Nat.cast_nonneg _) k
      have hnn : (n:ℝ) = Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ) :=
        calc (n:ℝ) = Real.sqrt (n:ℝ) ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg n)).symm
          _ = Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ) := by ring
      have hstep : (n:ℝ) ≤ Real.sqrt (X:ℝ) * Real.sqrt (n:ℝ) :=
        calc (n:ℝ) = Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ) := hnn
          _ ≤ Real.sqrt (X:ℝ) * Real.sqrt (n:ℝ) :=
              mul_le_mul_of_nonneg_right hsq (Real.sqrt_nonneg _)
      rw [← mul_div_assoc, div_le_div_iff₀ hs0 hnpos]
      calc ((n.divisors.card : ℝ)) ^ k * (n:ℝ)
          ≤ ((n.divisors.card : ℝ)) ^ k * (Real.sqrt (X:ℝ) * Real.sqrt (n:ℝ)) :=
            mul_le_mul_of_nonneg_left hstep hτ
        _ = Real.sqrt (X:ℝ) * ((n.divisors.card : ℝ)) ^ k * Real.sqrt (n:ℝ) := by ring
    calc (∑ n ∈ Finset.Icc 1 X, ((n.divisors.card : ℝ)) ^ k / Real.sqrt (n : ℝ))
        ≤ Real.sqrt (X:ℝ) * (∑ n ∈ Finset.Icc 1 X, ((n.divisors.card : ℝ)) ^ k / (n:ℝ)) := h1
      _ ≤ Real.sqrt (X:ℝ) * (C * (Real.log (X:ℝ) + 2)^(2^k)) :=
          mul_le_mul_of_nonneg_left (hC X) (Real.sqrt_nonneg _)
      _ = C * Real.sqrt (X:ℝ) * (Real.log (X:ℝ) + 2)^(2^k) := by ring

/-- `dsum1 K₁ K₂ ≤ C (log K₂+2)^{512} (log K₁+2)^{262144}`. -/
private lemma dsum1_bound : ∃ C : ℝ, 0 < C ∧ ∀ (K1 K2 : ℕ),
    dsum1 K1 K2 ≤ C * (Real.log (K2:ℝ)+2)^512 * (Real.log (K1:ℝ)+2)^262144 := by
  obtain ⟨Cg, hgp, hg⟩ := gcdTauSumLe 8
  obtain ⟨C18, h18p, h18⟩ := Work.FIArea2.sum_tau_pow_div_le 18
  refine ⟨Cg * C18, by positivity, fun K1 K2 => ?_⟩
  have hinner : ∀ d ∈ Finset.Icc 1 K1,
      (∑ e ∈ Finset.Icc 1 K2, Work.FIArea2.tauR e ^ 8 * (Nat.gcd d e : ℝ) / (e:ℝ))
        ≤ Cg * (Real.log (K2:ℝ)+2)^512 * (Work.FIArea2.tauR d)^9 := by
    intro d hd
    have h := hg K2 d (Finset.mem_Icc.mp hd).1
    simpa only [(show (8+1:ℕ) = 9 by norm_num), (show ((2:ℕ)^9) = 512 by norm_num),
      Work.FIArea2.tauR] using h
  have hfac : dsum1 K1 K2 = ∑ d ∈ Finset.Icc 1 K1, (Work.FIArea2.tauR d)^9 / (d:ℝ) *
      (∑ e ∈ Finset.Icc 1 K2, Work.FIArea2.tauR e ^ 8 * (Nat.gcd d e : ℝ) / (e:ℝ)) := by
    simp only [dsum1]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    ring
  have hstep : (∑ d ∈ Finset.Icc 1 K1, (Work.FIArea2.tauR d)^9 / (d:ℝ) *
        (∑ e ∈ Finset.Icc 1 K2, Work.FIArea2.tauR e ^ 8 * (Nat.gcd d e : ℝ) / (e:ℝ)))
      ≤ ∑ d ∈ Finset.Icc 1 K1, (Work.FIArea2.tauR d)^9 / (d:ℝ) *
        (Cg * (Real.log (K2:ℝ)+2)^512 * (Work.FIArea2.tauR d)^9) := by
    refine Finset.sum_le_sum fun d hd => ?_
    refine mul_le_mul_of_nonneg_left (hinner d hd) ?_
    exact div_nonneg (pow_nonneg (Work.FIArea2.tauR_nonneg d) 9) (Nat.cast_nonneg d)
  have hstep2 : (∑ d ∈ Finset.Icc 1 K1, (Work.FIArea2.tauR d)^9 / (d:ℝ) *
        (Cg * (Real.log (K2:ℝ)+2)^512 * (Work.FIArea2.tauR d)^9))
      = Cg * (Real.log (K2:ℝ)+2)^512 *
        (∑ d ∈ Finset.Icc 1 K1, (Work.FIArea2.tauR d)^18 / (d:ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [div_mul_eq_mul_div, ← mul_div_assoc]
    congr 1
    rw [show (18:ℕ) = 9 + 9 by norm_num, pow_add]
    ac_rfl
  have h18' : (∑ d ∈ Finset.Icc 1 K1, (Work.FIArea2.tauR d)^18 / (d:ℝ))
      ≤ C18 * (Real.log (K1:ℝ)+2)^262144 := by
    simpa only [(show ((2:ℕ)^18) = 262144 by norm_num), Work.FIArea2.tauR] using h18 K1
  rw [hfac]
  calc (∑ d ∈ Finset.Icc 1 K1, (Work.FIArea2.tauR d)^9 / (d:ℝ) *
      (∑ e ∈ Finset.Icc 1 K2, Work.FIArea2.tauR e ^ 8 * (Nat.gcd d e : ℝ) / (e:ℝ)))
      ≤ ∑ d ∈ Finset.Icc 1 K1, (Work.FIArea2.tauR d)^9 / (d:ℝ) *
        (Cg * (Real.log (K2:ℝ)+2)^512 * (Work.FIArea2.tauR d)^9) := hstep
    _ = Cg * (Real.log (K2:ℝ)+2)^512 *
        (∑ d ∈ Finset.Icc 1 K1, (Work.FIArea2.tauR d)^18 / (d:ℝ)) := hstep2
    _ ≤ Cg * (Real.log (K2:ℝ)+2)^512 * (C18 * (Real.log (K1:ℝ)+2)^262144) :=
        mul_le_mul_of_nonneg_left h18' (mul_nonneg hgp.le (pow_nonneg (log_base_nonneg K2) _))
    _ = Cg * C18 * (Real.log (K2:ℝ)+2)^512 * (Real.log (K1:ℝ)+2)^262144 := by ac_rfl

/-- `dsum2 K₁ K₂ ≤ C √K₁ · K₂ (log K₁+2)^{131072} (log K₂+2)^{256}`. -/
private lemma dsum2_bound : ∃ C : ℝ, 0 < C ∧ ∀ (K1 K2 : ℕ),
    dsum2 K1 K2 ≤ C * Real.sqrt (K1:ℝ) * (K2:ℝ)
      * (Real.log (K1:ℝ)+2)^131072 * (Real.log (K2:ℝ)+2)^256 := by
  obtain ⟨C9, h9p, h9⟩ := sum_tau_pow_div_sqrt_le 9
  obtain ⟨C8, h8p, h8⟩ := Work.FIArea2.sum_tau_pow_le 8
  refine ⟨C9 * C8, by positivity, fun K1 K2 => ?_⟩
  have hA : (∑ d ∈ Finset.Icc 1 K1, Work.FIArea2.tauR d ^ 9 / Real.sqrt (d:ℝ))
      ≤ C9 * Real.sqrt (K1:ℝ) * (Real.log (K1:ℝ)+2)^512 := by
    simpa only [(show ((2:ℕ)^9) = 512 by norm_num), Work.FIArea2.tauR] using h9 K1
  have hAlift : C9 * Real.sqrt (K1:ℝ) * (Real.log (K1:ℝ)+2)^512
      ≤ C9 * Real.sqrt (K1:ℝ) * (Real.log (K1:ℝ)+2)^131072 := by
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg h9p.le (Real.sqrt_nonneg _))
    exact pow_le_pow_right₀ (log_base_one K1) (by norm_num)
  have hB : (∑ e ∈ Finset.Icc 1 K2, Work.FIArea2.tauR e ^ 8)
      ≤ C8 * (K2:ℝ) * (Real.log (K2:ℝ)+2)^256 := by
    simpa only [(show ((2:ℕ)^8) = 256 by norm_num), Work.FIArea2.tauR] using h8 K2
  have hAnn : (0:ℝ) ≤ C9 * Real.sqrt (K1:ℝ) * (Real.log (K1:ℝ)+2)^131072 :=
    mul_nonneg (mul_nonneg h9p.le (Real.sqrt_nonneg _)) (pow_nonneg (log_base_nonneg K1) _)
  have hBnn : (0:ℝ) ≤ C8 * (K2:ℝ) * (Real.log (K2:ℝ)+2)^256 :=
    mul_nonneg (mul_nonneg h8p.le (Nat.cast_nonneg K2)) (pow_nonneg (log_base_nonneg K2) _)
  have hsum8nn : (0:ℝ) ≤ ∑ e ∈ Finset.Icc 1 K2, Work.FIArea2.tauR e ^ 8 :=
    Finset.sum_nonneg fun e he => pow_nonneg (Work.FIArea2.tauR_nonneg e) 8
  have hfac : dsum2 K1 K2 = (∑ d ∈ Finset.Icc 1 K1, Work.FIArea2.tauR d ^ 9 / Real.sqrt (d:ℝ))
      * (∑ e ∈ Finset.Icc 1 K2, Work.FIArea2.tauR e ^ 8) := by
    simp only [dsum2]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun e he => ?_
    ring
  rw [hfac]
  calc (∑ d ∈ Finset.Icc 1 K1, Work.FIArea2.tauR d ^ 9 / Real.sqrt (d:ℝ))
        * (∑ e ∈ Finset.Icc 1 K2, Work.FIArea2.tauR e ^ 8)
      ≤ (C9 * Real.sqrt (K1:ℝ) * (Real.log (K1:ℝ)+2)^131072)
        * (C8 * (K2:ℝ) * (Real.log (K2:ℝ)+2)^256) :=
        mul_le_mul (hA.trans hAlift) hB hsum8nn hAnn
    _ = C9 * C8 * Real.sqrt (K1:ℝ) * (K2:ℝ) * (Real.log (K1:ℝ)+2)^131072
        * (Real.log (K2:ℝ)+2)^256 := by ac_rfl

/-- `dsum3 K₁ K₂ ≤ C K₁ K₂ (log K₁+2)^{512} (log K₂+2)^{256}`. -/
private lemma dsum3_bound : ∃ C : ℝ, 0 < C ∧ ∀ (K1 K2 : ℕ),
    dsum3 K1 K2 ≤ C * (K1:ℝ) * (K2:ℝ)
      * (Real.log (K1:ℝ)+2)^512 * (Real.log (K2:ℝ)+2)^256 := by
  obtain ⟨C9, h9p, h9⟩ := Work.FIArea2.sum_tau_pow_le 9
  obtain ⟨C8, h8p, h8⟩ := Work.FIArea2.sum_tau_pow_le 8
  refine ⟨C9 * C8, by positivity, fun K1 K2 => ?_⟩
  have hA : (∑ d ∈ Finset.Icc 1 K1, Work.FIArea2.tauR d ^ 9)
      ≤ C9 * (K1:ℝ) * (Real.log (K1:ℝ)+2)^512 := by
    simpa only [(show ((2:ℕ)^9) = 512 by norm_num), Work.FIArea2.tauR] using h9 K1
  have hB : (∑ e ∈ Finset.Icc 1 K2, Work.FIArea2.tauR e ^ 8)
      ≤ C8 * (K2:ℝ) * (Real.log (K2:ℝ)+2)^256 := by
    simpa only [(show ((2:ℕ)^8) = 256 by norm_num), Work.FIArea2.tauR] using h8 K2
  have hAnn : (0:ℝ) ≤ C9 * (K1:ℝ) * (Real.log (K1:ℝ)+2)^512 :=
    mul_nonneg (mul_nonneg h9p.le (Nat.cast_nonneg K1)) (pow_nonneg (log_base_nonneg K1) _)
  have hfac : dsum3 K1 K2 = (∑ d ∈ Finset.Icc 1 K1, Work.FIArea2.tauR d ^ 9)
      * (∑ e ∈ Finset.Icc 1 K2, Work.FIArea2.tauR e ^ 8) := by
    simp only [dsum3]
    rw [Finset.sum_mul_sum]
  rw [hfac]
  calc (∑ d ∈ Finset.Icc 1 K1, Work.FIArea2.tauR d ^ 9)
        * (∑ e ∈ Finset.Icc 1 K2, Work.FIArea2.tauR e ^ 8)
      ≤ (C9 * (K1:ℝ) * (Real.log (K1:ℝ)+2)^512)
        * (C8 * (K2:ℝ) * (Real.log (K2:ℝ)+2)^256) :=
        mul_le_mul hA hB (Finset.sum_nonneg fun e he => pow_nonneg (Work.FIArea2.tauR_nonneg e) 8)
          hAnn
    _ = C9 * C8 * (K1:ℝ) * (K2:ℝ) * (Real.log (K1:ℝ)+2)^512
        * (Real.log (K2:ℝ)+2)^256 := by ac_rfl

theorem dsum_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ (K1 K2 : ℕ),
      Work.FIArea3.dsum1 K1 K2
          ≤ C * (Real.log (K2 : ℝ) + 2) ^ (512 : ℕ) * (Real.log (K1 : ℝ) + 2) ^ (262144 : ℕ)
      ∧ Work.FIArea3.dsum2 K1 K2
          ≤ C * Real.sqrt (K1 : ℝ) * (K2 : ℝ)
              * (Real.log (K1 : ℝ) + 2) ^ (131072 : ℕ) * (Real.log (K2 : ℝ) + 2) ^ (256 : ℕ)
      ∧ Work.FIArea3.dsum3 K1 K2
          ≤ C * (K1 : ℝ) * (K2 : ℝ)
              * (Real.log (K1 : ℝ) + 2) ^ (512 : ℕ) * (Real.log (K2 : ℝ) + 2) ^ (256 : ℕ) := by
  obtain ⟨C1, h1p, h1⟩ := dsum1_bound
  obtain ⟨C2, h2p, h2⟩ := dsum2_bound
  obtain ⟨C3, h3p, h3⟩ := dsum3_bound
  have hC1 : C1 ≤ C1 + C2 + C3 := by linarith only [h2p, h3p]
  have hC2 : C2 ≤ C1 + C2 + C3 := by linarith only [h1p, h3p]
  have hC3 : C3 ≤ C1 + C2 + C3 := by linarith only [h1p, h2p]
  refine ⟨C1 + C2 + C3, by positivity, fun K1 K2 => ⟨?_, ?_, ?_⟩⟩
  · have hP : (0:ℝ) ≤ (Real.log (K2:ℝ)+2)^(512:ℕ) := pow_nonneg (log_base_nonneg K2) _
    have hQ : (0:ℝ) ≤ (Real.log (K1:ℝ)+2)^(262144:ℕ) := pow_nonneg (log_base_nonneg K1) _
    have step1 : C1 * (Real.log (K2:ℝ)+2)^(512:ℕ)
        ≤ (C1+C2+C3) * (Real.log (K2:ℝ)+2)^(512:ℕ) := mul_le_mul_of_nonneg_right hC1 hP
    have step2 : C1 * (Real.log (K2:ℝ)+2)^(512:ℕ) * (Real.log (K1:ℝ)+2)^(262144:ℕ)
        ≤ (C1+C2+C3) * (Real.log (K2:ℝ)+2)^(512:ℕ) * (Real.log (K1:ℝ)+2)^(262144:ℕ) :=
      mul_le_mul_of_nonneg_right step1 hQ
    exact (h1 K1 K2).trans step2
  · have hA : (0:ℝ) ≤ (Real.log (K1:ℝ)+2)^(131072:ℕ) := pow_nonneg (log_base_nonneg K1) _
    have hB : (0:ℝ) ≤ (Real.log (K2:ℝ)+2)^(256:ℕ) := pow_nonneg (log_base_nonneg K2) _
    have hs : (0:ℝ) ≤ Real.sqrt (K1:ℝ) := Real.sqrt_nonneg _
    have hK2 : (0:ℝ) ≤ (K2:ℝ) := Nat.cast_nonneg K2
    have s1 : C2 * Real.sqrt (K1:ℝ) ≤ (C1+C2+C3) * Real.sqrt (K1:ℝ) :=
      mul_le_mul_of_nonneg_right hC2 hs
    have s2 : C2 * Real.sqrt (K1:ℝ) * (K2:ℝ) ≤ (C1+C2+C3) * Real.sqrt (K1:ℝ) * (K2:ℝ) :=
      mul_le_mul_of_nonneg_right s1 hK2
    have s3 : C2 * Real.sqrt (K1:ℝ) * (K2:ℝ) * (Real.log (K1:ℝ)+2)^(131072:ℕ)
        ≤ (C1+C2+C3) * Real.sqrt (K1:ℝ) * (K2:ℝ) * (Real.log (K1:ℝ)+2)^(131072:ℕ) :=
      mul_le_mul_of_nonneg_right s2 hA
    have s4 : C2 * Real.sqrt (K1:ℝ) * (K2:ℝ) * (Real.log (K1:ℝ)+2)^(131072:ℕ)
          * (Real.log (K2:ℝ)+2)^(256:ℕ)
        ≤ (C1+C2+C3) * Real.sqrt (K1:ℝ) * (K2:ℝ) * (Real.log (K1:ℝ)+2)^(131072:ℕ)
          * (Real.log (K2:ℝ)+2)^(256:ℕ) :=
      mul_le_mul_of_nonneg_right s3 hB
    exact (h2 K1 K2).trans s4
  · have hA : (0:ℝ) ≤ (Real.log (K1:ℝ)+2)^(512:ℕ) := pow_nonneg (log_base_nonneg K1) _
    have hB : (0:ℝ) ≤ (Real.log (K2:ℝ)+2)^(256:ℕ) := pow_nonneg (log_base_nonneg K2) _
    have hK1 : (0:ℝ) ≤ (K1:ℝ) := Nat.cast_nonneg K1
    have hK2 : (0:ℝ) ≤ (K2:ℝ) := Nat.cast_nonneg K2
    have t1 : C3 * (K1:ℝ) ≤ (C1+C2+C3) * (K1:ℝ) := mul_le_mul_of_nonneg_right hC3 hK1
    have t2 : C3 * (K1:ℝ) * (K2:ℝ) ≤ (C1+C2+C3) * (K1:ℝ) * (K2:ℝ) :=
      mul_le_mul_of_nonneg_right t1 hK2
    have t3 : C3 * (K1:ℝ) * (K2:ℝ) * (Real.log (K1:ℝ)+2)^(512:ℕ)
        ≤ (C1+C2+C3) * (K1:ℝ) * (K2:ℝ) * (Real.log (K1:ℝ)+2)^(512:ℕ) :=
      mul_le_mul_of_nonneg_right t2 hA
    have t4 : C3 * (K1:ℝ) * (K2:ℝ) * (Real.log (K1:ℝ)+2)^(512:ℕ) * (Real.log (K2:ℝ)+2)^(256:ℕ)
        ≤ (C1+C2+C3) * (K1:ℝ) * (K2:ℝ) * (Real.log (K1:ℝ)+2)^(512:ℕ) * (Real.log (K2:ℝ)+2)^(256:ℕ) :=
      mul_le_mul_of_nonneg_right t3 hB
    exact (h3 K1 K2).trans t4

end

end Work.FIArea3
