import Mathlib
import Submission.Work.LinnikAreas.Density4.LamRDefs
import Submission.Work.LinnikAreas.Density4.BzS3.S3InnerDefs
import Submission.Work.LinnikAreas.Density4.BzS3.S3_eq_restricted
import Submission.Work.LinnikAreas2.S3Hard.s3G_abel_sharp
import Submission.Work.LinnikAreas2.s3_hard_main_term
import Submission.Work.LinnikAreas2.s3_hard_error_BC
import Submission.Work.LinnikAreas2.s3_hard_error_sum_bound

set_option maxHeartbeats 1000000

namespace Work.LinnikAreas2

open Finset
open scoped BigOperators
open Work.LinnikAreas.Density4
open Work.LinnikAreas.Density4.BzS3

noncomputable section

/-!
# The hard-range second moment of the Graham correction term `B_z`

Target (`Work.LinnikAreas2.bz_sq_hard`): for `2 ≤ z ≤ N < z²`,

  `Σ_{n ≤ N} B_z(n)² ≤ N·log(N/z) + C·N`,

where `B_z(n) = Σ_{z < d ∣ n} μ(d)·log(d/z) = Λ_z(n) − Λ(n)` (`n ≥ 2`).

The proof is Graham's `S₃` computation (Graham, *J. Number Theory* **10** (1978) 83–94;
An, arXiv:2206.10104, §5, case `wy > x`, specialised to `k = ℚ`, `w = y = z`, `x = N`), i.e. the
exact quadruple reindexing of `Σ_{n≤N}B_z(n)²` followed by an asymptotic evaluation of its three
pieces.  The four analytic ingredients are proved in separate files:

* `Work.LinnikAreas.Density4.BzS3.S3_eq_restricted` — the exact reindexing
  `Σ_{n≤N}B_z(n)² = Σ_{q≤N/z}Σ_{r,t≤N/(qz)} [r⟂t]μ(r)μ(t)·(Gc(⌊N/(qrt)⌋) − Gc(max z/t z/r))`;
* `Work.LinnikAreas2.S3Hard.s3G_abel_sharp` — the sharp inner two-Abel estimate
  `|Gc(X) − Gm(X)| ≤ K·σ_{-1/2}(rt)·√X·(1+|log(2X) − α|)(1+|log(2X) − β|)`;
* `Work.LinnikAreas2.s3_hard_main_term`  — `Σ [...] Gm(⌊N/(qrt)⌋) = N·log(N/z) + O(N)`
  (Graham's `Σ_A`);
* `Work.LinnikAreas2.s3_hard_error_BC`   — `Σ [...] Gm(max z/t z/r) = O(N)`
  (Graham's `Σ_B + Σ_C`);
* `Work.LinnikAreas2.s3_hard_error_sum_bound` — the accumulated Abel error is `O(N)`.

This file handles the boundary case `X = 1` of the inner estimate (a finite explicit
computation) and assembles the five pieces into the target.
-/
/-! ## Abbreviations -/

/-- The Möbius multiplier `[r ⟂ t]·μ(r)·μ(t)` of the quadruple sum. -/
def mm (r t : ℕ) : ℝ :=
  if Nat.Coprime r t then
    (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) else 0

/-- The inner `s3G` at the cut-off `X`. -/
def Gc (z r t X : ℕ) : ℝ :=
  s3G (r * t) (Real.log ((z : ℝ) / (t : ℝ))) (Real.log ((z : ℝ) / (r : ℝ))) X

/-- The main term `s3main` at the cut-off `X`. -/
def Gm (z r t X : ℕ) : ℝ :=
  s3main (r * t) (Real.log ((z : ℝ) / (t : ℝ))) (Real.log ((z : ℝ) / (r : ℝ))) X

/-- The sharp inner-error weight, with the constant bumped to `K + 20` so that it also covers
the boundary case `X = 1`. -/
def Psi (K : ℝ) (α β : ℝ) (c X : ℕ) : ℝ :=
  (K + 20) * (∑ d ∈ c.divisors, 1 / Real.sqrt (d : ℝ)) * Real.sqrt (X : ℝ)
    * (1 + |Real.log (2 * (X : ℝ)) - α|) * (1 + |Real.log (2 * (X : ℝ)) - β|)

/-! ## Elementary lemmas -/

/-- `log A − log(z/t) = log(A·t/z)` for positive reals. -/
lemma log_sub_log_div_real {A t z : ℝ} (hA : 0 < A) (ht : 0 < t) (hz : 0 < z) :
    Real.log A - Real.log (z / t) = Real.log (A * t / z) := by
  rw [Real.log_div hz.ne' ht.ne', Real.log_div (by positivity) hz.ne',
    Real.log_mul hA.ne' ht.ne']
  ring

/-- `s3main` at `α = log(z/t)`, `β = log(z/r)`, with `log X − α` written as `log(X t / z)`. -/
lemma s3main_eq (c X t r z : ℕ) (hX : 0 < X) (ht : 0 < t) (hr : 0 < r) (hz : 0 < z) :
    s3main c (Real.log ((z : ℝ) / (t : ℝ))) (Real.log ((z : ℝ) / (r : ℝ))) X
      = (Real.pi ^ 2 / 6)⁻¹ * (∏ p ∈ c.primeFactors, (p : ℝ) / ((p : ℝ) + 1)) * (X : ℝ)
          * ((Real.log ((X : ℝ) * (t : ℝ) / (z : ℝ)) - 1)
              * (Real.log ((X : ℝ) * (r : ℝ) / (z : ℝ)) - 1) + 1) := by
  rw [s3main, s3c,
    log_sub_log_div_real (show (0 : ℝ) < (X : ℝ) by exact_mod_cast hX) (by exact_mod_cast ht)
      (by exact_mod_cast hz),
    log_sub_log_div_real (show (0 : ℝ) < (X : ℝ) by exact_mod_cast hX) (by exact_mod_cast hr)
      (by exact_mod_cast hz)]

/-- `|μ(n)| ≤ 1` for the real cast. -/
lemma abs_moebius_cast_le_one (n : ℕ) : |((ArithmeticFunction.moebius n : ℝ))| ≤ 1 := by
  have h2 : ((ArithmeticFunction.moebius n : ℝ)) ^ 2 ≤ 1 := by
    by_cases h : Squarefree n
    · have h1 : (ArithmeticFunction.moebius n : ℤ) ^ 2 = 1 :=
        ArithmeticFunction.moebius_sq_eq_one_of_squarefree h
      have hcast : ((ArithmeticFunction.moebius n : ℝ)) ^ 2
          = (((ArithmeticFunction.moebius n : ℤ) ^ 2 : ℤ) : ℝ) := by push_cast; ring
      rw [hcast, h1]; norm_num
    · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]; norm_num
  nlinarith [abs_nonneg ((ArithmeticFunction.moebius n : ℝ)),
    sq_abs ((ArithmeticFunction.moebius n : ℝ))]

/-- `|[r ⟂ t]·μ(r)·μ(t)| ≤ 1`. -/
lemma abs_mm_le_one (r t : ℕ) : |mm r t| ≤ 1 := by
  unfold mm
  split_ifs with h
  · rw [abs_mul]
    have h1 := abs_moebius_cast_le_one r
    have h2 := abs_moebius_cast_le_one t
    nlinarith [abs_nonneg ((ArithmeticFunction.moebius r : ℝ)),
      abs_nonneg ((ArithmeticFunction.moebius t : ℝ))]
  · simp

/-! ## The boundary case `X = 1` of the inner estimate -/

/-- At `X = 1` the difference `s3G − s3main` is the explicit `αβ − C_c((α+1)(β+1)+1)`, and
`(α+1) ≤ (1+log 2)(1+|log 2 − α|)` bounds it by the sharp weight. -/
lemma err_one (K : ℝ) (hK : 0 ≤ K) (c : ℕ) (hc : 1 ≤ c) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    |s3G c α β 1 - s3main c α β 1| ≤ Psi K α β c 1 := by
  have hG : s3G c α β 1 = α * β := by
    have h1 : (Finset.Icc 1 1).filter (fun m => Nat.Coprime m c ∧ Squarefree m) = {1} := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨h1, h2⟩, -⟩
        omega
      · rintro rfl
        exact ⟨⟨le_rfl, le_rfl⟩, Nat.coprime_one_left c, squarefree_one⟩
    rw [s3G, h1, Finset.sum_singleton]
    simp only [Nat.cast_one, Real.log_one]
    ring
  have hM : s3main c α β 1 = s3c c * ((α + 1) * (β + 1) + 1) := by
    rw [s3main]
    simp only [Nat.cast_one, Real.log_one]
    ring
  have hsc0 : 0 ≤ s3c c := by
    rw [s3c]
    positivity
  have hsc1 : s3c c ≤ 1 := by
    rw [s3c]
    have hpi : (1 : ℝ) < Real.pi ^ 2 / 6 := by
      have h3 := Real.pi_gt_three
      nlinarith [Real.pi_pos]
    have h1 : (Real.pi ^ 2 / 6)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ (by positivity)]
      exact le_of_lt hpi
    have h2 : (∏ p ∈ c.primeFactors, (p : ℝ) / ((p : ℝ) + 1)) ≤ 1 := by
      refine Finset.prod_le_one₀ (fun p _ => by positivity) (fun p hp => ?_)
      have hp2 : (0 : ℝ) < (p : ℝ) := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
      rw [div_le_one (by linarith)]
      linarith
    calc (Real.pi ^ 2 / 6)⁻¹ * (∏ p ∈ c.primeFactors, (p : ℝ) / ((p : ℝ) + 1))
        ≤ 1 * 1 := mul_le_mul h1 h2 (by positivity) (by norm_num)
      _ = 1 := by ring
  have hsig : 1 ≤ ∑ d ∈ c.divisors, 1 / Real.sqrt (d : ℝ) := by
    have hmem : (1 : ℕ) ∈ c.divisors := Nat.one_mem_divisors.mpr (by omega)
    have h := Finset.single_le_sum (s := c.divisors)
      (f := fun d : ℕ => (1 : ℝ) / Real.sqrt (d : ℝ)) (fun d _ => by positivity) hmem
    simpa using h
  have hαb : α + 1 ≤ (Real.log 2 + 1) * (1 + |Real.log 2 - α|) := by
    have h1 : α ≤ Real.log 2 + |Real.log 2 - α| := by
      have h := le_abs_self (α - Real.log 2)
      rw [abs_sub_comm] at h
      linarith
    have hL : (0 : ℝ) ≤ Real.log 2 := le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
    have hw : (0 : ℝ) ≤ |Real.log 2 - α| := abs_nonneg _
    have hmul : (0 : ℝ) ≤ Real.log 2 * |Real.log 2 - α| := mul_nonneg hL hw
    nlinarith [h1, hmul]
  have hβb : β + 1 ≤ (Real.log 2 + 1) * (1 + |Real.log 2 - β|) := by
    have h1 : β ≤ Real.log 2 + |Real.log 2 - β| := by
      have h := le_abs_self (β - Real.log 2)
      rw [abs_sub_comm] at h
      linarith
    have hL : (0 : ℝ) ≤ Real.log 2 := le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
    have hw : (0 : ℝ) ≤ |Real.log 2 - β| := abs_nonneg _
    have hmul : (0 : ℝ) ≤ Real.log 2 * |Real.log 2 - β| := mul_nonneg hL hw
    nlinarith [h1, hmul]
  have h1 : |α * β - s3c c * ((α + 1) * (β + 1) + 1)| ≤ 2 * ((α + 1) * (β + 1)) := by
    rw [abs_le]
    constructor <;> nlinarith [hsc0, hsc1, mul_nonneg hα hβ]
  have h2 : 2 * ((α + 1) * (β + 1))
      ≤ (K + 20) * (∑ d ∈ c.divisors, 1 / Real.sqrt (d : ℝ))
          * (1 + |Real.log 2 - α|) * (1 + |Real.log 2 - β|) := by
    have hprod : (α + 1) * (β + 1)
        ≤ (Real.log 2 + 1) * (1 + |Real.log 2 - α|)
          * ((Real.log 2 + 1) * (1 + |Real.log 2 - β|)) :=
      mul_le_mul hαb hβb (by positivity) (by positivity)
    have hconst : 2 * (Real.log 2 + 1) * (Real.log 2 + 1) ≤ K + 20 := by
      have hlog2 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
        linarith
      have h5 : (0 : ℝ) ≤ Real.log 2 + 1 := by
        have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
        linarith
      have h6 : (Real.log 2 + 1) * (Real.log 2 + 1) ≤ 2 * 2 :=
        mul_self_le_mul_self h5 (by linarith)
      nlinarith [hK, h6]
    have hbase : (0 : ℝ) ≤ (1 + |Real.log 2 - α|) * (1 + |Real.log 2 - β|) := by positivity
    calc 2 * ((α + 1) * (β + 1))
        ≤ 2 * ((Real.log 2 + 1) * (1 + |Real.log 2 - α|)
            * ((Real.log 2 + 1) * (1 + |Real.log 2 - β|))) := by linarith
      _ = (2 * (Real.log 2 + 1) * (Real.log 2 + 1))
            * ((1 + |Real.log 2 - α|) * (1 + |Real.log 2 - β|)) := by ring
      _ ≤ (K + 20) * ((1 + |Real.log 2 - α|) * (1 + |Real.log 2 - β|)) :=
            mul_le_mul_of_nonneg_right hconst hbase
      _ ≤ (K + 20) * (∑ d ∈ c.divisors, 1 / Real.sqrt (d : ℝ))
            * ((1 + |Real.log 2 - α|) * (1 + |Real.log 2 - β|)) := by
            have h20 : (0 : ℝ) ≤ K + 20 := by linarith
            have hk : (0 : ℝ) ≤ (K + 20) * ((1 + |Real.log 2 - α|) * (1 + |Real.log 2 - β|)) := by
              positivity
            calc (K + 20) * ((1 + |Real.log 2 - α|) * (1 + |Real.log 2 - β|))
                = ((K + 20) * ((1 + |Real.log 2 - α|) * (1 + |Real.log 2 - β|))) * 1 := by ring
              _ ≤ ((K + 20) * ((1 + |Real.log 2 - α|) * (1 + |Real.log 2 - β|)))
                    * (∑ d ∈ c.divisors, 1 / Real.sqrt (d : ℝ)) :=
                    mul_le_mul_of_nonneg_left hsig hk
              _ = (K + 20) * (∑ d ∈ c.divisors, 1 / Real.sqrt (d : ℝ))
                    * ((1 + |Real.log 2 - α|) * (1 + |Real.log 2 - β|)) := by ring
      _ = (K + 20) * (∑ d ∈ c.divisors, 1 / Real.sqrt (d : ℝ))
            * (1 + |Real.log 2 - α|) * (1 + |Real.log 2 - β|) := by ring
  have hPsi1 : Psi K α β c 1
      = (K + 20) * (∑ d ∈ c.divisors, 1 / Real.sqrt (d : ℝ))
          * (1 + |Real.log 2 - α|) * (1 + |Real.log 2 - β|) := by
    unfold Psi
    norm_num
  rw [hG, hM, hPsi1]
  exact le_trans h1 h2

/-! ## The range facts -/

/-- Arithmetic facts on the restricted range `1 ≤ q ≤ N/z`, `1 ≤ r,t ≤ N/(qz)`. -/
lemma range_facts {z N q r t : ℕ} (hz : 2 ≤ z) (hzN : N < z * z)
    (hq1 : 1 ≤ q) (hr1 : 1 ≤ r) (ht1 : 1 ≤ t)
    (hr2 : r ≤ N / (q * z)) (ht2 : t ≤ N / (q * z)) :
    1 ≤ N / (q * r * t) ∧ max (z / t) (z / r) ≤ N / (q * r * t) ∧ 1 ≤ max (z / t) (z / r)
      ∧ 1 ≤ r * t ∧ 0 ≤ Real.log ((z : ℝ) / (t : ℝ)) ∧ 0 ≤ Real.log ((z : ℝ) / (r : ℝ)) := by
  have hz0 : 0 < z := by omega
  have ht0 : 0 < t := by omega
  have hr0 : 0 < r := by omega
  have hqz : 0 < q * z := by positivity
  have hrN : r * (q * z) ≤ N := (Nat.le_div_iff_mul_le hqz).mp hr2
  have htN : t * (q * z) ≤ N := (Nat.le_div_iff_mul_le hqz).mp ht2
  have hqz' : z ≤ q * z := by
    calc z = z * 1 := by ring
      _ ≤ z * q := Nat.mul_le_mul_left z hq1
      _ = q * z := by ring
  have hqrz : q * r * z ≤ N := by
    calc q * r * z = r * (q * z) := by ring
      _ ≤ N := hrN
  have hqtz : q * t * z ≤ N := by
    calc q * t * z = t * (q * z) := by ring
      _ ≤ N := htN
  have htz : t * z ≤ N := le_trans (Nat.mul_le_mul_left t hqz') htN
  have hrz : r * z ≤ N := le_trans (Nat.mul_le_mul_left r hqz') hrN
  have htzlt : t < z := (Nat.mul_lt_mul_right hz0).mp (by linarith [htz, hzN])
  have hrzlt : r < z := (Nat.mul_lt_mul_right hz0).mp (by linarith [hrz, hzN])
  have hqrtpos : 0 < q * r * t := by positivity
  have hqrtN : q * r * t ≤ N := by
    calc q * r * t ≤ q * r * z := Nat.mul_le_mul_left (q * r) (le_of_lt htzlt)
      _ ≤ N := hqrz
  have hM1 : 1 ≤ N / (q * r * t) := by
    rw [Nat.le_div_iff_mul_le hqrtpos]
    simpa using hqrtN
  have hle1 : z / t ≤ N / (q * r * t) := by
    rw [Nat.le_div_iff_mul_le hqrtpos]
    calc z / t * (q * r * t) = (z / t * t) * (q * r) := by ring
      _ ≤ z * (q * r) := Nat.mul_le_mul_right (q * r) (Nat.div_mul_le_self z t)
      _ ≤ N := by
          calc z * (q * r) = q * r * z := by ring
            _ ≤ N := hqrz
  have hle2 : z / r ≤ N / (q * r * t) := by
    rw [Nat.le_div_iff_mul_le hqrtpos]
    calc z / r * (q * r * t) = (z / r * r) * (q * t) := by ring
      _ ≤ z * (q * t) := Nat.mul_le_mul_right (q * t) (Nat.div_mul_le_self z r)
      _ ≤ N := by
          calc z * (q * t) = q * t * z := by ring
            _ ≤ N := hqtz
  have hMle : max (z / t) (z / r) ≤ N / (q * r * t) := max_le hle1 hle2
  have hzt1 : 1 ≤ z / t := by
    rw [Nat.le_div_iff_mul_le ht0]
    simpa using le_of_lt htzlt
  have hzr1 : 1 ≤ z / r := by
    rw [Nat.le_div_iff_mul_le hr0]
    simpa using le_of_lt hrzlt
  have hMp1 : 1 ≤ max (z / t) (z / r) := le_trans hzt1 (le_max_left _ _)
  refine ⟨hM1, hMle, hMp1, by have := Nat.mul_le_mul hr1 ht1; simpa using this, ?_, ?_⟩
  · apply Real.log_nonneg
    have ht0' : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht0
    rw [le_div_iff₀ ht0']
    have : (t : ℝ) ≤ (z : ℝ) := by exact_mod_cast le_of_lt htzlt
    linarith
  · apply Real.log_nonneg
    have hr0' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr0
    rw [le_div_iff₀ hr0']
    have : (r : ℝ) ≤ (z : ℝ) := by exact_mod_cast le_of_lt hrzlt
    linarith

/-! ## The pointwise error bound -/

/-- The inner error at any cut-off `X ≥ 1` is bounded by the sharp weight `Psi K α β c X`
(the case `X ≥ 2` is `s3G_abel_sharp`, the case `X = 1` is `err_one`). -/
lemma err_bound {K : ℝ} (hK : 0 ≤ K)
    (hAbel : ∀ (c X : ℕ) (α β : ℝ), 1 ≤ c → 2 ≤ X → 0 ≤ α → 0 ≤ β →
      |s3G c α β X - s3main c α β X|
        ≤ K * (∑ d ∈ c.divisors, 1 / Real.sqrt (d : ℝ)) * Real.sqrt (X : ℝ)
            * (1 + |Real.log (2 * (X : ℝ)) - α|) * (1 + |Real.log (2 * (X : ℝ)) - β|))
    (c X : ℕ) (α β : ℝ) (hc : 1 ≤ c) (hX : 1 ≤ X) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    |s3G c α β X - s3main c α β X| ≤ Psi K α β c X := by
  rcases eq_or_lt_of_le hX with h | hX2
  · rw [← h]
    exact err_one K hK c hc α β hα hβ
  · have h := hAbel c X α β hc hX2 hα hβ
    refine le_trans h ?_
    unfold Psi
    have hs : (0 : ℝ) ≤ ∑ d ∈ c.divisors, 1 / Real.sqrt (d : ℝ) := by positivity
    have hXnn : (0 : ℝ) ≤ Real.sqrt (X : ℝ) := Real.sqrt_nonneg _
    have hu : (0 : ℝ) ≤ 1 + |Real.log (2 * (X : ℝ)) - α| := by positivity
    have hv : (0 : ℝ) ≤ 1 + |Real.log (2 * (X : ℝ)) - β| := by positivity
    have hK' : K ≤ K + 20 := by linarith
    have h1 : K * (∑ d ∈ c.divisors, 1 / Real.sqrt (d : ℝ))
        ≤ (K + 20) * (∑ d ∈ c.divisors, 1 / Real.sqrt (d : ℝ)) :=
      mul_le_mul_of_nonneg_right hK' hs
    have h2 : K * (∑ d ∈ c.divisors, 1 / Real.sqrt (d : ℝ)) * Real.sqrt (X : ℝ)
        ≤ (K + 20) * (∑ d ∈ c.divisors, 1 / Real.sqrt (d : ℝ)) * Real.sqrt (X : ℝ) :=
      mul_le_mul_of_nonneg_right h1 hXnn
    have h3 : K * (∑ d ∈ c.divisors, 1 / Real.sqrt (d : ℝ)) * Real.sqrt (X : ℝ)
          * (1 + |Real.log (2 * (X : ℝ)) - α|)
        ≤ (K + 20) * (∑ d ∈ c.divisors, 1 / Real.sqrt (d : ℝ)) * Real.sqrt (X : ℝ)
          * (1 + |Real.log (2 * (X : ℝ)) - α|) :=
      mul_le_mul_of_nonneg_right h2 hu
    exact mul_le_mul_of_nonneg_right h3 hv

/-! ## The pointwise key estimate -/

/-- `mm·(Gc(M) − Gc(M')) ≤ mm·(Gm(M) − Gm(M')) + (Psi(M) + Psi(M'))`. -/
lemma key_bound {K : ℝ} (hK : 0 ≤ K)
    (hAbel : ∀ (c X : ℕ) (α β : ℝ), 1 ≤ c → 2 ≤ X → 0 ≤ α → 0 ≤ β →
      |s3G c α β X - s3main c α β X|
        ≤ K * (∑ d ∈ c.divisors, 1 / Real.sqrt (d : ℝ)) * Real.sqrt (X : ℝ)
            * (1 + |Real.log (2 * (X : ℝ)) - α|) * (1 + |Real.log (2 * (X : ℝ)) - β|))
    {z N q r t : ℕ} (hz : 2 ≤ z) (hzN : N < z * z)
    (hq1 : 1 ≤ q) (hr1 : 1 ≤ r) (ht1 : 1 ≤ t)
    (hr2 : r ≤ N / (q * z)) (ht2 : t ≤ N / (q * z)) :
    mm r t * (Gc z r t (N / (q * r * t)) - Gc z r t (max (z / t) (z / r)))
      ≤ (mm r t * Gm z r t (N / (q * r * t)) - mm r t * Gm z r t (max (z / t) (z / r)))
        + (Psi K (Real.log ((z : ℝ) / (t : ℝ))) (Real.log ((z : ℝ) / (r : ℝ))) (r * t)
              (N / (q * r * t))
           + Psi K (Real.log ((z : ℝ) / (t : ℝ))) (Real.log ((z : ℝ) / (r : ℝ))) (r * t)
              (max (z / t) (z / r))) := by
  obtain ⟨hM1, hMle, hMp1, hrt1, hα, hβ⟩ := range_facts hz hzN hq1 hr1 ht1 hr2 ht2
  have he1 : |Gc z r t (N / (q * r * t)) - Gm z r t (N / (q * r * t))|
      ≤ Psi K (Real.log ((z : ℝ) / (t : ℝ))) (Real.log ((z : ℝ) / (r : ℝ))) (r * t)
          (N / (q * r * t)) :=
    err_bound hK hAbel (r * t) (N / (q * r * t)) _ _ hrt1 hM1 hα hβ
  have he2 : |Gc z r t (max (z / t) (z / r)) - Gm z r t (max (z / t) (z / r))|
      ≤ Psi K (Real.log ((z : ℝ) / (t : ℝ))) (Real.log ((z : ℝ) / (r : ℝ))) (r * t)
          (max (z / t) (z / r)) :=
    err_bound hK hAbel (r * t) (max (z / t) (z / r)) _ _ hrt1 hMp1 hα hβ
  have hmm : |mm r t| ≤ 1 := abs_mm_le_one r t
  have htri : |(Gc z r t (N / (q * r * t)) - Gm z r t (N / (q * r * t)))
        - (Gc z r t (max (z / t) (z / r)) - Gm z r t (max (z / t) (z / r)))|
      ≤ |Gc z r t (N / (q * r * t)) - Gm z r t (N / (q * r * t))|
        + |Gc z r t (max (z / t) (z / r)) - Gm z r t (max (z / t) (z / r))| := by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (Gc z r t (N / (q * r * t)) - Gm z r t (N / (q * r * t))),
        le_abs_self (Gc z r t (max (z / t) (z / r)) - Gm z r t (max (z / t) (z / r)))]
    · linarith [le_abs_self (Gc z r t (N / (q * r * t)) - Gm z r t (N / (q * r * t))),
        neg_le_abs (Gc z r t (max (z / t) (z / r)) - Gm z r t (max (z / t) (z / r)))]
  have key2 : mm r t * ((Gc z r t (N / (q * r * t)) - Gm z r t (N / (q * r * t)))
        - (Gc z r t (max (z / t) (z / r)) - Gm z r t (max (z / t) (z / r))))
      ≤ Psi K (Real.log ((z : ℝ) / (t : ℝ))) (Real.log ((z : ℝ) / (r : ℝ))) (r * t)
            (N / (q * r * t))
        + Psi K (Real.log ((z : ℝ) / (t : ℝ))) (Real.log ((z : ℝ) / (r : ℝ))) (r * t)
            (max (z / t) (z / r)) := by
    calc mm r t * ((Gc z r t (N / (q * r * t)) - Gm z r t (N / (q * r * t)))
          - (Gc z r t (max (z / t) (z / r)) - Gm z r t (max (z / t) (z / r))))
        ≤ |mm r t * ((Gc z r t (N / (q * r * t)) - Gm z r t (N / (q * r * t)))
          - (Gc z r t (max (z / t) (z / r)) - Gm z r t (max (z / t) (z / r))))| :=
          le_abs_self _
      _ = |mm r t| * |(Gc z r t (N / (q * r * t)) - Gm z r t (N / (q * r * t)))
          - (Gc z r t (max (z / t) (z / r)) - Gm z r t (max (z / t) (z / r)))| :=
          abs_mul _ _
      _ ≤ 1 * (|Gc z r t (N / (q * r * t)) - Gm z r t (N / (q * r * t))|
            + |Gc z r t (max (z / t) (z / r)) - Gm z r t (max (z / t) (z / r))|) :=
          mul_le_mul hmm htri (abs_nonneg _) (by norm_num)
      _ = |Gc z r t (N / (q * r * t)) - Gm z r t (N / (q * r * t))|
            + |Gc z r t (max (z / t) (z / r)) - Gm z r t (max (z / t) (z / r))| := by ring
      _ ≤ Psi K (Real.log ((z : ℝ) / (t : ℝ))) (Real.log ((z : ℝ) / (r : ℝ))) (r * t)
            (N / (q * r * t))
          + Psi K (Real.log ((z : ℝ) / (t : ℝ))) (Real.log ((z : ℝ) / (r : ℝ))) (r * t)
            (max (z / t) (z / r)) := add_le_add he1 he2
  calc mm r t * (Gc z r t (N / (q * r * t)) - Gc z r t (max (z / t) (z / r)))
      = mm r t * (Gm z r t (N / (q * r * t)) - Gm z r t (max (z / t) (z / r)))
        + mm r t * ((Gc z r t (N / (q * r * t)) - Gm z r t (N / (q * r * t)))
          - (Gc z r t (max (z / t) (z / r)) - Gm z r t (max (z / t) (z / r)))) := by ring
    _ ≤ (mm r t * Gm z r t (N / (q * r * t)) - mm r t * Gm z r t (max (z / t) (z / r)))
        + (Psi K (Real.log ((z : ℝ) / (t : ℝ))) (Real.log ((z : ℝ) / (r : ℝ))) (r * t)
              (N / (q * r * t))
           + Psi K (Real.log ((z : ℝ) / (t : ℝ))) (Real.log ((z : ℝ) / (r : ℝ))) (r * t)
              (max (z / t) (z / r))) := by
        have := key2
        have heq : mm r t * (Gm z r t (N / (q * r * t)) - Gm z r t (max (z / t) (z / r)))
            = mm r t * Gm z r t (N / (q * r * t)) - mm r t * Gm z r t (max (z / t) (z / r)) := by
          ring
        linarith [this, heq.symm.le, heq.le]


/-! ## The assembly -/

theorem bz_sq_hard_via_s3h :
    ∃ C : ℝ, 0 < C ∧ ∀ (z N : ℕ), 2 ≤ z → z ≤ N → N < z * z →
      (∑ n ∈ Finset.Icc 1 N, (Work.LinnikAreas.Density4.Bz z n) ^ 2)
        ≤ (N : ℝ) * Real.log ((N : ℝ) / (z : ℝ)) + C * (N : ℝ) := by
  obtain ⟨K, hKpos, hAbel⟩ := Work.LinnikAreas2.S3Hard.s3G_abel_sharp
  obtain ⟨C₁, hC₁pos, hMain⟩ := Work.LinnikAreas2.s3_hard_main_term
  obtain ⟨C₂, hC₂pos, hBC⟩ := Work.LinnikAreas2.s3_hard_error_BC
  obtain ⟨C₃, hC₃pos, hErrSum⟩ := Work.LinnikAreas2.s3_hard_error_sum_bound
  refine ⟨C₁ + C₂ + (K + 20) * C₃ + 1, by positivity, ?_⟩
  intro z N hz hzN hNz
  have hKnn : (0 : ℝ) ≤ K := le_of_lt hKpos
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hz0 : 0 < z := by omega
  rw [S3_eq_restricted z N hz hNz]
  change (∑ q ∈ Finset.Icc 1 (N / z), ∑ r ∈ Finset.Icc 1 (N / (q * z)),
      ∑ t ∈ Finset.Icc 1 (N / (q * z)),
        mm r t * (Gc z r t (N / (q * r * t)) - Gc z r t (max (z / t) (z / r))))
      ≤ (N : ℝ) * Real.log ((N : ℝ) / (z : ℝ)) + (C₁ + C₂ + (K + 20) * C₃ + 1) * (N : ℝ)
  have hkey : ∀ q ∈ Finset.Icc 1 (N / z), ∀ r ∈ Finset.Icc 1 (N / (q * z)), ∀ t ∈ Finset.Icc 1 (N / (q * z)),
      mm r t * (Gc z r t (N / (q * r * t)) - Gc z r t (max (z / t) (z / r)))
        ≤ (mm r t * Gm z r t (N / (q * r * t)) - mm r t * Gm z r t (max (z / t) (z / r)))
          + (Psi K (Real.log ((z : ℝ) / (t : ℝ))) (Real.log ((z : ℝ) / (r : ℝ))) (r * t)
                (N / (q * r * t))
             + Psi K (Real.log ((z : ℝ) / (t : ℝ))) (Real.log ((z : ℝ) / (r : ℝ))) (r * t)
                (max (z / t) (z / r))) := by
    intro q hq r hr t ht
    obtain ⟨hq1, _⟩ := Finset.mem_Icc.mp hq
    obtain ⟨hr1, hr2⟩ := Finset.mem_Icc.mp hr
    obtain ⟨ht1, ht2⟩ := Finset.mem_Icc.mp ht
    exact key_bound hKnn hAbel hz hNz hq1 hr1 ht1 hr2 ht2
  have hstep : (∑ q ∈ Finset.Icc 1 (N / z), ∑ r ∈ Finset.Icc 1 (N / (q * z)), ∑ t ∈ Finset.Icc 1 (N / (q * z)),
        mm r t * (Gc z r t (N / (q * r * t)) - Gc z r t (max (z / t) (z / r))))
      ≤ (∑ q ∈ Finset.Icc 1 (N / z), ∑ r ∈ Finset.Icc 1 (N / (q * z)),
        ∑ t ∈ Finset.Icc 1 (N / (q * z)),
          (mm r t * Gm z r t (N / (q * r * t)) - mm r t * Gm z r t (max (z / t) (z / r)))) + (∑ q ∈ Finset.Icc 1 (N / z), ∑ r ∈ Finset.Icc 1 (N / (q * z)),
        ∑ t ∈ Finset.Icc 1 (N / (q * z)),
          (Psi K (Real.log ((z : ℝ) / (t : ℝ))) (Real.log ((z : ℝ) / (r : ℝ))) (r * t)
              (N / (q * r * t))
           + Psi K (Real.log ((z : ℝ) / (t : ℝ))) (Real.log ((z : ℝ) / (r : ℝ))) (r * t)
              (max (z / t) (z / r)))) := by
    calc (∑ q ∈ Finset.Icc 1 (N / z), ∑ r ∈ Finset.Icc 1 (N / (q * z)), ∑ t ∈ Finset.Icc 1 (N / (q * z)),
          mm r t * (Gc z r t (N / (q * r * t)) - Gc z r t (max (z / t) (z / r))))
        ≤ (∑ q ∈ Finset.Icc 1 (N / z), ∑ r ∈ Finset.Icc 1 (N / (q * z)), ∑ t ∈ Finset.Icc 1 (N / (q * z)),
            ((mm r t * Gm z r t (N / (q * r * t)) - mm r t * Gm z r t (max (z / t) (z / r)))
              + (Psi K (Real.log ((z : ℝ) / (t : ℝ))) (Real.log ((z : ℝ) / (r : ℝ))) (r * t)
                    (N / (q * r * t))
                 + Psi K (Real.log ((z : ℝ) / (t : ℝ))) (Real.log ((z : ℝ) / (r : ℝ))) (r * t)
                    (max (z / t) (z / r))))) := by
          apply Finset.sum_le_sum
          intro q hq
          apply Finset.sum_le_sum
          intro r hr
          apply Finset.sum_le_sum
          intro t ht
          exact hkey q hq r hr t ht
      _ = (∑ q ∈ Finset.Icc 1 (N / z), ∑ r ∈ Finset.Icc 1 (N / (q * z)),
        ∑ t ∈ Finset.Icc 1 (N / (q * z)),
          (mm r t * Gm z r t (N / (q * r * t)) - mm r t * Gm z r t (max (z / t) (z / r)))) + (∑ q ∈ Finset.Icc 1 (N / z), ∑ r ∈ Finset.Icc 1 (N / (q * z)),
        ∑ t ∈ Finset.Icc 1 (N / (q * z)),
          (Psi K (Real.log ((z : ℝ) / (t : ℝ))) (Real.log ((z : ℝ) / (r : ℝ))) (r * t)
              (N / (q * r * t))
           + Psi K (Real.log ((z : ℝ) / (t : ℝ))) (Real.log ((z : ℝ) / (r : ℝ))) (r * t)
              (max (z / t) (z / r)))) := by
          simp only [Finset.sum_add_distrib]
  have hmid : (∑ q ∈ Finset.Icc 1 (N / z), ∑ r ∈ Finset.Icc 1 (N / (q * z)),
        ∑ t ∈ Finset.Icc 1 (N / (q * z)),
          (mm r t * Gm z r t (N / (q * r * t)) - mm r t * Gm z r t (max (z / t) (z / r))))
      = (∑ q ∈ Finset.Icc 1 (N / z), ∑ r ∈ Finset.Icc 1 (N / (q * z)),
        ∑ t ∈ Finset.Icc 1 (N / (q * z)), mm r t * Gm z r t (N / (q * r * t))) - (∑ q ∈ Finset.Icc 1 (N / z), ∑ r ∈ Finset.Icc 1 (N / (q * z)),
        ∑ t ∈ Finset.Icc 1 (N / (q * z)), mm r t * Gm z r t (max (z / t) (z / r))) := by
    simp only [Finset.sum_sub_distrib]
  have hTmain : (∑ q ∈ Finset.Icc 1 (N / z), ∑ r ∈ Finset.Icc 1 (N / (q * z)),
        ∑ t ∈ Finset.Icc 1 (N / (q * z)), mm r t * Gm z r t (N / (q * r * t))) = (∑ q ∈ Finset.Icc 1 (N / z), ∑ r ∈ Finset.Icc 1 (N / (q * z)),
            ∑ t ∈ Finset.Icc 1 (N / (q * z)),
              (if Nat.Coprime r t then
                (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) else 0)
              * ((Real.pi ^ 2 / 6)⁻¹ * (∏ p ∈ (r * t).primeFactors, (p : ℝ) / ((p : ℝ) + 1))
                  * ((N / (q * r * t) : ℕ) : ℝ)
                  * ((Real.log (((N / (q * r * t) : ℕ) : ℝ) * (t : ℝ) / (z : ℝ)) - 1)
                      * (Real.log (((N / (q * r * t) : ℕ) : ℝ) * (r : ℝ) / (z : ℝ)) - 1) + 1))) := by
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro t ht
    obtain ⟨hq1, _⟩ := Finset.mem_Icc.mp hq
    obtain ⟨hr1, hr2⟩ := Finset.mem_Icc.mp hr
    obtain ⟨ht1, ht2⟩ := Finset.mem_Icc.mp ht
    obtain ⟨hM1, _, _, hrt1, _, _⟩ := range_facts hz hNz hq1 hr1 ht1 hr2 ht2
    rw [mm, Gm, s3main_eq (r * t) (N / (q * r * t)) t r z (by omega) (by omega) (by omega) hz0]
  have hTbc : (∑ q ∈ Finset.Icc 1 (N / z), ∑ r ∈ Finset.Icc 1 (N / (q * z)),
        ∑ t ∈ Finset.Icc 1 (N / (q * z)), mm r t * Gm z r t (max (z / t) (z / r))) = (∑ q ∈ Finset.Icc 1 (N / z), ∑ r ∈ Finset.Icc 1 (N / (q * z)),
            ∑ t ∈ Finset.Icc 1 (N / (q * z)),
              (if Nat.Coprime r t then
                (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) else 0)
              * ((Real.pi ^ 2 / 6)⁻¹ * (∏ p ∈ (r * t).primeFactors, (p : ℝ) / ((p : ℝ) + 1))
                  * ((max (z / t) (z / r) : ℕ) : ℝ)
                  * ((Real.log (((max (z / t) (z / r) : ℕ) : ℝ) * (t : ℝ) / (z : ℝ)) - 1)
                      * (Real.log (((max (z / t) (z / r) : ℕ) : ℝ) * (r : ℝ) / (z : ℝ)) - 1)
                      + 1))) := by
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro t ht
    obtain ⟨hq1, _⟩ := Finset.mem_Icc.mp hq
    obtain ⟨hr1, hr2⟩ := Finset.mem_Icc.mp hr
    obtain ⟨ht1, ht2⟩ := Finset.mem_Icc.mp ht
    obtain ⟨_, _, hMp1, hrt1, _, _⟩ := range_facts hz hNz hq1 hr1 ht1 hr2 ht2
    rw [mm, Gm, s3main_eq (r * t) (max (z / t) (z / r)) t r z (by omega) (by omega) (by omega) hz0]
  have hMain_le : (∑ q ∈ Finset.Icc 1 (N / z), ∑ r ∈ Finset.Icc 1 (N / (q * z)),
            ∑ t ∈ Finset.Icc 1 (N / (q * z)),
              (if Nat.Coprime r t then
                (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) else 0)
              * ((Real.pi ^ 2 / 6)⁻¹ * (∏ p ∈ (r * t).primeFactors, (p : ℝ) / ((p : ℝ) + 1))
                  * ((N / (q * r * t) : ℕ) : ℝ)
                  * ((Real.log (((N / (q * r * t) : ℕ) : ℝ) * (t : ℝ) / (z : ℝ)) - 1)
                      * (Real.log (((N / (q * r * t) : ℕ) : ℝ) * (r : ℝ) / (z : ℝ)) - 1) + 1))) ≤ (N : ℝ) * Real.log ((N : ℝ) / (z : ℝ)) + C₁ * (N : ℝ) := by
    have h := hMain z N hz hzN hNz
    have h2 := (abs_le.mp h).2
    linarith
  have hBC_le : -((∑ q ∈ Finset.Icc 1 (N / z), ∑ r ∈ Finset.Icc 1 (N / (q * z)),
            ∑ t ∈ Finset.Icc 1 (N / (q * z)),
              (if Nat.Coprime r t then
                (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) else 0)
              * ((Real.pi ^ 2 / 6)⁻¹ * (∏ p ∈ (r * t).primeFactors, (p : ℝ) / ((p : ℝ) + 1))
                  * ((max (z / t) (z / r) : ℕ) : ℝ)
                  * ((Real.log (((max (z / t) (z / r) : ℕ) : ℝ) * (t : ℝ) / (z : ℝ)) - 1)
                      * (Real.log (((max (z / t) (z / r) : ℕ) : ℝ) * (r : ℝ) / (z : ℝ)) - 1)
                      + 1)))) ≤ C₂ * (N : ℝ) := by
    have h := hBC z N hz hzN hNz
    have h2 := (abs_le.mp h).1
    linarith
  have hErr : (∑ q ∈ Finset.Icc 1 (N / z), ∑ r ∈ Finset.Icc 1 (N / (q * z)),
        ∑ t ∈ Finset.Icc 1 (N / (q * z)),
          (Psi K (Real.log ((z : ℝ) / (t : ℝ))) (Real.log ((z : ℝ) / (r : ℝ))) (r * t)
              (N / (q * r * t))
           + Psi K (Real.log ((z : ℝ) / (t : ℝ))) (Real.log ((z : ℝ) / (r : ℝ))) (r * t)
              (max (z / t) (z / r)))) ≤ (K + 20) * C₃ * (N : ℝ) := by
    have heq : (∑ q ∈ Finset.Icc 1 (N / z), ∑ r ∈ Finset.Icc 1 (N / (q * z)),
        ∑ t ∈ Finset.Icc 1 (N / (q * z)),
          (Psi K (Real.log ((z : ℝ) / (t : ℝ))) (Real.log ((z : ℝ) / (r : ℝ))) (r * t)
              (N / (q * r * t))
           + Psi K (Real.log ((z : ℝ) / (t : ℝ))) (Real.log ((z : ℝ) / (r : ℝ))) (r * t)
              (max (z / t) (z / r)))) = (K + 20) * (∑ q ∈ Finset.Icc 1 (N / z), ∑ r ∈ Finset.Icc 1 (N / (q * z)),
      ∑ t ∈ Finset.Icc 1 (N / (q * z)),
        ((Real.sqrt (((N / (q * r * t) : ℕ) : ℝ))
            * (1 + |Real.log (2 * ((N / (q * r * t) : ℕ) : ℝ) * (t : ℝ) / (z : ℝ))|)
            * (1 + |Real.log (2 * ((N / (q * r * t) : ℕ) : ℝ) * (r : ℝ) / (z : ℝ))|)
          + Real.sqrt (((max (z / t) (z / r) : ℕ) : ℝ))
            * (1 + |Real.log (2 * ((max (z / t) (z / r) : ℕ) : ℝ) * (t : ℝ) / (z : ℝ))|)
            * (1 + |Real.log (2 * ((max (z / t) (z / r) : ℕ) : ℝ) * (r : ℝ) / (z : ℝ))|))
          * (∑ d ∈ (r * t).divisors, 1 / Real.sqrt (d : ℝ)))) := by
      have hpt : ∀ q ∈ Finset.Icc 1 (N / z), ∀ r ∈ Finset.Icc 1 (N / (q * z)),
          ∀ t ∈ Finset.Icc 1 (N / (q * z)),
          (Psi K (Real.log ((z : ℝ) / (t : ℝ))) (Real.log ((z : ℝ) / (r : ℝ))) (r * t)
              (N / (q * r * t))
           + Psi K (Real.log ((z : ℝ) / (t : ℝ))) (Real.log ((z : ℝ) / (r : ℝ))) (r * t)
              (max (z / t) (z / r)))
          = (K + 20) *
              ((Real.sqrt (((N / (q * r * t) : ℕ) : ℝ))
                  * (1 + |Real.log (2 * ((N / (q * r * t) : ℕ) : ℝ) * (t : ℝ) / (z : ℝ))|)
                  * (1 + |Real.log (2 * ((N / (q * r * t) : ℕ) : ℝ) * (r : ℝ) / (z : ℝ))|)
                + Real.sqrt (((max (z / t) (z / r) : ℕ) : ℝ))
                  * (1 + |Real.log (2 * ((max (z / t) (z / r) : ℕ) : ℝ) * (t : ℝ) / (z : ℝ))|)
                  * (1 + |Real.log (2 * ((max (z / t) (z / r) : ℕ) : ℝ) * (r : ℝ) / (z : ℝ))|))
                * (∑ d ∈ (r * t).divisors, 1 / Real.sqrt (d : ℝ))) := by
        intro q hq r hr t ht
        obtain ⟨hq1, _⟩ := Finset.mem_Icc.mp hq
        obtain ⟨hr1, hr2⟩ := Finset.mem_Icc.mp hr
        obtain ⟨ht1, ht2⟩ := Finset.mem_Icc.mp ht
        obtain ⟨hM1, _, hMp1, _, _, _⟩ := range_facts hz hNz hq1 hr1 ht1 hr2 ht2
        have hzpos : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hz0
        have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
        have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
        have hMpos : (0 : ℝ) < (((N / (q * r * t) : ℕ)) : ℝ) := by
          exact_mod_cast (by omega : 0 < N / (q * r * t))
        have hMppos : (0 : ℝ) < (((max (z / t) (z / r) : ℕ)) : ℝ) := by
          exact_mod_cast (by omega : 0 < max (z / t) (z / r))
        have hA1 : (0 : ℝ) < 2 * (((N / (q * r * t) : ℕ)) : ℝ) := by linarith
        have hA2 : (0 : ℝ) < 2 * (((max (z / t) (z / r) : ℕ)) : ℝ) := by linarith
        have h1 : |Real.log (2 * (((N / (q * r * t) : ℕ)) : ℝ))
              - Real.log ((z : ℝ) / (t : ℝ))|
            = |Real.log (2 * (((N / (q * r * t) : ℕ)) : ℝ) * (t : ℝ) / (z : ℝ))| :=
          congrArg abs (log_sub_log_div_real hA1 htpos hzpos)
        have h2 : |Real.log (2 * (((N / (q * r * t) : ℕ)) : ℝ))
              - Real.log ((z : ℝ) / (r : ℝ))|
            = |Real.log (2 * (((N / (q * r * t) : ℕ)) : ℝ) * (r : ℝ) / (z : ℝ))| :=
          congrArg abs (log_sub_log_div_real hA1 hrpos hzpos)
        have h3 : |Real.log (2 * (((max (z / t) (z / r) : ℕ)) : ℝ))
              - Real.log ((z : ℝ) / (t : ℝ))|
            = |Real.log (2 * (((max (z / t) (z / r) : ℕ)) : ℝ) * (t : ℝ) / (z : ℝ))| :=
          congrArg abs (log_sub_log_div_real hA2 htpos hzpos)
        have h4 : |Real.log (2 * (((max (z / t) (z / r) : ℕ)) : ℝ))
              - Real.log ((z : ℝ) / (r : ℝ))|
            = |Real.log (2 * (((max (z / t) (z / r) : ℕ)) : ℝ) * (r : ℝ) / (z : ℝ))| :=
          congrArg abs (log_sub_log_div_real hA2 hrpos hzpos)
        rw [Psi, Psi, h1, h2, h3, h4]
        ring
      rw [Finset.sum_congr rfl (fun q hq => Finset.sum_congr rfl (fun r hr =>
        Finset.sum_congr rfl (fun t ht => hpt q hq r hr t ht)))]
      simp only [Finset.mul_sum]
    rw [heq]
    have h := hErrSum z N hz hzN hNz
    have h20 : (0 : ℝ) ≤ K + 20 := by linarith
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h h20
  have hexp : (C₁ + C₂ + (K + 20) * C₃ + 1) * (N : ℝ)
      = C₁ * (N : ℝ) + C₂ * (N : ℝ) + (K + 20) * C₃ * (N : ℝ) + (N : ℝ) := by ring
  rw [hmid, hTmain, hTbc] at hstep
  linarith [hstep, hMain_le, hBC_le, hErr, hNnn, hexp]

end

end Work.LinnikAreas2
