/-
The area deliverable: primes `≡ 1 (mod 3)` with a logarithmic size bound.

For every `ℓ` there are `ℓ` distinct primes `r i ≡ 1 (mod 3)` with
`∑ i, log (r i) ≤ C * ℓ * log ℓ + C` for an absolute constant `C`.

This is proved by contradiction from the L-series lower bound of
`ArithmeticFunction.vonMangoldt.LSeries_residueClass_lower_bound` for the residue class
`1 mod 3`: if `goodPrimeSum` stayed below `ε * N` on some interval `[M, M ^ 400]`
with `ε = log 2 / 64`, the Dirichlet series of `Λ` on that class would be bounded
above by an expression incompatible with the lower bound `1 / (2 (x - 1)) - C`
(`bad_interval_impossible`).  Consequently, for every `ℓ`, taking `M` of size
`ℓ ^ 2` produces `N ≤ M ^ 400` with at least `ℓ` good primes below it, and the
enumeration lemma `exists_enum_of_sum_bound` extracts `r`.
-/
import Mathlib
import Submission.Work.Tower.APDensity.Basic
import Submission.Work.Tower.APDensity.Analytic.Assembly
import Submission.Work.Tower.APDensity.Count.exists_enum_of_sum_bound

open scoped BigOperators
open Finset

namespace Work.Tower

/-- For `n ≥ 1`: `n ≤ n log n / log 2 + 1 / log 2`. -/
private lemma self_le_mul_log_div_add {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) / Real.log 2 + 1 / Real.log 2 := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rcases eq_or_lt_of_le hn with h1 | h2
  · rw [← h1]
    have h2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have h3 : (1 : ℝ) ≤ 1 / Real.log 2 := by
      rw [le_div_iff₀ hlog2pos, one_mul]; exact h2
    simp only [Nat.cast_one, Real.log_one, mul_zero, zero_div, zero_add]
    exact h3
  · have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2
    have hlog : Real.log 2 ≤ Real.log (n : ℝ) := Real.log_le_log (by norm_num) hn2
    have h4 : (0 : ℝ) ≤ (n : ℝ) := by positivity
    have h5 : (n : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) / Real.log 2 := by
      rw [le_div_iff₀ hlog2pos]
      nlinarith [hlog, h4]
    have h6 : (0 : ℝ) ≤ 1 / Real.log 2 := by positivity
    linarith

/-- Elementary linear combination used at the end of the proof. -/
private lemma final_arith {A C x : ℝ} (hx : 0 ≤ x) (hAC : A + 800 ≤ C) :
    A * x + A + 800 * x ≤ C * x + C := by
  nlinarith [hx, hAC]

set_option maxHeartbeats 1000000 in
theorem exists_primes_mod_three_log_sum :
    ∃ C : ℝ, 0 < C ∧ ∀ ℓ : ℕ, ∃ r : Fin ℓ → ℕ,
      (∀ i, Nat.Prime (r i)) ∧ Function.Injective r ∧ (∀ i, r i % 3 = 1) ∧
      (∑ i, Real.log (r i : ℝ)) ≤ C * (ℓ : ℝ) * Real.log ℓ + C := by
  obtain ⟨M₀, hM₀pos, hM₀⟩ := bad_interval_impossible
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set B : ℝ := M₀ + 2 ^ 16 with hBdef
  have hB1 : 1 < B := by
    have : (2 : ℝ) ^ 16 ≤ B := by rw [hBdef]; linarith [hM₀pos]
    nlinarith
  have hlogBpos : 0 < Real.log B := Real.log_pos hB1
  set C : ℝ := 800 + 800 * Real.log B / Real.log 2 + 1 with hCdef
  have hCpos : 0 < C := by
    rw [hCdef]
    have h : 0 ≤ 800 * Real.log B / Real.log 2 :=
      div_nonneg (by linarith [hlogBpos]) hlog2pos.le
    linarith
  refine ⟨C, hCpos, fun ℓ => ?_⟩
  rcases Nat.eq_zero_or_pos ℓ with h0 | hpos
  · subst h0
    refine ⟨fun i => i.elim0, ?_, ?_, ?_, ?_⟩
    · intro i; exact i.elim0
    · intro i j _
      exact i.elim0
    · intro i; exact i.elim0
    · simp only [Finset.univ_eq_empty, Finset.sum_empty, Nat.cast_zero, mul_zero,
        Real.log_zero, zero_add]
      exact hCpos.le
  · -- the threshold and the analytic input
    set M : ℝ := max M₀ (2 ^ 16 * (ℓ : ℝ) ^ 2) with hMdef
    have hℓ1 : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hpos
    have hℓ2 : (1 : ℝ) ≤ (ℓ : ℝ) ^ 2 := by nlinarith
    have hM16 : 16 ≤ M := by
      have h2 : (16 : ℝ) ≤ 2 ^ 16 * (ℓ : ℝ) ^ 2 := by nlinarith [hℓ2]
      have h3 : (2 : ℝ) ^ 16 * (ℓ : ℝ) ^ 2 ≤ M := by rw [hMdef]; exact le_max_right _ _
      linarith
    obtain ⟨N, hMN, hNM, hSN⟩ := hM₀ M (le_max_left _ _)
    have hN2 : 2 ≤ N := by
      have : (2 : ℝ) ≤ (N : ℝ) := by linarith
      exact_mod_cast this
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
    have hN1 : 1 < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
    have hlogNpos : 0 < Real.log (N : ℝ) := Real.log_pos hN1
    -- the count of good primes below `N` is at least `ℓ`
    have hsqrt : 256 * (ℓ : ℝ) ≤ Real.sqrt M := by
      have h1 : Real.sqrt (2 ^ 16 * (ℓ : ℝ) ^ 2) ≤ Real.sqrt M := by
        rw [hMdef]; exact Real.sqrt_le_sqrt (le_max_right _ _)
      have h2 : Real.sqrt ((2 : ℝ) ^ 16 * (ℓ : ℝ) ^ 2) = 256 * (ℓ : ℝ) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ (2 : ℝ) ^ 16),
          Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (ℓ : ℝ))]
        rw [show Real.sqrt ((2 : ℝ) ^ 16) = 256 by
          rw [show (2 : ℝ) ^ 16 = (256 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      linarith [h1, h2 ▸ le_refl (256 * (ℓ : ℝ))]
    have hℓε : (ℓ : ℝ) ≤ (Real.log 2 / 64) * (N : ℝ) / Real.log (N : ℝ) := by
      have hεpos : 0 < Real.log 2 / 64 := by positivity
      have step1 : (ℓ : ℝ) ≤ (Real.log 2 / 64) * Real.sqrt M / 2 := by
        have hlog2gt : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
        nlinarith [hsqrt, hεpos, hlog2gt]
      have step2 : (Real.log 2 / 64) * Real.sqrt M / 2
          ≤ (Real.log 2 / 64) * Real.sqrt (N : ℝ) / 2 := by
        have := Real.sqrt_le_sqrt hMN
        nlinarith [this, hεpos]
      have step3 : (Real.log 2 / 64) * Real.sqrt (N : ℝ) / 2
          ≤ (Real.log 2 / 64) * (N : ℝ) / Real.log (N : ℝ) := by
        have hsq : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) := by
          rw [← pow_two, Real.sq_sqrt hN0]
        have h := log_le_two_mul_sqrt hN0
        have hkey : Real.sqrt (N : ℝ) * Real.log (N : ℝ) ≤ 2 * (N : ℝ) := by
          calc Real.sqrt (N : ℝ) * Real.log (N : ℝ)
              ≤ Real.sqrt (N : ℝ) * (2 * Real.sqrt (N : ℝ)) :=
                mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg _)
            _ = 2 * (Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ)) := by ring
            _ = 2 * (N : ℝ) := by rw [hsq]
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hlogNpos]
        have h3 : (Real.log 2 / 64) * (Real.sqrt (N : ℝ) * Real.log (N : ℝ))
            ≤ (Real.log 2 / 64) * (2 * (N : ℝ)) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
        linarith [h3]
      linarith [step1, step2, step3]
    obtain ⟨r, hpr, hinj, hmod, hlt, hsum⟩ :=
      Work.Tower.APDensity.Count.exists_enum_of_sum_bound hN2 hSN hℓε
    refine ⟨r, hpr, hinj, hmod, ?_⟩
    -- bound the sum of logarithms
    have hNbound : (N : ℝ) ≤ B ^ (400 : ℝ) * (ℓ : ℝ) ^ (800 : ℝ) := by
      have hMle : M ≤ B * (ℓ : ℝ) ^ 2 := by
        have h16B : (2 : ℝ) ^ 16 ≤ B := by rw [hBdef]; linarith [hM₀pos]
        have hM₀B : M₀ ≤ B := by rw [hBdef]; linarith
        rw [hMdef]
        refine max_le ?_ ?_
        · calc M₀ = M₀ * 1 := (mul_one M₀).symm
            _ ≤ M₀ * (ℓ : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hℓ2 hM₀pos.le
            _ ≤ B * (ℓ : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hM₀B (by positivity)
        · exact mul_le_mul_of_nonneg_right h16B (by positivity)
      calc (N : ℝ) ≤ M ^ (400 : ℝ) := hNM
        _ ≤ (B * (ℓ : ℝ) ^ 2) ^ (400 : ℝ) :=
            Real.rpow_le_rpow (by linarith) hMle (by norm_num)
        _ = B ^ (400 : ℝ) * (ℓ : ℝ) ^ (800 : ℝ) := by
            have h1 : (B * (ℓ : ℝ) ^ 2) ^ (400 : ℝ)
                = B ^ (400 : ℝ) * ((ℓ : ℝ) ^ 2) ^ (400 : ℝ) :=
              Real.mul_rpow (by linarith : (0 : ℝ) ≤ B) (by positivity)
            rw [h1, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (ℓ : ℝ))]
            norm_num
    have hlogNbound : Real.log (N : ℝ) ≤ 400 * (Real.log B + 2 * Real.log (ℓ : ℝ)) := by
      have h1 : Real.log (N : ℝ) ≤ Real.log (B ^ (400 : ℝ) * (ℓ : ℝ) ^ (800 : ℝ)) :=
        Real.log_le_log (by linarith) hNbound
      rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow (by linarith : (0 : ℝ) < B),
        Real.log_rpow (by linarith : (0 : ℝ) < (ℓ : ℝ))] at h1
      linarith [h1]
    have hsum2 : (∑ i : Fin ℓ, Real.log (r i : ℝ))
        ≤ (ℓ : ℝ) * (400 * (Real.log B + 2 * Real.log (ℓ : ℝ))) :=
      hsum.trans (mul_le_mul_of_nonneg_left hlogNbound (by positivity))
    -- conclude
    have haux : (ℓ : ℝ) ≤ (ℓ : ℝ) * Real.log (ℓ : ℝ) / Real.log 2 + 1 / Real.log 2 :=
      self_le_mul_log_div_add hpos
    have hlogℓnonneg : 0 ≤ Real.log (ℓ : ℝ) := Real.log_nonneg hℓ1
    have hxnonneg : 0 ≤ (ℓ : ℝ) * Real.log (ℓ : ℝ) := mul_nonneg (by positivity) hlogℓnonneg
    have hdnn : 0 ≤ 400 * Real.log B / Real.log 2 :=
      div_nonneg (by linarith [hlogBpos]) hlog2pos.le
    have hCbig2 : 400 * Real.log B / Real.log 2 + 800 ≤ C := by
      rw [hCdef]
      have h8 : 800 * Real.log B / Real.log 2
          = (400 * Real.log B / Real.log 2) + (400 * Real.log B / Real.log 2) := by ring
      rw [h8]; linarith
    have h3 : 400 * Real.log B * (ℓ : ℝ)
        ≤ 400 * Real.log B * ((ℓ : ℝ) * Real.log (ℓ : ℝ) / Real.log 2 + 1 / Real.log 2) :=
      mul_le_mul_of_nonneg_left haux (by positivity)
    have h4 : (ℓ : ℝ) * (400 * (Real.log B + 2 * Real.log (ℓ : ℝ)))
        = 400 * Real.log B * (ℓ : ℝ) + 800 * (ℓ : ℝ) * Real.log (ℓ : ℝ) := by ring
    have h5 : 400 * Real.log B * ((ℓ : ℝ) * Real.log (ℓ : ℝ) / Real.log 2 + 1 / Real.log 2)
        = 400 * Real.log B / Real.log 2 * ((ℓ : ℝ) * Real.log (ℓ : ℝ))
          + 400 * Real.log B / Real.log 2 := by
      field_simp
      try ring
    have h6 := final_arith hxnonneg hCbig2
    linarith [hsum2, h3, h4, h5, h6]

end Work.Tower
