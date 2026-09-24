import Mathlib
import Submission.GM.Interfaces
import Submission.Work.GM.HB.hb_defs
import Submission.Work.GM.HB.kerr_dual_chain
import Submission.Work.GM.HB.kerr_main1_small
import Submission.Commons.NumberTheory.DirichletPolynomial.difference_sum_large_sieve
import Submission.Commons.NumberTheory.DirichletPolynomial.kerr_assembly
import Submission.Commons.NumberTheory.DirichletPolynomial.reflection_assembly
import Submission.Commons.NumberTheory.DirichletPolynomial.mv_difference_small_delta
import Submission.Commons.NumberTheory.DirichletPolynomial.pointwise_reflection_vdc

/-!
# Heath-Brown's Theorem 1.6 (Guth–Maynard Theorem 1.6) via Kerr's reflection

The chain (all inputs proved in `Submission/Commons/`):

* `pointwise_reflection_vdc` : the pointwise van der Corput transform at scale `N` (dual range
  `[⌈τ/4πN⌉, ⌊τ/2πN⌋]`);
* `kerr_main1` (Kerr's `lem:main1`, proved below from `kerr_dual_chain` + `kerr_main1_small`) :
  the annulus difference sum at scale `N` is dominated by the reflected window sum at scale
  `[⌈Δ/2N⌉, 2⌈Δ/N⌉]` plus the number of pairs;
* `reflection_assembly` (`mv_difference_small_delta_one` + `kerr_main1`) : Kerr's
  `cor:reflection`;
* `kerr_assembly` : Kerr's Theorem 3.2 (the §4 assembly);
* `difference_sum_easy_regime` : the complementary regime `T ≤ N` (large sieve).

Together they give `heath_brown_difference_sum`, whose statement is exactly
`Submission.GM.HBStatement`.
-/

open Finset Complex
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.GM.HB

noncomputable section

/-! ## Step A: the per-pair van der Corput sum over the annulus -/

/-- **Step A.** Summing the pointwise van der Corput transform over the annulus pairs, where
`Cv` is the constant of `Commons.NumberTheory.DirichletPolynomial.pointwise_reflection_vdc`
(in the shape of `hbm_per_pair`'s hypothesis). -/
lemma per_pair_sum {Cv : ℝ} (hCv : 0 < Cv)
    (hvdc : ∀ (N : ℕ), 1 ≤ N → ∀ (τ : ℝ), (N : ℝ) ≤ τ →
      ‖hbm N (2 * N) τ‖ ^ 2 ≤ Cv * (1 + Real.log (2 + τ)) ^ 4 *
        (1 + ‖hbm (Nat.ceil (τ / (4 * Real.pi * (N:ℝ))))
                (Nat.floor (τ / (2 * Real.pi * (N:ℝ)))) τ‖ ^ 2))
    {N : ℕ} (hN : 1 ≤ N) {Δ : ℝ} (hΔ : 1 ≤ Δ) (hNΔ : (N:ℝ) ≤ Δ)
    (R : ℕ) (t : Fin R → ℝ) :
    annSum N Δ R t ≤ Cv * (1 + Real.log (2 + 2 * Δ)) ^ 4 *
      (annDual N Δ R t + pcount (2 * Δ) R t) := by
  have hlog1 : (0:ℝ) ≤ 1 + Real.log (2 + 2 * Δ) := by
    have h2 : (1:ℝ) ≤ 2 + 2 * Δ := by linarith
    have := Real.log_nonneg h2
    linarith
  have hcoef : (0:ℝ) ≤ Cv * (1 + Real.log (2 + 2 * Δ)) ^ 4 := by positivity
  have hterm : ∀ i j : Fin R,
      (if Δ ≤ |t i - t j| ∧ |t i - t j| ≤ 2 * Δ then ‖hbm N (2 * N) (t i - t j)‖ ^ 2 else 0)
        ≤ Cv * (1 + Real.log (2 + 2 * Δ)) ^ 4 *
          ((if Δ ≤ |t i - t j| ∧ |t i - t j| ≤ 2 * Δ then
             ‖hbm (Nat.ceil (|t i - t j| / (4 * Real.pi * (N:ℝ))))
                  (Nat.floor (|t i - t j| / (2 * Real.pi * (N:ℝ)))) (t i - t j)‖ ^ 2
            else 0)
          + (if |t i - t j| ≤ 2 * Δ then (1:ℝ) else 0)) := by
    intro i j
    by_cases hc : Δ ≤ |t i - t j| ∧ |t i - t j| ≤ 2 * Δ
    · rw [if_pos hc]
      have h := hbm_per_pair hCv hvdc hN hΔ hNΔ hc.1 hc.2
      rw [if_pos hc, if_pos hc.2]
      refine le_trans h (le_of_eq (by ring))
    · rw [if_neg hc]
      have h3 : (0:ℝ) ≤ Cv * (1 + Real.log (2 + 2 * Δ)) ^ 4 *
          ((if Δ ≤ |t i - t j| ∧ |t i - t j| ≤ 2 * Δ then
             ‖hbm (Nat.ceil (|t i - t j| / (4 * Real.pi * (N:ℝ))))
                  (Nat.floor (|t i - t j| / (2 * Real.pi * (N:ℝ)))) (t i - t j)‖ ^ 2
            else 0)
          + (if |t i - t j| ≤ 2 * Δ then (1:ℝ) else 0)) := by
        refine mul_nonneg hcoef (add_nonneg (by positivity) ?_)
        by_cases h4 : |t i - t j| ≤ 2 * Δ
        · rw [if_pos h4]; norm_num
        · rw [if_neg h4]
      linarith
  have hsum : (∑ i : Fin R, ∑ j : Fin R, Cv * (1 + Real.log (2 + 2 * Δ)) ^ 4 *
        ((if Δ ≤ |t i - t j| ∧ |t i - t j| ≤ 2 * Δ then
           ‖hbm (Nat.ceil (|t i - t j| / (4 * Real.pi * (N:ℝ))))
                (Nat.floor (|t i - t j| / (2 * Real.pi * (N:ℝ)))) (t i - t j)‖ ^ 2
          else 0)
        + (if |t i - t j| ≤ 2 * Δ then (1:ℝ) else 0)))
      = Cv * (1 + Real.log (2 + 2 * Δ)) ^ 4 * (annDual N Δ R t + pcount (2 * Δ) R t) := by
    simp only [annDual, pcount, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  calc annSum N Δ R t
      ≤ ∑ i : Fin R, ∑ j : Fin R, Cv * (1 + Real.log (2 + 2 * Δ)) ^ 4 *
          ((if Δ ≤ |t i - t j| ∧ |t i - t j| ≤ 2 * Δ then
             ‖hbm (Nat.ceil (|t i - t j| / (4 * Real.pi * (N:ℝ))))
                  (Nat.floor (|t i - t j| / (2 * Real.pi * (N:ℝ)))) (t i - t j)‖ ^ 2
            else 0)
          + (if |t i - t j| ≤ 2 * Δ then (1:ℝ) else 0)) := by
        rw [annSum]
        exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = Cv * (1 + Real.log (2 + 2 * Δ)) ^ 4 * (annDual N Δ R t + pcount (2 * Δ) R t) := hsum

/-! ## Kerr's `lem:main1` -/

/-- Arithmetic step for the main regime of `kerr_main1`: combines the per-pair step (`hA`), the
log-absorption (`hlog`) and the dual chain (`hB`). -/
private lemma eps_main {ε Cv Cl Kd Δ A M W P : ℝ} (hCv : 0 < Cv) (hCl : 0 < Cl) (hKd : 0 < Kd)
    (hε : 0 < ε) (hΔ : 1 ≤ Δ) (hM : 0 ≤ M)
    (hA : A ≤ Cv * (1 + Real.log (2 + 2 * Δ)) ^ 4 * (M + P))
    (hlog : (1 + Real.log (2 + 2 * Δ)) ^ 4 ≤ Cl * Δ ^ (ε / 2))
    (hB : M ≤ Kd * Δ ^ (ε / 2) * (W + P)) (hW : 0 ≤ W) (hP : 0 ≤ P) :
    A ≤ (2 * Cv * Cl * (Kd + 1) + 1) * Δ ^ ε * (W + P) := by
  have hΔpos : (0:ℝ) < Δ := by linarith
  have heps : (1:ℝ) ≤ Δ ^ (ε / 2) := Real.one_le_rpow hΔ (by linarith)
  have hepsnn : (0:ℝ) ≤ Δ ^ (ε / 2) := le_trans zero_le_one heps
  have hmul : Δ ^ (ε / 2) * Δ ^ (ε / 2) = Δ ^ ε := by
    rw [← Real.rpow_add hΔpos]; ring_nf
  have hstep : Cv * (1 + Real.log (2 + 2 * Δ)) ^ 4 * (M + P)
      ≤ Cv * (Cl * Δ ^ (ε / 2)) * (Kd * Δ ^ (ε / 2) * (W + P) + P) := by
    have h1 : Cv * (1 + Real.log (2 + 2 * Δ)) ^ 4 ≤ Cv * (Cl * Δ ^ (ε / 2)) :=
      mul_le_mul_of_nonneg_left hlog hCv.le
    have h2 : M + P ≤ Kd * Δ ^ (ε / 2) * (W + P) + P := by linarith
    exact mul_le_mul h1 h2 (by linarith) (by positivity)
  have h4 : P ≤ Δ ^ (ε / 2) * (W + P) := by nlinarith [heps, hW, hP]
  have h5 : Δ ^ (ε / 2) * P ≤ Δ ^ (ε / 2) * (Δ ^ (ε / 2) * (W + P)) :=
    mul_le_mul_of_nonneg_left h4 hepsnn
  have h6 : Cv * (Cl * Δ ^ (ε / 2)) * (Kd * Δ ^ (ε / 2) * (W + P) + P)
      ≤ Cv * Cl * (Kd + 1) * Δ ^ ε * (W + P) := by
    have hCvCl : (0:ℝ) ≤ Cv * Cl := by positivity
    have e1 : Cv * (Cl * Δ ^ (ε / 2)) * (Kd * Δ ^ (ε / 2) * (W + P) + P)
        = Cv * Cl * (Kd * (Δ ^ (ε / 2) * Δ ^ (ε / 2)) * (W + P) + Δ ^ (ε / 2) * P) := by
      ring
    rw [e1, hmul]
    have h7 : Kd * Δ ^ ε * (W + P) + Δ ^ (ε / 2) * P ≤ (Kd + 1) * Δ ^ ε * (W + P) := by
      have h9 : (1:ℝ) ≤ Δ ^ ε := Real.one_le_rpow hΔ hε.le
      have h10 : Δ ^ (ε / 2) * P = Δ ^ (ε / 2) * P := rfl
      nlinarith [h5, hmul, hKd, hW, hP, h9, hepsnn, h10]
    calc Cv * Cl * (Kd * Δ ^ ε * (W + P) + Δ ^ (ε / 2) * P)
        ≤ Cv * Cl * ((Kd + 1) * Δ ^ ε * (W + P)) := mul_le_mul_of_nonneg_left h7 hCvCl
      _ = Cv * Cl * (Kd + 1) * Δ ^ ε * (W + P) := by ring
  have hfin : Cv * Cl * (Kd + 1) * Δ ^ ε * (W + P)
      ≤ (2 * Cv * Cl * (Kd + 1) + 1) * Δ ^ ε * (W + P) := by
    have h1 : Cv * Cl * (Kd + 1) ≤ 2 * Cv * Cl * (Kd + 1) + 1 := by
      have hp : (0:ℝ) < Cv * Cl * (Kd + 1) := by positivity
      linarith
    have h2 : (0:ℝ) ≤ Δ ^ ε * (W + P) := by positivity
    calc Cv * Cl * (Kd + 1) * Δ ^ ε * (W + P)
        = (Cv * Cl * (Kd + 1)) * (Δ ^ ε * (W + P)) := by ring
      _ ≤ (2 * Cv * Cl * (Kd + 1) + 1) * (Δ ^ ε * (W + P)) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = (2 * Cv * Cl * (Kd + 1) + 1) * Δ ^ ε * (W + P) := by ring
  linarith [hA, hstep, h6, hfin]

/-- Arithmetic step for the small regime of `kerr_main1`. -/
private lemma eps_small {ε Ks Δ A W P : ℝ} (hKs : 0 < Ks) (hε : 0 < ε) (hΔ : 1 ≤ Δ)
    (h : A ≤ Ks * Δ ^ ε * P) (hW : 0 ≤ W) (hP : 0 ≤ P) :
    A ≤ (Ks + 1) * Δ ^ ε * (W + P) := by
  have h1 : Ks * Δ ^ ε * P ≤ Ks * Δ ^ ε * (W + P) := by
    have h2 : (0:ℝ) ≤ Ks * Δ ^ ε := by positivity
    nlinarith [hW, hP, h2]
  have h3 : Ks * Δ ^ ε * (W + P) ≤ (Ks + 1) * Δ ^ ε * (W + P) := by
    have h4 : (0:ℝ) ≤ Δ ^ ε * (W + P) := by positivity
    calc Ks * Δ ^ ε * (W + P) = Ks * (Δ ^ ε * (W + P)) := by ring
      _ ≤ (Ks + 1) * (Δ ^ ε * (W + P)) := mul_le_mul_of_nonneg_right (by linarith) h4
      _ = (Ks + 1) * Δ ^ ε * (W + P) := by ring
  linarith [h, h1, h3]

/-- **Kerr's `lem:main1`** (arXiv:1909.12075): the difference sum over the annulus
`Δ ≤ |t_i - t_j| ≤ 2Δ` at scale `N` is dominated by the (coefficient-free) difference sums over
the reflected window `[⌈Δ/2N⌉, 2⌈Δ/N⌉]`, plus the number of pairs.  This is the `hmain` input of
`Commons.NumberTheory.DirichletPolynomial.reflection_assembly`.

Proved by the case split `Δ ≥ 100 N` (`kerr_dual_chain`) / `Δ < 100 N` (`kerr_main1_small`) on
top of the per-pair step `per_pair_sum`. -/
theorem kerr_main1 : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ), 1 ≤ N → ∀ (Δ : ℝ), 1 ≤ Δ → (N : ℝ) ≤ Δ →
    ∀ (R : ℕ) (t : Fin R → ℝ), (∀ i j, i ≠ j → 1 ≤ |t i - t j|) →
    (∑ i : Fin R, ∑ j : Fin R,
      (if Δ ≤ |t i - t j| ∧ |t i - t j| ≤ 2 * Δ then
        ‖∑ n ∈ Finset.Icc N (2 * N),
          (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
       else 0))
    ≤ C * Δ ^ ε *
      ((∑ i : Fin R, ∑ j : Fin R,
        (if |t i - t j| ≤ 2 * Δ then
          ‖∑ n ∈ Finset.Icc (Nat.ceil (Δ / (2 * (N : ℝ)))) (2 * Nat.ceil (Δ / (N : ℝ))),
            (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
         else 0))
      + (∑ i : Fin R, ∑ j : Fin R, (if |t i - t j| ≤ 2 * Δ then (1 : ℝ) else 0))) := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨Kd, hKd, hd⟩ := kerr_dual_chain (ε / 2) hε2
  obtain ⟨Ks, hKs, hs⟩ := kerr_main1_small ε hε
  obtain ⟨Cv, hCv, hvdc⟩ := Commons.NumberTheory.DirichletPolynomial.pointwise_reflection_vdc
  obtain ⟨Cl, hCl, hlog⟩ := log_pow_four_le_rpow (η := ε / 2) hε2
  refine ⟨max (2 * Cv * Cl * (Kd + 1) + 1) (Ks + 1) + 1, by positivity, ?_⟩
  intro N hN Δ hΔ hNΔ R t hsep
  have hΔpos : (0:ℝ) < Δ := by linarith
  have hΔe : (0:ℝ) ≤ Δ ^ ε := Real.rpow_nonneg hΔpos.le _
  have hWnn : (0:ℝ) ≤ winS (M1 N Δ) (B2 N Δ) (2 * Δ) R t := winS_nonneg _ _ _ _ _
  have hPnn : (0:ℝ) ≤ pcount (2 * Δ) R t := pcount_nonneg _ _ _
  have hWP : (0:ℝ) ≤ winS (M1 N Δ) (B2 N Δ) (2 * Δ) R t + pcount (2 * Δ) R t := by linarith
  have hmain : annSum N Δ R t ≤
      (max (2 * Cv * Cl * (Kd + 1) + 1) (Ks + 1) + 1) * Δ ^ ε *
        (winS (M1 N Δ) (B2 N Δ) (2 * Δ) R t + pcount (2 * Δ) R t) := by
    by_cases hcase : 100 * (N:ℝ) ≤ Δ
    · have hA := per_pair_sum hCv hvdc hN hΔ hNΔ R t
      have hB := hd N hN Δ hΔ hcase R t hsep
      have hlogb := hlog Δ hΔ
      have h1 := eps_main hCv hCl hKd hε hΔ (annDual_nonneg N Δ R t) hA hlogb hB hWnn hPnn
      refine le_trans h1 ?_
      have h4 : 2 * Cv * Cl * (Kd + 1) + 1
          ≤ max (2 * Cv * Cl * (Kd + 1) + 1) (Ks + 1) + 1 := by
        have := le_max_left (2 * Cv * Cl * (Kd + 1) + 1) (Ks + 1); linarith
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h4 hΔe) hWP
    · have hlt : Δ < 100 * (N:ℝ) := lt_of_not_ge hcase
      have hs' := hs N hN Δ hΔ hNΔ hlt R t hsep
      have h1 := eps_small hKs hε hΔ hs' hWnn hPnn
      refine le_trans h1 ?_
      have h4 : Ks + 1 ≤ max (2 * Cv * Cl * (Kd + 1) + 1) (Ks + 1) + 1 := by
        have := le_max_right (2 * Cv * Cl * (Kd + 1) + 1) (Ks + 1); linarith
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h4 hΔe) hWP
  simpa only [annSum, winS, pcount, hbm, M1, B2] using hmain

/-! ## Kerr's `cor:reflection` -/

/-- **The reflection** (Kerr's `cor:reflection`, arXiv:1909.12075): the difference sum at
scale `N` is controlled by the difference sum at the reflected scale `⌈4Δ/N⌉`. -/
theorem hb_reflection :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ), 1 ≤ N → ∀ (Δ : ℝ), 1 ≤ Δ → (N : ℝ) ≤ Δ → ∀ (B : ℝ), 1 ≤ B →
    ∀ (c : ℕ → ℂ), (∀ n, ‖c n‖ ≤ B) → ∀ (R : ℕ) (t : Fin R → ℝ),
    (∀ i j, i ≠ j → 1 ≤ |t i - t j|) →
    (∑ i : Fin R, ∑ j : Fin R,
      (if |t i - t j| ≤ Δ then
        ‖∑ n ∈ Finset.Icc N (2 * N),
          c n * (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
       else 0))
    ≤ C * B ^ 2 * Δ ^ ε *
      ((∑ i : Fin R, ∑ j : Fin R,
        (if |t i - t j| ≤ Δ then
          ‖∑ n ∈ Finset.Icc (Nat.ceil (4 * Δ / N)) (2 * Nat.ceil (4 * Δ / N)),
            (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
         else 0))
      + (∑ i : Fin R, ∑ j : Fin R, (if |t i - t j| ≤ Δ then (1 : ℝ) else 0))
      + (N : ℝ) ^ (1 + ε) * ((R : ℝ) + 1)) := by
  refine Commons.NumberTheory.DirichletPolynomial.reflection_assembly ?hmv kerr_main1
  intro ε hε
  obtain ⟨C, hC, h⟩ :=
    Commons.NumberTheory.DirichletPolynomial.mv_difference_small_delta_one ε hε
  exact ⟨C, hC, fun N hN Δ hΔ _ R t hsep =>
    by simpa only [div_mul_eq_mul_div] using h N hN Δ hΔ R t hsep⟩

/-! ## The regime `T ≤ N` (large sieve) -/

/-- Pure arithmetic: in the regime `T ≤ N` or `T ≤ R` the large-sieve bound
`R (T+N) N` is dominated by `R² N + R N² + R^{5/4} T^{1/2} N`. -/
private lemma ls_arith (R N T : ℝ) (hR : 0 ≤ R) (hN : 1 ≤ N) (hT : 1 ≤ T)
    (h : T ≤ N ∨ T ≤ R) :
    R * (T + N) * N ≤ 2 * (R ^ 2 * N + R * N ^ 2 + R ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * N) := by
  have h3 : 0 ≤ R ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * N := by
    have h1 : 0 ≤ R ^ ((5 : ℝ) / 4) := Real.rpow_nonneg hR _
    have h2 : 0 ≤ T ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (by linarith) _
    have h4 : 0 ≤ N := by linarith
    positivity
  rcases h with h | h
  · have hTN : T + N ≤ 2 * N := by linarith
    have hstep : R * (T + N) * N ≤ R * (2 * N) * N := by
      have h1 : R * (T + N) ≤ R * (2 * N) := mul_le_mul_of_nonneg_left hTN hR
      exact mul_le_mul_of_nonneg_right h1 (by linarith)
    have h2 : R * (2 * N) * N = 2 * (R * N ^ 2) := by ring
    rw [h2] at hstep
    nlinarith [hstep, sq_nonneg R, hR, hN, h3, mul_nonneg hR (by linarith : (0 : ℝ) ≤ N)]
  · have hRT : R * T ≤ R * R := mul_le_mul_of_nonneg_left h hR
    have hexp : R * (T + N) * N = R * T * N + R * N ^ 2 := by ring
    rw [hexp]
    nlinarith [hRT, hR, hN, h3, sq_nonneg R]

/-- The "easy" regime of `heath_brown_difference_sum`: when `T ≤ N` or `T ≤ R`, the
sampled large sieve already gives the required bound. -/
theorem difference_sum_easy_regime : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ), 1 ≤ N → ∀ (T : ℝ), 1 ≤ T → ∀ (a : ℕ → ℂ), (∀ n, ‖a n‖ ≤ 1) →
    ∀ (R : ℕ) (t : Fin R → ℝ),
      (∀ i, t i ∈ Set.Icc 0 T) →
      (∀ i j, i ≠ j → 1 ≤ |t i - t j|) →
      (T ≤ (N : ℝ) ∨ T ≤ (R : ℝ)) →
      (∑ i : Fin R, ∑ j : Fin R,
          ‖∑ n ∈ Finset.Icc N (2 * N), a n * (n : ℂ) ^ (I * ((t i - t j : ℝ) : ℂ))‖ ^ 2)
        ≤ C * ((R : ℝ) ^ 2 * (N : ℝ) + (R : ℝ) * (N : ℝ) ^ 2
            + (R : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * (N : ℝ)) := by
  obtain ⟨C, hC, hls⟩ := Commons.NumberTheory.DirichletPolynomial.difference_sum_large_sieve
  refine ⟨2 * C, by positivity, ?_⟩
  intro N hN T hT a ha R t hIcc hsep heasy
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hR0 : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg R
  have hmain := hls N hN T hT a ha R t hIcc hsep
  have harith := ls_arith (R : ℝ) (N : ℝ) T hR0 hN1 hT heasy
  calc (∑ i : Fin R, ∑ j : Fin R,
          ‖∑ n ∈ Finset.Icc N (2 * N), a n * (n : ℂ) ^ (I * ((t i - t j : ℝ) : ℂ))‖ ^ 2)
      ≤ C * (R : ℝ) * (T + (N : ℝ)) * (N : ℝ) := hmain
    _ = C * ((R : ℝ) * (T + (N : ℝ)) * (N : ℝ)) := by ring
    _ ≤ C * (2 * ((R : ℝ) ^ 2 * (N : ℝ) + (R : ℝ) * (N : ℝ) ^ 2
            + (R : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * (N : ℝ))) :=
        mul_le_mul_of_nonneg_left harith hC.le
    _ = 2 * C * ((R : ℝ) ^ 2 * (N : ℝ) + (R : ℝ) * (N : ℝ) ^ 2
            + (R : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * (N : ℝ)) := by ring


def Assm (N : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n ∈ Finset.Icc N (2 * N) then a n * (Real.sqrt (n : ℝ) : ℂ) else 0

lemma Assm_bound (N : ℕ) (hN : 1 ≤ N) (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) :
    ∀ n, ‖Assm N a n‖ ≤ Real.sqrt (2 * (N:ℝ)) := by
  intro n
  by_cases hn : n ∈ Finset.Icc N (2 * N)
  · rw [Assm, if_pos hn, norm_mul,
      show ‖(Real.sqrt (n : ℝ) : ℂ)‖ = |Real.sqrt (n : ℝ)| from RCLike.norm_ofReal _,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    have hn2 : (n : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).2
    have hsn : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
    have h1 : Real.sqrt (n : ℝ) ≤ Real.sqrt (2 * (N : ℝ)) := Real.sqrt_le_sqrt hn2
    calc ‖a n‖ * Real.sqrt (n : ℝ) ≤ 1 * Real.sqrt (2 * (N : ℝ)) :=
          mul_le_mul (ha n) h1 hsn (by norm_num)
      _ = Real.sqrt (2 * (N:ℝ)) := by rw [one_mul]
  · rw [Assm, if_neg hn, norm_zero]; positivity

lemma Assm_summand (N : ℕ) (hN : 1 ≤ N) (a : ℕ → ℂ) (θ : ℝ) :
    ∑ n ∈ Finset.Icc N (2 * N),
        Assm N a n * (n : ℂ) ^ (Complex.I * (θ : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)
      = ∑ n ∈ Finset.Icc N (2 * N), a n * (n : ℂ) ^ (Complex.I * (θ : ℂ)) := by
  refine Finset.sum_congr rfl ?_
  intro n hn
  rw [Assm, if_pos hn]
  have hn1 : (1:ℕ) ≤ n := le_trans hN (Finset.mem_Icc.mp hn).1
  have hs : (Real.sqrt (n : ℝ) : ℂ) ≠ 0 := by
    have h : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn1)
    exact_mod_cast h.ne'
  field_simp

lemma assm_window_eq (T : ℝ) (N : ℕ) (hN : 1 ≤ N) (a : ℕ → ℂ) (R : ℕ) (t : Fin R → ℝ)
    (hIcc : ∀ i, t i ∈ Set.Icc 0 T) :
    (∑ i : Fin R, ∑ j : Fin R,
      (if |t i - t j| ≤ T then
        ‖∑ n ∈ Finset.Icc N (2 * N),
          Assm N a n * (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
       else 0))
      = ∑ i : Fin R, ∑ j : Fin R,
        ‖∑ n ∈ Finset.Icc N (2 * N), a n * (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ))‖ ^ 2 := by
  refine Finset.sum_congr rfl ?_; intro i _
  refine Finset.sum_congr rfl ?_; intro j _
  have hij : |t i - t j| ≤ T := by
    have hi := hIcc i; have hj := hIcc j
    exact abs_le.mpr ⟨by linarith [hi.1, hj.2], by linarith [hi.2, hj.1]⟩
  rw [if_pos hij, Assm_summand N hN a (t i - t j)]


/-! ## The final theorem -/

/-- Heath-Brown's bound for Dirichlet polynomials on difference sets (classical):
for a `1`-separated set `t : Fin R → ℝ` in an interval of length `T` and coefficients
`‖a n‖ ≤ 1`,

`Σ_{i,j} ‖Σ_{v ≤ n ≤ 2v} a_n n^{i(t_i − t_j)}‖² ≤ C_ε T^ε (R²v + R v² + R^{5/4} T^{1/2} v)`.

This is Heath-Brown's classical estimate (Guth–Maynard cite it as their 2.2), used there
to bound the `S_2` term and the additive energy `E(W)`.  The epsilon-form (for every
`ε > 0` an absolute constant `C_ε`) is what the application needs.  Useful tools already
in the commons: the Montgomery–Vaughan Hilbert inequality
`Commons.LinearAlgebra.Matrix.mv_hilbert_separated` (which underlies both the mean value
bounds and Heath-Brown's argument), the log-free mean value bounds
`Commons.NumberTheory.DirichletPolynomial.mv_mean_value_logfree` and the block sampled
large sieve `Commons.NumberTheory.DirichletPolynomial.large_sieve_block_sampled`. -/
theorem heath_brown_difference_sum :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ), 1 ≤ N → ∀ (T : ℝ), 1 ≤ T → ∀ (a : ℕ → ℂ), (∀ n, ‖a n‖ ≤ 1) →
      ∀ (R : ℕ) (t : Fin R → ℝ),
        (∀ i, t i ∈ Set.Icc 0 T) →
        (∀ i j, i ≠ j → 1 ≤ |t i - t j|) →
        (∑ i : Fin R, ∑ j : Fin R,
            ‖∑ n ∈ Finset.Icc N (2 * N), a n * (n : ℂ) ^ (I * ((t i - t j : ℝ) : ℂ))‖ ^ 2)
          ≤ C * T ^ ε * ((R : ℝ) ^ 2 * (N : ℝ) + (R : ℝ) * (N : ℝ) ^ 2
              + (R : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * (N : ℝ)) := by
  intro ε hε
  obtain ⟨Ce, hCe, heasy⟩ := difference_sum_easy_regime
  obtain ⟨Cm, hCm, Hassm⟩ := Commons.NumberTheory.DirichletPolynomial.kerr_assembly hb_reflection ε hε
  refine ⟨2 * Cm + Ce + 1, by positivity, ?_⟩
  intro N hN T hT a ha R t hIcc hsep
  have hNN : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hB : (1:ℝ) ≤ Real.sqrt (2 * (N:ℝ)) := by
    rw [Real.one_le_sqrt]; linarith [show (1:ℝ) ≤ (N:ℝ) by exact_mod_cast hN]
  have hBsq : (Real.sqrt (2 * (N:ℝ))) ^ 2 = 2 * (N:ℝ) := Real.sq_sqrt (by positivity)
  have hnn : (0:ℝ) ≤ (R:ℝ)^2 * (N:ℝ) + (R:ℝ)*(N:ℝ)^2
      + (R:ℝ)^((5:ℝ)/4) * T^((1:ℝ)/2) * (N:ℝ) := by
    have h1 : (0:ℝ) ≤ (R:ℝ)^2 * (N:ℝ) := by positivity
    have h2 : (0:ℝ) ≤ (R:ℝ)*(N:ℝ)^2 := by positivity
    have h3 : (0:ℝ) ≤ (R:ℝ)^((5:ℝ)/4) * T^((1:ℝ)/2) * (N:ℝ) := by
      have h4 : (0:ℝ) ≤ (R:ℝ)^((5:ℝ)/4) := Real.rpow_nonneg (Nat.cast_nonneg R) _
      have h5 : (0:ℝ) ≤ T^((1:ℝ)/2) := Real.rpow_nonneg (by linarith) _
      positivity
    linarith
  by_cases hTN : T ≤ (N:ℝ)
  · have h := heasy N hN T hT a ha R t hIcc hsep (Or.inl hTN)
    have hTeps : (1:ℝ) ≤ T^ε := Real.one_le_rpow hT hε.le
    calc (∑ i : Fin R, ∑ j : Fin R,
            ‖∑ n ∈ Finset.Icc N (2 * N), a n * (n : ℂ) ^ (I * ((t i - t j : ℝ) : ℂ))‖ ^ 2)
        ≤ Ce * ((R : ℝ) ^ 2 * (N : ℝ) + (R : ℝ) * (N : ℝ) ^ 2
            + (R : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * (N : ℝ)) := h
      _ ≤ (2 * Cm + Ce + 1) * T ^ ε * ((R : ℝ) ^ 2 * (N : ℝ) + (R : ℝ) * (N : ℝ) ^ 2
            + (R : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * (N : ℝ)) := by
          have hle : Ce ≤ (2 * Cm + Ce + 1) * T^ε := by
            have h1 : (0:ℝ) < 2 * Cm + Ce + 1 := by positivity
            nlinarith [hTeps, h1, hCe]
          exact mul_le_mul_of_nonneg_right hle hnn
  · push_neg at hTN
    have h := Hassm N hN T hT hTN.le (Real.sqrt (2 * (N:ℝ))) hB (Assm N a)
      (Assm_bound N hN a ha) R t hIcc hsep
    rw [assm_window_eq T N hN a R t hIcc] at h
    have hbound : (∑ i : Fin R, ∑ j : Fin R,
          ‖∑ n ∈ Finset.Icc N (2 * N), a n * (n : ℂ) ^ (I * ((t i - t j : ℝ) : ℂ))‖ ^ 2)
        ≤ Cm * 2 * (N:ℝ) * T ^ ε * ((R:ℝ)^2 + (N:ℝ)*(R:ℝ)
            + T^((1:ℝ)/2)*(R:ℝ)^((5:ℝ)/4)) := by
      calc (∑ i : Fin R, ∑ j : Fin R,
            ‖∑ n ∈ Finset.Icc N (2 * N), a n * (n : ℂ) ^ (I * ((t i - t j : ℝ) : ℂ))‖ ^ 2)
          ≤ Cm * (Real.sqrt (2 * (N:ℝ))) ^ 2 * T ^ ε * ((R:ℝ)^2 + (N:ℝ)*(R:ℝ)
              + T^((1:ℝ)/2)*(R:ℝ)^((5:ℝ)/4)) := h
        _ = Cm * 2 * (N:ℝ) * T ^ ε * ((R:ℝ)^2 + (N:ℝ)*(R:ℝ)
              + T^((1:ℝ)/2)*(R:ℝ)^((5:ℝ)/4)) := by rw [hBsq]; ring
    refine le_trans hbound ?_
    have heq : Cm * 2 * (N:ℝ) * T ^ ε * ((R:ℝ)^2 + (N:ℝ)*(R:ℝ)
          + T^((1:ℝ)/2)*(R:ℝ)^((5:ℝ)/4))
        = 2 * Cm * T^ε * ((R:ℝ)^2 * (N:ℝ) + (R:ℝ)*(N:ℝ)^2
            + (R:ℝ)^((5:ℝ)/4) * T^((1:ℝ)/2) * (N:ℝ)) := by ring
    rw [heq]
    have hle : 2 * Cm ≤ 2 * Cm + Ce + 1 := by linarith
    have hTeps : (0:ℝ) ≤ T^ε := Real.rpow_nonneg (by linarith) _
    calc 2 * Cm * T^ε * ((R:ℝ)^2 * (N:ℝ) + (R:ℝ)*(N:ℝ)^2
            + (R:ℝ)^((5:ℝ)/4) * T^((1:ℝ)/2) * (N:ℝ))
        ≤ (2 * Cm + Ce + 1) * T^ε * ((R:ℝ)^2 * (N:ℝ) + (R:ℝ)*(N:ℝ)^2
            + (R:ℝ)^((5:ℝ)/4) * T^((1:ℝ)/2) * (N:ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hTeps) hnn
      _ = (2 * Cm + Ce + 1) * T ^ ε * ((R : ℝ) ^ 2 * (N : ℝ) + (R : ℝ) * (N : ℝ) ^ 2
            + (R : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * (N : ℝ)) := by ring


/-- **Heath-Brown's Theorem 1.6** (GM Theorem 1.6; Kerr arXiv:1909.12075 Thm 3.2 with `γ ≡ 1`);
see `Submission/GM/Interfaces.lean`. -/
theorem hb_statement : Submission.GM.HBStatement := heath_brown_difference_sum

end

end Work.GM.HB
