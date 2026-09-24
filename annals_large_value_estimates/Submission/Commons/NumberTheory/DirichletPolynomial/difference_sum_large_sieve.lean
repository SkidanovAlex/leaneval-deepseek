import Mathlib
import Submission.Commons.NumberTheory.DirichletPolynomial.large_sieve_block_sampled
import Submission.Commons.NumberTheory.DirichletPolynomial.dirPolyA_neg_eq_conj

namespace Commons.NumberTheory.DirichletPolynomial

open Complex Finset
open scoped BigOperators ComplexConjugate

set_option autoImplicit false

/-- Conjugation commutes with complex exponentiation of a natural number. -/
private lemma conj_cpow_natCast (n : ℕ) (z : ℂ) :
    (starRingEnd ℂ) ((n : ℂ) ^ z) = (n : ℂ) ^ ((starRingEnd ℂ) z) := by
  have h := starRingEnd_cpow_ofReal_nonneg (n : ℝ) (by positivity) z
  rwa [Complex.ofReal_natCast] at h

/-- The conjugate of the imaginary exponent `i·u`. -/
private lemma conj_I_mul (u : ℝ) :
    (starRingEnd ℂ) (Complex.I * (u : ℂ)) = -(Complex.I * (u : ℂ)) := by
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal]; ring

/-- Splitting `n^{i(u-v)}`: its conjugate factors as `conj(a n^{iu}) · n^{iv}`. -/
private lemma conj_mul_cpow_sub (a : ℂ) {n : ℕ} (hn : 0 < n) (u v : ℝ) :
    (starRingEnd ℂ) (a * (n : ℂ) ^ (Complex.I * (((u - v : ℝ)) : ℂ)))
      = (starRingEnd ℂ) (a * (n : ℂ) ^ (Complex.I * (u : ℂ)))
          * ((n : ℂ) ^ (Complex.I * (v : ℂ))) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hL : (starRingEnd ℂ) (a * (n : ℂ) ^ (Complex.I * (((u - v : ℝ)) : ℂ)))
      = (starRingEnd ℂ) a * (n : ℂ) ^ (-(Complex.I * (((u - v : ℝ)) : ℂ))) := by
    rw [map_mul, conj_cpow_natCast, conj_I_mul]
  have hR : (starRingEnd ℂ) (a * (n : ℂ) ^ (Complex.I * (u : ℂ)))
      = (starRingEnd ℂ) a * (n : ℂ) ^ (-(Complex.I * (u : ℂ))) := by
    rw [map_mul, conj_cpow_natCast, conj_I_mul]
  rw [hL, hR]
  have hexp : -(Complex.I * (((u - v : ℝ)) : ℂ))
      = -(Complex.I * (u : ℂ)) + Complex.I * (v : ℂ) := by
    push_cast; ring
  rw [hexp, Complex.cpow_add _ _ hn0]
  ring

/-- Power of a natural number with purely imaginary exponent has norm one. -/
private lemma norm_cpow_I_mul (n : ℕ) (hn : 1 ≤ n) (u : ℝ) :
    ‖(n : ℂ) ^ (Complex.I * (u : ℂ))‖ = 1 := by
  rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hn)]
  simp

theorem difference_sum_large_sieve : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (T : ℝ), 1 ≤ T → ∀ (a : ℕ → ℂ), (∀ n, ‖a n‖ ≤ 1) → ∀ (R : ℕ) (t : Fin R → ℝ), (∀ i, t i ∈ Set.Icc 0 T) → (∀ i j, i ≠ j → 1 ≤ |t i - t j|) → (∑ i : Fin R, ∑ j : Fin R, ‖∑ n ∈ Finset.Icc N (2 * N), a n * (n : ℂ) ^ (I * ((t i - t j : ℝ) : ℂ))‖ ^ 2) ≤ C * (R : ℝ) * (T + (N : ℝ)) * (N : ℝ) := by
  obtain ⟨C₀, hC₀pos, hls⟩ := large_sieve_block_sampled
  refine ⟨2 * C₀, by positivity, ?_⟩
  intro N hN T hT a ha R t htIcc htsep
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hTN_nonneg : (0 : ℝ) ≤ T + (N : ℝ) := by positivity
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hrow : ∀ i : Fin R,
      (∑ j : Fin R, ‖∑ n ∈ Finset.Icc N (2 * N), a n * (n : ℂ) ^ (I * ((t i - t j : ℝ) : ℂ))‖ ^ 2)
        ≤ C₀ * (T + (N : ℝ)) * ((N : ℝ) + 1) := by
    intro i
    set d : ℕ → ℂ :=
      fun n => if n ∈ Finset.Icc N (2 * N)
        then (starRingEnd ℂ) (a n * (n : ℂ) ^ (I * ((t i : ℝ) : ℂ))) else 0 with hd
    have hsupp : ∀ n, n ∉ Finset.Icc N (2 * N) → d n = 0 := by
      intro n hn; rw [hd]; simp [hn]
    have hls_i := hls N hN T hT0 d R t htIcc htsep hsupp
    have hterm : ∀ j : Fin R,
        ‖∑ n ∈ Finset.Icc N (2 * N), d n * (n : ℂ) ^ (I * ((t j : ℝ) : ℂ))‖
          = ‖∑ n ∈ Finset.Icc N (2 * N), a n * (n : ℂ) ^ (I * ((t i - t j : ℝ) : ℂ))‖ := by
      intro j
      have hconj : (starRingEnd ℂ)
            (∑ n ∈ Finset.Icc N (2 * N), a n * (n : ℂ) ^ (I * ((t i - t j : ℝ) : ℂ)))
          = ∑ n ∈ Finset.Icc N (2 * N), d n * (n : ℂ) ^ (I * ((t j : ℝ) : ℂ)) := by
        rw [map_sum]
        refine Finset.sum_congr rfl (fun n hn => ?_)
        have hnpos : 0 < n := by
          have h1 := (Finset.mem_Icc.mp hn).1; omega
        rw [hd]
        simp only [hn, if_true]
        exact conj_mul_cpow_sub (a n) hnpos (t i) (t j)
      rw [← hconj, Complex.norm_conj]
    calc (∑ j : Fin R, ‖∑ n ∈ Finset.Icc N (2 * N), a n * (n : ℂ) ^ (I * ((t i - t j : ℝ) : ℂ))‖ ^ 2)
        = ∑ j : Fin R, ‖∑ n ∈ Finset.Icc N (2 * N), d n * (n : ℂ) ^ (I * ((t j : ℝ) : ℂ))‖ ^ 2 := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [hterm j]
      _ ≤ C₀ * (T + (N : ℝ)) * (∑ n ∈ Finset.Icc N (2 * N), ‖d n‖ ^ 2) := hls_i
      _ ≤ C₀ * (T + (N : ℝ)) * ((N : ℝ) + 1) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc ∑ n ∈ Finset.Icc N (2 * N), ‖d n‖ ^ 2
              ≤ ∑ n ∈ Finset.Icc N (2 * N), (1 : ℝ) := by
                refine Finset.sum_le_sum (fun n hn => ?_)
                have hn1 : 1 ≤ n := by
                  have h1 := (Finset.mem_Icc.mp hn).1; omega
                rw [hd]
                simp only [hn, if_true]
                rw [Complex.norm_conj, norm_mul, norm_cpow_I_mul n hn1 (t i), mul_one]
                nlinarith [ha n, norm_nonneg (a n)]
            _ = (N : ℝ) + 1 := by
                rw [Finset.sum_const, Nat.card_Icc]
                have hc : 2 * N + 1 - N = N + 1 := by omega
                rw [hc]
                simp
  calc (∑ i : Fin R, ∑ j : Fin R, ‖∑ n ∈ Finset.Icc N (2 * N), a n * (n : ℂ) ^ (I * ((t i - t j : ℝ) : ℂ))‖ ^ 2)
      ≤ ∑ i : Fin R, C₀ * (T + (N : ℝ)) * ((N : ℝ) + 1) := Finset.sum_le_sum (fun i _ => hrow i)
    _ = (R : ℝ) * (C₀ * (T + (N : ℝ)) * ((N : ℝ) + 1)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        simp [nsmul_eq_mul]
    _ ≤ (2 * C₀) * (R : ℝ) * (T + (N : ℝ)) * (N : ℝ) := by
        have hRnn : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg R
        have hA : (0 : ℝ) ≤ C₀ * (T + (N : ℝ)) := mul_nonneg hC₀pos.le hTN_nonneg
        have hB : (N : ℝ) + 1 ≤ 2 * (N : ℝ) := by linarith
        have hkey : C₀ * (T + (N : ℝ)) * ((N : ℝ) + 1)
            ≤ C₀ * (T + (N : ℝ)) * (2 * (N : ℝ)) :=
          mul_le_mul_of_nonneg_left hB hA
        calc (R : ℝ) * (C₀ * (T + (N : ℝ)) * ((N : ℝ) + 1))
            ≤ (R : ℝ) * (C₀ * (T + (N : ℝ)) * (2 * (N : ℝ))) :=
              mul_le_mul_of_nonneg_left hkey hRnn
          _ = (2 * C₀) * (R : ℝ) * (T + (N : ℝ)) * (N : ℝ) := by ring

end Commons.NumberTheory.DirichletPolynomial
