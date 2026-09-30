import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.mr_direct_defs
import Submission.Work.BMF.separated_row_sum
import Submission.Work.BMF.smoothing_exists
import Submission.Work.BMF.zeta_prime_sum_twist
import Submission.Work.BMF.mr_direct.lambda_smoothed_abel_clean
import Submission.Work.BMF.mr_direct.lambda_smoothed_error_vk_pos
import Submission.Work.BMF.mr_direct.sum_mul_normSq_eq_double
import Submission.Work.BMF.mr_direct.primeCounting_floor_le_div_log
import Submission.Commons.Analysis.Complex.conj_cpow_ofReal_of_nonneg

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.BMF.mr_core.badPartAux.dualMoment`

Clash-free copy of the two purely elementary lemmas `Work.BMF.dual_moment` and
`Work.BMF.main_term_bound` from `Submission/Work/BMF/prime_large_values.lean`
(that file's *other* contents are not needed here, and its import closure is currently
broken by an in-flight rewrite of `error_quadratic_form_twist`).

`dual_moment` is the finite-matrix duality principle; `main_term_bound` bounds the quadratic
form of the main term `δ ↦ P^{1+iδ} Mφ(1+iδ)` of the smoothed explicit formula, given the Mellin
decay of `φ` and the uniform row-sum constant from `Work.BMF.separated_row_sum`.
-/

set_option maxHeartbeats 1600000

namespace Work.BMF

open Finset
open scoped BigOperators

/-- **Duality for finite matrices (weighted form).**
If for every `b` the weighted quadratic form of the adjoint matrix is bounded by `D`,
then the quadratic form of the matrix itself is bounded by `D / c`, where `c` is a lower
bound for the weights on `N`. -/
lemma dual_moment {ι : Type*} [Fintype ι] (N : Finset ℕ) (X : ι → ℕ → ℂ)
    (w : ℕ → ℝ) {c D : ℝ} (hc : 0 < c) (hD : 0 ≤ D) (hw : ∀ n ∈ N, c ≤ w n)
    (hQ : ∀ b : ι → ℂ, ∑ n ∈ N, w n * ‖∑ i, b i * (starRingEnd ℂ) (X i n)‖ ^ 2
        ≤ D * ∑ i, ‖b i‖ ^ 2) :
    ∀ a : ℕ → ℂ, ∑ i, ‖∑ n ∈ N, a n * X i n‖ ^ 2 ≤ (D / c) * ∑ n ∈ N, ‖a n‖ ^ 2 := by
  intro a
  set Ta : ι → ℂ := fun i => ∑ n ∈ N, a n * X i n with hTa
  set Tb : ℕ → ℂ := fun n => ∑ i, Ta i * (starRingEnd ℂ) (X i n) with hTb
  set A : ℝ := ∑ n ∈ N, ‖a n‖ ^ 2 with hAdef
  set B : ℝ := ∑ n ∈ N, ‖Tb n‖ ^ 2 with hBdef
  set S : ℝ := ∑ i, ‖Ta i‖ ^ 2 with hSdef
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hS0 : 0 ≤ S := by rw [hSdef]; positivity
  have hkey : ∑ i, (starRingEnd ℂ) (Ta i) * Ta i = ∑ n ∈ N, a n * (starRingEnd ℂ) (Tb n) := by
    have h1 : ∀ i, (starRingEnd ℂ) (Ta i) * Ta i
        = ∑ n ∈ N, (starRingEnd ℂ) (Ta i) * (a n * X i n) := by
      intro i
      rw [hTa, Finset.mul_sum]
    calc ∑ i, (starRingEnd ℂ) (Ta i) * Ta i
        = ∑ i, ∑ n ∈ N, (starRingEnd ℂ) (Ta i) * (a n * X i n) :=
          Finset.sum_congr rfl fun i _ => h1 i
      _ = ∑ n ∈ N, ∑ i, (starRingEnd ℂ) (Ta i) * (a n * X i n) := Finset.sum_comm
      _ = ∑ n ∈ N, a n * (starRingEnd ℂ) (Tb n) := by
            apply Finset.sum_congr rfl; intro n hn
            rw [hTb, map_sum, Finset.mul_sum]
            apply Finset.sum_congr rfl; intro i hi
            simp only [map_mul]
            simp
            ring
  have hsum : ∑ i, (starRingEnd ℂ) (Ta i) * Ta i = ((S : ℝ) : ℂ) := by
    have h1 : ∀ i, (starRingEnd ℂ) (Ta i) * Ta i = ((Complex.normSq (Ta i) : ℝ) : ℂ) := by
      intro i; rw [mul_comm, Complex.mul_conj]
    have h2 : (∑ i, ((Complex.normSq (Ta i) : ℝ) : ℂ))
        = ((∑ i, Complex.normSq (Ta i) : ℝ) : ℂ) := by push_cast; ring
    have h3 : (∑ i, Complex.normSq (Ta i) : ℝ) = S := by
      rw [hSdef]; exact Finset.sum_congr rfl fun i _ => Complex.normSq_eq_norm_sq (Ta i)
    rw [Finset.sum_congr rfl (fun i _ => h1 i), h2, h3]
  have hS : S = ‖∑ n ∈ N, a n * (starRingEnd ℂ) (Tb n)‖ := by
    rw [← hkey, hsum]
    simp [abs_of_nonneg hS0]
  have hCS : ‖∑ n ∈ N, a n * (starRingEnd ℂ) (Tb n)‖ ≤ Real.sqrt A * Real.sqrt B := by
    have h1 : ‖∑ n ∈ N, a n * (starRingEnd ℂ) (Tb n)‖ ≤ ∑ n ∈ N, ‖a n‖ * ‖Tb n‖ := by
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun n hn => ?_)
      rw [norm_mul]
      simp
    refine le_trans h1 ?_
    rw [← Real.sqrt_mul hA0]
    exact Real.le_sqrt_of_sq_le
      (Finset.sum_mul_sq_le_sq_mul_sq N (fun n => ‖a n‖) (fun n => ‖Tb n‖))
  have hB : B ≤ (1 / c) * (D * S) := by
    have h1 : c * B ≤ ∑ n ∈ N, w n * ‖Tb n‖ ^ 2 := by
      rw [hBdef, Finset.mul_sum]
      exact Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_right (hw n hn) (by positivity)
    have h2 : ∑ n ∈ N, w n * ‖Tb n‖ ^ 2 ≤ D * S := by
      have h := hQ Ta
      rw [← hSdef] at h
      simpa only [hTb] using h
    have h3 : c * B ≤ D * S := le_trans h1 h2
    have h4 := mul_le_mul_of_nonneg_left h3 (show (0:ℝ) ≤ 1 / c by positivity)
    calc B = (1 / c) * (c * B) := by field_simp
      _ ≤ (1 / c) * (D * S) := h4
  have hS1 : S ≤ Real.sqrt A * Real.sqrt B := hS.le.trans hCS
  have hsq : S ^ 2 ≤ A * B := by
    have h2 : (Real.sqrt A * Real.sqrt B) ^ 2 = A * B := by
      rw [mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt hB0]
    calc S ^ 2 ≤ (Real.sqrt A * Real.sqrt B) ^ 2 := pow_le_pow_left₀ hS0 hS1 2
      _ = A * B := h2
  have hcomb : S ^ 2 ≤ (D / c * A) * S := by
    have h2 : A * B ≤ A * ((1 / c) * (D * S)) := mul_le_mul_of_nonneg_left hB hA0
    calc S ^ 2 ≤ A * B := hsq
      _ ≤ A * ((1 / c) * (D * S)) := h2
      _ = (D / c * A) * S := by ring
  have hfin : S ≤ D / c * A := by
    rcases eq_or_lt_of_le hS0 with h0 | hpos
    · rw [← h0]; positivity
    · exact le_of_mul_le_mul_right (by rw [pow_two] at hcomb; exact hcomb) hpos
  have hfin' : ∑ i, ‖Ta i‖ ^ 2 ≤ (D / c) * ∑ n ∈ N, ‖a n‖ ^ 2 := by
    rw [← hSdef, ← hAdef]; exact hfin
  simpa only [hTa] using hfin'

/-- **The main term of the smoothed explicit formula, in quadratic form.**
Given the Mellin decay of `φ` and the uniform separated row-sum bound, the quadratic form of
`δ ↦ P^{1+iδ} Mφ(1+iδ)` is bounded by `Cφ * Crow * P * Σ ‖η i‖²`. -/
lemma main_term_bound {R : ℕ} (φ : ℝ → ℝ) {Cφ Crow P : ℝ} (hCφ : 0 < Cφ) (hP : 0 < P)
    (hdecay : ∀ t : ℝ, ‖∫ y in (1 / 4 : ℝ)..4, (y : ℂ) ^ (Complex.I * (t : ℂ)) * (φ y : ℂ)‖
      ≤ Cφ / (1 + t ^ 2))
    (t : Fin R → ℝ) (hrow : ∀ i : Fin R, ∑ j : Fin R, 1 / (1 + (t i - t j) ^ 2) ≤ Crow)
    (η : Fin R → ℂ) :
    ‖∑ i, ∑ j, η i * (starRingEnd ℂ) (η j) *
        (P : ℂ) ^ (1 + Complex.I * ((t i - t j : ℝ) : ℂ)) *
        (∫ y in (1 / 4 : ℝ)..4, (y : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) * (φ y : ℂ))‖
      ≤ Cφ * Crow * P * ∑ i, ‖η i‖ ^ 2 := by
  have hPpow : ∀ d : ℝ, ‖(P : ℂ) ^ (1 + Complex.I * (d : ℂ))‖ = P := by
    intro d
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hP]
    simp [Complex.one_re]
  -- bound the double sum by the weighted kernel sum
  have h1 : ‖∑ i, ∑ j, η i * (starRingEnd ℂ) (η j) *
        (P : ℂ) ^ (1 + Complex.I * ((t i - t j : ℝ) : ℂ)) *
        (∫ y in (1 / 4 : ℝ)..4, (y : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) * (φ y : ℂ))‖
      ≤ P * ∑ i, ∑ j, ‖η i‖ * ‖η j‖ * (Cφ / (1 + (t i - t j) ^ 2)) := by
    refine le_trans (norm_sum_le _ _) ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    refine le_trans (norm_sum_le _ _) ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [norm_mul, norm_mul, hPpow, norm_mul]
    have h2 := hdecay ((t i - t j : ℝ))
    have h3 : 0 ≤ ‖η i‖ * ‖η j‖ := by positivity
    calc ‖η i‖ * ‖(starRingEnd ℂ) (η j)‖ * P *
          ‖∫ y in (1 / 4 : ℝ)..4, (y : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) * (φ y : ℂ)‖
        ≤ ‖η i‖ * ‖(starRingEnd ℂ) (η j)‖ * P * (Cφ / (1 + (t i - t j) ^ 2)) := by
          refine mul_le_mul_of_nonneg_left h2 ?_
          positivity
      _ = P * (‖η i‖ * ‖η j‖ * (Cφ / (1 + (t i - t j) ^ 2))) := by
          simp [norm_star]; ring
  -- symmetrise
  have h2 : ∑ i, ∑ j, ‖η i‖ * ‖η j‖ * (Cφ / (1 + (t i - t j) ^ 2))
      ≤ Cφ * Crow * ∑ i, ‖η i‖ ^ 2 := by
    have hk : ∀ i j : Fin R, 0 ≤ Cφ / (1 + (t i - t j) ^ 2) := fun i j => by positivity
    have hstep1 : ∑ i, ∑ j, ‖η i‖ * ‖η j‖ * (Cφ / (1 + (t i - t j) ^ 2))
        ≤ ∑ i, ∑ j, ((‖η i‖ ^ 2 + ‖η j‖ ^ 2) / 2) * (Cφ / (1 + (t i - t j) ^ 2)) := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro j _
      have h : 2 * (‖η i‖ * ‖η j‖) ≤ ‖η i‖ ^ 2 + ‖η j‖ ^ 2 := by
        nlinarith [sq_nonneg (‖η i‖ - ‖η j‖)]
      have h2' : ‖η i‖ * ‖η j‖ ≤ (‖η i‖ ^ 2 + ‖η j‖ ^ 2) / 2 := by linarith
      exact mul_le_mul_of_nonneg_right h2' (hk i j)
    have hstep2 : ∑ i, ∑ j, ((‖η i‖ ^ 2 + ‖η j‖ ^ 2) / 2) * (Cφ / (1 + (t i - t j) ^ 2))
        ≤ Cφ * Crow * ∑ i, ‖η i‖ ^ 2 := by
      have hA : ∀ i : Fin R,
          ∑ j, ((‖η i‖ ^ 2 + ‖η j‖ ^ 2) / 2) * (Cφ / (1 + (t i - t j) ^ 2))
            = (‖η i‖ ^ 2 / 2) * (∑ j, Cφ / (1 + (t i - t j) ^ 2))
              + ∑ j, (‖η j‖ ^ 2 / 2) * (Cφ / (1 + (t i - t j) ^ 2)) := by
        intro i
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro j _
        ring
      simp only [hA]
      rw [Finset.sum_add_distrib]
      have hB : ∑ i : Fin R, (‖η i‖ ^ 2 / 2) * (∑ j : Fin R, Cφ / (1 + (t i - t j) ^ 2))
          ≤ (Cφ * Crow) * ∑ i, ‖η i‖ ^ 2 / 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum; intro i _
        have hrowi := hrow i
        have hk' : (0:ℝ) ≤ ‖η i‖ ^ 2 / 2 := by positivity
        have heq : ∑ j : Fin R, Cφ / (1 + (t i - t j) ^ 2)
            = Cφ * ∑ j : Fin R, 1 / (1 + (t i - t j) ^ 2) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro j _
          ring
        rw [heq]
        calc (‖η i‖ ^ 2 / 2) * (Cφ * ∑ j : Fin R, 1 / (1 + (t i - t j) ^ 2))
            ≤ (‖η i‖ ^ 2 / 2) * (Cφ * Crow) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrowi hCφ.le) hk'
          _ = Cφ * Crow * (‖η i‖ ^ 2 / 2) := by ring
      have hC : ∑ j : Fin R, (‖η j‖ ^ 2 / 2) * (∑ i : Fin R, Cφ / (1 + (t i - t j) ^ 2))
          ≤ (Cφ * Crow) * ∑ j, ‖η j‖ ^ 2 / 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum; intro j _
        have hrowj := hrow j
        have hk' : (0:ℝ) ≤ ‖η j‖ ^ 2 / 2 := by positivity
        have heq : ∑ i : Fin R, Cφ / (1 + (t i - t j) ^ 2)
            = Cφ * ∑ i : Fin R, 1 / (1 + (t j - t i) ^ 2) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro i _
          rw [show (t i - t j) ^ 2 = (t j - t i) ^ 2 from by ring]
          ring
        rw [heq]
        calc (‖η j‖ ^ 2 / 2) * (Cφ * ∑ i : Fin R, 1 / (1 + (t j - t i) ^ 2))
            ≤ (‖η j‖ ^ 2 / 2) * (Cφ * Crow) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrowj hCφ.le) hk'
          _ = Cφ * Crow * (‖η j‖ ^ 2 / 2) := by ring
      have hsecond : (∑ i, ∑ j : Fin R, (‖η j‖ ^ 2 / 2) * (Cφ / (1 + (t i - t j) ^ 2)))
          = ∑ j : Fin R, (‖η j‖ ^ 2 / 2) * (∑ i : Fin R, Cφ / (1 + (t i - t j) ^ 2)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro j _
        rw [Finset.mul_sum]
      rw [hsecond]
      refine le_trans (add_le_add hB hC) (le_of_eq ?_)
      rw [← mul_add, ← Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl; intro i _
      ring
    exact le_trans hstep1 hstep2
  calc _ ≤ P * ∑ i, ∑ j, ‖η i‖ * ‖η j‖ * (Cφ / (1 + (t i - t j) ^ 2)) := h1
    _ ≤ P * (Cφ * Crow * ∑ i, ‖η i‖ ^ 2) := by
        refine mul_le_mul_of_nonneg_left h2 hP.le
    _ = Cφ * Crow * P * ∑ i, ‖η i‖ ^ 2 := by ring



end Work.BMF
