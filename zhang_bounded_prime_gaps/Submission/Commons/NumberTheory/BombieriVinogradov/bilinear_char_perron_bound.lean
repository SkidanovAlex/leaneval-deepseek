import Mathlib
import Submission.Commons.Analysis.Perron.bilinear_perron_bound
import Submission.Commons.NumberTheory.DirichletCharacter.norm_char_nat_le_one

namespace Commons.NumberTheory.BombieriVinogradov

open Finset
open scoped BigOperators

lemma perron_main_norm_le (x c T : ℝ) (hx : 0 < x) (hT : 0 < T) (A B : ℝ → ℂ) :
    ‖(1 / (2 * (Real.pi : ℂ))) * (∫ t in (-T)..T,
        (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) / ((c : ℂ) + (t : ℂ) * Complex.I)
          * A t * B t)‖
    ≤ (1 / (2 * Real.pi)) * x ^ c * (∫ t in (-T)..T,
        ‖A t * B t‖ / ‖(c : ℂ) + (t : ℂ) * Complex.I‖) := by
  have hscal : ‖(1 / (2 * (Real.pi : ℂ)))‖ = 1 / (2 * Real.pi) := by
    simp only [norm_div, norm_one]
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.norm_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
  have hnonneg : (0:ℝ) ≤ 1 / (2 * Real.pi) := by positivity
  have hcore : ‖(∫ t in (-T)..T,
        (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) / ((c : ℂ) + (t : ℂ) * Complex.I)
          * A t * B t)‖
      ≤ x ^ c * (∫ t in (-T)..T, ‖A t * B t‖ / ‖(c : ℂ) + (t : ℂ) * Complex.I‖) := by
    have hab : -T ≤ T := by linarith
    calc ‖(∫ t in (-T)..T, (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) / ((c : ℂ) + (t : ℂ) * Complex.I) * A t * B t)‖
        ≤ ∫ t in (-T)..T, ‖(x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) / ((c : ℂ) + (t : ℂ) * Complex.I) * A t * B t‖ :=
          intervalIntegral.norm_integral_le_integral_norm hab
      _ = ∫ t in (-T)..T, x ^ c * (‖A t * B t‖ / ‖(c : ℂ) + (t : ℂ) * Complex.I‖) := by
          apply intervalIntegral.integral_congr
          intro t _
          dsimp only
          rw [norm_mul, norm_mul, norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
          have hre : (((c : ℂ) + (t : ℂ) * Complex.I)).re = c := by simp
          rw [hre]
          ring
      _ = x ^ c * (∫ t in (-T)..T, ‖A t * B t‖ / ‖(c : ℂ) + (t : ℂ) * Complex.I‖) :=
          intervalIntegral.integral_const_mul (x^c) _
  rw [norm_mul, hscal, mul_assoc]
  exact mul_le_mul_of_nonneg_left hcore hnonneg

theorem bilinear_char_perron_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (M N : ℕ) (a b : ℕ → ℂ)
      (c x T : ℝ), 0 < c → 1 < x → 0 < T → (∀ n : ℕ, (n : ℝ) ≠ x) →
      ‖∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
          (if (m : ℝ) * (n : ℝ) < x then (1 : ℂ) else 0) * a m * b n * χ ((m * n : ℕ) : ZMod q)‖
      ≤ (1 / (2 * Real.pi)) * x ^ c *
          (∫ t in (-T)..T,
            ‖(∑ m ∈ Finset.Icc 1 M, a m * χ (m : ZMod q) * ((m : ℂ)) ^ (-((c : ℂ) + (t : ℂ) * Complex.I))) *
             (∑ n ∈ Finset.Icc 1 N, b n * χ (n : ZMod q) * ((n : ℂ)) ^ (-((c : ℂ) + (t : ℂ) * Complex.I)))‖
            / ‖(c : ℂ) + (t : ℂ) * Complex.I‖)
      + C * ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
            ‖a m‖ * ‖b n‖ * ((x / ((m : ℝ) * (n : ℝ))) ^ c) *
              min 1 (1 / (T * |Real.log (x / ((m : ℝ) * (n : ℝ)))|)) := by
  obtain ⟨C0, hC0pos, hC0⟩ := Commons.Analysis.Perron.bilinear_perron_bound
  refine ⟨C0, hC0pos, ?_⟩
  intro q _ χ M N a b c x T hc hx1 hT hxnnat
  have hx : 0 < x := by linarith
  have hbound := hC0 (fun m => a m * χ (m : ZMod q)) (fun n => b n * χ (n : ZMod q)) c x T M N hc hx1 hT hxnnat
  have hPn : ‖(1 / (2 * (Real.pi : ℂ))) * (∫ t in (-T)..T,
        (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) / ((c : ℂ) + (t : ℂ) * Complex.I)
          * (∑ m ∈ Finset.Icc 1 M, a m * χ (m : ZMod q) * ((m : ℂ)) ^ (-((c : ℂ) + (t : ℂ) * Complex.I)))
          * (∑ n ∈ Finset.Icc 1 N, b n * χ (n : ZMod q) * ((n : ℂ)) ^ (-((c : ℂ) + (t : ℂ) * Complex.I))))‖
      ≤ (1 / (2 * Real.pi)) * x ^ c * (∫ t in (-T)..T,
            ‖(∑ m ∈ Finset.Icc 1 M, a m * χ (m : ZMod q) * ((m : ℂ)) ^ (-((c : ℂ) + (t : ℂ) * Complex.I))) *
             (∑ n ∈ Finset.Icc 1 N, b n * χ (n : ZMod q) * ((n : ℂ)) ^ (-((c : ℂ) + (t : ℂ) * Complex.I)))‖
            / ‖(c : ℂ) + (t : ℂ) * Complex.I‖) :=
    perron_main_norm_le x c T hx hT _ _
  have hS : (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
        (if (m : ℝ) * (n : ℝ) < x then (1 : ℂ) else 0) * (a m * χ (m : ZMod q)) * (b n * χ (n : ZMod q)))
      = ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
        (if (m : ℝ) * (n : ℝ) < x then (1 : ℂ) else 0) * a m * b n * χ ((m * n : ℕ) : ZMod q) := by
    apply Finset.sum_congr rfl; intro m hm
    apply Finset.sum_congr rfl; intro n hn
    rw [Nat.cast_mul, map_mul]; ring
  have hE : (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
        ‖a m * χ (m : ZMod q)‖ * ‖b n * χ (n : ZMod q)‖ *
          ((x / ((m : ℝ) * (n : ℝ))) ^ c) *
            min 1 (1 / (T * |Real.log (x / ((m : ℝ) * (n : ℝ)))|)))
      ≤ ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
        ‖a m‖ * ‖b n‖ * ((x / ((m : ℝ) * (n : ℝ))) ^ c) *
          min 1 (1 / (T * |Real.log (x / ((m : ℝ) * (n : ℝ)))|)) := by
    apply Finset.sum_le_sum; intro m hm
    apply Finset.sum_le_sum; intro n hn
    have ha1 : ‖a m * χ (m : ZMod q)‖ ≤ ‖a m‖ := by
      calc ‖a m * χ (m : ZMod q)‖ = ‖a m‖ * ‖χ (m : ZMod q)‖ := norm_mul _ _
        _ ≤ ‖a m‖ * 1 := mul_le_mul_of_nonneg_left
            (Commons.NumberTheory.DirichletCharacter.norm_char_nat_le_one χ m) (norm_nonneg _)
        _ = ‖a m‖ := mul_one _
    have hb1 : ‖b n * χ (n : ZMod q)‖ ≤ ‖b n‖ := by
      calc ‖b n * χ (n : ZMod q)‖ = ‖b n‖ * ‖χ (n : ZMod q)‖ := norm_mul _ _
        _ ≤ ‖b n‖ * 1 := mul_le_mul_of_nonneg_left
            (Commons.NumberTheory.DirichletCharacter.norm_char_nat_le_one χ n) (norm_nonneg _)
        _ = ‖b n‖ := mul_one _
    have hF : 0 ≤ ((x / ((m : ℝ) * (n : ℝ))) ^ c) *
        min 1 (1 / (T * |Real.log (x / ((m : ℝ) * (n : ℝ)))|)) := by
      apply mul_nonneg
      · exact Real.rpow_nonneg (by positivity) c
      · apply le_min zero_le_one
        exact div_nonneg zero_le_one (mul_nonneg hT.le (abs_nonneg _))
    have hprod : ‖a m * χ (m : ZMod q)‖ * ‖b n * χ (n : ZMod q)‖ ≤ ‖a m‖ * ‖b n‖ := by
      calc ‖a m * χ (m : ZMod q)‖ * ‖b n * χ (n : ZMod q)‖
          ≤ ‖a m‖ * ‖b n * χ (n : ZMod q)‖ := mul_le_mul_of_nonneg_right ha1 (norm_nonneg _)
        _ ≤ ‖a m‖ * ‖b n‖ := mul_le_mul_of_nonneg_left hb1 (norm_nonneg _)
    have hstep := mul_le_mul_of_nonneg_right hprod hF
    simpa only [mul_assoc] using hstep
  -- abbreviate
  let S : ℂ := ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
        (if (m : ℝ) * (n : ℝ) < x then (1 : ℂ) else 0) * (a m * χ (m : ZMod q)) * (b n * χ (n : ZMod q))
  let P : ℂ := (1 / (2 * (Real.pi : ℂ))) * (∫ t in (-T)..T,
        (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) / ((c : ℂ) + (t : ℂ) * Complex.I)
          * (∑ m ∈ Finset.Icc 1 M, a m * χ (m : ZMod q) * ((m : ℂ)) ^ (-((c : ℂ) + (t : ℂ) * Complex.I)))
          * (∑ n ∈ Finset.Icc 1 N, b n * χ (n : ZMod q) * ((n : ℂ)) ^ (-((c : ℂ) + (t : ℂ) * Complex.I))))
  let E : ℝ := ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
        ‖a m * χ (m : ZMod q)‖ * ‖b n * χ (n : ZMod q)‖ *
          ((x / ((m : ℝ) * (n : ℝ))) ^ c) *
            min 1 (1 / (T * |Real.log (x / ((m : ℝ) * (n : ℝ)))|))
  let MN : ℝ := (1 / (2 * Real.pi)) * x ^ c * (∫ t in (-T)..T,
            ‖(∑ m ∈ Finset.Icc 1 M, a m * χ (m : ZMod q) * ((m : ℂ)) ^ (-((c : ℂ) + (t : ℂ) * Complex.I))) *
             (∑ n ∈ Finset.Icc 1 N, b n * χ (n : ZMod q) * ((n : ℂ)) ^ (-((c : ℂ) + (t : ℂ) * Complex.I)))‖
            / ‖(c : ℂ) + (t : ℂ) * Complex.I‖)
  let ER : ℝ := ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
        ‖a m‖ * ‖b n‖ * ((x / ((m : ℝ) * (n : ℝ))) ^ c) *
          min 1 (1 / (T * |Real.log (x / ((m : ℝ) * (n : ℝ)))|))
  rw [← hS]
  change ‖S‖ ≤ MN + C0 * ER
  have h1 : ‖S‖ ≤ ‖S - P‖ + ‖P‖ := by
    calc ‖S‖ = ‖S - P + P‖ := by rw [sub_add_cancel]
      _ ≤ ‖S - P‖ + ‖P‖ := norm_add_le _ _
  have h2 : ‖S - P‖ + ‖P‖ ≤ C0 * E + MN := add_le_add hbound hPn
  have h3 : C0 * E + MN ≤ C0 * ER + MN :=
    add_le_add (mul_le_mul_of_nonneg_left hE hC0pos.le) le_rfl
  have h4 : C0 * ER + MN = MN + C0 * ER := by ring
  exact h1.trans (h2.trans (h3.trans h4.le))

end Commons.NumberTheory.BombieriVinogradov

