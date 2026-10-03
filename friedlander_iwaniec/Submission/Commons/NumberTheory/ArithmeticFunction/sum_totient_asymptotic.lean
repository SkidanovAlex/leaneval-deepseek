import Mathlib
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Submission.Commons.NumberTheory.Moebius.moebius_abs_le_one
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Harmonic.Bounds

namespace Commons.NumberTheory.ArithmeticFunction

open Finset
open scoped ArithmeticFunction.Moebius

lemma totient_eq_sum_moebius (n : ℕ) :
    (Nat.totient n : ℝ) = ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * ((n / d : ℕ) : ℝ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hiff := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℝ)
        (f := fun n : ℕ => (Nat.totient n : ℝ)) (g := fun n : ℕ => (n : ℝ))).mp
        (fun m hm => by exact_mod_cast Nat.sum_totient m)
    have h := hiff n (Nat.pos_of_ne_zero hn)
    rw [Nat.sum_divisorsAntidiagonal
        (f := fun a b => (ArithmeticFunction.moebius a : ℝ) * (b : ℝ))] at h
    exact h.symm

lemma sum_range_cast_id (n : ℕ) :
    ∑ k ∈ range n, (k : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  rcases Nat.eq_zero_or_pos n with h0 | h1
  · subst h0; simp
  · have hcast : (∑ k ∈ range n, (k:ℝ)) * 2 = (n:ℝ) * ((n:ℝ) - 1) := by
      have h' : ((∑ k ∈ range n, k : ℕ) : ℝ) * 2 = ((n * (n - 1) : ℕ) : ℝ) := by
        rw [← Finset.sum_range_id_mul_two n]; push_cast; ring
      rw [Nat.cast_sum] at h'
      rw [h']
      have hs : ((n - 1 : ℕ) : ℝ) = (n:ℝ) - 1 := by
        rw [Nat.cast_sub (show (1:ℕ) ≤ n from h1)]; norm_num
      rw [Nat.cast_mul, hs]
    linarith

lemma sum_Icc_id_cast (m : ℕ) :
    ∑ e ∈ Icc 1 m, (e : ℝ) = (m : ℝ) * ((m : ℝ) + 1) / 2 := by
  have h2 : (∑ e ∈ Icc 1 m, (e:ℝ)) = ∑ k ∈ range m, ((k:ℝ) + 1) := by
    rw [show Icc 1 m = (range m).image (fun k => k+1) from by
      ext e; simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨e-1, by omega, by omega⟩
      · rintro ⟨k, hk, rfl⟩; omega]
    rw [Finset.sum_image (fun a _ b _ h => by omega)]
    apply Finset.sum_congr rfl
    intro k hk
    push_cast
    ring
  rw [h2, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      sum_range_cast_id]
  ring

lemma filter_Icc_dvd_eq_divisors' {x k : ℕ} (hk1 : 1 ≤ k) (hkx : k ≤ x) :
    (Finset.Icc 1 x).filter (fun n => n ∣ k) = k.divisors := by
  ext n
  rw [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h3, by omega⟩
  · rintro ⟨h3, hk0⟩
    have hn0 : n ≠ 0 := by rintro rfl; exact hk0 (zero_dvd_iff.mp h3)
    exact ⟨⟨by omega, le_trans (Nat.le_of_dvd (by omega) h3) hkx⟩, h3⟩

/-- Hyperbola method over `Icc 1 x`. -/
lemma sum_Icc_divisors_swap (f : ℕ → ℕ → ℝ) (x : ℕ) :
    (∑ n ∈ Icc 1 x, ∑ d ∈ n.divisors, f d (n/d))
      = ∑ d ∈ Icc 1 x, ∑ e ∈ Icc 1 (x/d), f d e := by
  have hdiv : ∀ n ∈ Icc 1 x, n.divisors = (Icc 1 x).filter (fun d => d ∣ n) := by
    intro n hn
    exact (filter_Icc_dvd_eq_divisors' (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2).symm
  have himg : ∀ d ∈ Icc 1 x,
      (Icc 1 x).filter (fun n => d ∣ n) = (Icc 1 (x/d)).image (fun e => d*e) := by
    intro d hd
    have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hn1, hnx⟩, hdn⟩
      obtain ⟨e, rfl⟩ := hdn
      refine ⟨e, ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos e with h0 | h
        · subst h0; simp at hn1
        · exact h
      · rw [Nat.le_div_iff_mul_le hdpos]
        simpa [Nat.mul_comm] using hnx
    · rintro ⟨e, ⟨he1, hex⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, dvd_mul_right d e⟩
      · have : 1 ≤ d * e := Nat.one_le_iff_ne_zero.mpr (by positivity)
        exact this
      · calc d * e ≤ d * (x / d) := Nat.mul_le_mul_left d hex
          _ ≤ x := Nat.mul_div_le x d
  calc (∑ n ∈ Icc 1 x, ∑ d ∈ n.divisors, f d (n/d))
      = ∑ n ∈ Icc 1 x, ∑ d ∈ (Icc 1 x).filter (fun d => d ∣ n), f d (n/d) :=
        Finset.sum_congr rfl (fun n hn => by rw [hdiv n hn])
    _ = ∑ n ∈ Icc 1 x, ∑ d ∈ Icc 1 x, (if d ∣ n then f d (n/d) else 0) := by
        apply Finset.sum_congr rfl; intro n _; rw [Finset.sum_filter]
    _ = ∑ d ∈ Icc 1 x, ∑ n ∈ Icc 1 x, (if d ∣ n then f d (n/d) else 0) :=
        Finset.sum_comm
    _ = ∑ d ∈ Icc 1 x, ∑ e ∈ Icc 1 (x/d), f d e := by
        apply Finset.sum_congr rfl; intro d hd
        have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
        rw [← Finset.sum_filter, himg d hd]
        rw [Finset.sum_image (f := fun n => f d (n/d)) (g := fun e => d*e)
              (fun a _ b _ h => Nat.mul_left_cancel hdpos h)]
        apply Finset.sum_congr rfl; intro e he
        rw [Nat.mul_div_cancel_left e hdpos]

lemma sum_totient_eq (x : ℕ) (_hx : 1 ≤ x) :
    (∑ n ∈ Icc 1 x, (Nat.totient n : ℝ))
      = (1/2) * ((∑ d ∈ Icc 1 x, (ArithmeticFunction.moebius d : ℝ) * (((x/d : ℕ) : ℝ))^2)
          + ∑ d ∈ Icc 1 x, (ArithmeticFunction.moebius d : ℝ) * ((x/d : ℕ) : ℝ)) := by
  have h1 : (∑ n ∈ Icc 1 x, (Nat.totient n : ℝ))
      = ∑ n ∈ Icc 1 x, ∑ d ∈ n.divisors,
          (ArithmeticFunction.moebius d : ℝ) * ((n/d : ℕ) : ℝ) :=
    Finset.sum_congr rfl (fun n _ => totient_eq_sum_moebius n)
  rw [h1, sum_Icc_divisors_swap
      (fun d e => (ArithmeticFunction.moebius d : ℝ) * (e : ℝ)) x]
  have hstep : ∀ d ∈ Icc 1 x,
      (∑ e ∈ Icc 1 (x/d), (ArithmeticFunction.moebius d : ℝ) * (e : ℝ))
        = (ArithmeticFunction.moebius d : ℝ) * ((x/d : ℕ) : ℝ)
            * (((x/d : ℕ) : ℝ) + 1) / 2 := by
    intro d hd
    rw [← Finset.mul_sum, sum_Icc_id_cast]
    ring
  rw [Finset.sum_congr rfl hstep]
  have hcongr : (∑ d ∈ Icc 1 x, (ArithmeticFunction.moebius d : ℝ) * ((x/d : ℕ) : ℝ)
        * (((x/d : ℕ) : ℝ) + 1) / 2)
      = (1/2) * ∑ d ∈ Icc 1 x,
          ((ArithmeticFunction.moebius d : ℝ) * (((x/d : ℕ) : ℝ))^2
            + (ArithmeticFunction.moebius d : ℝ) * ((x/d : ℕ) : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro d hd; ring
  rw [hcongr, Finset.sum_add_distrib]

lemma const_mul_log_bound (x : ℕ) (hx : 1 ≤ x) :
    (x:ℝ) * (2 + Real.log x) + 1/2 ≤ 8 * (x:ℝ) * Real.log ((x:ℝ) + 1) := by
  have hx1 : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
  have hxpos : (0:ℝ) < (x:ℝ) := by linarith
  have hlog2 : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog3 : (1/3:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h2x1 : (2:ℝ) ≤ (x:ℝ) + 1 := by linarith
  have hlog2le : Real.log 2 ≤ Real.log ((x:ℝ) + 1) :=
    Real.log_le_log (by norm_num) h2x1
  have hlogxle : Real.log x ≤ Real.log ((x:ℝ) + 1) :=
    Real.log_le_log hxpos (by linarith)
  have h1 : 1/(2*(x:ℝ)) ≤ Real.log ((x:ℝ)+1) := by
    have hle : 1/(2*(x:ℝ)) ≤ 1/2 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith
  have h2 : (2:ℝ) + Real.log x ≤ 7 * Real.log ((x:ℝ)+1) := by
    have : (6:ℝ) * Real.log ((x:ℝ)+1) ≥ 2 := by
      have hh := le_trans hlog3 hlog2le
      linarith
    linarith
  have key : 2 + Real.log x + 1/(2*(x:ℝ)) ≤ 8 * Real.log ((x:ℝ)+1) := by linarith
  have hmul := mul_le_mul_of_nonneg_left key hxpos.le
  rw [mul_add] at hmul
  have hxhalf : (x:ℝ) * (1/(2*(x:ℝ))) = 1/2 := by field_simp
  rw [hxhalf] at hmul
  have h8 : (x:ℝ) * (8 * Real.log ((x:ℝ)+1)) = 8 * (x:ℝ) * Real.log ((x:ℝ)+1) := by ring
  rw [h8] at hmul
  linarith

end Commons.NumberTheory.ArithmeticFunction
