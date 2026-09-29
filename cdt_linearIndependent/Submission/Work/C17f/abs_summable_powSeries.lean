import Mathlib

/-!
# Absolute summability of a power series and of its first two derived series

If a power series `∑ c n * z ^ n` converges at every point of the open disc of radius `r`,
then at every such point the series of absolute values and the two derived series
(`∑ (n+1) c (n+1) z ^ n` and `∑ (n+1)(n+2) c (n+2) z ^ n`) are again absolutely summable.

The proof is elementary: pick a second point `s` of the disc with `‖z‖ < s < r`.  At `s` the
terms `c n * s ^ n` are bounded by `M = ∑' n, ‖c n * s ^ n‖`, whence
`‖c (n+k)‖ * s ^ (n+k) ≤ M`, and comparison with the convergent series
`∑ ((n + 1) * (n + 2)) * (‖z‖ / s) ^ n` gives the claim.
-/

namespace Work.C17f

open scoped BigOperators

private lemma norm_ofReal_C (x : ℝ) : ‖(x : ℂ)‖ = |x| := by
  have h : ‖(x : ℂ)‖ ^ 2 = |x| ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_ofReal, sq_abs]
    ring
  nlinarith [h, norm_nonneg (x : ℂ), abs_nonneg x]

private lemma norm_natCast_add_one (n : ℕ) : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
  have h : (n : ℂ) + 1 = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  rw [h, norm_ofReal_C]
  exact abs_of_nonneg (by positivity)

private lemma norm_natCast_add_two (n : ℕ) : ‖(n : ℂ) + 2‖ = (n : ℝ) + 2 := by
  have h : (n : ℂ) + 2 = (((n : ℝ) + 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h, norm_ofReal_C]
  exact abs_of_nonneg (by positivity)

private lemma summable_succ_mul_geometric (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * t ^ n) := by
  have ht : ‖t‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg ht0]
  have h := summable_choose_mul_geometric_of_norm_lt_one (R := ℝ) 1 ht
  refine h.congr (fun n => ?_)
  simp [Nat.choose_one_right, Nat.cast_add]

private lemma summable_succ_succ_mul_geometric (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * ((n : ℝ) + 2) * t ^ n) := by
  have ht : ‖t‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg ht0]
  have h2 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 ht
  have h1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 ht
  have h0 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 0 ht
  have h := h2.add ((h1.mul_left 3).add (h0.mul_left 2))
  refine h.congr (fun n => ?_)
  simp only [pow_one, pow_zero]
  ring

theorem abs_summable_powSeries (c : ℕ → ℂ) (r : ℝ) (F : ℂ → ℂ)
    (h : ∀ z : ℂ, ‖z‖ < r → HasSum (fun n : ℕ => c n * z ^ n) (F z)) :
    ∀ z : ℂ, ‖z‖ < r →
      Summable (fun n : ℕ => ‖c n * z ^ n‖) ∧
      Summable (fun n : ℕ => ‖((n : ℂ) + 1) * c (n + 1) * z ^ n‖) ∧
      Summable (fun n : ℕ => ‖((n : ℂ) + 1) * ((n : ℂ) + 2) * c (n + 2) * z ^ n‖) := by
  intro z hz
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  obtain ⟨s, hzs, hrs, hs0⟩ : ∃ s : ℝ, ‖z‖ < s ∧ s < r ∧ 0 < s :=
    ⟨(‖z‖ + r) / 2, by linarith, by linarith, by linarith⟩
  have hscn : ‖(s : ℂ)‖ = s := by rw [norm_ofReal_C, abs_of_nonneg hs0.le]
  have hwlt : ‖(s : ℂ)‖ < r := by rw [hscn]; exact hrs
  have hsum_s : Summable (fun n : ℕ => c n * (s : ℂ) ^ n) := (h (s : ℂ) hwlt).summable
  have hnw : Summable (fun n : ℕ => ‖c n * (s : ℂ) ^ n‖) := hsum_s.norm
  set M : ℝ := ∑' n, ‖c n * (s : ℂ) ^ n‖ with hMdef
  have hb : ∀ n, ‖c n‖ * s ^ n ≤ M := by
    intro n
    have h1 : ‖c n * (s : ℂ) ^ n‖ = ‖c n‖ * s ^ n := by
      rw [norm_mul, norm_pow, hscn]
    have h2 : ‖c n * (s : ℂ) ^ n‖ ≤ M := by
      have h3 := Summable.le_tsum hnw n (fun j _ => norm_nonneg _)
      rw [hMdef]
      exact h3
    rwa [h1] at h2
  refine ⟨(h z hz).summable.norm, ?_, ?_⟩
  · have ht0 : 0 ≤ ‖z‖ / s := div_nonneg hz0 hs0.le
    have ht1 : ‖z‖ / s < 1 := (div_lt_one hs0).mpr hzs
    have hmaj : Summable (fun n : ℕ => (M / s) * (((n : ℝ) + 1) * (‖z‖ / s) ^ n)) :=
      (summable_succ_mul_geometric (‖z‖ / s) ht0 ht1).mul_left (M / s)
    refine Summable.of_nonneg_of_le
      (f := fun n : ℕ => (M / s) * (((n : ℝ) + 1) * (‖z‖ / s) ^ n))
      (g := fun n : ℕ => ‖((n : ℂ) + 1) * c (n + 1) * z ^ n‖) (fun n => norm_nonneg _) ?_ hmaj
    intro n
    have hcn : ‖c (n + 1)‖ ≤ M / s ^ (n + 1) := by
      rw [le_div_iff₀ (pow_pos hs0 _)]; exact hb (n + 1)
    calc ‖((n : ℂ) + 1) * c (n + 1) * z ^ n‖
        = ((n : ℝ) + 1) * ‖c (n + 1)‖ * ‖z‖ ^ n := by
          rw [norm_mul, norm_mul, norm_pow, norm_natCast_add_one]
      _ ≤ ((n : ℝ) + 1) * (M / s ^ (n + 1)) * ‖z‖ ^ n := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hcn (by positivity)) (pow_nonneg hz0 n)
      _ = (M / s) * (((n : ℝ) + 1) * (‖z‖ / s) ^ n) := by
          rw [div_pow]; field_simp; ring
  · have ht0 : 0 ≤ ‖z‖ / s := div_nonneg hz0 hs0.le
    have ht1 : ‖z‖ / s < 1 := (div_lt_one hs0).mpr hzs
    have hmaj : Summable (fun n : ℕ =>
        (M / s ^ 2) * (((n : ℝ) + 1) * ((n : ℝ) + 2) * (‖z‖ / s) ^ n)) :=
      (summable_succ_succ_mul_geometric (‖z‖ / s) ht0 ht1).mul_left (M / s ^ 2)
    refine Summable.of_nonneg_of_le
      (f := fun n : ℕ => (M / s ^ 2) * (((n : ℝ) + 1) * ((n : ℝ) + 2) * (‖z‖ / s) ^ n))
      (g := fun n : ℕ => ‖((n : ℂ) + 1) * ((n : ℂ) + 2) * c (n + 2) * z ^ n‖)
      (fun n => norm_nonneg _) ?_ hmaj
    intro n
    have hcn : ‖c (n + 2)‖ ≤ M / s ^ (n + 2) := by
      rw [le_div_iff₀ (pow_pos hs0 _)]; exact hb (n + 2)
    calc ‖((n : ℂ) + 1) * ((n : ℂ) + 2) * c (n + 2) * z ^ n‖
        = ((n : ℝ) + 1) * ((n : ℝ) + 2) * ‖c (n + 2)‖ * ‖z‖ ^ n := by
          rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_natCast_add_one, norm_natCast_add_two]
      _ ≤ ((n : ℝ) + 1) * ((n : ℝ) + 2) * (M / s ^ (n + 2)) * ‖z‖ ^ n := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hcn (by positivity)) (pow_nonneg hz0 n)
      _ = (M / s ^ 2) * (((n : ℝ) + 1) * ((n : ℝ) + 2) * (‖z‖ / s) ^ n) := by
          rw [div_pow]; field_simp; ring

end Work.C17f
