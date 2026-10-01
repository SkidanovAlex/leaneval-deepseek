import Mathlib
import Submission.Work.LinnikAreas.BGTZ.DetectorKernel
import Submission.Work.LinnikAreas.BGTZ.DetectorInterchange

open MeasureTheory
open scoped BigOperators

namespace Work.LinnikAreas.BGTZ

/-! ## Placeholders for the delegated analytic pieces (dev only, replaced by imports) -/

private theorem DetPerronKernel_local {c : ℝ} (hc : 0 < c) {x : ℝ} (hx : 0 < x) :
    mellK c (x : ℂ) = (if 1 ≤ x then (1 - 1 / x : ℝ) else 0 : ℂ) :=
  DetectorKernel hc hx

private theorem DetPerronInterchange_local (f : ℕ → ℂ) {c : ℝ} (hc : 0 < c) {N : ℕ}
    (hN : 1 ≤ N) (ρ : ℂ)
    (hconv : Summable (fun n : ℕ => ‖f n‖ / (n : ℝ) ^ (c + ρ.re))) :
    (1 / (2 * Real.pi)) * ∫ t : ℝ, (∑' n : ℕ, f n / (n : ℂ) ^ (ρ + (c + (t : ℂ) * Complex.I)))
        * (N : ℂ) ^ (c + (t : ℂ) * Complex.I)
        / ((c + (t : ℂ) * Complex.I) * (c + 1 + (t : ℂ) * Complex.I))
      = ∑' n : ℕ, (1 / (2 * Real.pi)) * ∫ t : ℝ, (f n / (n : ℂ) ^ (ρ + (c + (t : ℂ) * Complex.I)))
        * (N : ℂ) ^ (c + (t : ℂ) * Complex.I)
        / ((c + (t : ℂ) * Complex.I) * (c + 1 + (t : ℂ) * Complex.I)) :=
  DetectorInterchange f hc hN ρ hconv

/-! ## Elementary facts about the exponent -/

private lemma re_exponent (t c : ℝ) (ρ : ℂ) :
    (ρ + (c + (t : ℂ) * Complex.I)).re = c + ρ.re := by
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, zero_mul, add_zero]
  ring

private lemma im_exponent (t c : ℝ) (ρ : ℂ) :
    (ρ + (c + (t : ℂ) * Complex.I)).im = ρ.im + t := by
  simp only [Complex.add_im, Complex.add_re, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
    zero_mul, add_zero, mul_one]
  ring

/-- `0 ^ z = 0` along the Perron line, except possibly at a single point. -/
private lemma zero_cpow_exponent_ae (c : ℝ) (ρ : ℂ) :
    ∀ᵐ t : ℝ, (0 : ℂ) ^ (ρ + (c + (t : ℂ) * Complex.I)) = 0 := by
  rcases eq_or_ne (c + ρ.re) 0 with h0 | h0
  · rw [MeasureTheory.ae_iff]
    refine measure_mono_null ?_ (by simp : volume ({-ρ.im} : Set ℝ) = 0)
    intro t ht
    show t = -ρ.im
    have hz : ρ + (c + (t : ℂ) * Complex.I) = 0 := by
      by_contra hz
      exact ht (Complex.zero_cpow hz)
    have him := congrArg Complex.im hz
    rw [im_exponent, Complex.zero_im] at him
    linarith
  · exact Filter.Eventually.of_forall fun t => Complex.zero_cpow (by
      intro hz
      have := congrArg Complex.re hz
      rw [re_exponent, Complex.zero_re] at this
      exact h0 this)

/-! ## Per-term evaluation of the integral -/

private lemma natCast_div (m n : ℕ) : (m : ℂ) / (n : ℂ) = (((m : ℝ) / n : ℝ) : ℂ) := by
  rw [← Complex.ofReal_natCast m, ← Complex.ofReal_natCast n, ← Complex.ofReal_div]

private lemma perTerm_eq (f : ℕ → ℂ) {c : ℝ} (hc : 0 < c) {N : ℕ} (ρ : ℂ)
    {n : ℕ} (hn : 1 ≤ n) :
    (1 / (2 * Real.pi)) * ∫ t : ℝ, (f n / (n : ℂ) ^ (ρ + (c + (t : ℂ) * Complex.I)))
        * (N : ℂ) ^ (c + (t : ℂ) * Complex.I)
        / ((c + (t : ℂ) * Complex.I) * (c + 1 + (t : ℂ) * Complex.I))
      = f n * (n : ℂ) ^ (-ρ) * mellK c ((N : ℂ) / (n : ℂ)) := by
  have hn0 : ((n : ℝ) : ℂ) ≠ 0 := by
    have : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    simpa using Complex.ofReal_ne_zero.mpr this
  rw [mellK]
  have key : ∀ t : ℝ,
      (f n / (n : ℂ) ^ (ρ + (c + (t : ℂ) * Complex.I)))
        * (N : ℂ) ^ (c + (t : ℂ) * Complex.I)
        / ((c + (t : ℂ) * Complex.I) * (c + 1 + (t : ℂ) * Complex.I))
      = (f n * (n : ℂ) ^ (-ρ)) * (((N : ℂ) / (n : ℂ)) ^ (c + (t : ℂ) * Complex.I)
        / ((c + (t : ℂ) * Complex.I) * (c + 1 + (t : ℂ) * Complex.I))) := by
    intro t
    simp only [← Complex.ofReal_natCast N, ← Complex.ofReal_natCast n]
    rw [Complex.cpow_add ρ (c + (t : ℂ) * Complex.I) hn0,
        Complex.div_cpow_ofReal_nonneg (Nat.cast_nonneg N) (Nat.cast_nonneg n)]
    simp only [div_eq_mul_inv, mul_inv, ← Complex.cpow_neg]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall key), integral_const_mul]
  ring

/-- Evaluation of the kernel at `x = N / n` with `1 ≤ n ≤ N`. -/
private lemma kernel_value_le {N n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    (if 1 ≤ (N : ℝ) / n then (1 - 1 / ((N : ℝ) / n) : ℝ) else 0 : ℂ)
      = 1 - (n : ℂ) / (N : ℂ) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hle : (1 : ℝ) ≤ (N : ℝ) / n :=
    (one_le_div₀ hnpos).mpr (by exact_mod_cast hnN)
  rw [if_pos hle]
  have h1 : 1 / ((N : ℝ) / n) = (n : ℝ) / N := by rw [one_div, inv_div]
  rw [h1]
  push_cast
  ring

/-! ## Main theorem -/

theorem detPerronFormula (f : ℕ → ℂ) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (ρ : ℂ)
    (hconv : Summable (fun n : ℕ => ‖f n‖ / (n : ℝ) ^ (c + ρ.re))) :
    (1 / (2 * Real.pi)) * ∫ t : ℝ,
        (∑' n : ℕ, f n / (n : ℂ) ^ (ρ + (c + (t : ℂ) * Complex.I)))
          * (N : ℂ) ^ (c + (t : ℂ) * Complex.I)
          / ((c + (t : ℂ) * Complex.I) * (c + 1 + (t : ℂ) * Complex.I))
      = ∑ n ∈ Finset.Icc 1 N, f n * (n : ℂ) ^ (-ρ) * (1 - (n : ℂ) / (N : ℂ)) := by
  rw [DetPerronInterchange_local f hc hN ρ hconv]
  rw [tsum_eq_sum (s := Finset.Icc 1 N) ?_]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Icc] at hn
    obtain ⟨hn1, hnN⟩ := hn
    rw [perTerm_eq f hc ρ hn1, natCast_div N n,
        DetPerronKernel_local hc (x := (N : ℝ) / n) (by positivity), kernel_value_le hn1 hnN]
  · intro n hn
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
    rcases hn with hnlt | hngt
    · have hn0 : n = 0 := by omega
      subst hn0
      simp only [Nat.cast_zero]
      have hz : ∀ᵐ t : ℝ, (f 0 / (0 : ℂ) ^ (ρ + (c + (t : ℂ) * Complex.I)))
            * (N : ℂ) ^ (c + (t : ℂ) * Complex.I)
            / ((c + (t : ℂ) * Complex.I) * (c + 1 + (t : ℂ) * Complex.I)) = 0 :=
        (zero_cpow_exponent_ae c ρ).mono fun t ht => by rw [ht]; simp
      rw [MeasureTheory.integral_eq_zero_of_ae hz]
      ring
    · have hn1 : 1 ≤ n := by omega
      rw [perTerm_eq f hc ρ hn1, natCast_div N n,
          DetPerronKernel_local hc (x := (N : ℝ) / n) (by positivity),
          if_neg (by
            rw [not_le]
            exact (div_lt_one₀ (by positivity)).mpr (by exact_mod_cast hngt))]
      ring

end Work.LinnikAreas.BGTZ
