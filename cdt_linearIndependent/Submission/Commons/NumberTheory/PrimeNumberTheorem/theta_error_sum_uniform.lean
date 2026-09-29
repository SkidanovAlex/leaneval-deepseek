import Mathlib
import Submission.Commons.NumberTheory.PrimeNumberTheorem.theta_band_sub_id_isLittleO

namespace Commons.NumberTheory.PrimeNumberTheorem

open Filter in
open scoped Topology in
theorem theta_error_sum_uniform (ι : Type*) [Fintype ι] (γ C ε : ℝ) (hγ : 0 < γ) (hC : 0 < C)
    (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ y : ι → ℝ,
      (∀ i, γ * (n : ℝ) ≤ y i) → (∀ i, y i ≤ C * (n : ℝ)) →
      |∑ i, (Chebyshev.theta (y i) - y i)| ≤ ε * (n : ℝ) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · filter_upwards with n
    intro y hy1 hy2
    rw [Finset.univ_eq_empty, Finset.sum_empty, abs_zero]
    positivity
  · have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
    set δ : ℝ := ε / (2 * C * Fintype.card ι) with hδdef
    have hδpos : 0 < δ := by rw [hδdef]; positivity
    have hsmall : ∀ᶠ y : ℝ in Filter.atTop, |Chebyshev.theta y - y| ≤ δ * y := by
      have h : ∀ᶠ y : ℝ in Filter.atTop, ‖Chebyshev.theta y - y‖ ≤ δ * ‖y‖ :=
        Asymptotics.isLittleO_iff.mp theta_sub_id_isLittleO hδpos
      filter_upwards [h, Filter.eventually_ge_atTop (0 : ℝ)] with y hy hy0
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hy0] at hy
      exact hy
    rw [Filter.eventually_atTop] at hsmall
    obtain ⟨Y₀, hY₀⟩ := hsmall
    have htend : ∀ᶠ n : ℕ in Filter.atTop, Y₀ ≤ γ * (n : ℝ) :=
      (Filter.Tendsto.const_mul_atTop hγ
        (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (Filter.eventually_ge_atTop Y₀)
    filter_upwards [htend] with n hn
    intro y hy1 hy2
    have hbound : ∀ i, |Chebyshev.theta (y i) - y i| ≤ δ * C * (n : ℝ) := by
      intro i
      have hyi_ge : Y₀ ≤ y i := le_trans hn (hy1 i)
      have h1 : |Chebyshev.theta (y i) - y i| ≤ δ * y i := hY₀ (y i) hyi_ge
      have hCn : (0 : ℝ) ≤ C * (n : ℝ) := by positivity
      calc |Chebyshev.theta (y i) - y i| ≤ δ * y i := h1
        _ ≤ δ * (C * (n : ℝ)) := by
              exact mul_le_mul_of_nonneg_left (hy2 i) (le_of_lt hδpos)
        _ = δ * C * (n : ℝ) := by ring
    have hkey : (Fintype.card ι : ℝ) * δ * C = ε / 2 := by
      rw [hδdef]
      have hCne : C ≠ 0 := ne_of_gt hC
      have hcine : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hcard
      field_simp
    calc |∑ i, (Chebyshev.theta (y i) - y i)|
        ≤ ∑ i, |Chebyshev.theta (y i) - y i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : ι, δ * C * (n : ℝ) := Finset.sum_le_sum (fun i _ => hbound i)
      _ = (Fintype.card ι : ℝ) * (δ * C * (n : ℝ)) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ε / 2 * (n : ℝ) := by
            rw [← mul_assoc, ← mul_assoc]
            rw [hkey]
      _ ≤ ε * (n : ℝ) := by
            have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
            nlinarith [hε, hn0]

end Commons.NumberTheory.PrimeNumberTheorem
