import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Commons.Analysis.Fourier.hasSum_even_int_to_nat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Fourier

/-- The (even) summand of both sides of `neumann_lhs_eq_zeta`. -/
private noncomputable def nkHzeta (s t u v : ℝ) (n : ℤ) : ℝ :=
  Real.cos (Real.pi * (n : ℝ) * (u + s / 2) / s)
    * Real.cos (Real.pi * (n : ℝ) * (v + s / 2) / s)
    * Real.exp (-(t * (Real.pi * (n : ℝ) / s) ^ 2))

theorem neumann_lhs_eq_zeta {s t u v : ℝ} (hs : 0 < s) (ht : 0 < t) :
    (∑' k : ℕ, Real.cos (Real.pi * k * (u + s / 2) / s)
        * Real.cos (Real.pi * k * (v + s / 2) / s)
        * Real.exp (-(t * (Real.pi * k / s) ^ 2)) * (if k = 0 then s else s / 2)⁻¹)
      = s⁻¹ * ∑' n : ℤ, Real.cos (Real.pi * n * (u + s / 2) / s)
          * Real.cos (Real.pi * n * (v + s / 2) / s)
          * Real.exp (-(t * (Real.pi * n / s) ^ 2)) := by
  have hsne : s ≠ 0 := ne_of_gt hs
  -- Evenness of the summand.
  have hFe : ∀ n : ℤ, nkHzeta s t u v (-n) = nkHzeta s t u v n := by
    intro n
    have h1 : Real.pi * ((-n : ℤ) : ℝ) * (u + s / 2) / s
        = -(Real.pi * (n : ℝ) * (u + s / 2) / s) := by push_cast; ring
    have h2 : Real.pi * ((-n : ℤ) : ℝ) * (v + s / 2) / s
        = -(Real.pi * (n : ℝ) * (v + s / 2) / s) := by push_cast; ring
    have h3 : (Real.pi * ((-n : ℤ) : ℝ) / s) ^ 2 = (Real.pi * (n : ℝ) / s) ^ 2 := by
      push_cast; ring
    simp only [nkHzeta, h1, h2, h3, Real.cos_neg]
  -- Summability of the summand over `ℤ`.
  have hFs : Summable (nkHzeta s t u v) := by
    rw [summable_int_iff_summable_nat_and_neg]
    have hc : -(t * Real.pi ^ 2 / s ^ 2) < 0 := by
      have hpos : 0 < t * Real.pi ^ 2 / s ^ 2 := by positivity
      linarith
    have hge : Summable (fun n : ℕ =>
        Real.exp ((-(t * Real.pi ^ 2 / s ^ 2)) * (n : ℝ) ^ 2)) := by
      refine Real.summable_exp_nat_mul_of_ge hc (f := fun i : ℕ => (i : ℝ) ^ 2) ?_
      intro i
      rcases i with _ | i
      · simp
      · push_cast
        nlinarith [sq_nonneg (i : ℝ)]
    have hnat : Summable (fun n : ℕ => nkHzeta s t u v (n : ℤ)) := by
      refine Summable.of_norm_bounded hge (fun n => ?_)
      have hA : Real.pi * ((n : ℤ) : ℝ) * (u + s / 2) / s
          = Real.pi * (n : ℝ) * (u + s / 2) / s := by push_cast; ring
      have hB : Real.pi * ((n : ℤ) : ℝ) * (v + s / 2) / s
          = Real.pi * (n : ℝ) * (v + s / 2) / s := by push_cast; ring
      have hD : (Real.pi * ((n : ℤ) : ℝ) / s) ^ 2 = (Real.pi * (n : ℝ) / s) ^ 2 := by
        push_cast; ring
      rw [nkHzeta, hA, hB, hD]
      set A : ℝ := Real.pi * (n : ℝ) * (u + s / 2) / s with hAdef
      set B : ℝ := Real.pi * (n : ℝ) * (v + s / 2) / s with hBdef
      have hx := Real.abs_cos_le_one A
      have hy := Real.abs_cos_le_one B
      have hx0 := abs_nonneg (Real.cos A)
      have hy0 := abs_nonneg (Real.cos B)
      have hz : 0 ≤ Real.exp (-(t * (Real.pi * (n : ℝ) / s) ^ 2)) :=
        (Real.exp_pos _).le
      have hxy : |Real.cos A| * |Real.cos B| ≤ 1 := by
        calc |Real.cos A| * |Real.cos B| ≤ 1 * 1 := mul_le_mul hx hy hy0 (by norm_num)
          _ = 1 := by ring
      calc ‖Real.cos A * Real.cos B
              * Real.exp (-(t * (Real.pi * (n : ℝ) / s) ^ 2))‖
          = |Real.cos A| * |Real.cos B|
              * Real.exp (-(t * (Real.pi * (n : ℝ) / s) ^ 2)) := by
            rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
        _ ≤ 1 * Real.exp (-(t * (Real.pi * (n : ℝ) / s) ^ 2)) :=
            mul_le_mul_of_nonneg_right hxy hz
        _ = Real.exp ((-(t * Real.pi ^ 2 / s ^ 2)) * (n : ℝ) ^ 2) := by
            rw [one_mul]
            congr 1
            ring
    refine ⟨hnat, ?_⟩
    exact Summable.congr hnat (fun n => (hFe (n : ℤ)).symm)
  -- Apply the even-sum lemma.
  have hL := hasSum_even_int_to_nat hFe hFs.hasSum
  have hsum_eq : (∑' k : ℕ, (if k = 0 then (1 : ℝ) else 2) * nkHzeta s t u v (k : ℤ))
      = ∑' n : ℤ, nkHzeta s t u v n := hL.tsum_eq
  -- Termwise identification of the `ℕ`-summands.
  have hpoint : ∀ k : ℕ,
      Real.cos (Real.pi * k * (u + s / 2) / s)
        * Real.cos (Real.pi * k * (v + s / 2) / s)
        * Real.exp (-(t * (Real.pi * k / s) ^ 2)) * (if k = 0 then s else s / 2)⁻¹
      = s⁻¹ * ((if k = 0 then (1 : ℝ) else 2) * nkHzeta s t u v (k : ℤ)) := by
    intro k
    have hk : Real.pi * ((k : ℤ) : ℝ) * (u + s / 2) / s
        = Real.pi * (k : ℝ) * (u + s / 2) / s := by push_cast; ring
    have hk2 : Real.pi * ((k : ℤ) : ℝ) * (v + s / 2) / s
        = Real.pi * (k : ℝ) * (v + s / 2) / s := by push_cast; ring
    have hk3 : (Real.pi * ((k : ℤ) : ℝ) / s) ^ 2 = (Real.pi * (k : ℝ) / s) ^ 2 := by
      push_cast; ring
    rw [nkHzeta, hk, hk2, hk3]
    split_ifs with h0
    · subst h0
      simp
    · field_simp
  rw [tsum_congr hpoint, tsum_mul_left, hsum_eq]
  congr 1

end Commons.Analysis.Fourier