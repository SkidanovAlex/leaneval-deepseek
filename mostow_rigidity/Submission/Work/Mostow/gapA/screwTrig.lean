import Mathlib

namespace Work.Mostow.gapA

/-- Every point `(α, β)` on the unit circle is `(cos φ, sin φ)` for some real `φ`. -/
lemma exists_cos_eq_sin_eq (α β : ℝ) (h : α ^ 2 + β ^ 2 = 1) :
    ∃ φ : ℝ, Real.cos φ = α ∧ Real.sin φ = β := by
  have hz : Complex.normSq ((α : ℂ) + β * Complex.I) = 1 := by
    rw [Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      add_zero, zero_add]
    nlinarith [h]
  have hnorm : ‖((α : ℂ) + β * Complex.I)‖ = 1 := by
    have h2 := Complex.normSq_eq_norm_sq ((α : ℂ) + β * Complex.I)
    rw [hz] at h2
    nlinarith [norm_nonneg ((α : ℂ) + β * Complex.I)]
  refine ⟨((α : ℂ) + β * Complex.I).arg, ?_⟩
  have hexp : Complex.exp (↑(((α : ℂ) + β * Complex.I).arg) * Complex.I)
      = ((α : ℂ) + β * Complex.I) := by
    have hh := Complex.norm_mul_exp_arg_mul_I ((α : ℂ) + β * Complex.I)
    rw [hnorm, Complex.ofReal_one, one_mul] at hh
    exact hh
  rw [Complex.exp_mul_I] at hexp
  constructor
  · have hre := congrArg Complex.re hexp
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero,
      Complex.cos_ofReal_re, Complex.sin_ofReal_im] at hre
    exact hre
  · have him := congrArg Complex.im hexp
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, mul_one, add_zero,
      Complex.cos_ofReal_im, Complex.sin_ofReal_re, zero_add] at him
    exact him

/-- On the circle, the equally spaced angles `2πj/M` come within `π/M` of any point `φ`. -/
lemma exists_int_grid (M : ℕ) (hM : 0 < M) (φ : ℝ) :
    ∃ j : ℤ, |φ - 2 * Real.pi * (j : ℝ) / M| ≤ Real.pi / M := by
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  set x : ℝ := φ * (M : ℝ) / (2 * Real.pi) with hx
  refine ⟨⌊x + 1 / 2⌋, ?_⟩
  have h1 : (⌊x + 1 / 2⌋ : ℝ) ≤ x + 1 / 2 := Int.floor_le _
  have h2 : x + 1 / 2 < (⌊x + 1 / 2⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have habs : |x - (⌊x + 1 / 2⌋ : ℝ)| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith
  have hkey : φ - 2 * Real.pi * (⌊x + 1 / 2⌋ : ℝ) / M
      = (2 * Real.pi / M) * (x - (⌊x + 1 / 2⌋ : ℝ)) := by
    rw [hx]; field_simp
  rw [hkey, abs_mul]
  have hcoef : |2 * Real.pi / M| = 2 * Real.pi / M := by
    rw [abs_of_nonneg]; positivity
  rw [hcoef]
  calc (2 * Real.pi / M) * |x - (⌊x + 1 / 2⌋ : ℝ)|
        ≤ (2 * Real.pi / M) * (1 / 2) := by
          apply mul_le_mul_of_nonneg_left habs; positivity
    _ = Real.pi / M := by ring

/-- For points `α cos θ + β sin θ` with `α² + β² = 1` sampled at the `M`-th roots of
unity angles `θ = 2πj/M`, some sample is at least `cos (π/M)`. -/
theorem screwTrig (M : ℕ) (hM : 0 < M) (α β : ℝ) (h : α ^ 2 + β ^ 2 = 1) :
    ∃ j : ℤ, Real.cos (Real.pi / M)
      ≤ α * Real.cos (2 * Real.pi * (j : ℝ) / M) + β * Real.sin (2 * Real.pi * (j : ℝ) / M) := by
  obtain ⟨φ, hcos, hsin⟩ := exists_cos_eq_sin_eq α β h
  obtain ⟨j, hj⟩ := exists_int_grid M hM φ
  refine ⟨j, ?_⟩
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hsub : α * Real.cos (2 * Real.pi * (j : ℝ) / M)
        + β * Real.sin (2 * Real.pi * (j : ℝ) / M)
      = Real.cos (φ - 2 * Real.pi * (j : ℝ) / M) := by
    rw [Real.cos_sub, hcos, hsin]
  rw [hsub]
  have hcosabs : Real.cos (φ - 2 * Real.pi * (j : ℝ) / M)
      = Real.cos |φ - 2 * Real.pi * (j : ℝ) / M| := (Real.cos_abs _).symm
  rw [hcosabs]
  apply Real.cos_le_cos_of_nonneg_of_le_pi
  · positivity
  · exact div_le_self (le_of_lt Real.pi_pos) hM1
  · exact hj

end Work.Mostow.gapA
