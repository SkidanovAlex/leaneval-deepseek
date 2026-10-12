import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB7.Q3Defs
import Submission.Work.BoseBoxFock.GrowthEnv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

/-!
# `Work.BoseBoxFock.KzBogFS_envCoefSums`

Scalar (coefficient-level) estimates showing that every row coefficient of FS's
substituted Hamiltonian `KzOpFS ρ` is bounded, uniformly in `ρ ≥ 0`, by the
corresponding coefficient of the *reference* environment multiplied by the growth
envelope `genv ρ = 1 + √ρ·ρ`.  In other words: the coefficient sums of the
`ρ`-dependent operator are dominated by the coefficient sums of the `ρ`-free
operator, at the price of one factor `genv ρ`.

Everything here is elementary real arithmetic plus the three termwise bounds
`abs_add_rho_mul_le_genv`, `abs_rho_mul_le_genv`, `envCoef_third_le`.
-/

/-- `|x + ρ y| ≤ (|x| + |y|)·genv ρ` for `ρ ≥ 0` (uses `1 ≤ genv ρ` and `ρ ≤ genv ρ`). -/
lemma abs_add_rho_mul_le_genv {ρ : ℝ} (hρ : 0 ≤ ρ) (x y : ℝ) :
    |x + ρ * y| ≤ (|x| + |y|) * genv ρ := by
  have hg1 : 1 ≤ genv ρ := one_le_genv ρ
  have hr : ρ ≤ genv ρ := self_le_genv hρ
  have hx : |x| ≤ |x| * genv ρ := by
    have := mul_le_mul_of_nonneg_left hg1 (abs_nonneg x)
    linarith
  have hy : ρ * |y| ≤ |y| * genv ρ := by
    have := mul_le_mul_of_nonneg_right hr (abs_nonneg y)
    linarith
  calc |x + ρ * y| ≤ |x| + |ρ * y| := abs_add_le _ _
    _ = |x| + ρ * |y| := by rw [abs_mul, abs_of_nonneg hρ]
    _ ≤ (|x| + |y|) * genv ρ := by nlinarith [hx, hy]

/-- `|ρ y| ≤ |y|·genv ρ` for `ρ ≥ 0`. -/
lemma abs_rho_mul_le_genv {ρ : ℝ} (hρ : 0 ≤ ρ) (y : ℝ) :
    |ρ * y| ≤ |y| * genv ρ := by
  have hr : ρ ≤ genv ρ := self_le_genv hρ
  calc |ρ * y| = ρ * |y| := by rw [abs_mul, abs_of_nonneg hρ]
    _ ≤ |y| * genv ρ := by
        have := mul_le_mul_of_nonneg_right hr (abs_nonneg y)
        linarith

/-- `max 1 ρ · √ρ ≤ genv ρ`, valid for every real `ρ`. -/
lemma max_one_mul_sqrt_le_genv (ρ : ℝ) : max 1 ρ * Real.sqrt ρ ≤ genv ρ := by
  rcases lt_or_ge ρ 1 with h | h
  · rw [max_eq_left (le_of_lt h), one_mul]
    rcases lt_or_ge 0 ρ with h0 | h0
    · exact sqrt_le_genv (le_of_lt h0)
    · rw [Real.sqrt_eq_zero_of_nonpos h0]
      exact genv_nonneg ρ
  · rw [max_eq_right h, mul_comm]
    exact sqrt_mul_self_le_genv ρ

/-- `|ρ - μ| ≤ max 1 ρ · (1 + |μ|)` for `ρ ≥ 0`. -/
lemma abs_sub_mu_le (ρ μ : ℝ) (hρ : 0 ≤ ρ) :
    |ρ - μ| ≤ max 1 ρ * (1 + |μ|) := by
  have hm1 : 1 ≤ max 1 ρ := le_max_left _ _
  have hr : ρ ≤ max 1 ρ := le_max_right _ _
  have h1 : |ρ - μ| ≤ ρ + |μ| := by
    calc |ρ - μ| = |ρ + (-μ)| := by ring_nf
      _ ≤ |ρ| + |-μ| := abs_add_le _ _
      _ = ρ + |μ| := by rw [abs_of_nonneg hρ, abs_neg]
  have h2 : |μ| ≤ max 1 ρ * |μ| := by nlinarith [abs_nonneg μ, hm1]
  nlinarith [h1, h2, hr]

/-- `√(ρ ℓ³) ≤ √ρ · √|ℓ|³` for `ρ ≥ 0`. -/
lemma sqrt_mul_cube_le (ρ ell : ℝ) (hρ : 0 ≤ ρ) :
    Real.sqrt (ρ * ell ^ 3) ≤ Real.sqrt ρ * Real.sqrt (|ell| ^ 3) := by
  have h1 : ell ^ 3 ≤ |ell| ^ 3 := by
    rw [← abs_pow]
    exact le_abs_self _
  have h2 : ρ * ell ^ 3 ≤ ρ * |ell| ^ 3 := mul_le_mul_of_nonneg_left h1 hρ
  calc Real.sqrt (ρ * ell ^ 3) ≤ Real.sqrt (ρ * |ell| ^ 3) := Real.sqrt_le_sqrt h2
    _ = Real.sqrt ρ * Real.sqrt (|ell| ^ 3) := Real.sqrt_mul hρ _

/-- `|ρ - μ|·√(ρ ℓ³) ≤ (1 + |μ|)·√|ℓ|³·genv ρ` for `ρ ≥ 0`. -/
lemma abs_sub_mul_sqrt_le (ρ μ ell : ℝ) (hρ : 0 ≤ ρ) :
    |ρ - μ| * Real.sqrt (ρ * ell ^ 3)
      ≤ (1 + |μ|) * Real.sqrt (|ell| ^ 3) * genv ρ := by
  have hsub := abs_sub_mu_le ρ μ hρ
  have hm := max_one_mul_sqrt_le_genv ρ
  have hs := sqrt_mul_cube_le ρ ell hρ
  have hT0 : 0 ≤ Real.sqrt (|ell| ^ 3) := Real.sqrt_nonneg _
  have hμ0 : 0 ≤ 1 + |μ| := by positivity
  have hm0 : 0 ≤ max 1 ρ := le_trans zero_le_one (le_max_left _ _)
  have step1 : |ρ - μ| * Real.sqrt (ρ * ell ^ 3)
      ≤ (max 1 ρ * (1 + |μ|)) * (Real.sqrt ρ * Real.sqrt (|ell| ^ 3)) :=
    mul_le_mul hsub hs (Real.sqrt_nonneg _) (mul_nonneg hm0 hμ0)
  have step2 : (max 1 ρ * (1 + |μ|)) * (Real.sqrt ρ * Real.sqrt (|ell| ^ 3))
      = (max 1 ρ * Real.sqrt ρ) * ((1 + |μ|) * Real.sqrt (|ell| ^ 3)) := by ring
  have step3 : (max 1 ρ * Real.sqrt ρ) * ((1 + |μ|) * Real.sqrt (|ell| ^ 3))
      ≤ genv ρ * ((1 + |μ|) * Real.sqrt (|ell| ^ 3)) :=
    mul_le_mul_of_nonneg_right hm (mul_nonneg hμ0 hT0)
  calc |ρ - μ| * Real.sqrt (ρ * ell ^ 3)
      ≤ genv ρ * ((1 + |μ|) * Real.sqrt (|ell| ^ 3)) :=
        le_trans step1 (le_trans (le_of_eq step2) step3)
    _ = (1 + |μ|) * Real.sqrt (|ell| ^ 3) * genv ρ := by ring

/-- The third coefficient bound, termwise: for `ρ ≥ 0`,
`|(ρ-μ) w c √(ρ ℓ³)| ≤ |w c| √|ℓ|³ (1+|μ|) genv ρ`. -/
lemma envCoef_third_le (ρ μ w c ell : ℝ) (hρ : 0 ≤ ρ) :
    |(ρ - μ) * w * c * Real.sqrt (ρ * ell ^ 3)|
      ≤ |w * c| * Real.sqrt (|ell| ^ 3) * (1 + |μ|) * genv ρ := by
  have key := abs_sub_mul_sqrt_le ρ μ ell hρ
  have h1 : |(ρ - μ) * w * c * Real.sqrt (ρ * ell ^ 3)|
      = |w * c| * (|ρ - μ| * Real.sqrt (ρ * ell ^ 3)) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_mul]
    ring
  rw [h1]
  calc |w * c| * (|ρ - μ| * Real.sqrt (ρ * ell ^ 3))
      ≤ |w * c| * ((1 + |μ|) * Real.sqrt (|ell| ^ 3) * genv ρ) :=
        mul_le_mul_of_nonneg_left key (abs_nonneg _)
    _ = |w * c| * Real.sqrt (|ell| ^ 3) * (1 + |μ|) * genv ρ := by ring

theorem KzBogFS_envCoefSums {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (∑ k : Mode, |E.tau k + ρ * E.W1 k|) + (∑ k : Mode, |ρ * E.W1 k|)
      + 2 * (∑ k : Mode, |(ρ - E.mu) * E.W1 0 * E.hatChi k * Real.sqrt (ρ * E.ell ^ 3)|)
    ≤ ((∑ k : Mode, (|E.tau k| + |E.W1 k|)) + (∑ k : Mode, |E.W1 k|)
        + 2 * (∑ k : Mode, |E.W1 0 * E.hatChi k| * Real.sqrt (|E.ell| ^ 3) * (1 + |E.mu|)))
      * Work.BoseBoxFock.genv ρ := by
  have h1 : ∀ k : Mode, |E.tau k + ρ * E.W1 k| ≤ (|E.tau k| + |E.W1 k|) * genv ρ :=
    fun k => abs_add_rho_mul_le_genv hρ _ _
  have h2 : ∀ k : Mode, |ρ * E.W1 k| ≤ |E.W1 k| * genv ρ :=
    fun k => abs_rho_mul_le_genv hρ _
  have h3 : ∀ k : Mode,
      |(ρ - E.mu) * E.W1 0 * E.hatChi k * Real.sqrt (ρ * E.ell ^ 3)|
        ≤ |E.W1 0 * E.hatChi k| * Real.sqrt (|E.ell| ^ 3) * (1 + |E.mu|) * genv ρ :=
    fun k => envCoef_third_le ρ E.mu (E.W1 0) (E.hatChi k) E.ell hρ
  have s1 : (∑ k : Mode, |E.tau k + ρ * E.W1 k|)
      ≤ (∑ k : Mode, (|E.tau k| + |E.W1 k|)) * genv ρ := by
    have h := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset Mode)) => h1 k)
    simpa only [Finset.sum_mul] using h
  have s2 : (∑ k : Mode, |ρ * E.W1 k|)
      ≤ (∑ k : Mode, |E.W1 k|) * genv ρ := by
    have h := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset Mode)) => h2 k)
    simpa only [Finset.sum_mul] using h
  have s3 : (∑ k : Mode, |(ρ - E.mu) * E.W1 0 * E.hatChi k * Real.sqrt (ρ * E.ell ^ 3)|)
      ≤ (∑ k : Mode, |E.W1 0 * E.hatChi k| * Real.sqrt (|E.ell| ^ 3) * (1 + |E.mu|))
        * genv ρ := by
    have h := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset Mode)) => h3 k)
    simpa only [Finset.sum_mul] using h
  have hs3 : 2 * (∑ k : Mode,
        |(ρ - E.mu) * E.W1 0 * E.hatChi k * Real.sqrt (ρ * E.ell ^ 3)|)
      ≤ 2 * ((∑ k : Mode, |E.W1 0 * E.hatChi k| * Real.sqrt (|E.ell| ^ 3) * (1 + |E.mu|)))
        * genv ρ := by
    nlinarith [s3]
  nlinarith [s1, s2, hs3]

end Work.BoseBoxFock
