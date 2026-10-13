import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.Spaces.Defs
import Submission.Work.Stability.Cutoff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.PropL2Cut

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The two-scale cutoff of the `prop:L2` energy arguments

`Wc n z = ψ((n+1) z) · χ(z/(n+1))` where `ψ = Real.smoothTransition` is the smooth step
(`ψ = 0` on `(-∞,0]`, `ψ = 1` on `[1,∞)`) and `χ = Work.Stability.chi` is the bump
(`χ = 1` on `[-1,1]`, `χ = 0` off `(-2,2)`).

The factor `ψ((n+1)·)` makes the family one-sided (vanishing for `z ≤ 0`, as the truncated
`θ`-energy identity requires) and tends to `1` at each fixed `z > 0`; the factor `χ(·/(n+1))`
makes the support compact.  The two scales are what keep the radial weight-derivatives
`(z² W²)''` and `(z W²)'` uniformly bounded. -/

/-- The cutoff family `Wc n z = ψ((n+1) z) · χ(z/(n+1))`. -/
def Wc (n : ℕ) (z : ℝ) : ℝ :=
  Real.smoothTransition (((n : ℝ) + 1) * z) * Work.Stability.chi (z / ((n : ℝ) + 1))

/-- The coefficient of the truncated `θ`-energy identity at the cutoff `W`:
`Q = (α²/2)(z²W²)'' − (α(5+α)/2)(zW²)' + 6W²`. -/
def Qcoef (α : ℝ) (W : ℝ → ℝ) : ℝ → ℝ :=
  fun z => (α ^ 2 / 2) * deriv (fun z => deriv (fun z => z ^ 2 * (W z) ^ 2) z) z
    - (α * (5 + α) / 2) * deriv (fun z => z * (W z) ^ 2) z
    + 6 * (W z) ^ 2

/-! ## Elementary properties of the cutoff -/

theorem Wc_contDiff (n : ℕ) : ContDiff ℝ ∞ (Wc n) := by
  have h1 : ContDiff ℝ ∞ (fun z : ℝ => Real.smoothTransition (((n : ℝ) + 1) * z)) :=
    (Real.smoothTransition.contDiff : ContDiff ℝ ∞ _).comp (by fun_prop)
  have h2 : ContDiff ℝ ∞ (fun z : ℝ => Work.Stability.chi (z / ((n : ℝ) + 1))) :=
    Work.Stability.chi_contDiff.comp (by fun_prop)
  unfold Wc
  exact h1.mul h2

theorem Wc_continuous (n : ℕ) : Continuous (Wc n) := (Wc_contDiff n).continuous

theorem Wc_nonneg (n : ℕ) (z : ℝ) : 0 ≤ Wc n z := by
  unfold Wc
  exact mul_nonneg (Real.smoothTransition.nonneg _) (Work.Stability.chi_nonneg _)

theorem Wc_le_one (n : ℕ) (z : ℝ) : Wc n z ≤ 1 := by
  unfold Wc
  simpa using mul_le_mul (Real.smoothTransition.le_one (((n : ℝ) + 1) * z))
    (Work.Stability.chi_le_one (z / ((n : ℝ) + 1))) (Work.Stability.chi_nonneg _) zero_le_one

theorem Wc_sq_le_one (n : ℕ) (z : ℝ) : (Wc n z) ^ 2 ≤ 1 := by
  have h0 := Wc_nonneg n z
  have h1 := Wc_le_one n z
  nlinarith

/-- Off `[-(2(n+1)), 2(n+1)]` the cutoff vanishes. -/
theorem Wc_eq_zero_of_abs {n : ℕ} {z : ℝ} (h : 2 * ((n : ℝ) + 1) ≤ |z|) : Wc n z = 0 := by
  have hn' : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have habs : 2 ≤ |z / ((n : ℝ) + 1)| := by
    rw [abs_div, abs_of_nonneg hn'.le, le_div_iff₀ hn']
    linarith
  unfold Wc
  rw [Work.Stability.chi_eq_zero habs, mul_zero]

theorem Wc_hasCompactSupport (n : ℕ) : HasCompactSupport (Wc n) := by
  have hK : IsCompact (Set.Icc (-(2 * ((n : ℝ) + 1))) (2 * ((n : ℝ) + 1))) := isCompact_Icc
  refine HasCompactSupport.intro hK ?_
  intro z hz
  rw [Set.mem_Icc, not_and_or] at hz
  rcases hz with h | h
  · refine Wc_eq_zero_of_abs ?_
    rw [abs_of_nonpos (by linarith [not_le.mp h])]
    linarith [not_le.mp h]
  · refine Wc_eq_zero_of_abs ?_
    rw [abs_of_nonneg (by linarith [not_le.mp h])]
    linarith [not_le.mp h]

/-- The cutoff vanishes for `z ≤ 0`. -/
theorem Wc_eq_zero_of_nonpos {n : ℕ} {z : ℝ} (hz : z ≤ 0) : Wc n z = 0 := by
  unfold Wc
  rw [Real.smoothTransition.zero_of_nonpos
    (mul_nonpos_of_nonneg_of_nonpos (by positivity) hz), zero_mul]

theorem Wc_ne_zero_pos {n : ℕ} {z : ℝ} (h : Wc n z ≠ 0) : 0 < z := by
  by_contra hz
  exact h (Wc_eq_zero_of_nonpos (le_of_not_gt hz))

/-- Where both factors are at their maximal value the cutoff is exactly `1`. -/
theorem Wc_eq_one_of_le {n : ℕ} {z : ℝ} (h1 : 1 ≤ ((n : ℝ) + 1) * z)
    (h2 : |z / ((n : ℝ) + 1)| ≤ 1) : Wc n z = 1 := by
  unfold Wc
  rw [Real.smoothTransition.eq_one_iff_one_le.mpr h1, Work.Stability.chi_eq_one h2, mul_one]

/-- The cutoff tends to `1` at every fixed `z > 0`. -/
theorem Wc_tendsto_one (z : ℝ) (hz : 0 < z) :
    Tendsto (fun n : ℕ => Wc n z) atTop (𝓝 1) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (max (1 / z) z)
  have hev : ∀ n : ℕ, N ≤ n → Wc n z = 1 := by
    intro n hn
    have hn' : max (1 / z) z ≤ (n : ℝ) := le_trans hN (by exact_mod_cast hn)
    have hle1 : (1 : ℝ) ≤ ((n : ℝ) + 1) * z := by
      have h : 1 / z ≤ (n : ℝ) := le_trans (le_max_left _ _) hn'
      rw [div_le_iff₀ hz] at h
      nlinarith [h, hz]
    have hle2 : |z / ((n : ℝ) + 1)| ≤ 1 := by
      have hz0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      rw [abs_of_nonneg (div_nonneg hz.le hz0.le), div_le_one hz0]
      have h : z ≤ (n : ℝ) := le_trans (le_max_right _ _) hn'
      linarith
    exact Wc_eq_one_of_le hle1 hle2
  apply Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [eventually_ge_atTop N] with n hn
  exact (hev n hn).symm

theorem Wc_eq_zero_zero (n : ℕ) : Wc n 0 = 0 := Wc_eq_zero_of_nonpos le_rfl

end Work.FTS.EllipticEst.PropL2Cut
