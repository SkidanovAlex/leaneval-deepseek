import Mathlib
import Submission.Work.KMTAreas.A7.cw_etaCut_decay
import Submission.Work.KMTAreas.A7.SecondDerivIntegral

namespace Work.KMTAreas.A7

open MeasureTheory Filter
open scoped Topology FourierTransform

set_option linter.unusedVariables false

/-- The quadratic decay of the coefficient kernel `cw m j = ∫_ℝ m(θ)e(-jθ)dθ`
(`Work.KMTAreas.A7.cw`): if `m` is `C²`, vanishes off `[-1/R,1/R]` (`R > 0`), and has
`‖m‖_∞ ≤ C₀`, `‖m''‖_∞ ≤ C₀·R²`, then `‖cw m j‖ ≤ C·C₀·R/j²` for `j ≠ 0`, the constant `C`
being absolute.  (Two integrations by parts, or equivalently
`𝓕(m'')(j) = (2πij)² 𝓕 m (j)` with `‖𝓕 g j‖ ≤ ∫‖g‖`.) -/
theorem CwBoundSq :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℝ → ℂ) (C0 R : ℝ),
      0 < R → 0 ≤ C0 → ContDiff ℝ 2 m →
      (∀ θ, ‖m θ‖ ≤ C0) →
      (∀ θ, ‖deriv m θ‖ ≤ C0 * R) →
      (∀ θ, ‖deriv (deriv m) θ‖ ≤ C0 * R ^ 2) →
      (∀ θ, 1 / R < |θ| → m θ = 0) →
      ∀ j : ℤ, j ≠ 0 → ‖Work.KMTAreas.A7.cw m j‖ ≤ C * C0 * R / (j : ℝ) ^ 2 := by
  refine ⟨1 / (2 * Real.pi ^ 2), by positivity, ?_⟩
  intro m C0 R hR hC0 hm hm0 hm1 hm2 hsupp j hj
  have hRpos : 0 < 1 / R := one_div_pos.mpr hR
  have hjne : ((j : ℝ)) ≠ 0 := by exact_mod_cast hj
  have hj2pos : (0 : ℝ) < (j : ℝ) ^ 2 := by
    rw [pow_two]; exact mul_self_pos.mpr hjne
  -- ### `m` has compact support (it vanishes off `[-1/R, 1/R]`)
  have hc : HasCompactSupport m := by
    refine HasCompactSupport.intro (K := Set.Icc (-(1 / R)) (1 / R)) isCompact_Icc
      (fun x hx => ?_)
    have hx' : 1 / R < |x| := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hx
      rcases hx with h | h
      · rw [abs_of_neg (by linarith)]
        linarith
      · rw [abs_of_pos (by linarith)]
        linarith
    exact hsupp x hx'
  -- ### `iteratedDeriv 2 m = m''`
  have h2eq : iteratedDeriv 2 m = deriv (deriv m) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  -- ### integrability of `m`, `m'` and `m''`
  have hg0 : Integrable m := hm.continuous.integrable_of_hasCompactSupport hc
  have hcomp2 : HasCompactSupport (iteratedDeriv 2 m) := by
    rw [h2eq]; exact hc.deriv.deriv
  have hg2 : Integrable (iteratedDeriv 2 m) :=
    (hm.continuous_iteratedDeriv 2 (by norm_num)).integrable_of_hasCompactSupport hcomp2
  have hInt : ∀ n : ℕ, (n : ℕ∞) ≤ 2 → Integrable (iteratedDeriv n m) := by
    intro n hn
    have hn' : n ≤ 2 := by exact_mod_cast hn
    interval_cases n
    · rw [iteratedDeriv_zero]; exact hg0
    · have hc1 : HasCompactSupport (iteratedDeriv 1 m) := by
        rw [iteratedDeriv_one]; exact hc.deriv
      exact (hm.continuous_iteratedDeriv 1 (by norm_num)).integrable_of_hasCompactSupport hc1
    · exact hg2
  -- ### the Fourier transform of the second derivative
  have hF2 : FourierTransform.fourier (iteratedDeriv 2 m) =
      fun x : ℝ =>
        (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) ^ 2 • FourierTransform.fourier m x :=
    Real.fourier_iteratedDeriv (N := 2) (n := 2) hm
      (fun n hn => hInt n (by exact_mod_cast hn)) (by norm_num)
  have hnorm2 : ‖FourierTransform.fourier (iteratedDeriv 2 m) (j : ℝ)‖ =
      (2 * Real.pi * |(j : ℝ)|) ^ 2 * ‖FourierTransform.fourier m (j : ℝ)‖ := by
    rw [congr_fun hF2 (j : ℝ), norm_smul, norm_pow]
    congr 1
    have h1 : ‖(2 : ℂ)‖ = 2 := by norm_num
    have h2 : ‖(Real.pi : ℂ)‖ = |Real.pi| := RCLike.norm_ofReal Real.pi
    have h3 : ‖(((j : ℝ) : ℂ))‖ = |(j : ℝ)| := RCLike.norm_ofReal _
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, h1, h2, h3,
      abs_of_nonneg Real.pi_pos.le]
  -- ### `L¹`-bound for `m''`: at most `2 C₀ R`
  have hB : ∫ y : ℝ, ‖deriv (deriv m) y‖ ≤ 2 * C0 * R :=
    SecondDerivIntegral hR hC0 hm2 hsupp
  -- ### second-derivative bound, transferred to `𝓕 m (j)`
  have hbd2 : (2 * Real.pi * |(j : ℝ)|) ^ 2 * ‖FourierTransform.fourier m (j : ℝ)‖
      ≤ 2 * C0 * R := by
    rw [← hnorm2]
    calc ‖FourierTransform.fourier (iteratedDeriv 2 m) (j : ℝ)‖
        ≤ ∫ y : ℝ, ‖iteratedDeriv 2 m y‖ :=
          VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
      _ = ∫ y : ℝ, ‖deriv (deriv m) y‖ :=
          integral_congr_ae (Filter.Eventually.of_forall (fun y => by rw [h2eq]))
      _ ≤ 2 * C0 * R := hB
  -- ### the arithmetic
  have hkey : (2 * Real.pi * |(j : ℝ)|) ^ 2 = 4 * Real.pi ^ 2 * (j : ℝ) ^ 2 := by
    rw [mul_pow, mul_pow, sq_abs]; ring
  have hmain : ‖cw m j‖ ≤ (2 * C0 * R) / (4 * Real.pi ^ 2 * (j : ℝ) ^ 2) := by
    have hden : (0 : ℝ) < 4 * Real.pi ^ 2 * (j : ℝ) ^ 2 := by positivity
    rw [le_div_iff₀ hden]
    calc ‖cw m j‖ * (4 * Real.pi ^ 2 * (j : ℝ) ^ 2)
        = (2 * Real.pi * |(j : ℝ)|) ^ 2 * ‖cw m j‖ := by rw [← hkey]; ring
      _ = (2 * Real.pi * |(j : ℝ)|) ^ 2 * ‖FourierTransform.fourier m (j : ℝ)‖ := by
          rw [cw_eq_fourierTransform]
      _ ≤ 2 * C0 * R := hbd2
  calc ‖cw m j‖ ≤ (2 * C0 * R) / (4 * Real.pi ^ 2 * (j : ℝ) ^ 2) := hmain
    _ = (1 / (2 * Real.pi ^ 2)) * C0 * R / (j : ℝ) ^ 2 := by
        have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
        field_simp
        ring

end Work.KMTAreas.A7
