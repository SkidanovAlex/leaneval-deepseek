import Mathlib
import Submission.Work.GM.S3.Base

namespace Work.GM.S3

open MeasureTheory
open scoped FourierTransform

/-- `‖2 * π * I * x‖ = 2 * π * |x|` for real `x`. -/
private lemma norm_two_pi_I_mul (x : ℝ) :
    ‖(2 * Real.pi * Complex.I * (x : ℂ))‖ = 2 * Real.pi * |x| := by
  rw [norm_mul, norm_mul, norm_mul]
  simp only [Complex.norm_ofNat, Complex.norm_I, mul_one]
  rw [show ‖(Real.pi : ℂ)‖ = Real.pi by simp [abs_of_nonneg Real.pi_pos.le]]
  simp

/-- The integral `∫ exp(-2πiAu) φ u du` is the Fourier transform of `φ` at `A`. -/
private lemma integral_exp_eq_fourier (φ : ℝ → ℂ) (A : ℝ) :
    (∫ u : ℝ, Complex.exp (-(2 * Real.pi * Complex.I * A * u)) * φ u) = 𝓕 φ A := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  congr 1
  ext u
  simp only [smul_eq_mul]
  congr 1
  push_cast
  ring

/-- **Oscillatory integral with a uniform derivative bound** (the engine of GM Proposition 7.1).

Smoothness is required as `ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ`, i.e. `C^∞`; a bare
`ContDiff ℝ ⊤ φ` would mean *analytic*, and an analytic function vanishing off `[1,2]` is `0`,
which would make the statement vacuous.

For every `j : ℕ` there is `C > 0` such that for every real `B` and every smooth `φ : ℝ → ℂ` which
vanishes off `[1,2]` and satisfies `‖iteratedDeriv i φ x‖ ≤ B` for all `i ≤ j` and all `x`, one has
for all real `A ≠ 0`

`‖∫_ℝ exp(-2πi A u) φ u du‖ ≤ C * B / |A|^j`.

Proof idea: `j` integrations by parts (boundary terms vanish since `φ` is `C^∞` and vanishes off
`[1,2]`), using `∫ ‖φ^{(j)}‖ ≤ 2B` from the support and derivative hypotheses.  This is
`Commons.Analysis.Fourier.fourierTransform_iteratedDeriv_decay` (`𝓕 φ A = ∫ exp(-2πiAu) φ u du`) with
the constant tracked against `B`. -/
theorem osc_integral_decay (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℝ) (φ : ℝ → ℂ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ →
      (∀ x, x ∉ Set.Icc 1 2 → φ x = 0) →
      (∀ i ≤ j, ∀ x, ‖iteratedDeriv i φ x‖ ≤ B) →
      ∀ A : ℝ, A ≠ 0 →
      ‖∫ u : ℝ, Complex.exp (-(2 * Real.pi * Complex.I * A * u)) * φ u‖ ≤ C * B / |A| ^ j := by
  refine ⟨1, one_pos, ?_⟩
  intro B φ hφ hsupp hB A hA
  rw [integral_exp_eq_fourier]
  -- `φ` (and hence all its derivatives) vanishes off `[1,2]`.
  have hzero : ∀ x, x ∉ Set.Icc (1 : ℝ) 2 → iteratedDeriv j φ x = 0 := by
    intro x hx
    have hEqOn : Set.EqOn φ (fun _ : ℝ => (0 : ℂ)) (Set.Icc (1 : ℝ) 2)ᶜ := by
      intro y hy
      exact hsupp y (by simpa using hy)
    have hder := Set.EqOn.iteratedDeriv_of_isOpen hEqOn isClosed_Icc.isOpen_compl j
    have hx' : x ∈ (Set.Icc (1 : ℝ) 2)ᶜ := by simpa using hx
    have h := hder hx'
    rw [h]
    simp
  -- `φ` has compact support, so every iterated derivative is integrable.
  have hcs : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc hsupp
  have hint : ∀ n : ℕ, Integrable (iteratedDeriv n φ) := by
    intro n
    have hsupp' : HasCompactSupport (iteratedDeriv n φ) := by
      rw [iteratedDeriv_eq_equiv_comp]
      exact (hcs.iteratedFDeriv (𝕜 := ℝ) n).comp_left (map_zero _)
    exact (hφ.continuous_iteratedDeriv n (WithTop.coe_le_coe.mpr le_top)).integrable_of_hasCompactSupport
      hsupp'
  -- Differentiation becomes multiplication by `(2πi·)^j` under the Fourier transform.
  set Aint : ℝ := ∫ y, ‖iteratedDeriv j φ y‖ with hAdef
  have hfj : ContDiff ℝ ((j : ℕ∞) : WithTop ℕ∞) φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hfour := Real.fourier_iteratedDeriv (f := φ) (N := (j : ℕ∞)) (n := j) hfj
      (fun n _ => hint n) (by simp)
  have hfour' : ∀ x : ℝ, 𝓕 (iteratedDeriv j φ) x
        = (2 * Real.pi * Complex.I * (x : ℂ)) ^ j • (𝓕 φ x) := fun x => congrFun hfour x
  -- The Fourier transform of the `j`-th derivative is bounded by `∫ ‖φ^{(j)}‖`.
  have hAbound (η : ℝ) : ‖𝓕 (iteratedDeriv j φ) η‖ ≤ Aint := by
    rw [Real.fourier_eq]
    refine (norm_integral_le_integral_norm _).trans ?_
    simp only [Circle.norm_smul]
    exact le_of_eq hAdef.symm
  have h2pi : ∀ η : ℝ, ‖(2 * Real.pi * Complex.I * (η : ℂ)) ^ j‖ = (2 * Real.pi * |η|) ^ j := by
    intro η
    rw [norm_pow, norm_two_pi_I_mul]
  have hkey : ‖𝓕 φ A‖ * (2 * Real.pi * |A|) ^ j ≤ Aint := by
    have hb : (2 * Real.pi * |A|) ^ j * ‖𝓕 φ A‖ ≤ Aint := by
      have h := hAbound A
      rwa [hfour' A, norm_smul, h2pi A] at h
    calc ‖𝓕 φ A‖ * (2 * Real.pi * |A|) ^ j
        = (2 * Real.pi * |A|) ^ j * ‖𝓕 φ A‖ := by ring
      _ ≤ Aint := hb
  -- `∫ ‖φ^{(j)}‖ ≤ B`, using the support and the derivative bound.
  have hAB : Aint ≤ B := by
    rw [hAdef]
    have hind : (fun y => ‖iteratedDeriv j φ y‖)
        = (Set.Icc (1 : ℝ) 2).indicator (fun y => ‖iteratedDeriv j φ y‖) := by
      funext y
      by_cases hy : y ∈ Set.Icc (1 : ℝ) 2
      · rw [Set.indicator_of_mem hy]
      · rw [Set.indicator_of_notMem hy, hzero y hy, norm_zero]
    rw [hind, integral_indicator measurableSet_Icc]
    calc ∫ y in Set.Icc (1 : ℝ) 2, ‖iteratedDeriv j φ y‖
        ≤ ∫ _ in Set.Icc (1 : ℝ) 2, B := by
          refine setIntegral_mono (hint j).norm.integrableOn ?_ ?_
          · exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
          · exact fun x => hB j le_rfl x
      _ = B := by
          rw [setIntegral_const]
          simp
          ring
  have hAjpos : 0 < |A| ^ j := pow_pos (abs_pos.mpr hA) j
  have hle : ‖𝓕 φ A‖ * |A| ^ j ≤ B := by
    have h2 : |A| ^ j ≤ (2 * Real.pi * |A|) ^ j := by
      apply pow_le_pow_left₀ (abs_nonneg A)
      have hπ : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
      calc |A| = |A| * 1 := by ring
        _ ≤ |A| * (2 * Real.pi) := mul_le_mul_of_nonneg_left hπ (abs_nonneg A)
        _ = 2 * Real.pi * |A| := by ring
    calc ‖𝓕 φ A‖ * |A| ^ j
        ≤ ‖𝓕 φ A‖ * (2 * Real.pi * |A|) ^ j :=
          mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ ≤ Aint := hkey
      _ ≤ B := hAB
  rw [one_mul]
  exact (le_div_iff₀ hAjpos).mpr hle

end Work.GM.S3
