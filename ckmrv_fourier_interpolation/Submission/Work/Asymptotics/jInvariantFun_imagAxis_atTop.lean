import Mathlib
import Submission.Work.Kernels.All
import Submission.Work.Asymptotics.Basic
import Submission.Work.Modular.E4_tendsto_atImInfty

open UpperHalfPlane Filter Asymptotics
open scoped Topology

namespace Work.Asymptotics

/-- **`Δ` is `O(exp(-2π im τ))` at the cusp `i∞`.**  This is the upper bound half of the cusp
asymptotics of the discriminant; it is `CuspFormClass.exp_decay_atImInfty` for the normalized
cusp form `Δ = CuspForm.discriminant` of weight `12` and level one. -/
theorem deltaFun_isBigO_exp_atImInfty :
    (fun τ : ℍ => Work.Kernels.DeltaFun τ) =O[atImInfty]
      (fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im)) := by
  have h := CuspFormClass.exp_decay_atImInfty (f := CuspForm.discriminant) (h := 1)
    one_pos one_mem_strictPeriods_SL
  simpa using h

/-- The explicit form of `deltaFun_isBigO_exp_atImInfty`. -/
theorem exists_bound_norm_deltaFun :
    ∃ C : ℝ, 0 < C ∧ ∃ A : ℝ, ∀ τ : ℍ, A ≤ τ.im →
      ‖Work.Kernels.DeltaFun τ‖ ≤ C * Real.exp (-2 * Real.pi * τ.im) := by
  obtain ⟨c, hc⟩ := isBigO_iff.mp deltaFun_isBigO_exp_atImInfty
  obtain ⟨A, -, hA⟩ := UpperHalfPlane.atImInfty_basis.eventually_iff.mp hc
  refine ⟨max c 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), A, fun τ hτ => ?_⟩
  have h1 := hA (by simpa using hτ : τ ∈ UpperHalfPlane.im ⁻¹' Set.Ici A)
  have h2 : ‖Real.exp (-2 * Real.pi * τ.im)‖ = Real.exp (-2 * Real.pi * τ.im) :=
    Real.norm_of_nonneg (Real.exp_pos _).le
  rw [h2] at h1
  exact le_trans h1 (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)

/-- `E₄` is eventually bounded away from `0` near the cusp `i∞`. -/
theorem exists_bound_norm_E4Fun_atImInfty :
    ∃ A : ℝ, ∀ τ : ℍ, A ≤ τ.im → (1 / 2 : ℝ) ≤ ‖Work.Kernels.E4Fun τ‖ := by
  have hE := Work.Modular.E4_tendsto_atImInfty.eventually
    (Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨A, -, hA⟩ := UpperHalfPlane.atImInfty_basis.eventually_iff.mp hE
  refine ⟨A, fun τ hτ => ?_⟩
  have h1 : Work.Kernels.E4Fun τ ∈ Metric.ball (1 : ℂ) (1 / 2) := hA (by simpa using hτ)
  rw [Metric.mem_ball, Complex.dist_eq] at h1
  have h2 : |‖Work.Kernels.E4Fun τ‖ - ‖(1 : ℂ)‖| ≤ ‖Work.Kernels.E4Fun τ - 1‖ :=
    abs_norm_sub_norm_le _ _
  rw [norm_one] at h2
  have h3 : |‖Work.Kernels.E4Fun τ‖ - 1| < 1 / 2 := lt_of_le_of_lt h2 h1
  rw [abs_lt] at h3
  linarith [h3.1]

/-- **The cusp asymptotics of the `j`-invariant on the imaginary axis.**  `j(it)` blows up at
least like `e^{2πt}` for `t ≥ T`.  Since `Δ(τ)j(τ) = E₄(τ)³` this controls the *off-diagonal*
part of the CKMRV divisor `Δ(τ)Δ(it)^e(j(τ) - j(it))` on the contour. -/
theorem jInvariantFun_imagAxis_atTop :
    ∃ c T : ℝ, 0 < c ∧ 0 < T ∧
      ∀ (t : ℝ) (ht : 0 < t), T ≤ t →
        c * Real.exp (2 * Real.pi * t) ≤ ‖Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ := by
  obtain ⟨C, hCpos, A, hA⟩ := exists_bound_norm_deltaFun
  obtain ⟨B, hB⟩ := exists_bound_norm_E4Fun_atImInfty
  refine ⟨1 / (8 * C), max A (max B 1), by positivity,
    lt_of_lt_of_le zero_lt_one (le_trans (le_max_right B 1) (le_max_right A (max B 1))), ?_⟩
  intro t ht hT
  have hAt : A ≤ t := le_trans (le_max_left _ _) hT
  have hBt : B ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hIm : (Work.Kernels.imagAxis t ht).im = t := by
    simp [Work.Kernels.imagAxis]
  have hD : ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖
      ≤ C * Real.exp (-2 * Real.pi * t) := by
    have h := hA (Work.Kernels.imagAxis t ht) (by rw [hIm]; exact hAt)
    rwa [hIm] at h
  have hE : (1 / 2 : ℝ) ≤ ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)‖ :=
    hB (Work.Kernels.imagAxis t ht) (by rw [hIm]; exact hBt)
  have hDpos : 0 < ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ :=
    norm_pos_iff.mpr (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero _)
  have hG : (1 / 8 : ℝ) ≤ ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)‖ ^ 3 := by
    have h := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 / 2 by norm_num) hE 3
    rw [show ((1 : ℝ) / 2) ^ 3 = 1 / 8 by norm_num] at h
    exact h
  have hInv : 1 / (C * Real.exp (-2 * Real.pi * t))
      ≤ 1 / ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ :=
    one_div_le_one_div_of_le hDpos hD
  have hkey : (1 / (8 * C)) * Real.exp (2 * Real.pi * t)
      = (1 / 8) * (1 / (C * Real.exp (-2 * Real.pi * t))) := by
    have h1 : Real.exp (-2 * Real.pi * t) = (Real.exp (2 * Real.pi * t))⁻¹ := by
      have h : -2 * Real.pi * t = -(2 * Real.pi * t) := by ring
      rw [h, Real.exp_neg]
    rw [h1]
    have hC' : C ≠ 0 := ne_of_gt hCpos
    have hE' : Real.exp (2 * Real.pi * t) ≠ 0 := Real.exp_ne_zero _
    field_simp
  calc (1 / (8 * C)) * Real.exp (2 * Real.pi * t)
      = (1 / 8) * (1 / (C * Real.exp (-2 * Real.pi * t))) := hkey
    _ ≤ (1 / 8) * (1 / ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖) :=
        mul_le_mul_of_nonneg_left hInv (by norm_num)
    _ ≤ ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)‖ ^ 3
          * (1 / ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖) :=
        mul_le_mul_of_nonneg_right hG (by positivity)
    _ = ‖Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ := by
        simp only [Work.Kernels.jInvariantFun]
        rw [norm_div, norm_pow, mul_one_div]

end Work.Asymptotics
