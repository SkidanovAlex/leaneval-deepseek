import Mathlib
import Submission.Work.KMTPlan.A6.MdlTleKer
import Submission.Work.KMTAreas.A7.KmtKernelL1Uniform

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-! ## The `ℓ¹ ∗ ℓ² → ℓ^∞` bound for a kernel with quadratic decay

The elementary engine of the target below: if a kernel `κ` is dominated by the comparison weight
`kmtKernWeight j = (1 + |j|)^{-2}` (up to the constant `C₀`), then `κ` is in `ℓ¹`, hence
convolution with `κ` maps `ℓ²` to `ℓ^∞` with norm at most `‖κ‖_{ℓ¹}` (the `ℓ²`-element bound
`|F z| ≤ ‖F‖_{ℓ²}` is used, and `‖κ‖_{ℓ¹} ≤ C₀ ∑_j ‖kmtKernWeight j‖`). -/

/-- **A convolution with a kernel of quadratic decay maps `ℓ²` to `ℓ^∞`.** -/
theorem norm_tsum_mul_le_of_kernWeight {κ F : ℤ → ℂ} {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hκ : ∀ i : ℤ, ‖κ i‖ ≤ C₀ * ‖Work.KMTAreas.A7.kmtKernWeight i‖)
    (hF : Summable fun i : ℤ => ‖F i‖ ^ 2) (y : ℤ) :
    ‖∑' i : ℤ, κ i * F (y - i)‖
      ≤ (∑' i : ℤ, C₀ * ‖Work.KMTAreas.A7.kmtKernWeight i‖)
          * Real.sqrt (∑' i : ℤ, ‖F i‖ ^ 2) := by
  have hKw : Summable (fun i : ℤ => C₀ * ‖Work.KMTAreas.A7.kmtKernWeight i‖) :=
    Work.KMTAreas.A7.summable_kmtKernWeight.mul_left C₀
  have hκsum : Summable (fun i : ℤ => ‖κ i‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hκ hKw
  have hFbound : ∀ z : ℤ, ‖F z‖ ≤ Real.sqrt (∑' i : ℤ, ‖F i‖ ^ 2) := by
    intro z
    refine (Real.le_sqrt (norm_nonneg _) (tsum_nonneg (fun i => by positivity))).mpr ?_
    exact hF.le_tsum z (fun i _ => by positivity)
  have hprod : Summable (fun i : ℤ => ‖κ i‖ * ‖F (y - i)‖) :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun i => mul_le_mul_of_nonneg_left (hFbound (y - i)) (norm_nonneg _))
      (hκsum.mul_right (Real.sqrt (∑' i : ℤ, ‖F i‖ ^ 2)))
  have hsum : Summable (fun i : ℤ => κ i * F (y - i)) :=
    Summable.of_norm_bounded (hκsum.mul_right (Real.sqrt (∑' i : ℤ, ‖F i‖ ^ 2)))
      (fun i => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hFbound (y - i)) (norm_nonneg _))
  calc ‖∑' i : ℤ, κ i * F (y - i)‖
      ≤ ∑' i : ℤ, ‖κ i * F (y - i)‖ := norm_tsum_le_tsum_norm hsum.norm
    _ = ∑' i : ℤ, ‖κ i‖ * ‖F (y - i)‖ := tsum_congr (fun i => norm_mul _ _)
    _ ≤ ∑' i : ℤ,
          (C₀ * ‖Work.KMTAreas.A7.kmtKernWeight i‖) * Real.sqrt (∑' i : ℤ, ‖F i‖ ^ 2) :=
        Summable.tsum_le_tsum
          (fun i => mul_le_mul (hκ i) (hFbound (y - i)) (norm_nonneg _)
            (mul_nonneg hC₀ (norm_nonneg _)))
          hprod (hKw.mul_right _)
    _ = (∑' i : ℤ, C₀ * ‖Work.KMTAreas.A7.kmtKernWeight i‖)
          * Real.sqrt (∑' i : ℤ, ‖F i‖ ^ 2) := tsum_mul_right

/-- **`T^{≤l}_{φ_t}` maps `ℓ²` to `ℓ^∞`, uniformly in `t ∈ [1/2,1]`.**  If the kernel of the
Ionescu--Wainger multiplier `T^{≤l}_{φ_t}` (i.e. the Fourier coefficients of the symbol
`∑_{α ∈ (ℚ/ℤ)_{≤l}} (periodize (φ t))(· - α)`) is dominated, uniformly in `t`, by the quadratic
comparison weight `kmtKernWeight i = (1 + |i|)^{-2}`, then for every `ℓ²` sequence `F` the values
`T^{≤l}_{φ_t} F y` are bounded by a constant independent of `t` and `y`. -/
theorem Tle_bump_l2_bounded (ρ : ℝ) (l : ℕ) {φ : ℝ → ℝ → ℂ} {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hdec : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ i : ℤ,
      ‖Work.KMTPlan.A6.TleKer ρ l (φ t) i‖ ≤ C₀ * ‖Work.KMTAreas.A7.kmtKernWeight i‖)
    {F : ℤ → ℂ} (hF : MeasureTheory.MemLp F 2 MeasureTheory.Measure.count) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ y : ℤ,
      ‖Work.KMTAreas.A7.Tle ρ l (φ t) F y‖ ≤ C := by
  classical
  -- `F ∈ ℓ²` gives summability of `∑ ‖F i‖²`, hence the `ℓ^∞` bound `‖F z‖ ≤ ‖F‖_{ℓ²}`.
  have hmem : Memℓp F (2 : ℝ≥0∞) := memlpOfMemLpCount (by norm_num) (by norm_num) hF
  have hFsum : Summable (fun i : ℤ => ‖F i‖ ^ 2) := by
    have h := (memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)).mp hmem
    simpa using h
  refine ⟨(∑' i : ℤ, C₀ * ‖Work.KMTAreas.A7.kmtKernWeight i‖)
      * Real.sqrt (∑' i : ℤ, ‖F i‖ ^ 2), ?_⟩
  intro t ht y
  exact norm_tsum_mul_le_of_kernWeight hC₀ (fun i => hdec t ht i) hFsum y

end Work.KMTPlan.A6
