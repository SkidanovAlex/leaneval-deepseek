import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Submission.Commons.Probability.Gaussian.integral_norm_sq_starProjection_stdGaussian
import Submission.Commons.Probability.Gaussian.fourth_moment_gaussianReal

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ENNReal

namespace Commons.Probability.Gaussian

/-- **Fourth moment bound for a standard Gaussian vector.**  For a finite-dimensional real inner
product space `E` of dimension `d`, the standard Gaussian measure satisfies
`∫ ‖x‖ ^ 4 ∂(stdGaussian E) ≤ 3 * d ^ 2`.

The proof expands `‖x‖ ^ 4 = (∑ i, ⟪b i, x⟫²)²` in an orthonormal basis `b` and applies
Cauchy–Schwarz in the form `(∑ a i)² ≤ d * ∑ (a i)²` to the nonnegative numbers
`a i = ⟪b i, x⟫²`; each fourth moment of a coordinate is `3`. -/
theorem integral_norm_pow_four_stdGaussian_le_finrank
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] :
    (∫ x, ‖x‖ ^ 4 ∂(ProbabilityTheory.stdGaussian E))
      ≤ 3 * (Module.finrank ℝ E : ℝ) ^ 2 := by
  classical
  have h4int : Integrable (fun x : E => ‖x‖ ^ 4) (ProbabilityTheory.stdGaussian E) := by
    have h := (IsGaussian.memLp_id (ProbabilityTheory.stdGaussian E) (4 : ℝ≥0∞)
      (by norm_num)).integrable_norm_rpow (by norm_num) (by norm_num)
    simpa using h
  have hcoord : ∀ i : Fin (Module.finrank ℝ E),
      ∫ x : E, (⟪(stdOrthonormalBasis ℝ E) i, x⟫_ℝ) ^ 4
        ∂(ProbabilityTheory.stdGaussian E) = 3 := by
    intro i
    have hlaw : (ProbabilityTheory.stdGaussian E).map
        (innerSL ℝ ((stdOrthonormalBasis ℝ E) i))
        = ProbabilityTheory.gaussianReal 0 1 := by
      rw [IsGaussian.map_eq_gaussianReal
        (L := innerSL ℝ ((stdOrthonormalBasis ℝ E) i))]
      rw [integral_strongDual_stdGaussian, variance_dual_stdGaussian]
      have hn : ‖innerSL ℝ ((stdOrthonormalBasis ℝ E) i)‖ = 1 := by
        rw [innerSL_apply_norm, OrthonormalBasis.norm_eq_one]
      rw [hn]
      simp
    have hkey : ∫ t, t ^ 4 ∂((ProbabilityTheory.stdGaussian E).map
          (innerSL ℝ ((stdOrthonormalBasis ℝ E) i)))
        = ∫ x, (⟪(stdOrthonormalBasis ℝ E) i, x⟫_ℝ) ^ 4
            ∂(ProbabilityTheory.stdGaussian E) := by
      rw [integral_map (by fun_prop) (by fun_prop)]
      simp only [innerSL_apply_apply]
    rw [← hkey, hlaw]
    exact fourth_moment_gaussianReal
  have hpt : ∀ x : E, ‖x‖ ^ 4 ≤ (Module.finrank ℝ E : ℝ) *
      ∑ i, (⟪(stdOrthonormalBasis ℝ E) i, x⟫_ℝ) ^ 4 := by
    intro x
    have hcs : (∑ i, (⟪(stdOrthonormalBasis ℝ E) i, x⟫_ℝ) ^ 2) ^ 2
        ≤ (Module.finrank ℝ E : ℝ) *
          ∑ i, ((⟪(stdOrthonormalBasis ℝ E) i, x⟫_ℝ) ^ 2) ^ 2 := by
      simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ)
        (f := fun i : Fin (Module.finrank ℝ E) =>
          (⟪(stdOrthonormalBasis ℝ E) i, x⟫_ℝ) ^ 2)
    have hsum : (∑ i, ((⟪(stdOrthonormalBasis ℝ E) i, x⟫_ℝ) ^ 2) ^ 2)
        = ∑ i, (⟪(stdOrthonormalBasis ℝ E) i, x⟫_ℝ) ^ 4 := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [← pow_mul]
    calc ‖x‖ ^ 4
          = (∑ i, (⟪(stdOrthonormalBasis ℝ E) i, x⟫_ℝ) ^ 2) ^ 2 := by
            rw [(stdOrthonormalBasis ℝ E).sum_sq_inner_right]; ring
      _ ≤ _ := hcs
      _ = (Module.finrank ℝ E : ℝ) *
          ∑ i, (⟪(stdOrthonormalBasis ℝ E) i, x⟫_ℝ) ^ 4 := by rw [hsum]
  have hint_i : ∀ i : Fin (Module.finrank ℝ E),
      Integrable (fun x : E => (⟪(stdOrthonormalBasis ℝ E) i, x⟫_ℝ) ^ 4)
        (ProbabilityTheory.stdGaussian E) := by
    intro i
    have h : MemLp (innerSL ℝ ((stdOrthonormalBasis ℝ E) i)) (4 : ℝ≥0∞)
        (ProbabilityTheory.stdGaussian E) := IsGaussian.memLp_dual _ _ 4 (by norm_num)
    have h2' := h.integrable_norm_rpow (by norm_num) (by norm_num)
    simp only [ENNReal.toReal_ofNat] at h2'
    have habs : ∀ a : ℝ, |a| ^ 4 = a ^ 4 := by
      intro a
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]
    simpa [innerSL_apply_apply, Real.norm_eq_abs, habs] using h2'
  have hint_sum : Integrable (fun x : E => (Module.finrank ℝ E : ℝ) *
      ∑ i, (⟪(stdOrthonormalBasis ℝ E) i, x⟫_ℝ) ^ 4)
      (ProbabilityTheory.stdGaussian E) := by
    have hs : Integrable (fun x : E =>
        ∑ i, (⟪(stdOrthonormalBasis ℝ E) i, x⟫_ℝ) ^ 4)
        (ProbabilityTheory.stdGaussian E) :=
      integrable_finsetSum Finset.univ (fun i _ => hint_i i)
    exact hs.const_mul _
  calc (∫ x, ‖x‖ ^ 4 ∂(ProbabilityTheory.stdGaussian E))
      ≤ ∫ x, (Module.finrank ℝ E : ℝ) *
          ∑ i, (⟪(stdOrthonormalBasis ℝ E) i, x⟫_ℝ) ^ 4
          ∂(ProbabilityTheory.stdGaussian E) := integral_mono h4int hint_sum hpt
    _ = (Module.finrank ℝ E : ℝ) *
          ∫ x, ∑ i, (⟪(stdOrthonormalBasis ℝ E) i, x⟫_ℝ) ^ 4
            ∂(ProbabilityTheory.stdGaussian E) := by rw [integral_const_mul]
    _ = (Module.finrank ℝ E : ℝ) *
          ∑ i, ∫ x, (⟪(stdOrthonormalBasis ℝ E) i, x⟫_ℝ) ^ 4
            ∂(ProbabilityTheory.stdGaussian E) := by
          rw [integral_finsetSum]
          intro i _
          exact hint_i i
    _ = (Module.finrank ℝ E : ℝ) * ∑ _i : Fin (Module.finrank ℝ E), (3 : ℝ) := by
          rw [Finset.sum_congr rfl (fun i _ => hcoord i)]
    _ = 3 * (Module.finrank ℝ E : ℝ) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring

theorem integral_norm_pow_four_stdGaussian_le {ι : Type*} [Fintype ι] :
    (∫ x, ‖x‖ ^ 4 ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)))
      ≤ 3 * (Fintype.card ι : ℝ) ^ 2 * (Fintype.card ι : ℝ) ^ 2 := by
  have h := integral_norm_pow_four_stdGaussian_le_finrank (E := EuclideanSpace ℝ ι)
  rw [finrank_euclideanSpace] at h
  refine h.trans ?_
  by_cases hn : Fintype.card ι = 0
  · simp [hn]
  · have hc1 : 1 ≤ (Fintype.card ι : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hc2 : 1 ≤ (Fintype.card ι : ℝ) ^ 2 := by nlinarith
    have : 3 * (Fintype.card ι : ℝ) ^ 2 * 1
        ≤ 3 * (Fintype.card ι : ℝ) ^ 2 * (Fintype.card ι : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hc2 (by positivity)
    simpa using this

end Commons.Probability.Gaussian