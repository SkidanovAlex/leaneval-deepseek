import Submission.Commons.Analysis.Calculus.smoothTransition_radial_iteratedFDeriv_bound


open scoped Topology ContDiff
namespace Commons.Analysis.Calculus

/-- Smoothness of the scaled radial transition function `y ↦ smoothTransition (c * ‖y‖ - 1)`
for `c > 0`.  It is the composition of `z ↦ smoothTransition (‖z‖ - 1)` with the continuous linear
map `y ↦ c • y`. -/
private lemma contDiff_smoothTransition_scaled_mul_norm {d : ℕ} {c : ℝ} (hc : 0 < c) :
    ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin d) =>
      Real.smoothTransition (c * ‖y‖ - 1)) := by
  have hrad : ContDiff ℝ ∞ (fun z : EuclideanSpace ℝ (Fin d) =>
      Real.smoothTransition (‖z‖ - 1)) := smoothTransition_radial_contDiff
  have hclm : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin d) => c • y) :=
    contDiff_const_smul c
  have h := hrad.comp hclm
  have hfun : (fun y : EuclideanSpace ℝ (Fin d) => Real.smoothTransition (c * ‖y‖ - 1))
      = (fun z : EuclideanSpace ℝ (Fin d) => Real.smoothTransition (‖z‖ - 1))
        ∘ (fun y : EuclideanSpace ℝ (Fin d) => c • y) := by
    funext y
    simp only [Function.comp_apply, norm_smul, Real.norm_of_nonneg hc.le]
  rw [hfun]
  exact h

/-- **Derivative bounds for the radial dyadic cutoff.**  For each `a` and each dimension `d` there
is `C > 0` such that for all `k : ℕ` and all `x : ℝᵈ`,

`‖D^a (y ↦ smoothTransition (‖y‖/2^k - 1) - smoothTransition (‖y‖/2^{k+1} - 1)) x‖ ≤ C (2^k)^{-a}`. -/
theorem radialPsi_iteratedFDeriv_bound (a : ℕ) (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (x : EuclideanSpace ℝ (Fin d)),
      ‖iteratedFDeriv ℝ a
        (fun y : EuclideanSpace ℝ (Fin d) =>
          Real.smoothTransition (‖y‖ / 2 ^ k - 1) - Real.smoothTransition (‖y‖ / 2 ^ (k + 1) - 1))
        x‖ ≤ C * (((2 : ℝ) ^ k)⁻¹) ^ a := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := smoothTransition_radial_iteratedFDeriv_bound a
  refine ⟨2 * C₀, by linarith, ?_⟩
  intro k x
  have h2k : (0 : ℝ) < 2 ^ k := pow_pos (by norm_num) k
  have h2k1 : (0 : ℝ) < 2 ^ (k + 1) := pow_pos (by norm_num) (k + 1)
  have hcle : ((2 : ℝ) ^ (k + 1))⁻¹ ≤ ((2 : ℝ) ^ k)⁻¹ := by
    refine inv_anti₀ h2k ?_
    calc (2 : ℝ) ^ k ≤ (2 : ℝ) ^ k * 2 := le_mul_of_one_le_right h2k.le (by norm_num)
      _ = (2 : ℝ) ^ (k + 1) := by rw [pow_succ]
  have hfun : (fun y : EuclideanSpace ℝ (Fin d) =>
        Real.smoothTransition (‖y‖ / 2 ^ k - 1) -
          Real.smoothTransition (‖y‖ / 2 ^ (k + 1) - 1))
      = (fun y : EuclideanSpace ℝ (Fin d) =>
          Real.smoothTransition (((2 : ℝ) ^ k)⁻¹ * ‖y‖ - 1))
        - (fun y : EuclideanSpace ℝ (Fin d) =>
          Real.smoothTransition (((2 : ℝ) ^ (k + 1))⁻¹ * ‖y‖ - 1)) := by
    funext y
    simp only [Pi.sub_apply]
    have e1 : ((2 : ℝ) ^ k)⁻¹ * ‖y‖ = ‖y‖ / 2 ^ k := by rw [div_eq_mul_inv, mul_comm]
    have e2 : ((2 : ℝ) ^ (k + 1))⁻¹ * ‖y‖ = ‖y‖ / 2 ^ (k + 1) := by
      rw [div_eq_mul_inv, mul_comm]
    rw [e1, e2]
  have hf : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin d) =>
      Real.smoothTransition (((2 : ℝ) ^ k)⁻¹ * ‖y‖ - 1)) :=
    contDiff_smoothTransition_scaled_mul_norm (inv_pos.2 h2k)
  have hg : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin d) =>
      Real.smoothTransition (((2 : ℝ) ^ (k + 1))⁻¹ * ‖y‖ - 1)) :=
    contDiff_smoothTransition_scaled_mul_norm (inv_pos.2 h2k1)
  rw [hfun,
    iteratedFDeriv_sub_apply (hf.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
      (hg.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt]
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖iteratedFDeriv ℝ a (fun y : EuclideanSpace ℝ (Fin d) =>
      Real.smoothTransition (((2 : ℝ) ^ k)⁻¹ * ‖y‖ - 1)) x‖
      ≤ C₀ * (((2 : ℝ) ^ k)⁻¹) ^ a := hC₀ d _ (inv_pos.2 h2k) x
  have h2 : ‖iteratedFDeriv ℝ a (fun y : EuclideanSpace ℝ (Fin d) =>
      Real.smoothTransition (((2 : ℝ) ^ (k + 1))⁻¹ * ‖y‖ - 1)) x‖
      ≤ C₀ * (((2 : ℝ) ^ k)⁻¹) ^ a :=
    (hC₀ d _ (inv_pos.2 h2k1) x).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (inv_pos.2 h2k1).le hcle a) hC₀pos.le)
  calc ‖iteratedFDeriv ℝ a (fun y : EuclideanSpace ℝ (Fin d) =>
          Real.smoothTransition (((2 : ℝ) ^ k)⁻¹ * ‖y‖ - 1)) x‖
        + ‖iteratedFDeriv ℝ a (fun y : EuclideanSpace ℝ (Fin d) =>
          Real.smoothTransition (((2 : ℝ) ^ (k + 1))⁻¹ * ‖y‖ - 1)) x‖
      ≤ C₀ * (((2 : ℝ) ^ k)⁻¹) ^ a + C₀ * (((2 : ℝ) ^ k)⁻¹) ^ a := add_le_add h1 h2
    _ = 2 * C₀ * (((2 : ℝ) ^ k)⁻¹) ^ a := by ring

end Commons.Analysis.Calculus
