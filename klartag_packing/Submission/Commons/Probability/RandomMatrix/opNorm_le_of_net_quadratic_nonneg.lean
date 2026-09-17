import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Submission.Commons.Probability.RandomMatrix.spectral_norm_bounded_entries

namespace Commons.Probability.RandomMatrix

open scoped RealInnerProductSpace

noncomputable section

/-- Cauchy–Schwarz together with `‖T x‖ ≤ ‖T‖ ‖x‖`: the bilinear form of `T` is bounded by
`‖T‖ ‖x‖ ‖y‖`. -/
private lemma abs_inner_opNorm_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E) (x y : E) : |inner ℝ (T x) y| ≤ ‖T‖ * ‖x‖ * ‖y‖ := by
  have h1 : |inner ℝ (T x) y| ≤ ‖T x‖ * ‖y‖ := by
    simpa [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) (T x) y
  calc |inner ℝ (T x) y| ≤ ‖T x‖ * ‖y‖ := h1
    _ ≤ (‖T‖ * ‖x‖) * ‖y‖ := by
        gcongr
        exact ContinuousLinearMap.le_opNorm T x
    _ = ‖T‖ * ‖x‖ * ‖y‖ := by ring

/-- A quadratic-form bound on a `δ`-net of the unit sphere controls the operator norm of a
symmetric operator: if `|⟪T x, x⟫| ≤ θ` for every `x` in a `δ`-net `S` of the unit sphere, then
`‖T‖ ≤ θ / (1 - 2δ)`.  (This is the "Vershynin-style" net argument; `0 ≤ θ` is needed to rule
out the degenerate case of the trivial inner product space, where the hypotheses on `S` are
vacuous.) -/
theorem opNorm_le_of_net_quadratic_nonneg {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E) (hTsym : ∀ x y : E, inner ℝ (T x) y = inner ℝ x (T y))
    {δ θ : ℝ} (hδ0 : 0 ≤ δ) (h2δ : 2 * δ < 1) (hθ : 0 ≤ θ) (S : Finset E)
    (hSunit : ∀ x ∈ S, ‖x‖ = 1)
    (hcover : ∀ y : E, ‖y‖ = 1 → ∃ x ∈ S, ‖y - x‖ ≤ δ)
    (hnet : ∀ x ∈ S, |inner ℝ (T x) x| ≤ θ) :
    ‖T‖ ≤ θ / (1 - 2 * δ) := by
  classical
  have hγ : 0 < 1 - 2 * δ := by linarith
  have hC : 0 ≤ θ + 2 * δ * ‖T‖ := by positivity
  -- Step 1: the quadratic form is bounded by `θ + 2δ‖T‖` on the whole unit sphere.
  have hdiag : ∀ z : E, ‖z‖ = 1 → |inner ℝ (T z) z| ≤ θ + 2 * δ * ‖T‖ := by
    intro z hz
    rcases hcover z hz with ⟨u, huS, hzu⟩
    have hu1 : ‖u‖ = 1 := hSunit u huS
    have hident : inner ℝ (T z) z
        = inner ℝ (T u) u + inner ℝ (T u) (z - u) + inner ℝ (T (z - u)) z := by
      calc inner ℝ (T z) z = inner ℝ (T (u + (z - u))) z := by
              rw [show u + (z - u) = z by abel]
        _ = inner ℝ (T u + T (z - u)) z := by rw [map_add]
        _ = inner ℝ (T u) z + inner ℝ (T (z - u)) z := by rw [inner_add_left]
        _ = inner ℝ (T u) (u + (z - u)) + inner ℝ (T (z - u)) z := by
              rw [show u + (z - u) = z by abel]
        _ = (inner ℝ (T u) u + inner ℝ (T u) (z - u)) + inner ℝ (T (z - u)) z := by
              rw [inner_add_right]
        _ = inner ℝ (T u) u + inner ℝ (T u) (z - u) + inner ℝ (T (z - u)) z := by ring
    have h2 : |inner ℝ (T u) (z - u)| ≤ ‖T‖ * δ := by
      have h := abs_inner_opNorm_le T u (z - u)
      have hb : ‖T‖ * ‖u‖ * ‖z - u‖ ≤ ‖T‖ * 1 * δ := by
        rw [hu1]
        nlinarith [mul_le_mul_of_nonneg_left hzu (norm_nonneg T)]
      linarith [h.trans hb]
    have h3 : |inner ℝ (T (z - u)) z| ≤ ‖T‖ * δ := by
      have h := abs_inner_opNorm_le T (z - u) z
      have hb : ‖T‖ * ‖z - u‖ * ‖z‖ ≤ ‖T‖ * δ * 1 := by
        rw [hz]
        nlinarith [mul_le_mul_of_nonneg_left hzu (norm_nonneg T)]
      linarith [h.trans hb]
    calc |inner ℝ (T z) z|
        ≤ |inner ℝ (T u) u| + |inner ℝ (T u) (z - u)| + |inner ℝ (T (z - u)) z| := by
          rw [hident]
          refine (abs_add_le _ _).trans ?_
          exact add_le_add (abs_add_le _ _) le_rfl
      _ ≤ θ + ‖T‖ * δ + ‖T‖ * δ := by
          exact add_le_add (add_le_add (hnet u huS) h2) h3
      _ = θ + 2 * δ * ‖T‖ := by ring
  -- Step 2: hence every Rayleigh quotient of `T` is bounded by `θ + 2δ‖T‖`.
  have hray : ∀ x : E, |T.rayleighQuotient x| ≤ θ + 2 * δ * ‖T‖ := by
    intro x
    by_cases hx : x = 0
    · rw [hx, ContinuousLinearMap.rayleighQuotient_apply_zero, abs_zero]
      exact hC
    · have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      have hz1 : ‖(‖x‖)⁻¹ • x‖ = 1 := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
        exact inv_mul_cancel₀ hxn
      have hsmul : T.rayleighQuotient ((‖x‖)⁻¹ • x) = T.rayleighQuotient x :=
        ContinuousLinearMap.rayleigh_smul T x (by simp [hxn])
      have hval : T.rayleighQuotient ((‖x‖)⁻¹ • x)
          = inner ℝ (T ((‖x‖)⁻¹ • x)) ((‖x‖)⁻¹ • x) := by
        simp [ContinuousLinearMap.rayleighQuotient,
          ContinuousLinearMap.reApplyInnerSelf_apply, hz1]
      rw [← hsmul, hval]
      exact hdiag _ hz1
  -- Step 3: `‖T‖` is the supremum of the absolute values of the Rayleigh quotients.
  have hsym : (T : E →ₗ[ℝ] E).IsSymmetric := hTsym
  have hsup : ‖T‖ = ⨆ x, |T.rayleighQuotient x| :=
    ContinuousLinearMap.norm_eq_iSup_rayleighQuotient T hsym
  have hle : ‖T‖ ≤ θ + 2 * δ * ‖T‖ := by
    calc ‖T‖ = ⨆ x, |T.rayleighQuotient x| := hsup
      _ ≤ θ + 2 * δ * ‖T‖ := ciSup_le hray
  -- Step 4: rearrange.
  rw [le_div_iff₀ hγ]
  linarith

end

end Commons.Probability.RandomMatrix