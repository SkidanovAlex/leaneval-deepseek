import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.DKPlusQ1

/-!
# The `O(q²)` deviation bounds feeding `[dKPlus24]_{E²}`

The batch that turns the per-summand order estimates into
`dSm2 + 324·q·Φ_ref = O(q²)` (and hence `[dKPlus24]_{E²} = 324·c·z²·Φ_ref`).

* `dDq_bound`: `dDq = Δ(z)·q⁻¹ - (1 - 24q + 252q²) = O(q⁴)·q⁻¹ = O(q³)`, from the ℓ-free
  `DeltaFun_fourth_order` — the `q⁻¹` of the reference being supplied by the explicit `q` of
  `Δ`'s own truncation.
* `dE4c_bound`: `dE4c = dE4·(E4Fun² + E4Fun·E4Ref + E4Ref²) = O(q³)`, from the proved
  `dE4_bound` and the elementary bounds `‖E4Ref‖ ≤ 2401`, `‖E4Fun‖ ≤ 2401 + C` on `‖q‖ ≤ 1`.
-/

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

/-- **`dDq = O(q³)`** (i.e. `O(‖Ept z‖⁶)`). -/
lemma dDq_bound : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
    ‖dDq z‖ ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.DeltaFun_fourth_order
  refine ⟨C, hC, fun z hz => ?_⟩
  have hqz : Work.Kernels.qParamFun z ≠ 0 := Work.Asymptotics.qParamFun_ne_zero' z
  have hq0 : (0 : ℝ) < ‖Work.Kernels.qParamFun z‖ := norm_pos_iff.mpr hqz
  have hkey : dDq z
      = (Work.Kernels.DeltaFun z - (Work.Kernels.qParamFun z
          - 24 * (Work.Kernels.qParamFun z) ^ 2
          + 252 * (Work.Kernels.qParamFun z) ^ 3))
        * (Work.Kernels.qParamFun z)⁻¹ := by
    simp only [dDq, DqRef]
    field_simp
  rw [hkey, norm_mul, norm_inv]
  have hb := h z hz
  calc ‖Work.Kernels.DeltaFun z - (Work.Kernels.qParamFun z
          - 24 * (Work.Kernels.qParamFun z) ^ 2
          + 252 * (Work.Kernels.qParamFun z) ^ 3)‖
        * (‖Work.Kernels.qParamFun z‖)⁻¹
      ≤ (C * ‖Work.Kernels.qParamFun z‖ ^ 4) * (‖Work.Kernels.qParamFun z‖)⁻¹ :=
        mul_le_mul_of_nonneg_right hb (inv_nonneg.mpr hq0.le)
    _ = C * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
        field_simp

/-- **`dDelta = O(q⁴)`** (i.e. `O(‖Ept z‖⁸)`), straight from the ℓ-free
`DeltaFun_fourth_order`.  This is the bound needed for `dSm5 = -(dDelta·j(τ))·Θ₀`. -/
lemma dDelta_bound : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
    ‖dDelta z‖ ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 4 := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.DeltaFun_fourth_order
  refine ⟨C, hC, fun z hz => ?_⟩
  have hkey : dDelta z = Work.Kernels.DeltaFun z - (Work.Kernels.qParamFun z
      - 24 * (Work.Kernels.qParamFun z) ^ 2
      + 252 * (Work.Kernels.qParamFun z) ^ 3) := by
    simp only [dDelta, DeltaRef, DqRef]
    ring
  rw [hkey]
  exact h z hz

/-- **`j(τ)²·Δ(τ) = E₄(τ)³·j(τ)`** — the identity that keeps the `j(τ)²`-terms in
`j(τ)·Θ₀` at order `‖q(τ)‖⁻¹` rather than `‖q(τ)‖⁻²`.  It is the reason the `r₁`-multiples
(`r₁ = φ₁·Δ`) absorb one power of `j` in every product `j(τ)·(j(τ)-multiple of r₁)`, and hence
why `dSm5 = -(dDelta·j(τ))·Θ₀` is `O(q³ scale^N)` rather than `O(q² scale^N)` after the
`‖q(τ)‖⁻¹` from `j(τ)`. -/
lemma j_sq_mul_Delta (τ : ℍ) :
    Work.Kernels.jInvariantFun τ ^ 2 * Work.Kernels.DeltaFun τ
      = (Work.Kernels.E4Fun τ) ^ 3 * Work.Kernels.jInvariantFun τ := by
  have hD : Work.Kernels.DeltaFun τ ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ
  have hj : Work.Kernels.jInvariantFun τ
      = (Work.Kernels.E4Fun τ) ^ 3 / Work.Kernels.DeltaFun τ := rfl
  rw [hj]
  field_simp

/-- The elementary bound `‖E4Ref z‖ ≤ 2401` on `{1 ≤ Im z}`. -/
lemma norm_E4Ref_le {z : ℍ} (hz : 1 ≤ z.im) : ‖E4Ref z‖ ≤ 2401 := by
  have hqle : ‖Work.Kernels.qParamFun z‖ ≤ 1 := by
    rw [Work.Asymptotics.norm_qParamFun]
    rw [Real.exp_le_one_iff]
    nlinarith [Real.pi_pos, hz]
  have hqnn : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
  have h1 : ‖E4Ref z‖ ≤ 1 + 240 * ‖Work.Kernels.qParamFun z‖
      + 2160 * ‖Work.Kernels.qParamFun z‖ ^ 2 := by
    have a := norm_add_le ((1 : ℂ) + 240 * Work.Kernels.qParamFun z)
      ((2160 : ℂ) * (Work.Kernels.qParamFun z) ^ 2)
    have b := norm_add_le (1 : ℂ) ((240 : ℂ) * Work.Kernels.qParamFun z)
    simp only [E4Ref, norm_mul, norm_one, norm_pow, Complex.norm_ofNat] at a b ⊢
    linarith
  have h2 : 240 * ‖Work.Kernels.qParamFun z‖ ≤ 240 := by nlinarith [hqle, hqnn]
  have h3 : 2160 * ‖Work.Kernels.qParamFun z‖ ^ 2 ≤ 2160 := by nlinarith [hqle, hqnn]
  linarith

/-- **`dE4c = O(q³)`** (i.e. `O(‖Ept z‖⁶)`). -/
lemma dE4c_bound : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
    ‖dE4c z‖ ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
  obtain ⟨C, hC, h⟩ := dE4_bound
  refine ⟨C * ((2401 + C) ^ 2 + (2401 + C) * 2401 + 2401 ^ 2) + 1, by positivity,
    fun z hz => ?_⟩
  have hqle : ‖Work.Kernels.qParamFun z‖ ≤ 1 := by
    rw [Work.Asymptotics.norm_qParamFun]
    rw [Real.exp_le_one_iff]
    nlinarith [Real.pi_pos, hz]
  have hqnn : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
  have hq3 : ‖Work.Kernels.qParamFun z‖ ^ 3 ≤ 1 := by
    have := pow_le_one₀ hqnn hqle (n := 3); simpa using this
  have hR : ‖E4Ref z‖ ≤ 2401 := norm_E4Ref_le hz
  have hd := h z hz
  have hE4 : ‖Work.Kernels.E4Fun z‖ ≤ 2401 + C := by
    have heq : Work.Kernels.E4Fun z = E4Ref z + dE4 z := E4Fun_ref_split z
    have h2 : C * ‖Work.Kernels.qParamFun z‖ ^ 3 ≤ C := by nlinarith [hq3, hC.le]
    have h3 := norm_add_le (E4Ref z) (dE4 z)
    rw [heq]
    linarith [h3, hR, hd, h2]
  have hcof : ‖Work.Kernels.E4Fun z ^ 2 + Work.Kernels.E4Fun z * E4Ref z + E4Ref z ^ 2‖
      ≤ (2401 + C) ^ 2 + (2401 + C) * 2401 + 2401 ^ 2 := by
    have e1 := norm_add_le (Work.Kernels.E4Fun z ^ 2 + Work.Kernels.E4Fun z * E4Ref z)
      (E4Ref z ^ 2)
    have e2 := norm_add_le (Work.Kernels.E4Fun z ^ 2) (Work.Kernels.E4Fun z * E4Ref z)
    have e3 : ‖Work.Kernels.E4Fun z ^ 2‖ = ‖Work.Kernels.E4Fun z‖ ^ 2 := norm_pow _ _
    have e4 : ‖Work.Kernels.E4Fun z * E4Ref z‖
        = ‖Work.Kernels.E4Fun z‖ * ‖E4Ref z‖ := norm_mul _ _
    have e5 : ‖E4Ref z ^ 2‖ = ‖E4Ref z‖ ^ 2 := norm_pow _ _
    rw [e5] at e1
    rw [e3, e4] at e2
    have hnn2 : (0 : ℝ) ≤ ‖E4Ref z‖ := norm_nonneg _
    nlinarith [e1, e2, hE4, hR, hC.le, norm_nonneg (Work.Kernels.E4Fun z)]
  have hpos : (0 : ℝ) ≤ (2401 + C) ^ 2 + (2401 + C) * 2401 + 2401 ^ 2 := by positivity
  rw [dE4c, norm_mul]
  calc ‖dE4 z‖ * ‖Work.Kernels.E4Fun z ^ 2 + Work.Kernels.E4Fun z * E4Ref z
          + E4Ref z ^ 2‖
      ≤ (C * ‖Work.Kernels.qParamFun z‖ ^ 3)
          * ((2401 + C) ^ 2 + (2401 + C) * 2401 + 2401 ^ 2) :=
        mul_le_mul hd hcof (norm_nonneg _) (by positivity)
    _ = (C * ((2401 + C) ^ 2 + (2401 + C) * 2401 + 2401 ^ 2))
          * ‖Work.Kernels.qParamFun z‖ ^ 3 := by ring
    _ ≤ (C * ((2401 + C) ^ 2 + (2401 + C) * 2401 + 2401 ^ 2) + 1)
          * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
        have h0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ ^ 3 := by positivity
        nlinarith [h0]

end

end Work.Asymptotics.KhatE1Core
