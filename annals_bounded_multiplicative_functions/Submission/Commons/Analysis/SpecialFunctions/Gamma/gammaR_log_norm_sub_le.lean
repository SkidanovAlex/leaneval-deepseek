import Mathlib
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_mid_strip_le
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gammaR_vertical_poly_lower

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Complex
open scoped Real
set_option autoImplicit false
noncomputable section

namespace Commons.Analysis.SpecialFunctions.Gamma

/-- **Derivative of the log-modulus of `Γ` along a vertical line.**
For `u > 0` and any real `v`,
`d/du log ‖Γ(u + i v)‖ = Re ψ(u + i v)`.

The proof avoids any branch of the logarithm: writing `log ‖w‖ = (1/2) log (‖w‖²)`
(valid for *all* `w ∈ ℂ` because Mathlib's `Real.log` is even and `log 0 = 0`), the
squared modulus `u ↦ ‖Γ(u + i v)‖²` has derivative `2 ⟪Γ, Γ'⟫` (`HasDerivAt.norm_sq`),
and `⟪Γ, Γ'⟫ = Re(ψ · ‖Γ‖²)` because `Γ' = ψ · Γ` and `Γ · conj Γ = ‖Γ‖²`. -/
lemma hasDerivAt_log_norm_Gamma (u v : ℝ) (hu : 0 < u) :
    HasDerivAt (fun x : ℝ => Real.log ‖Complex.Gamma ((x : ℂ) + (v : ℂ) * I)‖)
      (Complex.digamma ((u : ℂ) + (v : ℂ) * I)).re u := by
  have hne : ∀ m : ℕ, ((u : ℂ) + (v : ℂ) * I) ≠ -↑(m : ℂ) := by
    intro m hm
    have hre := congrArg Complex.re hm
    rw [Complex.add_re, Complex.mul_re] at hre
    simp at hre
    have : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
    linarith
  have hΓne : Complex.Gamma ((u : ℂ) + (v : ℂ) * I) ≠ 0 := Complex.Gamma_ne_zero hne
  have hG0 : deriv Complex.Gamma ((u : ℂ) + (v : ℂ) * I) =
      Complex.digamma ((u : ℂ) + (v : ℂ) * I) * Complex.Gamma ((u : ℂ) + (v : ℂ) * I) := by
    rw [Complex.digamma_def, logDeriv_apply]
    field_simp [hΓne]
  have hs : HasDerivAt (fun x : ℝ => ‖Complex.Gamma ((x : ℂ) + (v : ℂ) * I)‖ ^ 2)
      (2 * inner ℝ (Complex.Gamma ((u : ℂ) + (v : ℂ) * I))
        (deriv Complex.Gamma ((u : ℂ) + (v : ℂ) * I))) u := by
    apply HasDerivAt.norm_sq
    have hc : HasDerivAt (fun x : ℝ => (x : ℂ) + (v : ℂ) * I) 1 u := by
      simpa using ((hasDerivAt_id u).ofReal_comp).add_const ((v : ℂ) * I)
    have hG : HasDerivAt Complex.Gamma (deriv Complex.Gamma ((u : ℂ) + (v : ℂ) * I))
        ((u : ℂ) + (v : ℂ) * I) :=
      (Complex.differentiableAt_Gamma _ hne).hasDerivAt
    have := hG.comp u hc
    simpa [Function.comp_def] using this
  have hmc : Complex.Gamma ((u : ℂ) + (v : ℂ) * I)
      * (starRingEnd ℂ) (Complex.Gamma ((u : ℂ) + (v : ℂ) * I))
      = ↑(‖Complex.Gamma ((u : ℂ) + (v : ℂ) * I)‖ ^ 2) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hval : 2 * inner ℝ (Complex.Gamma ((u : ℂ) + (v : ℂ) * I))
        (deriv Complex.Gamma ((u : ℂ) + (v : ℂ) * I))
      = 2 * ((Complex.digamma ((u : ℂ) + (v : ℂ) * I)).re
        * ‖Complex.Gamma ((u : ℂ) + (v : ℂ) * I)‖ ^ 2) := by
    rw [hG0, Complex.inner]
    rw [show Complex.digamma ((u : ℂ) + (v : ℂ) * I) * Complex.Gamma ((u : ℂ) + (v : ℂ) * I)
          * (starRingEnd ℂ) (Complex.Gamma ((u : ℂ) + (v : ℂ) * I))
        = Complex.digamma ((u : ℂ) + (v : ℂ) * I)
          * (Complex.Gamma ((u : ℂ) + (v : ℂ) * I)
            * (starRingEnd ℂ) (Complex.Gamma ((u : ℂ) + (v : ℂ) * I))) by ring]
    rw [hmc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hval] at hs
  have hnorm2ne : ‖Complex.Gamma ((u : ℂ) + (v : ℂ) * I)‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr hΓne)
  have hlog := hs.log hnorm2ne
  have hhalf : HasDerivAt
      (fun x : ℝ => (1 / 2) * Real.log (‖Complex.Gamma ((x : ℂ) + (v : ℂ) * I)‖ ^ 2))
      ((1 / 2) * ((2 * ((Complex.digamma ((u : ℂ) + (v : ℂ) * I)).re
        * ‖Complex.Gamma ((u : ℂ) + (v : ℂ) * I)‖ ^ 2))
        / ‖Complex.Gamma ((u : ℂ) + (v : ℂ) * I)‖ ^ 2)) u :=
    hlog.const_mul (1 / 2)
  have hsimp : (1 / 2 : ℝ) *
        ((2 * ((Complex.digamma ((u : ℂ) + (v : ℂ) * I)).re
          * ‖Complex.Gamma ((u : ℂ) + (v : ℂ) * I)‖ ^ 2))
          / ‖Complex.Gamma ((u : ℂ) + (v : ℂ) * I)‖ ^ 2)
      = (Complex.digamma ((u : ℂ) + (v : ℂ) * I)).re := by
    have hnn : ‖Complex.Gamma ((u : ℂ) + (v : ℂ) * I)‖ ≠ 0 := norm_ne_zero_iff.mpr hΓne
    field_simp [hnn]
  rw [hsimp] at hhalf
  refine hhalf.congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  intro x
  dsimp only
  rw [Real.log_pow]
  ring

/-- **Increment bound for `log ‖Γ` along a vertical line.**  For
`1/2 ≤ u₁ ≤ u₂ ≤ 8` and any real `v`,
`log ‖Γ(u₂ + i v)‖ - log ‖Γ(u₁ + i v)‖ ≤ (u₂ - u₁) (log (2 + |v|) + 2)`. -/
lemma log_norm_Gamma_sub_le (u₁ u₂ v : ℝ) (h1 : (1 : ℝ) / 2 ≤ u₁) (h12 : u₁ ≤ u₂)
    (h2 : u₂ ≤ 8) :
    Real.log ‖Complex.Gamma ((u₂ : ℂ) + (v : ℂ) * I)‖ -
      Real.log ‖Complex.Gamma ((u₁ : ℂ) + (v : ℂ) * I)‖ ≤
      (u₂ - u₁) * (Real.log (2 + |v|) + 2) := by
  set F : ℝ → ℝ := fun u => Real.log ‖Complex.Gamma ((u : ℂ) + (v : ℂ) * I)‖ with hF
  set C : ℝ := Real.log (2 + |v|) + 2 with hC
  have hdiff : ∀ u ∈ Set.Icc u₁ u₂, DifferentiableAt ℝ F u := by
    intro u hu
    have hu0 : 0 < u := by linarith [(Set.mem_Icc.mp hu).1, h1]
    exact (hasDerivAt_log_norm_Gamma u v hu0).differentiableAt
  have hbound : ∀ u ∈ Set.Icc u₁ u₂, ‖deriv F u‖ ≤ C := by
    intro u hu
    obtain ⟨hu1', hu2'⟩ := Set.mem_Icc.mp hu
    have hu0 : 0 < u := by linarith [hu1', h1]
    have hu1 : (1 : ℝ) / 2 ≤ u := le_trans h1 hu1'
    have hu8 : u ≤ 8 := le_trans hu2' h2
    have hderiv : deriv F u = (Complex.digamma ((u : ℂ) + (v : ℂ) * I)).re :=
      (hasDerivAt_log_norm_Gamma u v hu0).deriv
    rw [hderiv, Real.norm_eq_abs]
    have hψ : ‖Complex.digamma ((u : ℂ) + (v : ℂ) * I)‖ ≤ C := by
      rw [hC]
      exact digamma_mid_strip_le u v hu1 hu8
    exact le_trans (Complex.abs_re_le_norm _) hψ
  have hconvex : Convex ℝ (Set.Icc u₁ u₂) := convex_Icc _ _
  have hmain := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound hconvex
    (Set.left_mem_Icc.mpr h12) (Set.right_mem_Icc.mpr h12)
  have habs : ‖F u₂ - F u₁‖ ≤ C * (u₂ - u₁) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr h12)] using hmain
  have hle : F u₂ - F u₁ ≤ ‖F u₂ - F u₁‖ := le_abs_self _
  have hgoal : F u₂ - F u₁ ≤ C * (u₂ - u₁) := le_trans hle habs
  have hgoal' : F u₂ - F u₁ ≤ (Real.log (2 + |v|) + 2) * (u₂ - u₁) := by rwa [hC] at hgoal
  rw [hF] at hgoal'
  rw [mul_comm (Real.log (2 + |v|) + 2) (u₂ - u₁)] at hgoal'
  exact hgoal'

/-- The logarithm of the modulus of `Gammaℝ` splits into the logarithmic factor
`-(x/2) log π` and the log-modulus of `Γ` at half the argument. -/
lemma log_norm_gammaR_eq (x t : ℝ) (hx : 0 < x) :
    Real.log ‖Complex.Gammaℝ ((x : ℂ) + I * (t : ℂ))‖ =
      -(x / 2) * Real.log Real.pi +
        Real.log ‖Complex.Gamma (((x / 2 : ℝ) : ℂ) + I * ((t / 2 : ℝ) : ℂ))‖ := by
  have hΓne : Complex.Gamma (((x / 2 : ℝ) : ℂ) + I * ((t / 2 : ℝ) : ℂ)) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m hm
    have hre := congrArg Complex.re hm
    rw [Complex.add_re, Complex.mul_re] at hre
    simp at hre
    have hx2 : 0 < x / 2 := by linarith
    have : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
    linarith
  have hnz : ‖Complex.Gamma (((x / 2 : ℝ) : ℂ) + I * ((t / 2 : ℝ) : ℂ))‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hΓne
  rw [norm_gammaR_vertical_eq]
  rw [Real.log_mul (Real.rpow_pos_of_pos Real.pi_pos _).ne' hnz,
    Real.log_rpow Real.pi_pos]

/-- The target lemma. -/
theorem gammaR_log_norm_sub_le (x₁ x₂ t : ℝ) (h1 : 1 ≤ x₁) (h12 : x₁ ≤ x₂) (h2 : x₂ ≤ 16) :
    Real.log ‖Complex.Gammaℝ ((x₂ : ℂ) + Complex.I * (t : ℂ))‖ -
      Real.log ‖Complex.Gammaℝ ((x₁ : ℂ) + Complex.I * (t : ℂ))‖ ≤
      (x₂ - x₁) * (Real.log Real.pi / 2 + (Real.log (2 + |t / 2|) + 2) / 2) := by
  have hx1pos : 0 < x₁ := by linarith
  have hx2pos : 0 < x₂ := by linarith
  rw [log_norm_gammaR_eq x₂ t hx2pos, log_norm_gammaR_eq x₁ t hx1pos]
  -- normalise `I * ↑(t/2)` to `↑(t/2) * I`
  rw [mul_comm Complex.I ((t / 2 : ℝ) : ℂ)]
  set v : ℝ := t / 2 with hv
  set u₁ : ℝ := x₁ / 2 with hu₁
  set u₂ : ℝ := x₂ / 2 with hu₂
  have hu1 : (1 : ℝ) / 2 ≤ u₁ := by rw [hu₁]; linarith
  have hu12 : u₁ ≤ u₂ := by rw [hu₁, hu₂]; linarith
  have hu2 : u₂ ≤ 8 := by rw [hu₂]; linarith
  have hincr := log_norm_Gamma_sub_le u₁ u₂ v hu1 hu12 hu2
  have hx12 : 0 ≤ x₂ - x₁ := sub_nonneg.mpr h12
  have hxu : x₂ / 2 - x₁ / 2 = u₂ - u₁ := by rw [hu₁, hu₂]
  have hlogπnn : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hstep : -(x₂ / 2) * Real.log Real.pi + Real.log ‖Complex.Gamma ((u₂ : ℂ) + (v : ℂ) * I)‖
        - (-(x₁ / 2) * Real.log Real.pi + Real.log ‖Complex.Gamma ((u₁ : ℂ) + (v : ℂ) * I)‖)
      = -(x₂ - x₁) / 2 * Real.log Real.pi
        + (Real.log ‖Complex.Gamma ((u₂ : ℂ) + (v : ℂ) * I)‖
          - Real.log ‖Complex.Gamma ((u₁ : ℂ) + (v : ℂ) * I)‖) := by ring
  have hXeq : x₂ - x₁ = 2 * (u₂ - u₁) := by rw [hu₁, hu₂]; ring
  have hs : 0 ≤ u₂ - u₁ := sub_nonneg.mpr hu12
  have hlogπ : -(x₂ - x₁) / 2 * Real.log Real.pi + (u₂ - u₁) * (Real.log (2 + |v|) + 2)
      ≤ (x₂ - x₁) * (Real.log Real.pi / 2 + (Real.log (2 + |v|) + 2) / 2) := by
    rw [hXeq]
    nlinarith [hlogπnn, hs]
  calc -(x₂ / 2) * Real.log Real.pi + Real.log ‖Complex.Gamma ((u₂ : ℂ) + (v : ℂ) * I)‖
        - (-(x₁ / 2) * Real.log Real.pi + Real.log ‖Complex.Gamma ((u₁ : ℂ) + (v : ℂ) * I)‖)
      = -(x₂ - x₁) / 2 * Real.log Real.pi
        + (Real.log ‖Complex.Gamma ((u₂ : ℂ) + (v : ℂ) * I)‖
          - Real.log ‖Complex.Gamma ((u₁ : ℂ) + (v : ℂ) * I)‖) := hstep
    _ ≤ -(x₂ - x₁) / 2 * Real.log Real.pi + (u₂ - u₁) * (Real.log (2 + |v|) + 2) := by
          linarith [hincr]
    _ ≤ (x₂ - x₁) * (Real.log Real.pi / 2 + (Real.log (2 + |v|) + 2) / 2) := hlogπ
    _ = (x₂ - x₁) * (Real.log Real.pi / 2 + (Real.log (2 + |t / 2|) + 2) / 2) := by rw [hv]

end Commons.Analysis.SpecialFunctions.Gamma
