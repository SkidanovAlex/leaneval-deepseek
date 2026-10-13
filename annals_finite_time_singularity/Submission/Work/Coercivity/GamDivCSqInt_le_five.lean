import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.L2CoercivityTransport

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

/-! ## Two elementary bounds on the angular interval -/

/-- The pointwise `L²`-weighted AM–GM estimate behind the sharp constant:
`F² ≤ (22/7)(F-G)² + (22/15)G²` for all reals `F, G`.

The two coefficients are chosen so that `(22/7 - 1)(F-G)² - 2(F-G)G + (22/15 - 1)G²`
`= (15(F-G) - 7G)²/105 ≥ 0`; this makes `(22/7)·(7/10)² + (22/15)·(9/4) = 121/25 < 5`. -/
theorem sq_le_two_thirds (F G : ℝ) :
    F ^ 2 ≤ (22 / 7) * (F - G) ^ 2 + (22 / 15) * G ^ 2 := by
  nlinarith [sq_nonneg (15 * (F - G) - 7 * G)]

/-- `|K θ| ≤ 3` on the angular interval, since `K θ = 3 sin θ cos²θ` and both `sin` and
`cos` are bounded by `1` in absolute value. -/
theorem abs_K_le_three {θ : ℝ} :
    |Spaces.K θ| ≤ 3 := by
  have hs : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
  have hc : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
  have hc2 : |Real.cos θ| ^ 2 ≤ 1 := by nlinarith [abs_nonneg (Real.cos θ), hc]
  rw [Spaces.K, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3), abs_pow]
  nlinarith [hs, hc2, abs_nonneg (Real.sin θ), abs_nonneg (Real.cos θ)]

/-- The sharp angular `L²` bound for `Γ/c`: `∫_θ (Γ(θ)/c)² dθ ≤ 5`.

`GammaL2Bnd α` (in `Submission/Work/Coercivity/Defs.lean`) is
`∫ θ in Spaces.Iθ, (Γ(θ)/c - K(θ))² ≤ (7/10)²`, and `integral_Iθ_Ksq_le`
(in `Submission/Work/Coercivity/L2CoercivityTransport.lean`) is
`∫ θ in Spaces.Iθ, K(θ)² ≤ 9/4`.  Writing `Γ/c = (Γ/c - K) + K` and expanding the square
gives `∫(Γ/c)² ≤ (∫(Γ/c-K)²) + 2∫(Γ/c-K)K + ∫K²`, and Cauchy–Schwarz in `L²`
(`cs_integral_mul`, same file) bounds the cross term by `√(∫(Γ/c-K)²)·√(∫K²)`, so that
`∫_θ (Γ/c)² ≤ (7/10 + 3/2)² = 4.84 ≤ 5`.

All the integrability side conditions are automatic: on `Spaces.Iθ = [0,π/2]`
`Gam α θ / c α` and `K θ` are bounded (e.g. `Gam_div_c_bound` in
`Submission/Work/Coercivity/Basic.lean` gives `|Γ/c| ≤ 10` for `0 < α ≤ 1`) and `Iθ` has
finite measure (`instance : IsFiniteMeasure (volume.restrict Spaces.Iθ)` in
`L2CoercivityTransport.lean`).

Here the cross term is handled by the *pointwise* weighted AM–GM inequality
`2(F-G)G ≤ λ(F-G)² + G²/λ` with `λ = 15/7` (`sq_le_two_thirds`) rather than by an
abstract `L²` Cauchy–Schwarz; the numerical constant is the same. -/
theorem GamDivCSqInt_le_five (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hΓ : GammaL2Bnd α) :
    ∫ θ in Spaces.Iθ, (Spaces.Gam α θ / Spaces.c α) ^ 2 ≤ 5 := by
  have hae : ∀ᵐ θ ∂(volume.restrict Spaces.Iθ), θ ∈ Spaces.Iθ :=
    ae_restrict_mem measurableSet_Icc
  -- measurability of the three integrands
  have hmeasF : Measurable (fun θ : ℝ => (Spaces.Gam α θ / Spaces.c α) ^ 2) := by
    unfold Spaces.Gam; fun_prop
  have hmeasFG : Measurable (fun θ : ℝ =>
      (Spaces.Gam α θ / Spaces.c α - Spaces.K θ) ^ 2) := by
    unfold Spaces.Gam Spaces.K; fun_prop
  have hmeasG : Measurable (fun θ : ℝ => (Spaces.K θ) ^ 2) := by
    unfold Spaces.K; fun_prop
  -- a.e. bounds
  have hFbdd' : ∀ᵐ θ ∂(volume.restrict Spaces.Iθ),
      |Spaces.Gam α θ / Spaces.c α| ≤ 10 :=
    hae.mono (fun θ hθ => Gam_div_c_bound hα hα1 hθ)
  have hKbdd : ∀ᵐ θ ∂(volume.restrict Spaces.Iθ), |Spaces.K θ| ≤ 3 :=
    hae.mono (fun _ _ => abs_K_le_three)
  have hFbdd : ∀ᵐ θ ∂(volume.restrict Spaces.Iθ),
      ‖(Spaces.Gam α θ / Spaces.c α) ^ 2‖ ≤ 100 := by
    filter_upwards [hFbdd'] with θ h
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_abs (Spaces.Gam α θ / Spaces.c α),
      abs_nonneg (Spaces.Gam α θ / Spaces.c α), h]
  have hFGbdd : ∀ᵐ θ ∂(volume.restrict Spaces.Iθ),
      ‖(Spaces.Gam α θ / Spaces.c α - Spaces.K θ) ^ 2‖ ≤ 169 := by
    filter_upwards [hFbdd', hKbdd] with θ h1 h2
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h3 : |Spaces.Gam α θ / Spaces.c α - Spaces.K θ| ≤ 13 := by
      calc |Spaces.Gam α θ / Spaces.c α - Spaces.K θ|
          ≤ |Spaces.Gam α θ / Spaces.c α| + |Spaces.K θ| := abs_sub _ _
        _ ≤ 10 + 3 := by linarith
        _ = 13 := by norm_num
    nlinarith [sq_abs (Spaces.Gam α θ / Spaces.c α - Spaces.K θ),
      abs_nonneg (Spaces.Gam α θ / Spaces.c α - Spaces.K θ), h3]
  have hGbdd : ∀ᵐ θ ∂(volume.restrict Spaces.Iθ), ‖(Spaces.K θ) ^ 2‖ ≤ 9 := by
    filter_upwards [hKbdd] with θ h
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_abs (Spaces.K θ), abs_nonneg (Spaces.K θ), h]
  -- integrability (bounded functions on a finite measure space)
  have hFsq_int : Integrable (fun θ : ℝ => (Spaces.Gam α θ / Spaces.c α) ^ 2)
      (volume.restrict Spaces.Iθ) :=
    Integrable.of_bound hmeasF.aestronglyMeasurable 100 hFbdd
  have hFGsq_int : Integrable (fun θ : ℝ =>
      (Spaces.Gam α θ / Spaces.c α - Spaces.K θ) ^ 2) (volume.restrict Spaces.Iθ) :=
    Integrable.of_bound hmeasFG.aestronglyMeasurable 169 hFGbdd
  have hGsq_int : Integrable (fun θ : ℝ => (Spaces.K θ) ^ 2) (volume.restrict Spaces.Iθ) :=
    Integrable.of_bound hmeasG.aestronglyMeasurable 9 hGbdd
  -- splitting the integral of the weighted sum
  have hsplit : (∫ θ in Spaces.Iθ, ((22 / 7) * (Spaces.Gam α θ / Spaces.c α - Spaces.K θ) ^ 2
        + (22 / 15) * (Spaces.K θ) ^ 2))
      = (22 / 7) * (∫ θ in Spaces.Iθ, (Spaces.Gam α θ / Spaces.c α - Spaces.K θ) ^ 2)
        + (22 / 15) * (∫ θ in Spaces.Iθ, (Spaces.K θ) ^ 2) := by
    rw [integral_add (hFGsq_int.const_mul (22 / 7)) (hGsq_int.const_mul (22 / 15)),
      integral_const_mul, integral_const_mul]
  -- the pointwise AM–GM inequality, integrated
  have hmono : ∫ θ in Spaces.Iθ, (Spaces.Gam α θ / Spaces.c α) ^ 2
      ≤ (22 / 7) * (∫ θ in Spaces.Iθ, (Spaces.Gam α θ / Spaces.c α - Spaces.K θ) ^ 2)
        + (22 / 15) * (∫ θ in Spaces.Iθ, (Spaces.K θ) ^ 2) := by
    rw [← hsplit]
    refine integral_mono_ae hFsq_int
      ((hFGsq_int.const_mul (22 / 7)).add (hGsq_int.const_mul (22 / 15)))
      (Eventually.of_forall fun θ => sq_le_two_thirds _ _)
  -- the two hypotheses on the pieces
  have hA : ∫ θ in Spaces.Iθ, (Spaces.Gam α θ / Spaces.c α - Spaces.K θ) ^ 2 ≤ 49 / 100 := by
    have hΓ' : ∫ θ in Spaces.Iθ, (Spaces.Gam α θ / Spaces.c α - Spaces.K θ) ^ 2
        ≤ ((7 : ℝ) / 10) ^ 2 := hΓ
    have h7 : ((7 : ℝ) / 10) ^ 2 = 49 / 100 := by norm_num
    linarith [hΓ', h7]
  have hB : ∫ θ in Spaces.Iθ, (Spaces.K θ) ^ 2 ≤ 9 / 4 := integral_Iθ_Ksq_le
  have hAnn : 0 ≤ ∫ θ in Spaces.Iθ, (Spaces.Gam α θ / Spaces.c α - Spaces.K θ) ^ 2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hBnn : 0 ≤ ∫ θ in Spaces.Iθ, (Spaces.K θ) ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  -- `(22/7) · (49/100) + (22/15) · (9/4) = 121/25 < 5`
  linarith [hmono, hA, hB, hAnn, hBnn]

end Work.Coercivity
