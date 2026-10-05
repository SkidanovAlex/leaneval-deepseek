import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B5.deriv_bounds_family
import Submission.Work.RPB.B5.pos_min_of_compact

/-!
# B5: positivity of the signed area is open in the `C¹` topology

`Work.RPB.B5.pos_area_of_close_family`: for a jointly `C¹` family `γ : ℝ → ℝ → ℂ` of closed curves
with `‖γ τ t‖ ≤ K` and `‖deriv (γ τ) t‖ ≤ K` on `τ ∈ [0,1]` and `signedArea (γ τ) > 0` for every
`τ ∈ [0,1]`, there is a single `ε > 0` such that *every* `C¹` perturbation `η` of *every* slice
`γ τ` with `‖η t‖ < ε` and `‖deriv η t‖ < ε` still has positive signed area.

The proof has three parts.

* `τ ↦ signedArea (γ τ)` is continuous (`Work.RPB.B5.continuous_signedArea_of_contDiff_one`), so on
  the compact interval `[0,1]` it is bounded below by a positive constant `m`
  (`Work.RPB.B5.pos_min_of_compact`).
* The area form `ω_ℂ (a,b) = Im (conj a * b)` is `ℝ`-bilinear and satisfies
  `|ω_ℂ a b| ≤ ‖a‖ ‖b‖`, so writing `u = γ τ + η`,
  `ω_ℂ (u t) (deriv u t) = ω_ℂ (γ τ t) (deriv (γ τ) t) + R t` with
  `R t = ω_ℂ (γ τ t) (deriv η t) + ω_ℂ (η t) (deriv (γ τ) t) + ω_ℂ (η t) (deriv η t)`, and
  `|R t| ≤ 2 K ε + ε²` whenever `‖η t‖ < ε` and `‖deriv η t‖ < ε`
  (`signedArea_close_bound`).  Integrating gives
  `signedArea (γ τ) - π (2 K ε + ε²) ≤ signedArea (γ τ + η)`.
* Choosing `ε = min 1 (m / (4 π (K+1)))` makes `π (2 K ε + ε²) < m`, so
  `signedArea (γ τ + η) > 0`.

No periodicity of `γ` in `t` is needed anywhere: the estimate is purely pointwise in the
integrand.
-/

open MeasureTheory intervalIntegral
open scoped Interval

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-! ## Elementary facts about the area form `ω_ℂ` -/

/-- The area form `ω_ℂ (a,b) = Im (conj a * b)` is continuous in the pair `(a,b)`. -/
lemma continuous_ωC {X : Type*} [TopologicalSpace X] {f h : X → ℂ} (hf : Continuous f)
    (hh : Continuous h) : Continuous (fun x => Work.RPV.ωC (f x) (h x)) := by
  show Continuous (fun x => ((starRingEnd ℂ) (f x) * h x).im)
  exact Complex.continuous_im.comp ((continuous_star.comp hf).mul hh)

/-- `ω_ℂ (-,-)` is additive in its first argument. -/
lemma ωC_add_left (a b c : ℂ) :
    Work.RPV.ωC (a + b) c = Work.RPV.ωC a c + Work.RPV.ωC b c := by
  simp only [Work.RPV.ωC, map_add, add_mul, Complex.add_im]

/-- `ω_ℂ (-,-)` is additive in its second argument. -/
lemma ωC_add_right (a b c : ℂ) :
    Work.RPV.ωC a (b + c) = Work.RPV.ωC a b + Work.RPV.ωC a c := by
  simp only [Work.RPV.ωC, mul_add, Complex.add_im]

/-- The area form is bounded by the product of the norms. -/
lemma abs_ωC_le (a b : ℂ) : |Work.RPV.ωC a b| ≤ ‖a‖ * ‖b‖ := by
  have h1 : |((starRingEnd ℂ) a * b).im| ≤ ‖(starRingEnd ℂ) a * b‖ := Complex.abs_im_le_norm _
  rw [Work.RPV.ωC]
  refine h1.trans ?_
  rw [norm_mul, Complex.norm_conj]

/-! ## The `C¹`-stability estimate for the signed area -/

/-- **The signed area is `1/2`-Lipschitz for the `C¹` uniform norm, with the constants made
explicit.**

Let `g : ℝ → ℂ` be `C¹` with `‖g t‖ ≤ K` and `‖deriv g t‖ ≤ K` for all `t`, and let `η` be a
`C¹` perturbation with `‖η t‖ < ε` and `‖deriv η t‖ < ε`.  Then

`1/2 ∫₀^{2π} (ω_ℂ (u,u') - ω_ℂ (g,g'))  ≥  - π (2 K ε + ε²)`,  `u = g + η`,

i.e. `signedArea g - π (2 K ε + ε²) ≤ signedArea (g + η)`.

The point is that `ω_ℂ (u, u') - ω_ℂ (g, g') = ω_ℂ (g, η') + ω_ℂ (η, g') + ω_ℂ (η, η')` is
pointwise bounded by `2 K ε + ε²` in absolute value. -/
lemma signedArea_close_bound (g η : ℝ → ℂ) (hg : ContDiff ℝ 1 g) (hη : ContDiff ℝ 1 η)
    (K ε : ℝ) (hbn : ∀ t, ‖g t‖ ≤ K) (hbd : ∀ t, ‖deriv g t‖ ≤ K)
    (hη1 : ∀ t, ‖η t‖ < ε) (hη2 : ∀ t, ‖deriv η t‖ < ε) :
    Work.RPB.signedArea g - Real.pi * (2 * K * ε + ε ^ 2) ≤ Work.RPB.signedArea (g + η) := by
  -- `K ≥ 0` and `ε ≥ 0` are automatic consequences of the bounds.
  have hK : 0 ≤ K := le_trans (norm_nonneg (g 0)) (hbn 0)
  have hε0 : 0 ≤ ε := le_of_lt (lt_of_le_of_lt (norm_nonneg (η 0)) (hη1 0))
  have hgc : Continuous g := hg.continuous
  have hηc : Continuous η := hη.continuous
  have hdgc : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hdηc : Continuous (deriv η) := hη.continuous_deriv le_rfl
  have hdiffg : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hdiffη : Differentiable ℝ η := hη.differentiable (by norm_num)
  have hu : ContDiff ℝ 1 (g + η) := hg.add hη
  have huc : Continuous (g + η) := hu.continuous
  have hduc : Continuous (deriv (g + η)) := hu.continuous_deriv le_rfl
  have hderiv : ∀ t, deriv (g + η) t = deriv g t + deriv η t := fun t =>
    deriv_add hdiffg.differentiableAt hdiffη.differentiableAt
  -- the correction term
  set R : ℝ → ℝ := fun t => Work.RPV.ωC (g t) (deriv η t) + Work.RPV.ωC (η t) (deriv g t)
      + Work.RPV.ωC (η t) (deriv η t) with hR
  have hRc : Continuous R := by
    rw [hR]
    exact ((continuous_ωC hgc hdηc).add (continuous_ωC hηc hdgc)).add (continuous_ωC hηc hdηc)
  have hGint : IntervalIntegrable (fun t => Work.RPV.ωC (g t) (deriv g t)) volume 0 (2 * Real.pi) :=
    (continuous_ωC hgc hdgc).intervalIntegrable _ _
  have hRint : IntervalIntegrable R volume 0 (2 * Real.pi) := hRc.intervalIntegrable _ _
  -- pointwise decomposition of the integrand
  have hkey : ∀ t, Work.RPV.ωC ((g + η) t) (deriv (g + η) t)
      = Work.RPV.ωC (g t) (deriv g t) + R t := by
    intro t
    rw [hderiv t]
    simp only [Pi.add_apply, hR, ωC_add_left, ωC_add_right]
    ring
  have hF_eq : ∫ t in (0:ℝ)..(2 * Real.pi), Work.RPV.ωC ((g + η) t) (deriv (g + η) t)
      = (∫ t in (0:ℝ)..(2 * Real.pi), Work.RPV.ωC (g t) (deriv g t))
        + ∫ t in (0:ℝ)..(2 * Real.pi), R t := by
    rw [show (fun t => Work.RPV.ωC ((g + η) t) (deriv (g + η) t))
        = (fun t => Work.RPV.ωC (g t) (deriv g t) + R t) from funext hkey]
    exact intervalIntegral.integral_add hGint hRint
  -- pointwise bound on the correction
  have hpt : ∀ t, |R t| ≤ 2 * K * ε + ε ^ 2 := by
    intro t
    have h1 : |Work.RPV.ωC (g t) (deriv η t)| ≤ K * ε :=
      (abs_ωC_le _ _).trans (mul_le_mul (hbn t) (le_of_lt (hη2 t)) (norm_nonneg _) hK)
    have h2 : |Work.RPV.ωC (η t) (deriv g t)| ≤ ε * K :=
      (abs_ωC_le _ _).trans (mul_le_mul (le_of_lt (hη1 t)) (hbd t) (norm_nonneg _) hε0)
    have h3 : |Work.RPV.ωC (η t) (deriv η t)| ≤ ε * ε :=
      (abs_ωC_le _ _).trans (mul_le_mul (le_of_lt (hη1 t)) (le_of_lt (hη2 t)) (norm_nonneg _) hε0)
    have hsub : R t = Work.RPV.ωC (g t) (deriv η t) + Work.RPV.ωC (η t) (deriv g t)
        + Work.RPV.ωC (η t) (deriv η t) := rfl
    rw [hsub]
    have hsum : |Work.RPV.ωC (g t) (deriv η t) + Work.RPV.ωC (η t) (deriv g t)
        + Work.RPV.ωC (η t) (deriv η t)|
        ≤ |Work.RPV.ωC (g t) (deriv η t)| + |Work.RPV.ωC (η t) (deriv g t)|
          + |Work.RPV.ωC (η t) (deriv η t)| := by
      linarith [abs_add_le (Work.RPV.ωC (g t) (deriv η t) + Work.RPV.ωC (η t) (deriv g t))
        (Work.RPV.ωC (η t) (deriv η t)),
        abs_add_le (Work.RPV.ωC (g t) (deriv η t)) (Work.RPV.ωC (η t) (deriv g t))]
    linarith [hsum, h1, h2, h3]
  have hbound : |∫ t in (0:ℝ)..(2 * Real.pi), R t| ≤ (2 * K * ε + ε ^ 2) * (2 * Real.pi) := by
    have hpt' : ∀ t ∈ Set.uIoc (0:ℝ) (2 * Real.pi), ‖R t‖ ≤ 2 * K * ε + ε ^ 2 := by
      intro t _
      rw [Real.norm_eq_abs]
      exact hpt t
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt'
    rwa [Real.norm_eq_abs, sub_zero, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)] at h
  have hsA : Work.RPB.signedArea (g + η)
      = Work.RPB.signedArea g + (1/2) * (∫ t in (0:ℝ)..(2*Real.pi), R t) := by
    simp only [Work.RPB.signedArea]
    rw [hF_eq]
    ring
  have hlow : Work.RPB.signedArea g - Real.pi * (2 * K * ε + ε ^ 2)
      ≤ Work.RPB.signedArea (g + η) := by
    rw [hsA]
    have h2 := (abs_le.mp hbound).1
    nlinarith [h2]
  exact hlow

/-! ## The main theorem -/

end Work.RPB.B5
