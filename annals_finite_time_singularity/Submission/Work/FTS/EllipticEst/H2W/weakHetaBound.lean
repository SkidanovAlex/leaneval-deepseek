import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Elliptic.DivSinDefs
import Submission.Work.FTS.EllipticEst.TT.Heta_le_of_sin_bound
import Submission.Work.FTS.EllipticEst.TT.slice_coercive
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.absLeMulOfDerivBoundOpen
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.sliceCSWeightedOpen
import Submission.Work.FTS.EllipticEst.SgamBound.integrableOn_abs_of_sq_mul_sEta

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

open MeasureTheory Set Filter
open scoped Real Topology Interval

/-- On `Iθ = [0, π/2]` the distance to the nearer endpoint is dominated by `(π/4)·sin(2θ)`
(Jordan's inequality applied to `2θ ≤ π/2` on the left half of the interval and to
`2(π/2 - θ) = π - 2θ` on the right half). -/
theorem min_le_sin_two {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi / 2) :
    min θ (Real.pi / 2 - θ) ≤ (Real.pi / 4) * Real.sin (2 * θ) := by
  rw [min_le_iff]
  rcases le_total θ (Real.pi / 4) with h | h
  · left
    have h1' : 0 ≤ 2 * θ := by linarith
    have h2' : 2 * θ ≤ Real.pi / 2 := by linarith
    have hs := Real.mul_le_sin h1' h2'
    calc θ = (Real.pi / 4) * ((2 / Real.pi) * (2 * θ)) := by field_simp; ring
      _ ≤ (Real.pi / 4) * Real.sin (2 * θ) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
  · right
    have h1' : 0 ≤ 2 * (Real.pi / 2 - θ) := by linarith
    have h2' : 2 * (Real.pi / 2 - θ) ≤ Real.pi / 2 := by linarith
    have hs := Real.mul_le_sin h1' h2'
    have hsin : Real.sin (2 * (Real.pi / 2 - θ)) = Real.sin (2 * θ) := by
      rw [show 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ by ring, Real.sin_pi_sub]
    rw [hsin] at hs
    calc Real.pi / 2 - θ = (Real.pi / 4) * ((2 / Real.pi) * (2 * (Real.pi / 2 - θ))) := by
          field_simp; ring
      _ ≤ (Real.pi / 4) * Real.sin (2 * θ) :=
          mul_le_mul_of_nonneg_left hs (by positivity)

/-- **Weak `η`-weighted angular Poincaré inequality.**  For a slice `u` that is smooth on the
open interval `(0, π/2)`, continuous on `Iθ = [0, π/2]`, vanishing at both endpoints, and whose
second derivative is square-integrable against the singular weight `sEta θ = sin(2θ)^{-η}`,

  `∫_{Iθ} u² sin(2θ)^{-η} ≤ C · ∫_{Iθ} (u'')² sin(2θ)^{-η}`,

with the universal constant `C = (π/4)²(π/2)²`.

Proof: `u'` vanishes somewhere inside (Rolle, since `u` has equal endpoint values), so the
fundamental theorem of calculus gives `|u' θ| ≤ ∫_{Iθ} |u''|` on the open interval; the weighted
Cauchy–Schwarz inequality turns this into the uniform bound `|u' θ| ≤ √(A B)` with
`A = ∫_{Iθ} (u'')² sEta` and `B = ∫_{Iθ} sin(2θ)^{η} ≤ π/2`.  Two Lagrange mean-value bounds
then give `|u θ| ≤ min(θ, π/2-θ)·√(A B) ≤ (π/4) sin(2θ)·√(A B)` on `Iθ`, and integration
against `sin(2θ)^{-η}` (`TT.Heta_le_of_sin_bound`, using `2 - η > 0`) yields the claim. -/
theorem weakHetaBound : ∃ C : ℝ, 0 < C ∧ ∀ (u : ℝ → ℝ),
    (∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2))) →
    ContinuousOn u Work.Spaces.Iθ → u 0 = 0 → u (Real.pi / 2) = 0 →
    MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ →
    (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      ≤ C * (∫ θ in Work.Spaces.Iθ,
          (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
  refine ⟨(Real.pi / 4) ^ 2 * (Real.pi / 2) * (Real.pi / 2), by positivity, ?_⟩
  intro u hu hcont h0 h1 hint
  set A : ℝ := ∫ θ in Work.Spaces.Iθ,
      (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ with hA
  set B : ℝ := ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta) with hB
  have hAnn : 0 ≤ A := by
    rw [hA]
    exact setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.TT.sEta_nonneg hθ))
  have hBnn : 0 ≤ B := by
    rw [hB]
    exact setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => Real.rpow_nonneg (Work.FTS.EllipticEst.TT.sin_two_nonneg hθ) _)
  have hBle : B ≤ Real.pi / 2 := by
    rw [hB]
    exact (Work.FTS.EllipticEst.integrableOn_sin_two_rpow Work.Spaces.eta_nonneg).2
  -- ## Smoothness and integrability of the second derivative on the open interval
  have hd1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
    (hu 2).deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hd2cont : ContinuousOn (fun θ => deriv (fun t => deriv u t) θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    hd1.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
  have hint_abs : MeasureTheory.IntegrableOn
      (fun s => |deriv (fun t => deriv u t) s|) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.SgamBound.integrableOn_abs_of_sq_mul_sEta hd2cont (by simpa using hint)
  -- ## Rolle: `u'` vanishes at some interior point
  obtain ⟨c, hc, hcz⟩ := exists_deriv_eq_zero (f := u) (a := (0 : ℝ)) (b := Real.pi / 2)
    (by positivity) hcont (h0.trans h1.symm)
  -- ## Fundamental theorem of calculus: `|u'| ≤ ∫_{Iθ} |u''|`
  have hftc : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |deriv u θ| ≤ ∫ s in Work.Spaces.Iθ, |deriv (fun t => deriv u t) s| :=
    Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv hd1 hc hcz hint_abs
  -- ## Weighted Cauchy–Schwarz: `(∫_{Iθ} |u''|)² ≤ A · B`
  have hcs : (∫ s in Work.Spaces.Iθ, |deriv (fun t => deriv u t) s|) ^ 2 ≤ A * B := by
    have h := Work.FTS.EllipticEst.sliceCSWeightedOpen
      (g := fun θ => deriv (fun t => deriv u t) θ) hd2cont (by simpa using hint)
    simpa [hA, hB] using h
  have hbound1 : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), (deriv u θ) ^ 2 ≤ A * B := by
    intro θ hθ
    have h1' := hftc θ hθ
    have h2 : |deriv u θ| ^ 2
        ≤ (∫ s in Work.Spaces.Iθ, |deriv (fun t => deriv u t) s|) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) h1' 2
    rw [sq_abs] at h2
    linarith [h2, hcs]
  have hbd : ∀ x ∈ Set.Ioo 0 (Real.pi / 2), |deriv u x| ≤ Real.sqrt (A * B) := by
    intro x hx
    calc |deriv u x| = Real.sqrt ((deriv u x) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (A * B) := Real.sqrt_le_sqrt (hbound1 x hx)
  -- ## Two mean-value bounds for `u`, and their combination with Jordan's inequality
  obtain ⟨hmv1, hmv2⟩ := Work.FTS.EllipticEst.absLeMulOfDerivBoundOpen (u := u)
    (M := Real.sqrt (A * B)) ((hu 2).differentiableOn (by norm_num)) hcont h0 h1 hbd
  have hsqrtnn : 0 ≤ Real.sqrt (A * B) := Real.sqrt_nonneg _
  have hu_bound : ∀ θ ∈ Work.Spaces.Iθ,
      |u θ| ≤ ((Real.pi / 4) * Real.sqrt (A * B)) * Real.sin (2 * θ) := by
    intro θ hθ
    rcases lt_or_eq_of_le hθ.1 with hlt0 | heq0
    · rcases lt_or_eq_of_le hθ.2 with hlt1 | heq1
      · have hI : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨le_of_lt hlt0, le_of_lt hlt1⟩
        have hcase : |u θ| ≤ min θ (Real.pi / 2 - θ) * Real.sqrt (A * B) := by
          rcases le_total θ (Real.pi / 2 - θ) with hh | hh
          · rw [min_eq_left hh]; exact hmv1 θ hI
          · rw [min_eq_right hh]; exact hmv2 θ hI
        have hmin := min_le_sin_two (le_of_lt hlt0) (le_of_lt hlt1)
        calc |u θ| ≤ min θ (Real.pi / 2 - θ) * Real.sqrt (A * B) := hcase
          _ ≤ ((Real.pi / 4) * Real.sin (2 * θ)) * Real.sqrt (A * B) :=
              mul_le_mul_of_nonneg_right hmin hsqrtnn
          _ = ((Real.pi / 4) * Real.sqrt (A * B)) * Real.sin (2 * θ) := by ring
      · rw [heq1, h1, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi, mul_zero,
          abs_zero]
    · rw [← heq0, h0]
      simp
  -- ## Integrate the pointwise bound against the singular weight
  have hK : 0 ≤ (Real.pi / 4) * Real.sqrt (A * B) := by positivity
  have hmain := Work.FTS.EllipticEst.TT.Heta_le_of_sin_bound u hK hu_bound
  have hKs : (Real.sqrt (A * B)) ^ 2 = A * B := Real.sq_sqrt (mul_nonneg hAnn hBnn)
  have hK2 : ((Real.pi / 4) * Real.sqrt (A * B)) ^ 2 * (Real.pi / 2)
      ≤ ((Real.pi / 4) ^ 2 * (Real.pi / 2) * (Real.pi / 2)) * A := by
    rw [mul_pow, hKs]
    have hAB : A * B ≤ A * (Real.pi / 2) := mul_le_mul_of_nonneg_left hBle hAnn
    have hc : 0 ≤ (Real.pi / 4) ^ 2 * (Real.pi / 2) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hAB hc]
  exact le_trans hmain hK2

end Work.FTS.EllipticEst.H2W
