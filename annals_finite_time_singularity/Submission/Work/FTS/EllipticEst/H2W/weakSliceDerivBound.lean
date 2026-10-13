import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Elliptic.DivSinDefs
import Submission.Work.FTS.EllipticEst.slice_cs_weighted
import Submission.Work.FTS.EllipticEst.TT.abs_le_sin_mul_of_deriv_bound
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.sliceCSWeightedOpen
import Submission.Work.FTS.EllipticEst.absLeMulOfDerivBoundOpen
import Submission.Work.FTS.EllipticEst.SgamBound.integrableOn_abs_of_sq_mul_sEta

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

open MeasureTheory Set Filter
open scoped Real Topology Interval

/-- On `Iθ = [0, π/2]` the distance to the nearer endpoint is dominated by `(π/4)·sin(2θ)`.
Concavity of `sin` on `[0, π/2]` gives `(2/π)·x ≤ sin x` there; applied to `2θ ≤ π/2`
(equivalently to `2(π/2 - θ) ≤ π/2`, using `sin(π - x) = sin x`) this yields `θ ≤ (π/4)sin 2θ`
on the left half of `Iθ` and `π/2 - θ ≤ (π/4)sin 2θ` on the right half. -/
theorem min_le_sin_Iθ {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi / 2) :
    min θ (Real.pi / 2 - θ) ≤ (Real.pi / 4) * Real.sin (2 * θ) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  rcases le_total θ (Real.pi / 4) with hle | hge
  · -- left half: `2θ ≤ π/2`, so `(2/π)·(2θ) ≤ sin(2θ)`
    have hmin : min θ (Real.pi / 2 - θ) = θ := by
      refine min_eq_left ?_
      linarith
    rw [hmin]
    have hsin : (2 / Real.pi) * (2 * θ) ≤ Real.sin (2 * θ) :=
      Real.mul_le_sin (by linarith) (by linarith)
    calc θ = (Real.pi / 4) * ((2 / Real.pi) * (2 * θ)) := by
          field_simp
          ring
      _ ≤ (Real.pi / 4) * Real.sin (2 * θ) := mul_le_mul_of_nonneg_left hsin (by positivity)
  · -- right half: `2(π/2 - θ) = π - 2θ ≤ π/2`, so `(2/π)·2(π/2 - θ) ≤ sin(π - 2θ) = sin(2θ)`
    have hmin : min θ (Real.pi / 2 - θ) = Real.pi / 2 - θ := by
      refine min_eq_right ?_
      linarith
    rw [hmin]
    have hsin : (2 / Real.pi) * (2 * (Real.pi / 2 - θ))
        ≤ Real.sin (2 * (Real.pi / 2 - θ)) :=
      Real.mul_le_sin (by linarith) (by linarith)
    have harg : Real.sin (2 * (Real.pi / 2 - θ)) = Real.sin (2 * θ) := by
      rw [show 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ by ring, Real.sin_pi_sub]
    rw [harg] at hsin
    calc Real.pi / 2 - θ = (Real.pi / 4) * ((2 / Real.pi) * (2 * (Real.pi / 2 - θ))) := by
          field_simp
          ring
      _ ≤ (Real.pi / 4) * Real.sin (2 * θ) := mul_le_mul_of_nonneg_left hsin (by positivity)

theorem weakSliceDerivBound (u : ℝ → ℝ)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2)))
    (hcont : ContinuousOn u Work.Spaces.Iθ) (h0 : u 0 = 0) (h1 : u (Real.pi / 2) = 0)
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ) :
    (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        (deriv u θ) ^ 2
          ≤ (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv u t) θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ)
            * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta)))
      ∧ (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
          |u θ| ≤ (Real.pi / 4) * Real.sin (2 * θ)
            * Real.sqrt ((∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv u t) θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ)
              * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta)))) := by
  set A : ℝ := ∫ θ in Work.Spaces.Iθ,
    (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ with hA
  set B : ℝ := ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta) with hB
  -- ## Smoothness of `u''` on the open interval
  have hd1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
    (hu 2).deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hd2cont : ContinuousOn (fun θ => deriv (fun t => deriv u t) θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    hd1.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
  -- ## Integrability of `|u''|` on `Iθ` (from `hint` and `sEta ≥ 1`)
  have hint_abs : MeasureTheory.IntegrableOn
      (fun s => |deriv (fun t => deriv u t) s|) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.SgamBound.integrableOn_abs_of_sq_mul_sEta hd2cont hint
  -- ## Rolle: some interior point has `u' = 0`
  obtain ⟨c, hc, hcz⟩ := exists_deriv_eq_zero (f := u) (a := (0 : ℝ)) (b := Real.pi / 2)
    (by positivity) hcont (h0.trans h1.symm)
  -- ## Fundamental theorem of calculus: `|u' θ| ≤ ∫_{Iθ} |u''|`
  have hftc : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |deriv u θ| ≤ ∫ s in Work.Spaces.Iθ, |deriv (fun t => deriv u t) s| :=
    Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv hd1 hc hcz hint_abs
  -- ## Weighted Cauchy–Schwarz: `(∫_{Iθ} |u''|)² ≤ A · B`
  have hcs : (∫ s in Work.Spaces.Iθ, |deriv (fun t => deriv u t) s|) ^ 2 ≤ A * B := by
    have h := Work.FTS.EllipticEst.sliceCSWeightedOpen
      (g := fun θ => deriv (fun t => deriv u t) θ) hd2cont hint
    simpa [hA, hB] using h
  -- ## First conjunct
  have hbound1 : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), (deriv u θ) ^ 2 ≤ A * B := by
    intro θ hθ
    have h1' := hftc θ hθ
    have h2 : |deriv u θ| ^ 2
        ≤ (∫ s in Work.Spaces.Iθ, |deriv (fun t => deriv u t) s|) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) h1' 2
    rw [sq_abs] at h2
    linarith [h2, hcs]
  -- ## Second conjunct: mean-value bounds in `θ` and `(π/2 - θ)`
  have hsqrtnn : 0 ≤ Real.sqrt (A * B) := Real.sqrt_nonneg _
  have hbd : ∀ x ∈ Set.Ioo 0 (Real.pi / 2), |deriv u x| ≤ Real.sqrt (A * B) := by
    intro x hx
    calc |deriv u x| = Real.sqrt ((deriv u x) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (A * B) := Real.sqrt_le_sqrt (hbound1 x hx)
  have hmvt := Work.FTS.EllipticEst.absLeMulOfDerivBoundOpen
    (u := u) (M := Real.sqrt (A * B)) ((hu 2).differentiableOn (by norm_num)) hcont h0 h1 hbd
  refine ⟨fun θ hθ => by simpa [hA, hB] using hbound1 θ hθ, fun θ hθ => ?_⟩
  have hI : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hleft := hmvt.1 θ hI
  have hright := hmvt.2 θ hI
  have hcase : |u θ| ≤ min θ (Real.pi / 2 - θ) * Real.sqrt (A * B) := by
    rcases le_total θ (Real.pi / 2 - θ) with hh | hh
    · rw [min_eq_left hh]; exact hleft
    · rw [min_eq_right hh]; exact hright
  have hmin := mul_le_mul_of_nonneg_right
    (min_le_sin_Iθ (le_of_lt hθ.1) (le_of_lt hθ.2)) hsqrtnn
  have hfinal : |u θ| ≤ (Real.pi / 4) * Real.sin (2 * θ) * Real.sqrt (A * B) :=
    le_trans hcase hmin
  simpa [hA, hB] using hfinal

end Work.FTS.EllipticEst.H2W
