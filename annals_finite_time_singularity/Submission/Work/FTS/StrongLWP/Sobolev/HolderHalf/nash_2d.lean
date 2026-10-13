import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Coercivity.integrable_sqrt_mul_sqrt
import Submission.Work.Blocks.IMC.cs_integral_mul_le
import Submission.Work.FTS.StrongLWP.Sobolev.HolderHalf.NashData.slice_facts
import Submission.Work.FTS.StrongLWP.Sobolev.HolderHalf.NashData.integrable_facts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongLWP.Sobolev.HolderHalf

open MeasureTheory

/-- Cauchy–Schwarz for the product of two square roots, in the form needed below:
`∫ √A √B ≤ √(∫A) √(∫B)` for nonnegative `A B`, together with integrability of `√A √B`. -/
lemma cs_sqrt {A B : ℝ → ℝ} (hA : Integrable A) (hB : Integrable B)
    (hAn : ∀ t, 0 ≤ A t) (hBn : ∀ t, 0 ≤ B t) :
    Integrable (fun t => Real.sqrt (A t) * Real.sqrt (B t)) ∧
    ∫ t, Real.sqrt (A t) * Real.sqrt (B t) ≤ Real.sqrt (∫ t, A t) * Real.sqrt (∫ t, B t) := by
  refine ⟨Work.Coercivity.integrable_sqrt_mul_sqrt volume A B hA hB hAn hBn, ?_⟩
  have habs := Work.Blocks.IMC.cs_integral_mul_le (mu := volume)
    (f := fun t => Real.sqrt (A t)) (g := fun t => Real.sqrt (B t))
    (Real.continuous_sqrt.comp_aestronglyMeasurable hA.aestronglyMeasurable)
    (Real.continuous_sqrt.comp_aestronglyMeasurable hB.aestronglyMeasurable)
    (hA.congr (Filter.Eventually.of_forall fun t => (Real.sq_sqrt (hAn t)).symm))
    (hB.congr (Filter.Eventually.of_forall fun t => (Real.sq_sqrt (hBn t)).symm))
  have hAsq : (∫ t, (Real.sqrt (A t)) ^ 2) = ∫ t, A t :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => Real.sq_sqrt (hAn t))
  have hBsq : (∫ t, (Real.sqrt (B t)) ^ 2) = ∫ t, B t :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => Real.sq_sqrt (hBn t))
  have hnn : 0 ≤ ∫ t, Real.sqrt (A t) * Real.sqrt (B t) :=
    MeasureTheory.integral_nonneg fun t => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [hAsq, hBsq, abs_of_nonneg hnn] at habs
  exact habs

/-- Derivative of the second-coordinate slice equals the `(0,1)` partial derivative. -/
lemma deriv_snd {u : ℝ × ℝ → ℝ} (hu : ContDiff ℝ 1 u) (s t : ℝ) :
    deriv (fun r : ℝ => u (s, r)) t = fderiv ℝ u (s, t) (0, 1) := by
  have hd : DifferentiableAt ℝ u (s, t) :=
    (hu.differentiable (by norm_num)).differentiableAt
  have hφ : HasFDerivAt (fun r : ℝ => (s, r)) (ContinuousLinearMap.inr ℝ ℝ ℝ) t :=
    hasFDerivAt_prodMk_right s t
  have hcomp : HasDerivAt (fun r : ℝ => u (s, r))
      (fderiv ℝ u (s, t) (ContinuousLinearMap.inr ℝ ℝ ℝ 1)) t :=
    (hd.hasFDerivAt.comp t hφ).hasDerivAt
  rw [hcomp.deriv, ContinuousLinearMap.inr_apply]

set_option maxHeartbeats 1000000 in
/-- Two-dimensional Nash inequality: for `u : ℝ² → ℝ` of class `C¹` with compact support,
`∫ u⁴ ≤ 4 (∫ u²) (∫ ‖∇u‖²)`, deduced from the one-dimensional Agmon/Nash inequality `h1d`
applied to the slices in both coordinate directions. -/
theorem nash_2d {u : ℝ × ℝ → ℝ} (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u)
    (h1d : ∀ (f : ℝ → ℝ), ContDiff ℝ 1 f → HasCompactSupport f →
      ∀ y : ℝ, (f y) ^ 2 ≤ 2 * Real.sqrt (∫ x : ℝ, (f x) ^ 2) * Real.sqrt (∫ x : ℝ, (deriv f x) ^ 2)) :
    ∫ x : ℝ × ℝ, (u x) ^ 4 ≤ 4 * (∫ x : ℝ × ℝ, (u x) ^ 2) * (∫ x : ℝ × ℝ, ‖fderiv ℝ u x‖ ^ 2) := by
  obtain ⟨hctA, hctB, hcsA, hcsB, hderiv, hbdA, hbdB⟩ :=
    NashData.slice_facts hu hc
  obtain ⟨hI2, hI4, hIfd, hIt2, hIs2, hItf, hIsf, hTeq1, hTeq2, hTle1, hTle2⟩ :=
    NashData.integrable_facts hu hc
  let A : ℝ → ℝ := fun t => ∫ s : ℝ, (u (s, t)) ^ 2
  let B : ℝ → ℝ := fun t => ∫ s : ℝ, (deriv (fun r : ℝ => u (r, t)) s) ^ 2
  let C : ℝ → ℝ := fun s => ∫ t : ℝ, (u (s, t)) ^ 2
  let D : ℝ → ℝ := fun s => ∫ t : ℝ, (deriv (fun r : ℝ => u (s, r)) t) ^ 2
  -- integrability of the four slice-integral functions
  have hAint : Integrable A := hIt2
  have hBint : Integrable B := by
    refine hItf.congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [B]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => by simp only [hderiv])
  have hCint : Integrable C := hIs2
  have hDint : Integrable D := by
    refine hIsf.congr (Filter.Eventually.of_forall fun s => ?_)
    simp only [D]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => by
      simp only [deriv_snd hu s t])
  -- nonnegativity
  have hAnn : ∀ t, 0 ≤ A t := fun t => by
    simp only [A]
    exact MeasureTheory.integral_nonneg fun s => sq_nonneg _
  have hBnn : ∀ t, 0 ≤ B t := fun t => by
    simp only [B]
    exact MeasureTheory.integral_nonneg fun s => sq_nonneg _
  have hCnn : ∀ s, 0 ≤ C s := fun s => by
    simp only [C]
    exact MeasureTheory.integral_nonneg fun t => sq_nonneg _
  have hDnn : ∀ s, 0 ≤ D s := fun s => by
    simp only [D]
    exact MeasureTheory.integral_nonneg fun t => sq_nonneg _
  -- the scalar identities and bounds
  have hAeq : (∫ t : ℝ, A t) = ∫ p : ℝ × ℝ, (u p) ^ 2 := by
    simp only [A]; exact hTeq1
  have hCeq : (∫ s : ℝ, C s) = ∫ p : ℝ × ℝ, (u p) ^ 2 := by
    simp only [C]; exact hTeq2
  have hBle : (∫ t : ℝ, B t) ≤ ∫ p : ℝ × ℝ, ‖fderiv ℝ u p‖ ^ 2 := by
    have h1 : (∫ t : ℝ, B t) = ∫ t : ℝ, ∫ s : ℝ, (fderiv ℝ u (s, t) (1, 0)) ^ 2 := by
      simp only [B]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t =>
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => by simp only [hderiv]))
    rw [h1]; exact hTle1
  have hDle : (∫ s : ℝ, D s) ≤ ∫ p : ℝ × ℝ, ‖fderiv ℝ u p‖ ^ 2 := by
    have h1 : (∫ s : ℝ, D s) = ∫ s : ℝ, ∫ t : ℝ, (fderiv ℝ u (s, t) (0, 1)) ^ 2 := by
      simp only [D]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s =>
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => by
          simp only [deriv_snd hu s t]))
    rw [h1]; exact hTle2
  have hQ0nn : 0 ≤ ∫ p : ℝ × ℝ, (u p) ^ 2 :=
    MeasureTheory.integral_nonneg fun p => sq_nonneg _
  have hQ1nn : 0 ≤ ∫ p : ℝ × ℝ, ‖fderiv ℝ u p‖ ^ 2 :=
    MeasureTheory.integral_nonneg fun p => sq_nonneg _
  -- pointwise Agmon bounds, in the two coordinate directions
  have keyA : ∀ s t : ℝ, (u (s, t)) ^ 2 ≤ 2 * Real.sqrt (A t) * Real.sqrt (B t) := by
    intro s t
    have h := h1d (fun r : ℝ => u (r, t)) (hctA t) (hcsA t) s
    simpa only [A, B] using h
  have keyC : ∀ s t : ℝ, (u (s, t)) ^ 2 ≤ 2 * Real.sqrt (C s) * Real.sqrt (D s) := by
    intro s t
    have h := h1d (fun r : ℝ => u (s, r)) (hctB s) (hcsB s) t
    simpa only [C, D] using h
  have keypt : ∀ p : ℝ × ℝ, (u p) ^ 4 ≤
      4 * (Real.sqrt (A p.2) * Real.sqrt (B p.2)) *
        (Real.sqrt (C p.1) * Real.sqrt (D p.1)) := by
    rintro ⟨s, t⟩
    have h1 := keyA s t
    have h2 := keyC s t
    have h3 : (u (s, t)) ^ 2 * (u (s, t)) ^ 2 ≤
        (2 * Real.sqrt (A t) * Real.sqrt (B t)) *
          (2 * Real.sqrt (C s) * Real.sqrt (D s)) :=
      mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
    calc (u (s, t)) ^ 4 = (u (s, t)) ^ 2 * (u (s, t)) ^ 2 := by ring
      _ ≤ (2 * Real.sqrt (A t) * Real.sqrt (B t)) *
            (2 * Real.sqrt (C s) * Real.sqrt (D s)) := h3
      _ = 4 * (Real.sqrt (A t) * Real.sqrt (B t)) *
            (Real.sqrt (C s) * Real.sqrt (D s)) := by ring
  have hPint : Integrable (fun t : ℝ => Real.sqrt (A t) * Real.sqrt (B t)) :=
    (cs_sqrt hAint hBint hAnn hBnn).1
  have hQint : Integrable (fun s : ℝ => Real.sqrt (C s) * Real.sqrt (D s)) :=
    (cs_sqrt hCint hDint hCnn hDnn).1
  have hRHSint : Integrable (fun p : ℝ × ℝ =>
      4 * (Real.sqrt (A p.2) * Real.sqrt (B p.2)) *
        (Real.sqrt (C p.1) * Real.sqrt (D p.1))) := by
    refine (Integrable.mul_prod (hQint.const_mul 4) hPint).congr
      (Filter.Eventually.of_forall fun p => ?_)
    ring
  have hstep1 : ∫ p : ℝ × ℝ, (u p) ^ 4 ≤ ∫ p : ℝ × ℝ,
      4 * (Real.sqrt (A p.2) * Real.sqrt (B p.2)) *
        (Real.sqrt (C p.1) * Real.sqrt (D p.1)) := by
    refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => ?_)
      hRHSint (Filter.Eventually.of_forall keypt)
    positivity
  have hstep2 : ∫ p : ℝ × ℝ,
      4 * (Real.sqrt (A p.2) * Real.sqrt (B p.2)) *
        (Real.sqrt (C p.1) * Real.sqrt (D p.1))
      = 4 * (∫ t : ℝ, Real.sqrt (A t) * Real.sqrt (B t)) *
          (∫ s : ℝ, Real.sqrt (C s) * Real.sqrt (D s)) := by
    rw [show (∫ p : ℝ × ℝ,
        4 * (Real.sqrt (A p.2) * Real.sqrt (B p.2)) *
          (Real.sqrt (C p.1) * Real.sqrt (D p.1)))
        = ∫ p : ℝ × ℝ,
            (fun s : ℝ => 4 * (Real.sqrt (C s) * Real.sqrt (D s))) p.1 *
              (fun t : ℝ => Real.sqrt (A t) * Real.sqrt (B t)) p.2 from
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => by ring)]
    rw [Measure.volume_eq_prod ℝ ℝ,
      MeasureTheory.integral_prod_mul
        (f := fun s : ℝ => 4 * (Real.sqrt (C s) * Real.sqrt (D s)))
        (g := fun t : ℝ => Real.sqrt (A t) * Real.sqrt (B t)),
      MeasureTheory.integral_const_mul]
    ring
  have hbig : 4 * (∫ t : ℝ, Real.sqrt (A t) * Real.sqrt (B t)) *
        (∫ s : ℝ, Real.sqrt (C s) * Real.sqrt (D s))
      ≤ 4 * (Real.sqrt (∫ t : ℝ, A t) * Real.sqrt (∫ t : ℝ, B t)) *
          (Real.sqrt (∫ s : ℝ, C s) * Real.sqrt (∫ s : ℝ, D s)) := by
    have h2 : 0 ≤ ∫ s : ℝ, Real.sqrt (C s) * Real.sqrt (D s) :=
      MeasureTheory.integral_nonneg fun s => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    exact mul_le_mul (mul_le_mul_of_nonneg_left (cs_sqrt hAint hBint hAnn hBnn).2 (by norm_num))
      (cs_sqrt hCint hDint hCnn hDnn).2 h2 (by positivity)
  have hfinal : 4 * (Real.sqrt (∫ t : ℝ, A t) * Real.sqrt (∫ t : ℝ, B t)) *
        (Real.sqrt (∫ s : ℝ, C s) * Real.sqrt (∫ s : ℝ, D s))
      ≤ 4 * (∫ p : ℝ × ℝ, (u p) ^ 2) * (∫ p : ℝ × ℝ, ‖fderiv ℝ u p‖ ^ 2) := by
    rw [hAeq, hCeq]
    have hb := Real.sqrt_le_sqrt hBle
    have hd := Real.sqrt_le_sqrt hDle
    have hsq0 : Real.sqrt (∫ p : ℝ × ℝ, (u p) ^ 2) * Real.sqrt (∫ p : ℝ × ℝ, (u p) ^ 2)
        = ∫ p : ℝ × ℝ, (u p) ^ 2 := by
      rw [← pow_two, Real.sq_sqrt hQ0nn]
    have hsq1 : Real.sqrt (∫ p : ℝ × ℝ, ‖fderiv ℝ u p‖ ^ 2) *
        Real.sqrt (∫ p : ℝ × ℝ, ‖fderiv ℝ u p‖ ^ 2)
        = ∫ p : ℝ × ℝ, ‖fderiv ℝ u p‖ ^ 2 := by
      rw [← pow_two, Real.sq_sqrt hQ1nn]
    have hprod : Real.sqrt (∫ t : ℝ, B t) * Real.sqrt (∫ s : ℝ, D s)
        ≤ ∫ p : ℝ × ℝ, ‖fderiv ℝ u p‖ ^ 2 :=
      (mul_le_mul hb hd (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).trans hsq1.le
    have hre : 4 * (Real.sqrt (∫ p : ℝ × ℝ, (u p) ^ 2) * Real.sqrt (∫ t : ℝ, B t)) *
        (Real.sqrt (∫ p : ℝ × ℝ, (u p) ^ 2) * Real.sqrt (∫ s : ℝ, D s))
        = 4 * (Real.sqrt (∫ p : ℝ × ℝ, (u p) ^ 2) * Real.sqrt (∫ p : ℝ × ℝ, (u p) ^ 2)) *
          (Real.sqrt (∫ t : ℝ, B t) * Real.sqrt (∫ s : ℝ, D s)) := by ring
    rw [hre, hsq0]
    exact mul_le_mul_of_nonneg_left hprod (by nlinarith [hQ0nn])
  calc ∫ p : ℝ × ℝ, (u p) ^ 4
      ≤ ∫ p : ℝ × ℝ, 4 * (Real.sqrt (A p.2) * Real.sqrt (B p.2)) *
          (Real.sqrt (C p.1) * Real.sqrt (D p.1)) := hstep1
    _ = 4 * (∫ t : ℝ, Real.sqrt (A t) * Real.sqrt (B t)) *
          (∫ s : ℝ, Real.sqrt (C s) * Real.sqrt (D s)) := hstep2
    _ ≤ 4 * (Real.sqrt (∫ t : ℝ, A t) * Real.sqrt (∫ t : ℝ, B t)) *
          (Real.sqrt (∫ s : ℝ, C s) * Real.sqrt (∫ s : ℝ, D s)) := hbig
    _ ≤ 4 * (∫ p : ℝ × ℝ, (u p) ^ 2) * (∫ p : ℝ × ℝ, ‖fderiv ℝ u p‖ ^ 2) := hfinal

end Work.FTS.StrongLWP.Sobolev.HolderHalf
