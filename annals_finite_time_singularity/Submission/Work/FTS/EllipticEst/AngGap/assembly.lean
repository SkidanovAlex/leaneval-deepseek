/-
# The assembly of the angular gap-Wirtinger inequality

This file isolates the *logic* of the proof of `Work.FTS.EllipticEst.ang_gap_wirtinger`,
i.e. the Cauchy–Schwarz step and the elementary arithmetic, from the three analytic
identities (`stepD`, `hardy`, `ibp`), which enter as hypotheses.  The main theorem in
`Submission/Work/FTS/EllipticEst/ang_gap_wirtinger.lean` instantiates them with the
lemmas proved in `AngGap/stepD`, `AngGap/hardy`, `AngGap/ibp`.

The chain: with `V = angV h = G / sin 2θ` and `Q = h' - 2 cot(2θ) h`,

* `∫ h² = - ∫ V Q` (integration by parts, hypothesis `hI`);
* hence `(∫ h²)² ≤ (∫ V²) (∫ Q²)` (Cauchy–Schwarz, `Work.Spaces.cs_integral`);
* `12 ∫ V² ≤ ∫ h²` (weighted Hardy, hypothesis `hH`);
* `∫ Q² = ∫ h'² - 4 ∫ h²` (completion of squares, hypothesis `hD`);

so `(∫ h²)² ≤ (1/12)(∫ h²)(∫ Q²)` and hence `16 ∫ h² ≤ ∫ h'²`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.cs_integral
import Submission.Work.FTS.EllipticEst.AngGap.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngGap

set_option autoImplicit false

/-- The open interval `(0,π/2)` and `Iθ` carry the same restricted Lebesgue measure, since
they differ by the two null points `0` and `π/2`. -/
theorem restrict_Ioo_eq_restrict_Iθ :
    volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) = volume.restrict Work.Spaces.Iθ :=
  Measure.restrict_congr_set (by rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc)

/-- On the open interval, `sin (2θ) ≠ 0`. -/
theorem sin_two_ne_zero_of_mem {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Real.sin (2 * θ) ≠ 0 :=
  ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos]))

/-- **Elementary arithmetic core.**  Given `A² ≤ W·Z`, `12W ≤ A`, `Z = B - 4A`, all of
`A, B, Z` nonnegative, one has `16 A ≤ B` (the case `A = 0` is trivial; otherwise
`A ≤ Z/12` and `Z = B - 4A`). -/
theorem arith_core {A B W Z : ℝ} (hAnn : 0 ≤ A) (hZnn : 0 ≤ Z) (hBnn : 0 ≤ B)
    (hcs : A ^ 2 ≤ W * Z) (hH : 12 * W ≤ A) (hZeq : Z = B - 4 * A) : 16 * A ≤ B := by
  have hWZ : W * Z ≤ (A / 12) * Z := mul_le_mul_of_nonneg_right (by linarith) hZnn
  have hkey : A ^ 2 ≤ (A / 12) * Z := le_trans hcs hWZ
  rcases eq_or_lt_of_le hAnn with h | h
  · rw [← h]; nlinarith [hBnn]
  · have h12 : 12 * A ≤ Z := by
      by_contra hcon
      push_neg at hcon
      nlinarith [hkey, h, hcon]
    linarith

/-- **Assembly.**  If `h` satisfies the bounds and if the three analytic identities hold,
then the gap-Wirtinger inequality follows. -/
theorem assembly (h : ℝ → ℝ) (hh : ContDiffOn ℝ 2 h (Set.Icc 0 (π / 2))) (C : ℝ) (hC : 0 < C)
    (hbdd : ∀ θ ∈ Set.Icc 0 (π / 2), |h θ| ≤ C * Real.sin (2 * θ))
    (hbdd' : ∀ θ ∈ Set.Ioo 0 (π / 2), |deriv h θ| ≤ C)
    (hg : ∀ θ ∈ Set.Ioo 0 (π / 2), HasDerivAt (angG h) (h θ * Real.sin (2 * θ)) θ)
    (Cg : ℝ) (hCgpos : 0 < Cg) (hCg : ∀ θ ∈ Set.Icc 0 (π / 2),
        |angG h θ| ≤ Cg * (Real.sin (2 * θ)) ^ 3)
    (hD : (∫ θ in Work.Spaces.Iθ, (deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2)
        = (∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2) - 4 * (∫ θ in Work.Spaces.Iθ, (h θ) ^ 2))
    (hH : 12 * (∫ θ in Work.Spaces.Iθ, (angV h θ) ^ 2) ≤ ∫ θ in Work.Spaces.Iθ, (h θ) ^ 2)
    (hI : (∫ θ in Work.Spaces.Iθ, (h θ) ^ 2)
        = - (∫ θ in Work.Spaces.Iθ, angV h θ * (deriv h θ - 2 * Real.cot (2 * θ) * h θ))) :
    16 * (∫ θ in Work.Spaces.Iθ, (h θ) ^ 2) ≤ (∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2) := by
  haveI : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) :=
    Real.isFiniteMeasure_restrict_Icc 0 (π / 2)
  set Q : ℝ → ℝ := fun θ => deriv h θ - 2 * Real.cot (2 * θ) * h θ with hQdef
  set V : ℝ → ℝ := fun θ => angV h θ with hVdef
  -- ## Continuity on the open interval
  have hScont : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (π / 2)) := by fun_prop
  have hSne : ∀ θ ∈ Set.Ioo 0 (π / 2), Real.sin (2 * θ) ≠ 0 :=
    fun θ hθ => sin_two_ne_zero_of_mem hθ
  have hGcont : ContinuousOn (angG h) (Set.Ioo 0 (π / 2)) :=
    fun θ hθ => (hg θ hθ).continuousAt.continuousWithinAt
  have hVcont : ContinuousOn V (Set.Ioo 0 (π / 2)) := by
    rw [hVdef]
    exact hGcont.div hScont hSne
  have hdcont : ContinuousOn (deriv h) (Set.Ioo 0 (π / 2)) :=
    (hh.mono Set.Ioo_subset_Icc_self).continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hcotcont : ContinuousOn (fun θ : ℝ => Real.cot (2 * θ)) (Set.Ioo 0 (π / 2)) := by
    have hfun : (fun θ : ℝ => Real.cot (2 * θ))
        = fun θ : ℝ => Real.cos (2 * θ) / Real.sin (2 * θ) := by
      funext θ; rw [Real.cot_eq_cos_div_sin]
    rw [hfun]
    exact (by fun_prop : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ)) (Set.Ioo 0 (π / 2))).div
      (by fun_prop) hSne
  have hhcont : ContinuousOn h (Set.Ioo 0 (π / 2)) :=
    (hh.mono Set.Ioo_subset_Icc_self).continuousOn
  have hQcont : ContinuousOn Q (Set.Ioo 0 (π / 2)) := by
    rw [hQdef]
    have h2c : ContinuousOn (fun θ : ℝ => 2 * Real.cot (2 * θ) * h θ) (Set.Ioo 0 (π / 2)) :=
      (hcotcont.const_mul 2).mul hhcont
    exact hdcont.sub (by simpa only [mul_assoc] using h2c)
  -- ## A.e. strong measurability on `Iθ`
  have hVmeas : AEStronglyMeasurable V (volume.restrict Work.Spaces.Iθ) := by
    rw [← restrict_Ioo_eq_restrict_Iθ]
    exact hVcont.aestronglyMeasurable measurableSet_Ioo
  have hQmeas : AEStronglyMeasurable Q (volume.restrict Work.Spaces.Iθ) := by
    rw [← restrict_Ioo_eq_restrict_Iθ]
    exact hQcont.aestronglyMeasurable measurableSet_Ioo
  -- ## A.e. bounds on `Iθ`
  have hVbdd : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), |V θ| ≤ Cg := by
    rw [← restrict_Ioo_eq_restrict_Iθ]
    refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have hspos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hsnn : 0 ≤ Real.sin (2 * θ) := le_of_lt hspos
    have hsin1 : (Real.sin (2 * θ)) ^ 2 ≤ 1 :=
      pow_le_one₀ hsnn (Real.sin_le_one (2 * θ))
    have hG := hCg θ ⟨hθ.1.le, hθ.2.le⟩
    simp only [hVdef, angV]
    rw [abs_div, abs_of_pos hspos]
    have h1 : |angG h θ| / Real.sin (2 * θ)
        ≤ Cg * (Real.sin (2 * θ)) ^ 3 / Real.sin (2 * θ) :=
      div_le_div_of_nonneg_right hG hspos.le
    have h2 : Cg * (Real.sin (2 * θ)) ^ 3 / Real.sin (2 * θ)
        = Cg * (Real.sin (2 * θ)) ^ 2 := by
      field_simp
    have h3 : Cg * (Real.sin (2 * θ)) ^ 2 ≤ Cg := by nlinarith [hCgpos, hsin1]
    linarith
  have hQbdd : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), |Q θ| ≤ 3 * C := by
    rw [← restrict_Ioo_eq_restrict_Iθ]
    refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have hspos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hcot := abs_cot_two_le hθ
    have hhθ := hbdd θ ⟨hθ.1.le, hθ.2.le⟩
    have hd := hbdd' θ hθ
    have h2 : |2 * Real.cot (2 * θ) * h θ| ≤ 2 * C := by
      have habs : |2 * Real.cot (2 * θ) * h θ| = 2 * (|Real.cot (2 * θ)| * |h θ|) := by
        rw [show 2 * Real.cot (2 * θ) * h θ = 2 * (Real.cot (2 * θ) * h θ) by ring,
          abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_mul]
      rw [habs]
      have hmul : |Real.cot (2 * θ)| * |h θ|
          ≤ (1 / Real.sin (2 * θ)) * (C * Real.sin (2 * θ)) :=
        mul_le_mul hcot hhθ (abs_nonneg _) (by positivity)
      have h3 : (1 / Real.sin (2 * θ)) * (C * Real.sin (2 * θ)) = C := by field_simp
      linarith [hmul.trans_eq h3]
    have hsplit : |deriv h θ - 2 * Real.cot (2 * θ) * h θ|
        ≤ |deriv h θ| + |2 * Real.cot (2 * θ) * h θ| := by
      have := abs_add_le (deriv h θ) (-(2 * Real.cot (2 * θ) * h θ))
      simpa only [sub_eq_add_neg, abs_neg] using this
    simp only [hQdef]
    linarith
  -- ## `MemLp`
  have hVmem : MemLp V 2 (volume.restrict Work.Spaces.Iθ) :=
    MemLp.of_bound hVmeas Cg (by
      filter_upwards [hVbdd] with θ hθ
      simpa only [Real.norm_eq_abs] using hθ)
  have hQmem : MemLp Q 2 (volume.restrict Work.Spaces.Iθ) :=
    MemLp.of_bound hQmeas (3 * C) (by
      filter_upwards [hQbdd] with θ hθ
      simpa only [Real.norm_eq_abs] using hθ)
  -- ## Cauchy–Schwarz
  have hcs := Work.Spaces.cs_integral hVmem hQmem
  have hsgn : (∫ θ in Work.Spaces.Iθ, V θ * Q θ)
      = - (∫ θ in Work.Spaces.Iθ, (h θ) ^ 2) := by
    rw [hVdef, hQdef]
    linarith [hI]
  have hcs' : (∫ θ in Work.Spaces.Iθ, (h θ) ^ 2) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, (V θ) ^ 2) * (∫ θ in Work.Spaces.Iθ, (Q θ) ^ 2) := by
    rw [hsgn, neg_sq] at hcs
    exact hcs
  -- ## Arithmetic
  have hAnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (h θ) ^ 2 :=
    integral_nonneg (fun θ => sq_nonneg _)
  have hZnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Q θ) ^ 2 := integral_nonneg (fun θ => sq_nonneg _)
  have hBnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2 :=
    integral_nonneg (fun θ => sq_nonneg _)
  have hZeq : (∫ θ in Work.Spaces.Iθ, (Q θ) ^ 2)
      = (∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2) - 4 * (∫ θ in Work.Spaces.Iθ, (h θ) ^ 2) := by
    rw [hQdef]; exact hD
  have hWle : 12 * (∫ θ in Work.Spaces.Iθ, (V θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, (h θ) ^ 2 := by
    rw [hVdef]; exact hH
  exact arith_core hAnn hZnn hBnn hcs' hWle hZeq

end Work.FTS.EllipticEst.AngGap
