/-
# `MG G` is locally integrable on `(0,∞)`

The dominating function `MG G w = |G w (π/4)| + |∂_θG w (π/4)| + √(E2sl G w)` of the
double-mollification transfer is locally integrable on the positive half-line, as soon as the
datum is `C^∞` on the open quadrant (`SmoothOpen G`) and its four weighted slice functionals are
integrable in `z` (`FourInts G`).

* the two interior values at `θ = π/4` are continuous functions of `z` on `(0,∞)` (they are
  `z`-slices of `G` and of `∂_θG`), hence integrable on every compact interval;
* `√(E2sl G z) = √|ttIntS G z| / w z` because `ttIntS G z = w z ^ 2 * E2sl G z`, and
  `w z = (1+z)^2/z^2 ≥ b^2/(1+b)^2` on `(a,b)`; the elementary bound
  `√|t| ≤ (|t| + 1)/2` finishes, the dominating function `(|ttIntS G ·| + 1)/2 · (b^2/(1+b)^2)`
  being integrable by `FourInts`.  (This is the "Cauchy–Schwarz"/AM–GM step announced in
  `MollConvDefs`.)
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.EllPkgAux.MollConvDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollSmooth

open MeasureTheory Set Filter

theorem MG_integrableOn (G : ℝ → ℝ → ℝ) (hS : Work.FTS.EllipticEst.SmoothOpen G)
    (hFI : Work.FTS.EllSol.EllPkgAux.FourInts G) :
    ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (Work.FTS.EllSol.EllPkgAux.MG G) (Set.Ioo a b) := by
  intro a b ha hab
  have hθ0 : (Real.pi / 4) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hsub : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun x hx => lt_of_lt_of_le ha hx.1
  -- the two interior slice values are continuous on `(0,∞)`, hence integrable on `(a,b)`
  have h_int1 : MeasureTheory.IntegrableOn (fun w => |G w (Real.pi / 4)|) (Set.Ioo a b) :=
    (((hS.curry_z hθ0).continuousOn.abs).mono hsub).integrableOn_compact isCompact_Icc
      |>.mono_set Set.Ioo_subset_Icc_self
  have h_int2 : MeasureTheory.IntegrableOn (fun w => |Work.Spaces.pth G w (Real.pi / 4)|)
      (Set.Ioo a b) :=
    (((hS.pth.curry_z hθ0).continuousOn.abs).mono hsub).integrableOn_compact isCompact_Icc
      |>.mono_set Set.Ioo_subset_Icc_self
  -- the square root of the slice functional
  have h_int3 : MeasureTheory.IntegrableOn
      (fun w => Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2sl G w)) (Set.Ioo a b) := by
    have hT : MeasureTheory.IntegrableOn (Work.EllipticEst.Core.ttIntS G) (Set.Ioo a b) :=
      hFI.2.2.1.mono_set (fun x hx => le_of_lt (lt_trans ha hx.1))
    have hwpos : ∀ z ∈ Set.Ioo a b, 0 < Work.Spaces.w z := by
      intro z hz; rw [Work.Spaces.w]; have : (0 : ℝ) < z := lt_trans ha hz.1; positivity
    -- the dominating function `(|ttIntS G ·| + 1)/2 · (b^2/(1+b)^2)`
    have hgint : MeasureTheory.IntegrableOn
        (fun z => (|Work.EllipticEst.Core.ttIntS G z| + 1) / 2 * (b ^ 2 / (1 + b) ^ 2))
        (Set.Ioo a b) := by
      have hc : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioo a b) :=
        (continuousOn_const.integrableOn_compact isCompact_Icc).mono_set Set.Ioo_subset_Icc_self
      exact (((MeasureTheory.Integrable.abs hT).add hc).div_const 2).mul_const (b ^ 2 / (1 + b) ^ 2)
    -- `E2sl G = ttIntS G / w²` on `(a,b)`, so it is a.e. strongly measurable
    have hw2cont : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioo a b) := by
      have hfun : (fun z : ℝ => (Work.Spaces.w z) ^ 2) = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := rfl
      rw [hfun]
      refine ContinuousOn.pow ?_ 2
      exact ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2) (continuousOn_id.pow 2)
        (fun z hz => pow_ne_zero 2 (ne_of_gt (lt_trans ha hz.1)))
    have hwit : ∀ z ∈ Set.Ioo a b,
        Work.EllipticEst.Core.ttIntS G z / (Work.Spaces.w z) ^ 2
          = Work.FTS.EllSol.EllPkgAux.E2sl G z := by
      intro z hz
      have hwz : Work.Spaces.w z ≠ 0 := ne_of_gt (hwpos z hz)
      rw [show Work.EllipticEst.Core.ttIntS G z
            = (Work.Spaces.w z) ^ 2 * Work.FTS.EllSol.EllPkgAux.E2sl G z from rfl]
      exact mul_div_cancel_left₀ (Work.FTS.EllSol.EllPkgAux.E2sl G z) (pow_ne_zero 2 hwz)
    have hE2meas : AEStronglyMeasurable (fun w => Work.FTS.EllSol.EllPkgAux.E2sl G w)
        (volume.restrict (Set.Ioo a b)) :=
      (hT.aemeasurable.div (hw2cont.aemeasurable measurableSet_Ioo)).aestronglyMeasurable |>.congr
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo hwit)
    have hmeas : AEStronglyMeasurable
        (fun w => Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2sl G w))
        (volume.restrict (Set.Ioo a b)) :=
      (hE2meas.aemeasurable.sqrt).aestronglyMeasurable
    -- the pointwise domination
    have hdom : ∀ᵐ z ∂(volume.restrict (Set.Ioo a b)),
        ‖Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2sl G z)‖
          ≤ (|Work.EllipticEst.Core.ttIntS G z| + 1) / 2 * (b ^ 2 / (1 + b) ^ 2) := by
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun z hz => ?_)
      have hE2nn : 0 ≤ Work.FTS.EllSol.EllPkgAux.E2sl G z := by
        rw [Work.FTS.EllSol.EllPkgAux.E2sl]
        refine MeasureTheory.integral_nonneg_of_ae ?_
        refine MeasureTheory.ae_restrict_of_forall_mem (show MeasurableSet Work.Spaces.Iθ from by
          rw [Work.Spaces.Iθ]; exact measurableSet_Icc) ?_
        intro θ hθ
        exact mul_nonneg (sq_nonneg _)
          (Work.FTS.EllipticEst.thEta_nonneg (by rw [Work.Spaces.Iθ]; exact hθ))
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      have hz1 : 0 < z := lt_trans ha hz.1
      have hzb : z < b := hz.2
      have hwzp : 0 < Work.Spaces.w z := hwpos z hz
      have hnn : 0 ≤ (Work.Spaces.w z) ^ 2 * Work.FTS.EllSol.EllPkgAux.E2sl G z :=
        mul_nonneg (sq_nonneg _) hE2nn
      -- `√(E2sl) = √|ttIntS| / w`
      have hsq : Real.sqrt (|Work.EllipticEst.Core.ttIntS G z|)
          = Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2sl G z) * Work.Spaces.w z := by
        rw [show Work.EllipticEst.Core.ttIntS G z
              = (Work.Spaces.w z) ^ 2 * Work.FTS.EllSol.EllPkgAux.E2sl G z from rfl,
          abs_of_nonneg hnn, Real.sqrt_mul (sq_nonneg (Work.Spaces.w z)), Real.sqrt_sq_eq_abs,
          abs_of_nonneg (le_of_lt hwzp)]
        ring
      have h4 : Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2sl G z)
          = Real.sqrt (|Work.EllipticEst.Core.ttIntS G z|) / Work.Spaces.w z := by
        rw [eq_div_iff (ne_of_gt hwzp)]
        simpa [mul_comm] using hsq.symm
      -- `√|t| ≤ (|t| + 1)/2`
      have hup : Real.sqrt (|Work.EllipticEst.Core.ttIntS G z|)
          ≤ (|Work.EllipticEst.Core.ttIntS G z| + 1) / 2 := by
        rw [Real.sqrt_le_iff]
        refine ⟨by positivity, ?_⟩
        nlinarith [abs_nonneg (Work.EllipticEst.Core.ttIntS G z),
          sq_nonneg (|Work.EllipticEst.Core.ttIntS G z| - 1)]
      -- `1/w z ≤ b²/(1+b)²` on `(a,b)`
      have hinvw : 1 / Work.Spaces.w z ≤ b ^ 2 / (1 + b) ^ 2 := by
        have hb1 : 0 < b := lt_trans hz1 hzb
        have hw : 1 / Work.Spaces.w z = z ^ 2 / (1 + z) ^ 2 := by
          rw [Work.Spaces.w]; field_simp
        rw [hw]
        have hsub2 : 0 ≤ b ^ 2 / (1 + b) ^ 2 - z ^ 2 / (1 + z) ^ 2 := by
          rw [show b ^ 2 / (1 + b) ^ 2 - z ^ 2 / (1 + z) ^ 2
                = (b - z) * (b + 2 * b * z + z) / ((1 + b) ^ 2 * (1 + z) ^ 2) from by
            field_simp; ring]
          exact div_nonneg (mul_nonneg (by linarith) (by nlinarith [hb1, hz1])) (by positivity)
        linarith
      rw [h4]
      calc Real.sqrt (|Work.EllipticEst.Core.ttIntS G z|) / Work.Spaces.w z
          ≤ ((|Work.EllipticEst.Core.ttIntS G z| + 1) / 2) / Work.Spaces.w z :=
            div_le_div_of_nonneg_right hup (le_of_lt hwzp)
        _ = (|Work.EllipticEst.Core.ttIntS G z| + 1) / 2 * (1 / Work.Spaces.w z) := by ring
        _ ≤ (|Work.EllipticEst.Core.ttIntS G z| + 1) / 2 * (b ^ 2 / (1 + b) ^ 2) :=
            mul_le_mul_of_nonneg_left hinvw (by positivity)
    exact hgint.mono' hmeas hdom
  show MeasureTheory.IntegrableOn (fun w => |G w (Real.pi / 4)|
      + |Work.Spaces.pth G w (Real.pi / 4)|
      + Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2sl G w)) (Set.Ioo a b)
  exact (h_int1.add h_int2).add h_int3

end Work.FTS.EllSol.EllPkgAux.MollSmooth
