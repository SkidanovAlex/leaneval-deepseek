/-
# `Work.FTS.ClassCHon.Zpz.Aux.slice_mul_phiW_integrable`

The angular slices of `F` and `∂_zF` weighted by the mode function `phiW m` are `L¹` on
`Iθ = [0, π/2]`, for a source `F` which is `C^∞` on the open quadrant and honest in the
weighted space `ℋ^1` (`Work.Spaces.HkMem α 1 F`), at every radius `z > 0`.

Route (nothing else is needed).  The angular modes are *bounded on* `Iθ`:

  `|phiW m θ| = |eFam m θ · cos θ| ≤ C`  (`Work.FTS.PhiStar.Honesty.exists_bound_eFam_mul_cos`),

because `eFam m θ · cos θ = cos²θ · gC (2m+1) (sin θ)` with `gC (2m+1)` continuous on the
compact interval `[-1,1]`.  The two slices are `L¹` by the sibling lemma

  `Work.FTS.PhiStar.Honesty.slice_abs_integrable`  (`|F z ·|`, `|∂_zF z ·| ∈ L¹(Iθ)`),

and multiplying an `L¹` function by a bounded a.e.-strongly-measurable function preserves
integrability (`MeasureTheory.Integrable.mono'` with the dominating function `C·|F z ·|`, the
a.e.-strong measurability of `phiW m` coming from its continuity).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Honesty.slice_abs_integrable
import Submission.Work.FTS.ClassCHon.Zpz.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.PhiStar.Honesty.exists_bound_eFam_mul_cos

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.Zpz.Aux

open MeasureTheory Set Filter
open scoped Real Topology

/-- The angular mode weight `phiW m` is continuous on `ℝ` (it is `cos²θ · gC (2m+1) (sin θ)`
with `gC (2m+1)` a Gegenbauer polynomial). -/
theorem sliceMulPhiW_continuous (m : ℕ) : Continuous (Work.FTS.ClassCHon.Zpz.phiW m) := by
  unfold Work.FTS.ClassCHon.Zpz.phiW Work.FTS.PhiStar.Gegenbauer.eFam
  exact (Real.continuous_cos.mul
    (((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous).comp
      Real.continuous_sin)).mul Real.continuous_cos

theorem slice_mul_phiW_integrable {α : ℝ} {F : ℝ → ℝ → ℝ} (m : ℕ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF : Work.Spaces.HkMem α 1 F)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => F z θ * Work.FTS.ClassCHon.Zpz.phiW m θ) Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.Spaces.pz F z θ * Work.FTS.ClassCHon.Zpz.phiW m θ)
        Work.Spaces.Iθ := by
  obtain ⟨hFabs, hpzabs⟩ := Work.FTS.PhiStar.Honesty.slice_abs_integrable hsm hF hz
  obtain ⟨C, hC0, hCb⟩ := Work.FTS.PhiStar.Honesty.exists_bound_eFam_mul_cos m
  have hmeasIθ : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  -- `phiW m` is bounded by `C` on `Iθ`, a.e. w.r.t. the restricted measure
  have hbound : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖Work.FTS.ClassCHon.Zpz.phiW m θ‖ ≤ C :=
    MeasureTheory.ae_restrict_of_forall_mem hmeasIθ (fun θ hθ => by
      rw [Real.norm_eq_abs]
      simpa only [Work.FTS.ClassCHon.Zpz.phiW] using hCb θ hθ)
  -- a.e. strong measurability of the two slices, from smoothness on the open quadrant
  have haesmF : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => F z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ => F p.1 p.2)
      hsm.continuousOn hz
  have haesmP : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.pz F z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using
      hsm.aesm_slice_pzIter 1 hz
  have haesmW : MeasureTheory.AEStronglyMeasurable (Work.FTS.ClassCHon.Zpz.phiW m)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (sliceMulPhiW_continuous m).aestronglyMeasurable
  constructor
  · refine MeasureTheory.Integrable.mono' (hFabs.const_mul C)
      (haesmF.mul haesmW) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem hmeasIθ (fun θ hθ => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |F z θ| * |Work.FTS.ClassCHon.Zpz.phiW m θ|
        ≤ |F z θ| * C := mul_le_mul_of_nonneg_left (hCb θ hθ) (abs_nonneg _)
      _ = C * |F z θ| := by ring
  · refine MeasureTheory.Integrable.mono' (hpzabs.const_mul C)
      (haesmP.mul haesmW) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem hmeasIθ (fun θ hθ => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |Work.Spaces.pz F z θ| * |Work.FTS.ClassCHon.Zpz.phiW m θ|
        ≤ |Work.Spaces.pz F z θ| * C := mul_le_mul_of_nonneg_left (hCb θ hθ) (abs_nonneg _)
      _ = C * |Work.Spaces.pz F z θ| := by ring

end Work.FTS.ClassCHon.Zpz.Aux
