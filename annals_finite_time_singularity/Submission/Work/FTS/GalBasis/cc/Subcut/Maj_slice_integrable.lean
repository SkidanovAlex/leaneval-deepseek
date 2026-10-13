import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.GalBasis.cc.Subcut.MajDefs
import Submission.Work.FTS.GalBasis.cc.Subcut.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongLWP.Xn6Limit.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc.Subcut

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **Nonnegativity of the majorant.**  `Maj α C κN N f = C · (1_{UN N} · HkIntegrand + 1_{LN N} ·
∑_{b<4} slotW²)` and both summands are products of an indicator (taking the values `0, 1`) with a
square or with the `HkIntegrand`, which is a sum of squares.  Only `0 < C` is needed (`κN` does not
occur in `Maj`). -/
private theorem Maj_nonneg {α : ℝ} {f : Fn} {C κN : ℝ} (N : ℕ) (hC : 0 < C) (z θ : ℝ) :
    0 ≤ Work.FTS.GalBasis.cc.Maj α C κN N f z θ := by
  rw [Work.FTS.GalBasis.cc.Maj_eq_sum_form]
  refine mul_nonneg hC.le (add_nonneg ?_ ?_)
  · exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
      (Work.Spaces.HkIntegrand_nonneg α 4 f z θ)
  · exact Finset.sum_nonneg fun b _ => mul_nonneg
      (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (sq_nonneg _)

/-- **The angular slice of the majorant is a.e. strongly measurable for `z > 0`.**  Expand `Maj`
with `Maj_eq_sum_form`; each piece is (a.e.) strongly measurable for `volume.restrict Iθ`:
`HkIntegrand α 4 f z ·` and `DzIter b f z · * Wt α z ·` are the `θ`-slices of functions continuous
on the open quadrant (`Work.Spaces.aesm_slice_of_continuousOn_Qd`,
`Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand`, `SmoothOpen.DzIter`,
`Work.FTS.StrongLWP.Xn6Limit.continuousOn_Wt_Qd`), while the two indicator slices `θ ↦
1_{UN N}(z,θ)` and `θ ↦ 1_{LN N}(θ)` are measurable. -/
private theorem Maj_aesm_slice {α : ℝ} {f : Fn} (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (C κN : ℝ) (N : ℕ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Work.FTS.GalBasis.cc.Maj α C κN N f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  -- the `θ`-slice of `HkIntegrand α 4 f`
  have hHk : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Work.Spaces.HkIntegrand α 4 f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 f p.1 p.2)
      (hsm.continuousOn_HkIntegrand α 4) hz
  -- the two indicator slices
  have hindU : Measurable (fun θ : ℝ => (Work.FTS.GalBasis.cc.UN N).indicator
      (fun _ => (1 : ℝ)) (z, θ)) :=
    ((measurable_const : Measurable (fun _ : ℝ × ℝ => (1 : ℝ))).indicator
      (measurableSet_UN N)).comp (measurable_const.prodMk measurable_id)
  have hindL : Measurable (fun θ : ℝ => (Work.FTS.GalBasis.cc.LN N).indicator
      (fun _ => (1 : ℝ)) θ) :=
    (measurable_const : Measurable (fun _ : ℝ => (1 : ℝ))).indicator (measurableSet_LN N)
  -- the `θ`-slices of the wrong-weight slots `D_z^b f · Wt`
  have hWtb : ∀ b : ℕ, MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Work.FTS.GalBasis.cc.zslotW α b f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := fun b =>
    Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.FTS.GalBasis.cc.zslotW α b f p.1 p.2)
      (show ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter b f p.1 p.2
            * Work.Spaces.Wt α p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) from
        ((hsm.DzIter b).continuousOn).mul (Work.FTS.StrongLWP.Xn6Limit.continuousOn_Wt_Qd α))
      hz
  have hmain : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => C * ((Work.FTS.GalBasis.cc.UN N).indicator (fun _ => (1 : ℝ)) (z, θ)
        * Work.Spaces.HkIntegrand α 4 f z θ
        + ∑ b ∈ Finset.range 4, (Work.FTS.GalBasis.cc.LN N).indicator (fun _ => (1 : ℝ)) θ
            * (Work.FTS.GalBasis.cc.zslotW α b f z θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine MeasureTheory.AEStronglyMeasurable.const_mul ?_ C
    refine MeasureTheory.AEStronglyMeasurable.add ?_ ?_
    · exact hindU.aestronglyMeasurable.mul hHk
    · exact Finset.aestronglyMeasurable_sum (Finset.range 4) fun b _ =>
        hindL.aestronglyMeasurable.mul ((hWtb b).pow 2)
  simpa only [Work.FTS.GalBasis.cc.Maj_eq_sum_form] using hmain

/-- **The angular slices of the majorant `Maj α C κN N f` are integrable for a.e. `z ∈ Iz`.**

`Maj` is dominated on the open quadrant by `C (1 + κN) HkIntegrand α 4 f` (`hcap`), which is
integrable on the angular slice `Iθ` for every `z ∈ Iz` by `hmem.1`; since the product measure
`(volume.restrict Iz).prod (volume.restrict Iθ)` concentrates on the open quadrant (`z = 0` is
null, and the two angular endpoints are null), the domination holds a.e. in `θ`.  Route:
`filter_upwards` with `0 < z` (a.e. on `Iz`, use `MeasureTheory.Ioi_ae_eq_Ici` +
`MeasureTheory.Measure.restrict_congr_set`), prove `AEStronglyMeasurable (fun θ => Maj … z θ)
(volume.restrict Iθ)` by unfolding `Maj_eq_sum_form` into
`C * (1_{UN N}(z,·) * HkIntegrand α 4 f z · + 1_{LN N}(·) * ∑_{b<4} (DzIter b f z · * Wt α z ·)²)`
and using `Work.Spaces.aesm_slice_of_continuousOn_Qd` on
`Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand`, `SmoothOpen.DzIter` and
`Work.FTS.StrongLWP.Xn6Limit.continuousOn_Wt_Qd` together with the measurability of the two
indicator slices, then `MeasureTheory.Integrable.mono'` (dominating function
`fun θ => C * (1 + κN) * HkIntegrand α 4 f z θ`, integrable by `hmem.1 z hz.le`) with the a.e. bound
`‖Maj … z θ‖ ≤ C (1 + κN) HkIntegrand α 4 f z θ` obtained from `hcap` and the pointwise
nonnegativity of `Maj` (which uses `hC : 0 < C` and `Work.Spaces.HkIntegrand_nonneg`). -/
theorem Maj_slice_integrable {α : ℝ} {f : Work.FTS.Galerkin.Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    {C κN : ℝ} (N : ℕ) (hC : 0 < C)
    (hcap : ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      Work.FTS.GalBasis.cc.Maj α C κN N f z θ
        ≤ C * (1 + κN) * Work.Spaces.HkIntegrand α 4 f z θ) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.FTS.GalBasis.cc.Maj α C κN N f z θ) Work.Spaces.Iθ := by
  -- `Iz = [0,∞)` agrees with the open half-line `(0,∞)` up to the null set `{0}`
  have hIzeq : Work.Spaces.Iz =ᵐ[MeasureTheory.volume] Set.Ioi (0 : ℝ) :=
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm
  rw [MeasureTheory.Measure.restrict_congr_set hIzeq]
  filter_upwards [MeasureTheory.self_mem_ae_restrict (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi]
    with z hz
  -- the dominating function `θ ↦ |C (1 + κN)| · HkIntegrand α 4 f z θ` is integrable on `Iθ`
  have hzIz : z ∈ Work.Spaces.Iz := by
    simp only [Work.Spaces.Iz, Set.mem_Ici]
    exact le_of_lt hz
  have hdom : MeasureTheory.Integrable
      (fun θ : ℝ => |C * (1 + κN)| * Work.Spaces.HkIntegrand α 4 f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (hmem.1 z hzIz).const_mul _
  refine MeasureTheory.Integrable.mono' hdom (Maj_aesm_slice hsm C κN N hz) ?_
  -- the pointwise bound only needs to hold a.e. in `θ`, i.e. on the interior of `Iθ`
  have hIθeq : Work.Spaces.Iθ =ᵐ[MeasureTheory.volume] Set.Ioo (0 : ℝ) (π / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0) (b := π / 2)).symm
  rw [MeasureTheory.Measure.restrict_congr_set hIθeq]
  filter_upwards
    [MeasureTheory.self_mem_ae_restrict (s := Set.Ioo (0 : ℝ) (π / 2)) measurableSet_Ioo]
    with θ hθ
  rw [Real.norm_of_nonneg
    (Maj_nonneg (α := α) (f := f) (C := C) (κN := κN) N hC z θ)]
  refine le_trans (hcap z θ hz ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩) ?_
  exact mul_le_mul_of_nonneg_right (le_abs_self (C * (1 + κN)))
    (Work.Spaces.HkIntegrand_nonneg α 4 f z θ)

end Work.FTS.GalBasis.cc.Subcut
