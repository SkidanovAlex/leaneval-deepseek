import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.BadTermSqBound
import Submission.Work.FTS.H2.HQ.Glue

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.HQ

open MeasureTheory Set Filter
open scoped Real Topology
open Work.Spaces
open Work.FTS.LocData (SmoothQuad)

set_option maxHeartbeats 800000

/-- The `L2Mem` half of the bad-term package of the interior product rule `HProdQ`: given the
a.e.-in-`θ` norm-domination of the bad-term integrand `(D_z³f · D_θg · Wt)²` by the product
`badU α f z · badV α g θ` of the two one-dimensional Hardy bounds, together with the
integrability of the two dominating functions, the weighted product is square integrable in the
iterated sense (every angular slice integrable, and the resulting function of `z` integrable). -/
theorem BadMemQ (α : ℝ) (f g : ℝ → ℝ → ℝ)
    (hf : Work.FTS.LocData.SmoothQuad f) (hg : Work.FTS.LocData.SmoothQuad g)
    (hUint : MeasureTheory.Integrable (Work.Spaces.badU α f)
      (MeasureTheory.volume.restrict Work.Spaces.Iz))
    (hVint : MeasureTheory.Integrable (Work.Spaces.badV α g)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hdom : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), ∀ z ∈ Work.Spaces.Iz,
      ‖(Work.Spaces.DzIter 3 f z θ * Work.Spaces.Dth g z θ * Work.Spaces.Wt α z θ) ^ 2‖
        ≤ Work.Spaces.badU α f z * Work.Spaces.badV α g θ) :
    Work.Spaces.L2Mem (fun z θ => Work.Spaces.DzIter 3 f z θ * Work.Spaces.Dth g z θ
        * Work.Spaces.Wt α z θ) := by
  -- The joint strong measurability of the squared weighted product and that of every angular
  -- slice, supplied by the interior glue (`SmoothQuad` is closed under `D_z^3` and `D_θ`).
  have haesm := aesm_sq_prod_quad α (A := DzIter 3 f) (B := Dth g) (hf.DzIter 3) (hg.DthIter 1)
  -- The a.e.-in-`θ` domination, restricted to a fixed `z ∈ Iz`.
  have hdom' : ∀ z ∈ Iz, ∀ᵐ θ ∂(volume.restrict Iθ),
      ‖(DzIter 3 f z θ * Dth g z θ * Wt α z θ) ^ 2‖ ≤ badU α f z * badV α g θ :=
    fun z hz => hdom.mono fun θ hθ => hθ z hz
  constructor
  · -- Every angular slice is integrable, by domination by the (integrable) `θ ↦ badV α g θ`.
    intro z hz
    refine MeasureTheory.Integrable.mono' (hVint.const_mul (badU α f z)) (haesm.2 z hz) ?_
    filter_upwards [hdom' z hz] with θ hθ
    simpa only [Real.norm_of_nonneg (sq_nonneg (DzIter 3 f z θ * Dth g z θ * Wt α z θ))]
      using hθ
  · -- The iterated integral is integrable: its `z`-value is bounded by
    -- `badU α f z * ∫_θ badV α g`, and `badU α f` is integrable.
    refine MeasureTheory.Integrable.mono'
      (hUint.mul_const (∫ θ in Iθ, badV α g θ)) haesm.1.integral_prod_right' ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Iz from measurableSet_Ici)] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
    calc ∫ θ in Iθ, (DzIter 3 f z θ * Dth g z θ * Wt α z θ) ^ 2
        ≤ ∫ θ in Iθ, badU α f z * badV α g θ := by
          refine MeasureTheory.integral_mono_ae
            (MeasureTheory.Integrable.mono'
              (hVint.const_mul (badU α f z)) (haesm.2 z hz) ?_)
            (hVint.const_mul (badU α f z)) ?_
          · filter_upwards [hdom' z hz] with θ hθ
            simpa only [Real.norm_of_nonneg
              (sq_nonneg (DzIter 3 f z θ * Dth g z θ * Wt α z θ))] using hθ
          · filter_upwards [hdom' z hz] with θ hθ
            simpa only [Real.norm_of_nonneg
              (sq_nonneg (DzIter 3 f z θ * Dth g z θ * Wt α z θ))] using hθ
      _ = badU α f z * ∫ θ in Iθ, badV α g θ := MeasureTheory.integral_const_mul _ _

end Work.FTS.H2.HQ
