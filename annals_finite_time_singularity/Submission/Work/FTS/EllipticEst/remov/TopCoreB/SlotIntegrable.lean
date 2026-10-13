import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.remov.high_chain_sum_self
import Submission.Work.FTS.EllipticEst.H2W.Slot11Src.integrableOn_mixed_slot_sq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `TopCoreB/slotIntegrable`: integrability of a single mixed slot

For `f` of class `C^∞` on the open quadrant which is honestly in `ℋ^k`, every mixed slot
`(D_z^j D_θ^i f · W)²` with `1 ≤ i` and `i + j ≤ k` is integrable on every angular slice
`Iθ` (`z ∈ Iz`) and its `θ`-integral is integrable on `Iz`.

The `z`-part is `Work.FTS.EllipticEst.H2W.Slot11Src.integrableOn_mixed_slot_sq`; the
`θ`-slice part is proved here, by domination by the `ℋ^k`-integrand
(`Work.Spaces.sq_le_HkIntegrand_mixed`) together with the a.e. strong measurability coming
from the joint continuity of the slot on the open quadrant.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.TopCoreB

set_option autoImplicit false

/-- The weight `W = w·sin(2θ)^{-γ/2}` is continuous on the open quadrant. -/
theorem continuousOn_Wt_Q0 (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hsinpos : ∀ p ∈ (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) : Set (ℝ × ℝ)),
      0 < Real.sin (2 * p.2) := by
    intro p hp
    rw [Set.mem_prod] at hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
      (by linarith [hp.2.2, Real.pi_pos])
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => ?_)
    rw [Set.mem_prod] at hp
    exact pow_ne_zero 2 (ne_of_gt hp.1)
  have hsin : ContinuousOn
      (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ =>
          Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p; rfl
  rw [hfun]
  exact hw.mul hsin

/-- **Integrability of a single mixed slot.**  For `f` of class `C^∞` on the open quadrant
and honestly in `ℋ^k`, and a slot with `1 ≤ i`, `i + j ≤ k`, the slot square
`θ ↦ (D_z^j D_θ^i f · W)²` is integrable on `Iθ` for every `z ∈ Iz`, and its `θ`-integral is
integrable on `Iz`. -/
theorem slotIntegrable (α : ℝ) (k : ℕ) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ k) :
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
        Work.Spaces.Iθ)
      ∧ MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2) Work.Spaces.Iz := by
  refine ⟨?_, Work.FTS.EllipticEst.H2W.Slot11Src.integrableOn_mixed_slot_sq α k hf hmem j i
    hi hij⟩
  intro z hz
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hz0
  · -- at `z = 0` the radial weight vanishes and the slot is identically zero
    have hzero : (fun θ : ℝ => (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
        = fun _ : ℝ => (0 : ℝ) := by
      funext θ
      rw [← h0]
      simp [Work.Spaces.Wt, Work.Spaces.w]
    rw [hzero]
    exact integrableOn_zero
  · -- for `z > 0`: domination by the `ℋ^k`-integrand of `f`
    have hcont : ContinuousOn
        (fun p : ℝ × ℝ => (Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      (((hf.mixed j i).continuousOn).mul (continuousOn_Wt_Q0 α)).pow 2
    have haesm : AEStronglyMeasurable
        (fun θ : ℝ => (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
        (volume.restrict Work.Spaces.Iθ) :=
      Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hz0
    refine Integrable.mono' (hmem.1 z hz) haesm ?_
    rw [ae_restrict_iff' (show MeasurableSet Work.Spaces.Iθ from
      by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)]
    exact Filter.Eventually.of_forall fun θ hθ => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact Work.Spaces.sq_le_HkIntegrand_mixed α k f z θ i j hi hij

end Work.FTS.EllipticEst.remov.TopCoreB
