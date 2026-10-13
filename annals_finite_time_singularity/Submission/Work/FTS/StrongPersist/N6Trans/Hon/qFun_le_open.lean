import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.TransportS.T2Sup.delicateBound
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `qFun_le_open`: the honest `(3,1)`-slot energy bound

The frozen sibling `Work.FTS.TransportS.T2Sup.delicate_qFun_le` proves this statement for the
*rich* bundle `T2SG α g` (which carries `SmoothQuad`, `HkMem α 5 g`, decay and the boundary
traces).  Here the same conclusion is obtained from the **honest** bundle
`SmoothOpen g ∧ HkMem α 4 g` alone: the only inputs actually used are

* `Work.FTS.TransportS.SlotT2.mslot_slice_integrable` — `θ`-slice integrability of
  `w²σ^{-γ}(mixed 3 1 g)²` (from `SmoothOpen`, `HkMem α 4`);
* `Work.FTS.TransportS.SlotT2.mslot_marginal_integrable` — the same for the `z`-marginal of
  `w²σ^{-γ}(mixed 3 1 g)²`;
* `Work.FTS.TransportS.SlotT2.canonW_mixed_iterated_le` — the iterated bound by `HkSq α 4 g`;
* `Work.FTS.TransportS.T2Sup.delicate_aesm_weight_mul` — a.e. strong measurability of
  `θ ↦ σ^{-γ}v(θ)` for `v` continuous on the open interval;
* the `rpow` identity `Wt α z θ ^ 2 = w z ^ 2 · sin(2θ)^{-γ}` (`hbi_Wm_sq`), which upgrades
  `w²σ^{-γ}` to the canonical slot weight `canonW (gam α)`.
-/

open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.Hon

set_option maxHeartbeats 1600000

theorem qFun_le_open {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hsm : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g) :
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
        (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed 3 1 g z θ) ^ 2) Work.Spaces.Iθ)
      ∧ MeasureTheory.IntegrableOn
          (fun z => (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
            (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed 3 1 g z θ) ^ 2)
          Work.Spaces.Iz
      ∧ (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
            (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed 3 1 g z θ) ^ 2)
        ≤ Work.Spaces.HkSq α 4 g := by
  have hγpos : 0 < Work.Spaces.gam α := Work.Spaces.gam_pos hα
  -- the canonical slot weight equals `w z ^ 2 · sin(2θ)^{-γ}` on `Iθ`
  have hcanon : ∀ z θ : ℝ, θ ∈ Work.Spaces.Iθ →
      Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
        = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    intro z θ hθ
    rw [Work.FTS.TransportS.SlotT2.canonW_gam_eq α z θ hθ,
      show Work.Spaces.Wt α z θ = Work.FTS.H2.Wm α z θ from rfl,
      Work.FTS.H2.hbi_Wm_sq α z θ (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ)]
  refine ⟨?_, ?_, ?_⟩
  · -- `θ`-slice integrability
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · -- at `z = 0` the `D_z`-flow kills the integrand
      subst hz0
      have hzero : (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed 3 1 g 0 θ) ^ 2) = fun _ : ℝ => (0 : ℝ) := by
        funext θ
        have hm : Work.Spaces.mixed 3 1 g 0 θ = 0 := by
          show (0 : ℝ) * Work.Spaces.pz (Work.Spaces.DzIter 2 (Work.Spaces.DthIter 1 g)) 0 θ = 0
          ring
        rw [hm]
        simp
      rw [hzero]
      exact integrableOn_zero
    · have hcw := Work.FTS.TransportS.SlotT2.mslot_slice_integrable (α := α)
        (q := Work.Spaces.gam α) hγpos le_rfl hsm hmem 3 1 le_rfl (by norm_num) hz
      refine hcw.mono' ?_ ?_
      · exact Work.FTS.TransportS.T2Sup.delicate_aesm_weight_mul
          (((hsm.mixed 3 1).curry_θ (z := z) hzpos).continuousOn.pow 2)
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
        have hw1 : 1 ≤ (Work.Spaces.w z) ^ 2 :=
          one_le_pow₀ (Work.FTS.TransportS.one_le_w hzpos)
        have hσnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
          Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ) _
        have h0 : 0 ≤ (Work.Spaces.mixed 3 1 g z θ) ^ 2 := sq_nonneg _
        rw [Real.norm_of_nonneg (mul_nonneg hσnn h0), hcanon z θ hθ]
        have h1 : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 3 1 g z θ) ^ 2
            ≤ (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                * (Work.Spaces.mixed 3 1 g z θ) ^ 2) :=
          le_mul_of_one_le_left (mul_nonneg hσnn h0) hw1
        linarith [h1]
  · -- `z`-marginal integrability
    have hmarg := Work.FTS.TransportS.SlotT2.mslot_marginal_integrable (α := α)
      (q := Work.Spaces.gam α) hγpos le_rfl hsm hmem 3 1 le_rfl (by norm_num)
    refine MeasureTheory.IntegrableOn.congr_fun hmarg (fun z _ => ?_) measurableSet_Ici
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    rw [hcanon z θ hθ]
    ring
  · -- the iterated bound
    have hEq : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * ∫ θ in Work.Spaces.Iθ,
            (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed 3 1 g z θ) ^ 2)
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
              * (Work.Spaces.mixed 3 1 g z θ) ^ 2 := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
      rw [hcanon z θ hθ]
      ring
    rw [hEq]
    exact Work.FTS.TransportS.SlotT2.canonW_mixed_iterated_le (α := α)
      (q := Work.Spaces.gam α) hγpos le_rfl hmem 3 1 le_rfl (by norm_num)

end Work.FTS.StrongPersist.N6Trans.Hon
