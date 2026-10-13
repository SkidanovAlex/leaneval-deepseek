import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.TransportS.T2Sup.delicateBound
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.StrongPersist.N6Trans.Hon

/-- The `θ`-marginal of the `(2,1)`-slot of `g`, in the *open* (weak-hypothesis) setting:
`∫_θ σ^{-γ} ∫_s w²(D_z²D_θ g)² ≤ |g|_{ℋ⁴}²`, from only `SmoothOpen g` and `HkMem α 4 g`.

This is the twin of `Work.FTS.TransportS.T2Sup.delicate_psiMarginal_le`, whose hypothesis
bundle `T2SG α g` (= `RegQ α 4 g ∧ HkMem α 5 g ∧ DecayAll 4 g`) enters its proof only through
`SmoothOpen g` and `HkMem α 4 g`.  Every slot lemma invoked below is stated and proved for
exactly those two hypotheses (`SmoothOpen g`, `HkMem α 4 g`) in
`Submission/Work/FTS/TransportS/SlotT2/Basic.lean`. -/
theorem psiMarginal_le_open {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hsm : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g) :
    MeasureTheory.IntegrableOn
        (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * ∫ s in Work.Spaces.Iz, (Work.Spaces.w s) ^ 2 * (Work.Spaces.mixed 2 1 g s θ) ^ 2)
        Work.Spaces.Iθ
      ∧ (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * ∫ s in Work.Spaces.Iz, (Work.Spaces.w s) ^ 2 * (Work.Spaces.mixed 2 1 g s θ) ^ 2)
        ≤ Work.Spaces.HkSq α 4 g := by
  have hγpos : 0 < Work.Spaces.gam α := Work.Spaces.gam_pos hα
  set G : ℝ → ℝ → ℝ := fun s θ =>
    Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) s θ * (Work.Spaces.mixed 2 1 g s θ) ^ 2
    with hGdef
  have haesm : MeasureTheory.AEStronglyMeasurable (Function.uncurry G)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [hGdef]
    exact Work.FTS.TransportS.SlotT2.mslot_joint_aesm hsm 2 1
  have hslice : ∀ᵐ s ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => G s θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun s hs => by
      rw [hGdef]
      exact Work.FTS.TransportS.SlotT2.mslot_slice_integrable hγpos le_rfl hsm hmem 2 1
        le_rfl (by norm_num) hs)
  have hmarg : MeasureTheory.Integrable
      (fun s => ∫ θ, G s θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    rw [hGdef]
    exact Work.FTS.TransportS.SlotT2.mslot_marginal_integrable hγpos le_rfl hsm hmem 2 1
      le_rfl (by norm_num)
  have hnorm : (fun s => ∫ θ, ‖G s θ‖ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      = fun s => ∫ θ, G s θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    funext s
    refine MeasureTheory.integral_congr_ae ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    exact Real.norm_of_nonneg (mul_nonneg
      (Work.FTS.TransportS.SlotT2.canonW_nonneg (q := Work.Spaces.gam α)
        (z := s) (θ := θ) hθ) (sq_nonneg _))
  have hjoint : MeasureTheory.Integrable (Function.uncurry G)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (MeasureTheory.integrable_prod_iff haesm).mpr
      ⟨hslice, by simpa only [Function.uncurry, hnorm] using hmarg⟩
  have hmargθ : MeasureTheory.Integrable
      (fun θ => ∫ s, G s θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.Integrable.integral_prod_right hjoint
  have hswap := MeasureTheory.integral_integral_swap
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ) hjoint
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * ∫ s in Work.Spaces.Iz, (Work.Spaces.w s) ^ 2 * (Work.Spaces.mixed 2 1 g s θ) ^ 2
        = ∫ s, G s θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    intro θ hθ
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun s => ?_))
    have hcanon : Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) s θ
        = (Work.Spaces.w s) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
      rw [Work.FTS.TransportS.SlotT2.canonW_gam_eq α s θ hθ,
        show Work.Spaces.Wt α s θ = Work.FTS.H2.Wm α s θ from rfl,
        Work.FTS.H2.hbi_Wm_sq α s θ (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ)]
    rw [hGdef]
    simp only
    rw [hcanon]
    ring
  constructor
  · exact MeasureTheory.IntegrableOn.congr_fun hmargθ (fun θ hθ => (hpt θ hθ).symm)
      measurableSet_Icc
  · have h1 : (∫ θ in Work.Spaces.Iθ,
          (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * ∫ s in Work.Spaces.Iz, (Work.Spaces.w s) ^ 2 * (Work.Spaces.mixed 2 1 g s θ) ^ 2)
        = ∫ θ in Work.Spaces.Iθ,
            (∫ s, G s θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)) :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => hpt θ hθ)
    rw [h1]
    rw [← hswap]
    have hslot := Work.FTS.TransportS.SlotT2.canonW_mixed_iterated_le (α := α)
      (q := Work.Spaces.gam α) hγpos le_rfl hmem 2 1 le_rfl (by norm_num)
    simpa only [hGdef] using hslot

end Work.FTS.StrongPersist.N6Trans.Hon
