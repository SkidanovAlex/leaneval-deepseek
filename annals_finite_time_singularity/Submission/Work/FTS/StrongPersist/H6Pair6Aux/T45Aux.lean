import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.slotCS_z
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.radialMul6Cont
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-!
# `T45Aux` — weight and leaf facts for the row `T45aRow`

Elementary facts about the radial weight `w` and the leaf weights, the continuity of the
angular factor `Abnd` on the open quadrant, and the domination of a leaf-weighted square of an
`f`-slot by the level-six integrand `HkIntegrand α 6 f`.
-/

/-! ## Elementary facts about the weights -/

/-- The radial weight is nonnegative. -/
theorem w_nonneg (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]; positivity

/-- The radial weight is positive at `z > 0`. -/
theorem w_pos_of_pos {z : ℝ} (hz : 0 < z) : 0 < Work.Spaces.w z := by
  rw [Work.Spaces.w]; positivity


/-- The angular factor `Abnd` is continuous on the open quadrant. -/
theorem continuousOn_Abnd (α : ℝ) (a : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Abnd α a p.2) Work.FTS.EllipticEst.Q0 := by
  unfold Abnd
  split_ifs with h
  · exact continuousOn_const
  · have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
        Work.FTS.EllipticEst.Q0 :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
    have hpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, Real.sin (2 * p.2) ≠ 0 := by
      intro p hp
      obtain ⟨-, h2, h3⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
    exact (continuousOn_const.add hsin).mul
      (hsin.rpow_const (fun p hp => Or.inl (hpos p hp)))

/-! ## The f-slot square is dominated by the level-six integrand -/

theorem rhoV2_slice {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hm6 : Work.Spaces.HkMem α 6 f)
    {a b : ℕ} {ρ : ℝ → ℝ → ℝ} (hleaf : Work.FTS.TransportS.IsLeafW α a ρ)
    (hab : a + b ≤ 6) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
        (fun θ => ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ := by
  have hzIz : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => ρ p.1 p.2 * (Work.Spaces.mixed b a f p.1 p.2) ^ 2)
      Work.FTS.EllipticEst.Q0 :=
    (continuousOn_leaf hleaf).mul (((hso.mixed b a).continuousOn).pow 2)
  have haesm : AEStronglyMeasurable
      (fun θ => ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2) (volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hz
  have hpt : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
    Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ h1 h2 =>
      le_trans (mul_le_mul_of_nonneg_right
        ((Work.FTS.TransportS.IsLeafW_le α hα hleaf).2 z θ hz h1 h2) (sq_nonneg _))
        (slotW_slot_le6 hα ⟨h1, h2⟩ hab))
  have hnn : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      0 ≤ ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2 :=
    Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ h1 h2 =>
      mul_nonneg ((Work.FTS.TransportS.IsLeafW_le α hα hleaf).1 z θ hz h1 h2) (sq_nonneg _))
  refine ⟨MeasureTheory.Integrable.mono' (hm6.1 z hzIz) haesm ?_,
    MeasureTheory.integral_mono_of_nonneg hnn (hm6.1 z hzIz) hpt⟩
  filter_upwards [hpt, hnn] with θ h1 h2
  rwa [Real.norm_of_nonneg h2]

theorem rhoV2_z {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hm6 : Work.Spaces.HkMem α 6 f)
    {a b : ℕ} {ρ : ℝ → ℝ → ℝ} (hleaf : Work.FTS.TransportS.IsLeafW α a ρ)
    (hab : a + b ≤ 6) :
    MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ, ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2)
        Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2) ≤ Work.Spaces.HkSq α 6 f := by
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => ρ p.1 p.2 * (Work.Spaces.mixed b a f p.1 p.2) ^ 2)
      Work.FTS.EllipticEst.Q0 :=
    (continuousOn_leaf hleaf).mul (((hso.mixed b a).continuousOn).pow 2)
  have haesm : AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2)
      (volume.restrict Work.Spaces.Iz) :=
    (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).integral_prod_right'
  have hle : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ := by
    filter_upwards [Work.FTS.StrongPersist.H6Pair6Aux.ae_restrict_Iz_of_pos
      (fun z hz => hz)] with z hz
    exact (rhoV2_slice hα hso hm6 hleaf hab hz).2
  have hnn : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      0 ≤ ∫ θ in Work.Spaces.Iθ, ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2 :=
    Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg_of_ae
      (ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
        mul_nonneg (leaf_nonneg_Iθ hleaf z θ hθ) (sq_nonneg _)))
  refine ⟨MeasureTheory.Integrable.mono' hm6.2 haesm ?_,
    MeasureTheory.integral_mono_of_nonneg hnn hm6.2 hle⟩
  filter_upwards [hle, hnn] with z h1 h2
  rwa [Real.norm_of_nonneg h2]


end Work.FTS.StrongPersist.H6Pair6Aux
