import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.AngSecond.Defs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest.AesmCross

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false

/-! ## Continuity of the two weights on the open quadrant

The point of these two elementary lemmas is that they are *local to the open quadrant*: the
radial weight `w2 z = ((1+z)²/z²)²` is continuous wherever `z ≠ 0`, and the angular weight
`sig θ = sin(2θ)^{-η}` is continuous wherever `sin(2θ) ≠ 0`; both conditions hold on
`Q0 = (0,∞) × (0,π/2)`.  Nothing is asserted on the boundary `z = 0` or `θ ∈ {0, π/2}`,
which is all that is needed since that boundary is null. -/

/-- The radial factor `w2 z = w z ^ 2` of the weight is continuous on the open quadrant. -/
lemma continuousOn_w2_quadrant :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AngSecond.w2 p.1)
      Work.FTS.EllipticEst.Q0 := by
  have hfun : (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AngSecond.w2 p.1)
      = fun p : ℝ × ℝ => (((1 + p.1) ^ 2 / p.1 ^ 2) ^ 2) := by
    funext p
    rw [Work.FTS.EllipticEst.AngSecond.w2, Work.Spaces.w]
  rw [hfun]
  refine ContinuousOn.pow ?_ 2
  exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2)
    (fun p hp => pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1))

/-- The angular factor `sig θ = sin(2θ)^{-η}` of the weight is continuous on the open
quadrant. -/
lemma continuousOn_sig_quadrant :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AngSecond.sig p.2)
      Work.FTS.EllipticEst.Q0 := by
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hfun : (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AngSecond.sig p.2)
      = fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) := by
    funext p
    rw [Work.FTS.EllipticEst.AngSecond.sig]
  rw [hfun]
  exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))

/-- **The product of two functions, each of which agrees on the open quadrant with a smooth
function, is a.e. strongly measurable** for the product of the restrictions of Lebesgue
measure to `Iz = [0,∞)` and `Iθ = [0,π/2]`.

Indeed, on the open quadrant the product `g · h` coincides with the product `g' · h'` of the
two smooth representatives, and `g' h' w2 σ` is continuous there (the two weights being
continuous on the quadrant, so that no boundary behaviour of `w2` at `z = 0` or of `σ` at
`θ = 0, π/2` is ever used); the complement of the open quadrant inside `Iz ×ˢ Iθ` is
contained in the three coordinate hyperplanes and hence is null. -/
theorem aesmProdCross {g h g' h' : ℝ → ℝ → ℝ} (hg' : Work.FTS.EllipticEst.SmoothOpen g')
    (hh' : Work.FTS.EllipticEst.SmoothOpen h')
    (hgg : Work.FTS.EllipticEst.AgreeOnQ g g') (hhh : Work.FTS.EllipticEst.AgreeOnQ h h') :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => g p.1 p.2 * h p.1 p.2 * Work.FTS.EllipticEst.AngSecond.w2 p.1
        * Work.FTS.EllipticEst.AngSecond.sig p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  -- `Iz` and `Iθ` agree a.e. with the open half-line and the open interval, so the product of
  -- the restricted measures is the restriction of the planar Lebesgue measure to the quadrant.
  have hz : Work.Spaces.Iz =ᵐ[MeasureTheory.volume] Set.Ioi (0 : ℝ) :=
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm
  have hθ : Work.Spaces.Iθ =ᵐ[MeasureTheory.volume] Set.Ioo (0 : ℝ) (π / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0) (b := π / 2)).symm
  have hprod : (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ))
      =ᵐ[MeasureTheory.volume.prod MeasureTheory.volume] Work.FTS.EllipticEst.Q0 :=
    MeasureTheory.Measure.set_prod_ae_eq hz hθ
  have hμ : (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      = (MeasureTheory.volume.prod MeasureTheory.volume).restrict Work.FTS.EllipticEst.Q0 := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact MeasureTheory.Measure.restrict_congr_set hprod
  rw [hμ]
  -- The smooth representative is continuous on the open quadrant, hence a.e. strongly measurable.
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => g' p.1 p.2 * h' p.1 p.2 * Work.FTS.EllipticEst.AngSecond.w2 p.1
        * Work.FTS.EllipticEst.AngSecond.sig p.2) Work.FTS.EllipticEst.Q0 :=
    ((hg'.continuousOn.mul hh'.continuousOn).mul continuousOn_w2_quadrant).mul
      continuousOn_sig_quadrant
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => g' p.1 p.2 * h' p.1 p.2 * Work.FTS.EllipticEst.AngSecond.w2 p.1
        * Work.FTS.EllipticEst.AngSecond.sig p.2)
      ((MeasureTheory.volume.prod MeasureTheory.volume).restrict Work.FTS.EllipticEst.Q0) := by
    rw [← hμ]
    exact Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  -- Transfer along the a.e. equality on the (conull) open quadrant.
  refine haesm.congr ?_
  refine (MeasureTheory.ae_restrict_iff' (μ := MeasureTheory.volume.prod MeasureTheory.volume)
    (s := Work.FTS.EllipticEst.Q0) Work.FTS.EllipticEst.isOpen_Q0.measurableSet).mpr ?_
  refine Eventually.of_forall fun p hp => ?_
  obtain ⟨hz0, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  show g' p.1 p.2 * h' p.1 p.2 * Work.FTS.EllipticEst.AngSecond.w2 p.1
      * Work.FTS.EllipticEst.AngSecond.sig p.2
    = g p.1 p.2 * h p.1 p.2 * Work.FTS.EllipticEst.AngSecond.w2 p.1
      * Work.FTS.EllipticEst.AngSecond.sig p.2
  rw [hgg p.1 p.2 hz0 hθ0 hθ1, hhh p.1 p.2 hz0 hθ0 hθ1]

end Work.FTS.EllipticEst.Honest.AesmCross
