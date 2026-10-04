import Mathlib
import Submission.Work.OddBound.LiftKit
import Submission.Work.OddBound.polygon.riemannianDist_eq_toReal
import Submission.Work.OddBound.polygonValue.balancing.Instances
import Submission.Work.OddBound.liftPiecewise.exists_lift_of_piecewise_short

set_option backward.isDefEq.respectTransparency.types false

/-!
# The Riemannian distance is bounded by the length of a `C¹` curve on an interval `[α,β]`

`Submission.Work.OddBound.polygonValue.distLeLength` proves `d(h a, h b) ≤ curveLength h a b` for a
curve `h` of class `C¹` on the fixed interval `[0,1]`.  The piecewise-length toolkit
(`Work.OddBound.liftPiecewise`) needs the same statement for a curve that is `C¹` only on a
*piece* `[α,β]` of a partition, so we prove here the general-interval version.

The proof is the same as in `distLeLength`: `Manifold.riemannianEDist_le_pathELength` bounds the
extended distance by the manifold path length, `intervalIntegrable_curveSpeed_of_contMDiffOn_Icc`
supplies the integrability of the speed on `[c,d] ⊆ [α,β]`, the commons lemma
`pathELength_eq_ofReal_integral_of_enorm_eq_nonneg` identifies `pathELength` with the `ENNReal.ofReal`
of the Riemannian length, and `Work.OddBound.polygon.riemannianDist_eq_toReal` converts the extended
distance into `Submission.Distance.riemannianDist`; finally `toReal` is taken on both sides.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set MeasureTheory
open scoped MeasureTheory Interval

namespace Work.OddBound.piecewiseDist

/-- **The Riemannian distance is bounded by the length of a `C¹` curve on a general interval.**
If `h` is of class `C¹` on `Icc α β` and `α ≤ c ≤ d ≤ β`, then
`d(h c, h d) ≤ curveLength h c d`. -/
theorem dist_le_curveLength_of_contMDiffOn_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I (WithTop.some (⊤ : ENat)) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I (WithTop.some (⊤ : ENat)) E
      (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {h : ℝ → M} {α β : ℝ} (hαβ : α ≤ β)
    (hh : ContMDiffOn 𝓘(ℝ) I 1 h (Set.Icc α β))
    {c d : ℝ} (hc : α ≤ c) (hcd : c ≤ d) (hd : d ≤ β) :
    Submission.Distance.riemannianDist (I := I) (h c) (h d)
      ≤ Submission.Length.curveLength (I := I) h c d := by
  rcases lt_or_eq_of_le hαβ with hlt | heq
  · have hmono : ContMDiffOn 𝓘(ℝ) I 1 h (Set.Icc c d) := hh.mono (Set.Icc_subset_Icc hc hd)
    have hint : IntervalIntegrable (Submission.Length.curveSpeed (I := I) h) MeasureTheory.volume
        c d :=
      Work.OddBound.liftPiecewise.intervalIntegrable_curveSpeed_of_contMDiffOn_Icc
        hlt hh c d hc hcd hd
    have hle := Manifold.riemannianEDist_le_pathELength (I := I) (γ := h) (a := c) (b := d)
      (x := h c) (y := h d) hmono rfl rfl hcd
    have hpl : Manifold.pathELength I h c d
        = ENNReal.ofReal (Submission.Length.curveLength (I := I) h c d) := by
      rw [Submission.Length.curveLength_def]
      refine Commons.Geometry.Manifold.pathELength_eq_ofReal_integral_of_enorm_eq_nonneg
        (I := I) (γ := h) (a := c) (b := d)
        (f := fun t : ℝ => Submission.Length.curveSpeed (I := I) h t)
        hcd ((intervalIntegrable_iff_integrableOn_Icc_of_le hcd).mp hint)
        (fun t _ => Submission.Length.curveSpeed_nonneg (I := I) h t) ?_
      intro t ht
      show ‖(mfderiv 𝓘(ℝ) I h t) (1 : ℝ)‖ₑ
        = ENNReal.ofReal (Submission.Length.curveSpeed (I := I) h t)
      rw [Submission.Minimal.enorm_eq_ofReal_norm, Submission.GeodesicSpeed.curveSpeed_eq_norm,
        Submission.Geodesic.curveVelocity_apply]
    rw [hpl] at hle
    rw [Work.OddBound.polygon.riemannianDist_eq_toReal (I := I) (h c) (h d)]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hle).trans
      (le_of_eq (ENNReal.toReal_ofReal (Submission.Length.curveLength_nonneg (I := I) h hcd)))
  · have hd' : d ≤ α := heq.symm ▸ hd
    have hce : c = α := le_antisymm (le_trans hcd hd') hc
    have hde : d = α := le_antisymm hd' (le_trans hc hcd)
    subst hce; subst hde
    rw [Submission.Distance.riemannianDist_self, Submission.Length.curveLength_self]

end Work.OddBound.piecewiseDist
