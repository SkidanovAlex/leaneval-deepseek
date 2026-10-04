import Mathlib
import Submission.Work.OddBound.polygonValue.balancing.Instances
import Submission.Work.OddBound.polygon.riemannianDist_eq_toReal
import Submission.Work.OddBound.longHomotopy.curveLength_toolkit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Riemannian distance is bounded by the length of a `C¹` curve on `[0,1]`

For a curve `γ : ℝ → M` that is `C¹` on the closed interval `[0,1]` and `0 ≤ a ≤ b ≤ 1`, the
Riemannian distance of the endpoints `γ a`, `γ b` is at most the Riemannian length
`curveLength γ a b` of the sub-curve.

The proof is the same as for `Work.OddBound.polygonValue.distLeLength` (which is stated for the
global smoothness exponent `∞`): `Manifold.riemannianEDist_le_pathELength` bounds the extended
distance by the manifold path length, `curveLength_toolkit` identifies the latter with the
`ENNReal.ofReal` of the Riemannian length, and `Work.OddBound.polygon.riemannianDist_eq_toReal`
converts the extended distance to `Submission.Distance.riemannianDist`; finally `toReal` is taken on
both sides (all quantities are finite and nonnegative).
-/

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set MeasureTheory

namespace Work.OddBound.polygonValue.balancing

theorem distLeCurveLengthOfContMDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I (WithTop.some (⊤ : ENat)) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I (WithTop.some (⊤ : ENat)) E
      (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {γ : ℝ → M} (hγ : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 γ (Set.Icc (0 : ℝ) 1))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Submission.Distance.riemannianDist (I := I) (γ a) (γ b)
      ≤ Submission.Length.curveLength (I := I) γ a b := by
  -- `γ` is `C¹` on the subinterval `Icc a b ⊆ Icc 0 1`.
  have hmono : ContMDiffOn 𝓘(ℝ) I 1 γ (Set.Icc a b) := hγ.mono (Set.Icc_subset_Icc ha hb)
  -- The extended Riemannian distance of the endpoints is at most the manifold path length.
  have hle := Manifold.riemannianEDist_le_pathELength (I := I) (γ := γ) (a := a) (b := b)
    (x := γ a) (y := γ b) hmono rfl rfl hab
  -- For a `C¹` curve the manifold path length is the `ofReal` of the Riemannian length.
  have hpl := (Work.OddBound.longHomotopy.curveLength_toolkit (I := I)
    (h := γ) (S := 1) hγ).2.2 a b ha hab hb
  rw [hpl] at hle
  -- Convert the distance on the left-hand side to the `toReal` of the extended distance.
  rw [Work.OddBound.polygon.riemannianDist_eq_toReal (I := I) (γ a) (γ b)]
  -- Take `toReal` on both sides of `hle`; the right-hand side is finite, and `ofReal` is nonneg.
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hle).trans
    (le_of_eq (ENNReal.toReal_ofReal (Submission.Length.curveLength_nonneg (I := I) γ hab)))

end Work.OddBound.polygonValue.balancing
