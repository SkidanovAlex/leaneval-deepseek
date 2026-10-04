import Mathlib
import Submission.Work.OddBound.LiftKit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.OddBound.longHomotopy

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open LeanEval.Geometry.SphereTheorem Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length Submission.InjRadius

/-- The velocity of the time-reflected curve `s ↦ c (b - s)` at `s` is the negative of the
velocity of `c` at `b - s`.  (Proved here from scratch, since the version in
`Submission.HopfRinow` carries `CompactSpace M` and a covariant derivative among its hypotheses.) -/
theorem curveVelocity_comp_sub_eq_neg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {c : ℝ → M} {b : ℝ} {s : ℝ}
    (hs : MDifferentiableAt 𝓘(ℝ) I c (b - s)) :
    Submission.Geodesic.curveVelocity (I := I) (fun s : ℝ => c (b - s)) s
      = -Submission.Geodesic.curveVelocity (I := I) c (b - s) := by
  have harg : (-1 : ℝ) * s + b = b - s := by ring
  have hfun : (fun s : ℝ => c ((-1 : ℝ) * s + b)) = (fun s : ℝ => c (b - s)) := by
    funext u; congr 1; ring
  have h := Submission.Length.curveVelocity_comp_mul_add (I := I) (γ := c) (c := -1) (d := b)
    (t := s) (by rw [harg]; exact hs)
  rw [hfun, harg] at h
  simpa using h

/-- The speed of the reversed curve `s ↦ c (b - s)` equals the speed of `c` at the reflected
time. -/
theorem curveSpeed_comp_sub_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {c : ℝ → M} {b : ℝ} {s : ℝ}
    (hs : MDifferentiableAt 𝓘(ℝ) I c (b - s)) :
    Submission.Length.curveSpeed (I := I) (fun s : ℝ => c (b - s)) s
      = Submission.Length.curveSpeed (I := I) c (b - s) := by
  rw [Submission.Length.curveSpeed_def, Submission.Length.curveSpeed_def,
    curveVelocity_comp_sub_eq_neg (I := I) hs, inner_neg_neg]

/-- **Reversing a curve preserves its length.**  If `c` is `C¹` on `[a,b]`, the length of
`s ↦ c (b - s)` over `[0, b - a]` equals the length of `c` over `[a,b]`. -/
theorem curveLength_comp_sub
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E]
    {c : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hc : ContMDiffOn 𝓘(ℝ) I 1 c (Set.Icc a b)) :
    Submission.Length.curveLength (I := I) (fun s : ℝ => c (b - s)) 0 (b - a)
      = Submission.Length.curveLength (I := I) c a b := by
  -- `c` is differentiable at every interior point of `[a,b]`
  have hmd : ∀ t ∈ Set.Ioo a b, MDifferentiableAt 𝓘(ℝ) I c t := by
    intro t ht
    exact ((hc t (Set.mem_Icc.2 ⟨ht.1.le, ht.2.le⟩)).contMDiffAt
      (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt one_ne_zero
  -- the speeds agree on the interior of the interval of integration
  have hspeed : ∀ s ∈ Set.Ioo 0 (b - a),
      Submission.Length.curveSpeed (I := I) (fun s : ℝ => c (b - s)) s
        = Submission.Length.curveSpeed (I := I) c (b - 1 * s) := by
    intro s hs
    obtain ⟨hs1, hs2⟩ := hs
    have hb : b - s ∈ Set.Ioo a b := ⟨by linarith, by linarith⟩
    rw [curveSpeed_comp_sub_eq (I := I) (hmd (b - s) hb),
      show b - s = b - 1 * s from by ring]
  have hcongr1 : (∫ s in 0..(b - a),
        Submission.Length.curveSpeed (I := I) (fun s : ℝ => c (b - s)) s)
      = ∫ s in 0..(b - a), Submission.Length.curveSpeed (I := I) c (b - 1 * s) :=
    intervalIntegral.integral_congr_Ioo_of_le (by linarith : (0:ℝ) ≤ b - a) hspeed
  -- the substitution `t = b - s` on the interval integral
  rw [Submission.Length.curveLength_def, Submission.Length.curveLength_def, hcongr1,
    intervalIntegral.integral_comp_sub_mul (f := Submission.Length.curveSpeed (I := I) c)
      one_ne_zero b]
  simp only [one_mul, inv_one, one_smul, sub_sub_cancel, sub_zero]

end Work.OddBound.longHomotopy
