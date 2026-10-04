import Mathlib
import Submission.Work.Diff.GE.CurvDerivDefs
import Submission.Work.Diff.GE.kato_cov3RmExt_field
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.covRm_linear_thd
import Submission.Work.Diff.GE.covRm_linear_fth
import Submission.Work.Diff.GE.Kato3.CovRmKit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `curvDerivInner`: the vector `(∇_X R)(Y,P)Z` is the `g`-dual of `(∇_X Rm)(Y,P,·,Z)`

The frozen `curvDeriv g x X Y P Z` is defined as the frame expansion
`∑ k, covRm g x X Y P (onFrame g x k) Z • onFrame g x k` of the vector `(∇_X R)(Y,P)Z`.
This file proves that it is exactly the `g`-dual of the `(0,5)`-tensor `∇Rm`:

`g.inner x (curvDeriv g x X Y P Z) Z' = covRm g x X Y P Z' Z`.

The content is the standard one: `g.inner x` is a continuous linear map in its first
argument, so the left hand side is `∑ k covRm g x X Y P e_k Z * ⟪e_k, Z'⟫`; expanding `Z'` in
the orthonormal frame `e = onFrame g x` and using the `ℝ`-linearity of `covRm` in its fourth
argument turns the right hand side into `∑ k ⟪e_k, Z'⟫ * covRm g x X Y P e_k Z`, and the two
sums agree termwise.  The frame expansion holds in every dimension (`frame_expand_curvDeriv`:
for `finrank = 0` the space is a subsingleton and the sum is empty).
-/

set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

section Helpers

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
  [T2Space M]

/-- Expansion of a tangent vector in the chosen orthonormal frame `onFrame g x`, valid also
in dimension zero (where `TangentSpace I x` is a subsingleton and the frame is empty). -/
theorem frame_expand_curvDeriv (g : Submission.Diff.SMet I M) (x : M)
    (v : TangentSpace I x) :
    ∑ i, g.inner x (onFrame g x i) v • onFrame g x i = v := by
  by_cases hpos : 0 < Module.finrank ℝ E
  · exact sum_inner_smul_eq_self (I := I) (M := M) g x hpos (onFrame g x)
      (isONFrame_onFrame (I := I) (M := M) g x) v
  · have h0 : Module.finrank ℝ E = 0 := Nat.eq_zero_of_not_pos hpos
    haveI hsubE : Subsingleton E := Module.finrank_zero_iff.mp h0
    haveI hsubT : Subsingleton (TangentSpace I x) := hsubE
    rw [Subsingleton.elim v 0]
    apply Finset.sum_eq_zero
    intro i _
    exact absurd (h0 ▸ i.isLt) (Nat.not_lt_zero i.val)

/-- `covRm` is additive over finite linear combinations in its fourth argument. -/
theorem covRm_sum_fourth_aux (hLC : Submission.Diff.LCSmooth I M)
    (g : Submission.Diff.SMet I M) (x : M) (v a b d : TangentSpace I x) {ι : Type*}
    (s : Finset ι) (c : ι → ℝ) (w : ι → TangentSpace I x) :
    Submission.Diff.covRm g x v a b (∑ i ∈ s, c i • w i) d
      = ∑ i ∈ s, c i * Submission.Diff.covRm g x v a b (w i) d := by
  classical
  induction s using Finset.induction with
  | empty =>
      have h := covRm_linear_fth (I := I) (M := M) hLC g x v a b (0 : ℝ) (0 : ℝ)
        (0 : TangentSpace I x) (0 : TangentSpace I x) d
      simpa using h
  | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj]
      have h := covRm_linear_fth (I := I) (M := M) hLC g x v a b (c j) (1 : ℝ) (w j)
        (∑ i ∈ s, c i • w i) d
      rw [one_smul] at h
      rw [h, ih]
      ring

end Helpers

theorem curvDerivInner
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (X Y P Z Z' : TangentSpace I x) :
    g.inner x (Work.Diff.GE.curvDeriv g x X Y P Z) Z'
      = Submission.Diff.covRm g x X Y P Z' Z := by
  rw [curvDeriv]
  rw [map_sum]
  simp only [sum_apply, map_smul, smul_apply, smul_eq_mul]
  conv_rhs => rw [← frame_expand_curvDeriv (I := I) (M := M) g x Z']
  rw [covRm_sum_fourth_aux (I := I) (M := M) hLC g x X Y P Z Finset.univ
    (fun i => g.inner x (onFrame g x i) Z') (onFrame g x)]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end Work.Diff.GE
