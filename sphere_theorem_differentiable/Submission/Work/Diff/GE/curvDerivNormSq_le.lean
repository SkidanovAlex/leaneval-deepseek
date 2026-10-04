import Mathlib
import Submission.Work.Diff.GE.CurvDerivDefs
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.covRm_linear_thd
import Submission.Work.Diff.GE.covRm_linear_fth
import Submission.Work.Diff.GE.kato_cov3RmExt_field
import Submission.Work.Diff.GE.curvDerivInner
import Submission.Work.Diff.GE.rmP_norm_bound
import Submission.Work.Diff.GE.covRm_expand_four
import Submission.Work.Diff.GE.dRmNormSq_eq_sum_slots

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The pointwise bound `|(∇_X R)(Y,P)Z|² ≤ |∇Rm|² |X|²|Y|²|P|²|Z|²`

`Work.Diff.GE.curvDeriv g x X Y P Z` is the vector `(∇_X R)(Y,P)Z` of the covariant derivative of
the curvature, defined as the frame expansion `∑ k, covRm g x X Y P eₖ Z • eₖ` in the chosen
`g`-orthonormal frame `e = onFrame g x`.  This module proves the pointwise norm bound that is
needed to estimate `|∇Rm|²` against `|∇Rm|²` itself (Hamilton's gradient estimate).

The proof has four steps, all pointwise, all in the orthonormal frame `e = onFrame g x`:

1. **Parseval + duality.**  `⟪(∇_X R)(Y,P)Z, ·⟫ = (∇_X Rm)(Y,P,·,Z)` (`curvDerivInner`), so
   Parseval in the orthonormal frame gives
   `⟪(∇_X R)(Y,P)Z, (∇_X R)(Y,P)Z⟫ = ∑ k, (covRm X Y P eₖ Z)²`.

2. **Frame expansion.**  `∇Rm` is a `(0,5)`-tensor, so each component expands as
   `covRm X Y P eₖ Z = ∑ i j l m, αᵢβⱼγₗδ_m · covRm eᵢ eⱼ eₗ eₖ e_m`
   where `α, β, γ, δ` are the frame coefficients of `X, Y, P, Z`
   (`Work.Diff.GE.covRm_expand_four`).

3. **Cauchy–Schwarz.**  The four-fold contraction of the *rank one* coefficient tensor
   `αᵢβⱼγₗδ_m` with the array `covRm eᵢ eⱼ eₗ eₖ e_m` is bounded by the product of the `ℓ²` norms
   (`Work.Diff.GE.sum4_coeff_sq_le`), and Parseval turns those into `⟪X,X⟫, ⟪Y,Y⟫, ⟪P,P⟫, ⟪Z,Z⟫`.

4. **Sum over `k`.**  Summing the resulting inequality over the *middle* index `k` produces
   `∑ k ∑ i ∑ j ∑ l ∑ m (covRm eᵢ eⱼ eₗ eₖ e_m)²`, which is `|∇Rm|²` by definition of
   `dRmNormSq` up to a permutation of the (dummy) frame indices
   (`Work.Diff.GE.dRmNormSq_eq_sum_slots`).  Crucially the summation index `k` is *shared* between
   the squared component and the `|∇Rm|²` on the right, so no dimension factor is lost.

The case `finrank ℝ E = 0` is degenerate: tangent spaces are subsingletons and both sides vanish.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

theorem curvDerivNormSq_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (X Y P Z : TangentSpace I x) :
    g.inner x (Work.Diff.GE.curvDeriv g x X Y P Z) (Work.Diff.GE.curvDeriv g x X Y P Z)
      ≤ Submission.Diff.dRmNormSq g x * (g.inner x X X) * (g.inner x Y Y)
        * (g.inner x P P) * (g.inner x Z Z) := by
  by_cases hn : 0 < Module.finrank ℝ E
  · -- Step 1: Parseval in the orthonormal frame `e = onFrame g x`.
    have hLHS : g.inner x (Work.Diff.GE.curvDeriv g x X Y P Z)
          (Work.Diff.GE.curvDeriv g x X Y P Z)
        = ∑ k, (Submission.Diff.covRm g x X Y P (Submission.Diff.onFrame g x k) Z) ^ 2 := by
      rw [← Work.Diff.GE.onFrame_parseval_sq g x hn (Work.Diff.GE.curvDeriv g x X Y P Z)]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [g.symm x (Submission.Diff.onFrame g x k) (Work.Diff.GE.curvDeriv g x X Y P Z),
        Work.Diff.GE.curvDerivInner hLC g x X Y P Z (Submission.Diff.onFrame g x k)]
    -- Steps 2 and 3: frame expansion of each component plus Cauchy–Schwarz.
    have hkey : ∀ k, (Submission.Diff.covRm g x X Y P (Submission.Diff.onFrame g x k) Z) ^ 2
        ≤ ((g.inner x X X) * (g.inner x Y Y) * (g.inner x P P) * (g.inner x Z Z)) *
          (∑ i, ∑ j, ∑ l, ∑ m,
            (Submission.Diff.covRm g x (Submission.Diff.onFrame g x i)
              (Submission.Diff.onFrame g x j) (Submission.Diff.onFrame g x l)
              (Submission.Diff.onFrame g x k) (Submission.Diff.onFrame g x m)) ^ 2) := by
      intro k
      -- expansion of `∇Rm` in the orthonormal frame `onFrame g x`
      have hexp : Submission.Diff.covRm g x X Y P (Submission.Diff.onFrame g x k) Z
          = ∑ i, ∑ j, ∑ l, ∑ m,
              ((g.inner x (Submission.Diff.onFrame g x i) X)
                * (g.inner x (Submission.Diff.onFrame g x j) Y)
                * (g.inner x (Submission.Diff.onFrame g x l) P)
                * (g.inner x (Submission.Diff.onFrame g x m) Z))
              * Submission.Diff.covRm g x (Submission.Diff.onFrame g x i)
                (Submission.Diff.onFrame g x j) (Submission.Diff.onFrame g x l)
                (Submission.Diff.onFrame g x k) (Submission.Diff.onFrame g x m) := by
        conv_lhs =>
          rw [← Work.Diff.GE.sum_inner_smul_eq_self g x hn (Submission.Diff.onFrame g x)
                (Work.Diff.GE.isONFrame_onFrame g x) X,
              ← Work.Diff.GE.sum_inner_smul_eq_self g x hn (Submission.Diff.onFrame g x)
                (Work.Diff.GE.isONFrame_onFrame g x) Y,
              ← Work.Diff.GE.sum_inner_smul_eq_self g x hn (Submission.Diff.onFrame g x)
                (Work.Diff.GE.isONFrame_onFrame g x) P,
              ← Work.Diff.GE.sum_inner_smul_eq_self g x hn (Submission.Diff.onFrame g x)
                (Work.Diff.GE.isONFrame_onFrame g x) Z]
        exact covRm_expand_four hLC g x (Submission.Diff.onFrame g x) _ _ _ _ k
      rw [hexp]
      -- Cauchy–Schwarz for the rank-one coefficient tensor, then Parseval
      have hcs := Work.Diff.GE.sum4_coeff_sq_le
        (A := fun i j l m => Submission.Diff.covRm g x (Submission.Diff.onFrame g x i)
          (Submission.Diff.onFrame g x j) (Submission.Diff.onFrame g x l)
          (Submission.Diff.onFrame g x k) (Submission.Diff.onFrame g x m))
        (fun i => g.inner x (Submission.Diff.onFrame g x i) X)
        (fun j => g.inner x (Submission.Diff.onFrame g x j) Y)
        (fun l => g.inner x (Submission.Diff.onFrame g x l) P)
        (fun m => g.inner x (Submission.Diff.onFrame g x m) Z)
      rw [Work.Diff.GE.onFrame_parseval_sq g x hn X, Work.Diff.GE.onFrame_parseval_sq g x hn Y,
        Work.Diff.GE.onFrame_parseval_sq g x hn P,
        Work.Diff.GE.onFrame_parseval_sq g x hn Z] at hcs
      exact le_trans hcs (le_of_eq (by ring))
    -- Step 4: sum over `k` and identify the result with `dRmNormSq`.
    calc g.inner x (Work.Diff.GE.curvDeriv g x X Y P Z) (Work.Diff.GE.curvDeriv g x X Y P Z)
        = ∑ k, (Submission.Diff.covRm g x X Y P (Submission.Diff.onFrame g x k) Z) ^ 2 := hLHS
      _ ≤ ∑ k, ((g.inner x X X) * (g.inner x Y Y) * (g.inner x P P) * (g.inner x Z Z)) *
            (∑ i, ∑ j, ∑ l, ∑ m,
              (Submission.Diff.covRm g x (Submission.Diff.onFrame g x i)
                (Submission.Diff.onFrame g x j) (Submission.Diff.onFrame g x l)
                (Submission.Diff.onFrame g x k) (Submission.Diff.onFrame g x m)) ^ 2) :=
          Finset.sum_le_sum (fun k _ => hkey k)
      _ = ((g.inner x X X) * (g.inner x Y Y) * (g.inner x P P) * (g.inner x Z Z)) *
            ∑ k, (∑ i, ∑ j, ∑ l, ∑ m,
              (Submission.Diff.covRm g x (Submission.Diff.onFrame g x i)
                (Submission.Diff.onFrame g x j) (Submission.Diff.onFrame g x l)
                (Submission.Diff.onFrame g x k) (Submission.Diff.onFrame g x m)) ^ 2) := by
          rw [Finset.mul_sum]
      _ = ((g.inner x X X) * (g.inner x Y Y) * (g.inner x P P) * (g.inner x Z Z)) *
            Submission.Diff.dRmNormSq g x := by rw [dRmNormSq_eq_sum_slots]
      _ = Submission.Diff.dRmNormSq g x * (g.inner x X X) * (g.inner x Y Y)
            * (g.inner x P P) * (g.inner x Z Z) := by ring
  · -- degenerate case: `finrank ℝ E = 0`, so all tangent spaces are subsingletons
    have h0 : Module.finrank ℝ E = 0 := Nat.eq_zero_of_not_pos hn
    haveI hE : Subsingleton E := Module.finrank_zero_iff.mp h0
    haveI hT : Subsingleton (TangentSpace I x) := hE
    have hv0 : Work.Diff.GE.curvDeriv g x X Y P Z = 0 := Subsingleton.elim _ _
    have hX0 : X = 0 := Subsingleton.elim X 0
    have hY0 : Y = 0 := Subsingleton.elim Y 0
    have hP0 : P = 0 := Subsingleton.elim P 0
    have hZ0 : Z = 0 := Subsingleton.elim Z 0
    rw [hv0, hX0, hY0, hP0, hZ0]
    simp

end Work.Diff.GE
