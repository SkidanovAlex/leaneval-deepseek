import Mathlib
import Submission.Work.Diff.L.Defs
import Submission.Work.Diff.L.Stmt
import Submission.Work.Diff.T.lc_smooth
import Submission.Work.Diff.GE.scal_lapl
import Submission.Work.Diff.GE.exists_ON_frame_field_eq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `|∇ scal|² ≤ n² |∇Rm|²` uniformly in the metric

The gradient of the scalar curvature is the *contraction* `∑ᵢⱼ (∇ₘRm)_{ijij}` of the covariant
derivative of the curvature tensor, in the chosen orthonormal frame `onFrame g x`.  Unfolding the
frozen definitions (`Submission.Diff.gradSq`, `Submission.Diff.scalAt`, `Submission.Diff.dRmNormSq`)
this says, with `e := onFrame g x`,

`gradSq g (scalAt g) x = ∑ m, (∑ i, ∑ j, covRm g x (e m) (e i) (e j) (e i) (e j)) ^ 2`
and `dRmNormSq g x = ∑ m, ∑ i, ∑ j, ∑ k, ∑ l, covRm g x (e m) (e i) (e j) (e k) (e l) ^ 2`.

Cauchy–Schwarz on the `n²` terms of the inner contraction (`(∑ᵢⱼ aᵢⱼ)² ≤ n² ∑ᵢⱼ aᵢⱼ²`) and the
trivial bound `aᵢⱼ² ≤ ∑_{k,l} aᵢⱼₖₗ²` give

`gradSq g (scalAt g) x ≤ (finrank ℝ E)² * dRmNormSq g x`

for *every* smooth metric `g` and every point `x`.  So the existential constant of the statement is
`K = (finrank ℝ E)²`, positive because `finrank ℝ E ≥ 2`; neither compactness nor completeness of `M`
is used.

## The analytic input

`∇ₘ scal` is the trace of `∇Rm` in an orthonormal frame.  This is *not* immediate from the frozen
definitions, because `scalAt g y = scalAlg (rmFrame g y (onFrame g y))` is stated through the
`Classical.epsilon`-chosen frame `onFrame g y`, which is not a smooth field in `y`.  The proof:

* `Work.Diff.GE.exists_ON_frame_field_eq` produces a globally `C^∞` field of frames `Ef` which is
  `g`-orthonormal near `x` with `Ef i x = onFrame g x i`;
* `Work.Diff.GE.scalAt_eq_scalAlg_rmFrame_of_isONFrame` (frame independence of the trace) shows
  `scalAt g =ᶠ[𝓝 x] fun y ↦ scalAlg (rmFrame g y (fun i ↦ Ef i y))`;
* `Work.Diff.GE.mvfderiv_scalAlg_rmFrame_frame` (Leibniz rule for `Rm` in a smooth orthonormal
  frame field together with the cancellation of the frame-velocity corrections, via metric
  compatibility) computes the derivative of that function as the contraction of `∇Rm`;
* `Work.Diff.GE.mvfderiv_congr_of_eventuallyEq_real` transfers this to `mvfderiv I (scalAt g) x`.

The `LCSmooth I M` hypothesis needed by those lemmas is discharged by `Work.Diff.T.lc_smooth`
(area T1), which is proved and depends only on the standard axioms.
-/

namespace Work.Diff.L

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M] [I.Boundaryless] [T2Space M] [CompactSpace M]

/-! ## 1. The derivative of the scalar curvature in the chosen frame -/

/-- **`∇ scal` is the contraction of `∇Rm`** (in the `Classical.epsilon`-chosen frame
`onFrame g x`, the frame implicitly used by the frozen definitions). -/
theorem mvfderiv_scalAt_eq_sum (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (hn : 0 < Module.finrank ℝ E) (v : TangentSpace I x) :
    mvfderiv I (scalAt g) x v
      = ∑ i, ∑ j, covRm g x v (onFrame g x i) (onFrame g x j) (onFrame g x i)
          (onFrame g x j) := by
  obtain ⟨Ef, hEfx, hEfsm, hON⟩ :=
    Work.Diff.GE.exists_ON_frame_field_eq (I := I) (M := M) g x (onFrame g x)
      (Work.Diff.GE.isONFrame_onFrame g x)
  have hgerm : scalAt g =ᶠ[𝓝 x] (fun y : M ↦ scalAlg (rmFrame g y (fun i ↦ Ef i y))) := by
    filter_upwards [hON] with y hy
    exact Work.Diff.GE.scalAt_eq_scalAlg_rmFrame_of_isONFrame (I := I) (M := M) g hLC y
      (fun i ↦ Ef i y) hy
  rw [Work.Diff.GE.mvfderiv_congr_of_eventuallyEq_real (I := I) hgerm,
    Work.Diff.GE.mvfderiv_scalAlg_rmFrame_frame (I := I) (M := M) hLC g Ef hEfsm hON hn v]
  simp only [scalAlg, hEfx]

/-! ## 2. `gradSq` of the scalar curvature as a sum of contractions -/

/-- **`|∇ scal|²` is the sum of the squares of the contractions of `∇Rm`.** -/
theorem gradSq_scalAt_eq_sum (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (hn : 0 < Module.finrank ℝ E) :
    gradSq g (scalAt g) x
      = ∑ m, (∑ i, ∑ j, covRm g x (onFrame g x m) (onFrame g x i) (onFrame g x j)
          (onFrame g x i) (onFrame g x j)) ^ 2 := by
  simp only [gradSq]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [mvfderiv_scalAt_eq_sum (I := I) (M := M) hLC g x hn]

/-! ## 3. The elementary bound `(∑ᵢⱼ aᵢⱼ)² ≤ n² ∑ᵢⱼₖₗ aᵢⱼₖₗ²` for a curvature array -/

/-- Pulling a constant out of a double sum. -/
private theorem mul_sum_sum {ι κ : Type*} [Fintype ι] [Fintype κ] (c : ℝ) (f : ι → κ → ℝ) :
    c * ∑ i, ∑ j, f i j = ∑ i, c * ∑ j, f i j := by
  rw [Finset.mul_sum]

/-- Cauchy–Schwarz for a sum over a finite type, in the form used below. -/
private theorem sq_sum_le_card_mul_sum_sq_real {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    (∑ i, f i) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, f i ^ 2 := by
  simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := f)

/-- **The trace of a curvature array is controlled by its total square.**  For an array
`T : Fin N → Fin N → Fin N → Fin N → Fin N → ℝ` (only the *size* of the index type matters here),
the `N` traces `∑ᵢⱼ T m i j i j` of the slices satisfy
`∑ₘ (trace m)² ≤ N² ∑ₘ ∑ᵢⱼₖₗ (T m i j k l)²`. -/
theorem trace_sq_le_sum_sq {N : ℕ} (hN : 1 ≤ N)
    (T : Fin N → Fin N → Fin N → Fin N → Fin N → ℝ) :
    ∑ m, (∑ i, ∑ j, T m i j i j) ^ 2
      ≤ (N : ℝ) ^ 2 * ∑ m, ∑ i, ∑ j, ∑ k, ∑ l, (T m i j k l) ^ 2 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  -- Cauchy–Schwarz over `Fin N`
  have key : ∀ f : Fin N → ℝ, (∑ i, f i) ^ 2 ≤ (N : ℝ) * ∑ i, f i ^ 2 := by
    intro f
    simpa using sq_sum_le_card_mul_sum_sq_real f
  -- a single contraction is bounded by the corresponding block of squares
  have hpair : ∀ m i j, (T m i j i j) ^ 2 ≤ ∑ k, ∑ l, (T m i j k l) ^ 2 := by
    intro m i j
    have h1 : (T m i j i j) ^ 2 ≤ ∑ l, (T m i j i l) ^ 2 :=
      Finset.single_le_sum (f := fun l => (T m i j i l) ^ 2)
        (fun l _ => sq_nonneg _) (Finset.mem_univ j)
    have h2 : (∑ l, (T m i j i l) ^ 2) ≤ ∑ k, ∑ l, (T m i j k l) ^ 2 :=
      Finset.single_le_sum (f := fun k => ∑ l, (T m i j k l) ^ 2)
        (fun k _ => Finset.sum_nonneg (fun l _ => sq_nonneg _)) (Finset.mem_univ i)
    linarith
  have hstep : ∀ m, (∑ i, ∑ j, T m i j i j) ^ 2
      ≤ (N : ℝ) ^ 2 * ∑ i, ∑ j, ∑ k, ∑ l, (T m i j k l) ^ 2 := by
    intro m
    have hinner : ∀ i, (∑ j, T m i j i j) ^ 2 ≤ (N : ℝ) * ∑ j, (T m i j i j) ^ 2 :=
      fun i => key (fun j => T m i j i j)
    have houter : (∑ i, (∑ j, T m i j i j)) ^ 2
        ≤ (N : ℝ) * ∑ i, (∑ j, T m i j i j) ^ 2 := key (fun i => ∑ j, T m i j i j)
    have hsum : (∑ i, ∑ j, (T m i j i j) ^ 2) ≤ ∑ i, ∑ j, ∑ k, ∑ l, (T m i j k l) ^ 2 :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpair m i j))
    calc (∑ i, ∑ j, T m i j i j) ^ 2
        ≤ (N : ℝ) * ∑ i, (∑ j, T m i j i j) ^ 2 := houter
      _ ≤ (N : ℝ) * ∑ i, ((N : ℝ) * ∑ j, (T m i j i j) ^ 2) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hinner i)) (le_of_lt hNpos)
      _ = (N : ℝ) ^ 2 * ∑ i, ∑ j, (T m i j i j) ^ 2 := by
            rw [mul_sum_sum]
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun i _ => by ring)
      _ ≤ (N : ℝ) ^ 2 * ∑ i, ∑ j, ∑ k, ∑ l, (T m i j k l) ^ 2 :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
  calc ∑ m, (∑ i, ∑ j, T m i j i j) ^ 2
      ≤ ∑ m, (N : ℝ) ^ 2 * (∑ i, ∑ j, ∑ k, ∑ l, (T m i j k l) ^ 2) :=
        Finset.sum_le_sum (fun m _ => hstep m)
    _ = (N : ℝ) ^ 2 * ∑ m, ∑ i, ∑ j, ∑ k, ∑ l, (T m i j k l) ^ 2 := by
        rw [Finset.mul_sum]

/-! ## 4. The uniform bound -/

/-- **`|∇ scal|² ≤ n² |∇Rm|²` for every smooth metric, with `n = finrank ℝ E`.** -/
theorem gradSq_scalAt_le_dRmNormSq (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (hdim : 2 ≤ Module.finrank ℝ E) :
    gradSq g (scalAt g) x ≤ (Module.finrank ℝ E : ℝ) ^ 2 * dRmNormSq g x := by
  have hn : 0 < Module.finrank ℝ E := by omega
  have hN : 1 ≤ Module.finrank ℝ E := by omega
  rw [gradSq_scalAt_eq_sum (I := I) (M := M) hLC g x hn]
  have hD : dRmNormSq g x
      = ∑ m, ∑ i, ∑ j, ∑ k, ∑ l, (covRm g x (onFrame g x m) (onFrame g x i)
          (onFrame g x j) (onFrame g x k) (onFrame g x l)) ^ 2 := rfl
  rw [hD]
  exact trace_sq_le_sum_sq hN
    (fun m i j k l => covRm g x (onFrame g x m) (onFrame g x i) (onFrame g x j)
      (onFrame g x k) (onFrame g x l))

theorem gradSq_le_dRmNormSq_v3
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M] [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hdim : 2 ≤ Module.finrank ℝ E) :
    ∃ K : ℝ, 0 < K ∧ ∀ (g : Submission.Diff.SMet I M) (x : M),
      Submission.Diff.gradSq g (Submission.Diff.scalAt g) x
        ≤ K * Submission.Diff.dRmNormSq g x := by
  have hLC : LCSmooth I M := Work.Diff.T.lc_smooth (I := I) (M := M)
  have hNpos : (0 : ℝ) < (Module.finrank ℝ E : ℝ) := by
    have h : 0 < Module.finrank ℝ E := by omega
    exact_mod_cast h
  exact ⟨(Module.finrank ℝ E : ℝ) ^ 2, pow_pos hNpos 2,
    fun g x => gradSq_scalAt_le_dRmNormSq (I := I) (M := M) hLC g x hdim⟩

end Work.Diff.L
