import Mathlib
import Submission.Work.Diff.EXT.towerReactDefs
import Submission.Work.Diff.EXT.reactDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

/-!
# The reaction `R_k` traced in a frame *field*, with a one-sided time derivative

`Submission/Work/Diff/EXT/towerReactDefs.lean` explains why the reaction must be traced in a frame
*field* `Ef` which is smooth and orthonormal on a **neighbourhood** of the base point `x`
(`Work.Diff.EXT.IsFrameNear`): tracing in the ε-chosen extensions of a frame of `TₓM` gives the
honest value at `x` but not the honest *jets*, and the defect carries the uncontrolled derivatives
`∇_v (smoothExt x (onFrame (G t) x m))`.  With an `Ef` orthonormal near `x` the operator
`Work.Diff.EXT.reactOpEf` agrees with the honest reaction near `x`, so its `jetAll`-jets are the
honest jets `∇^j R_k` (independent of `Ef`).

This module makes one further change, needed because the target `Work.Diff.EXT.EvolCompKFixReact k`
is stated for `t ∈ Set.Ico 0 T`, i.e. *including* `t = 0`, where `IsRicciFlow G T` only controls
`G` on `[0, T)`: the time derivative is taken with `derivWithin … (Set.Ioi 0)` instead of `deriv`.
On `(0, T)` the two agree (`derivWithin_of_mem_nhds`, since `Ioi 0 ∈ 𝓝 t` for `t > 0`), while at
`t = 0` the two-sided `deriv` is junk (the family is not controlled for `s < 0`) whereas the
one-sided derivative is exactly what the target's `HasDerivWithinAt … (Set.Ico 0 T) 0` asks for.

The ladder invariant `LadderEfD G t x Ef k j C` is `Work.Diff.EXT.LadderForm` with this operator.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- **The reaction operator, traced in the frame field `Ef`, with a one-sided time derivative**:
`R_k = ∂ₜ⁺(∇^k Rm) − ∑_m ∇_{Ef m}∇_{Ef m}(∇^k Rm)`.  For `Ef` smooth and orthonormal near `x`
this agrees with the honest reaction `∂ₜ(∇^k Rm) − Δ(∇^k Rm)` near `x`. -/
noncomputable def reactOpEfD [T2Space M]
    (Ef : Fin (Module.finrank ℝ E) → TField (I := I) (M := M))
    (G : ℝ → SMet I M) (t : ℝ) (k : ℕ) :
    (Fin (k + 4) → TField (I := I) (M := M)) → M → ℝ :=
  fun F y =>
    derivWithin (fun s => ckt (G s) k F y) (Set.Ioi 0) t
      - ∑ m : Fin (Module.finrank ℝ E),
          ckt (G t) (k + 2) (Fin.cons (Ef m) (Fin.cons (Ef m) F)) y

/-- **The ladder invariant of the reaction at level `k` and jet order `j`**, with the reaction
traced in the frame field `Ef`.  `LadderEfD G t x Ef k j C` says: `0 ≤ C` and, for every `N` with
`N = k + 4 + j` and every tuple `w : Fin N → TₓM`, the `j`-th covariant derivative of the level-`k`
reaction at `x`, evaluated on the smooth extensions of the entries of `w`, is bounded by
`C · Shape (G t) x (k+j)` times the product of the metric norms of the entries.

The tuple is carried as `w : Fin N` together with `N = k + 4 + j` so that the two sides of the
recursion `(k+1, j) ← (k, j+1)` — which have the same total length `k + 5 + j` but different
summands — can be compared on one tuple. -/
def LadderEfD [T2Space M] (G : ℝ → SMet I M) (t : ℝ) (x : M)
    (Ef : Fin (Module.finrank ℝ E) → TField (I := I) (M := M)) (k j : ℕ) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ (N : ℕ) (hN : N = k + 4 + j) (w : Fin N → TangentSpace I x),
    |jetAll (G t) j (k + 4) (reactOpEfD (I := I) (M := M) Ef G t k)
        (fun r : Fin (k + 4 + j) => smoothExt x (w (Fin.cast hN.symm r))) x|
      ≤ C * Shape (G t) x (k + j)
          * Finset.univ.prod (fun r : Fin N => Real.sqrt ((G t).inner x (w r) (w r)))

/-- **Monotonicity of `LadderEfD` in the constant.** -/
theorem LadderEfD_mono [T2Space M] {G : ℝ → SMet I M} {t : ℝ} {x : M}
    {Ef : Fin (Module.finrank ℝ E) → TField (I := I) (M := M)} {k j : ℕ} {C C' : ℝ}
    (h : LadderEfD G t x Ef k j C) (hCC' : C ≤ C') : LadderEfD G t x Ef k j C' := by
  obtain ⟨h0, hb⟩ := h
  refine ⟨le_trans h0 hCC', fun N hN w => ?_⟩
  refine le_trans (hb N hN w) ?_
  have hS : 0 ≤ Shape (G t) x (k + j) := Shape_nonneg (G t) x (k + j)
  have hP : 0 ≤ Finset.univ.prod
      (fun r : Fin N => Real.sqrt ((G t).inner x (w r) (w r))) :=
    Finset.prod_nonneg fun r _ => Real.sqrt_nonneg _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC' hS) hP

end Work.Diff.EXT
