import Mathlib
import Submission.Work.Diff.EXT.reactDefs
import Submission.Work.Diff.EXT.Kpt_eq_covKRm_packed

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

/-!
# The reaction operator `R_k = ∂ₜ(∇^k Rm) − Δ(∇^k Rm)` of a metric family

`Work.Diff.EXT.reactOp G t x k` is the *reaction* `R_k` of the metric family `G` at time `t` and
point `x`, as a packed tensorial operator of arity `k + 4`:

`R_k(F) = ∂ₜ (∇^k Rm)(F) − Δ(∇^k Rm)(F)`,

where the time derivative is taken *within* `[0, ∞)` (`derivWithin … (Set.Ioi 0)`, so that it is the
one-sided time derivative at `t = 0`, where a two-sided `deriv` would be junk because
`IsRicciFlow G T` only controls `G` on `[0, T)`), and the rough Laplacian is traced in the
orthonormal frame `onFrame (G t) x` of the metric at time `t`, written with the smooth extensions
`smoothExt x ·` of the frame vectors so that the trace really is the value of `Δ∇^kRm` at `x`
(the tower is value-dependent, `Work.Diff.EXT.ckt_val_dep_all`).

The operator is *tensorial* in `F`, so `Work.Diff.EXT.jetAll` applied to it computes the honest
jets `∇^j R_k` (`Work.Diff.EXT.LadderAt`), and the `j = 0` case is the reaction bound of the
`k`-th order Shi estimate (`Work.Diff.EXT.ladderAt_zero`).

> **WARNING.** The operator `reactOp` of this module traces the rough Laplacian in the
> `Classical.epsilon` extensions `smoothExt x (onFrame (G t) x m)` of the frame *at the base point*.
> That gives the honest *value* of `Δ∇^k Rm` at `x`, but **not** the honest *jets*: for `y` near `x`
> the traced sum differs from `Δ∇^k Rm(y)` by a defect which vanishes at `x` but whose first
> derivative involves the covariant derivatives of those arbitrary extensions.  Consequently the
> ladder `LadderAt` of this operator is **not provable** at jet orders `j ≥ 1`, and it is *not* the
> invariant used by the proof of `Work.Diff.EXT.EvolCompKFixReact`.  The working version traces the
> Laplacian in a frame *field* which is orthonormal on a neighbourhood of `x`: see
> `Work.Diff.EXT.reactOpEfD` / `Work.Diff.EXT.LadderEfD` in
> `Submission/Work/Diff/EXT/ladderEfDefs.lean` (and the discussion in
> `Submission/Work/Diff/EXT/towerReactDefs.lean`).  The definitions below are retained because the
> packing bridges `covKRm_eq_ckt_of_packed` / `covKRm_eq_ckt_append` proved here are used
> everywhere.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- **The reaction** `R_k = ∂ₜ(∇^k Rm) − Δ(∇^k Rm)` of the family `G` at time `t` and point `x`, as
a packed field-level tensorial operator of arity `k + 4`: the one-sided `s`-derivative of the tower
`ckt (G s) k` (with the `s`-independent tuple `F`), minus the rough Laplacian traced in the
orthonormal frame, written with the smooth extensions of the frame vectors so that the trace is the
genuine value of `Δ∇^kRm`.

The time derivative is `derivWithin … (Set.Ioi 0)`: on `(0, T)` it is the ordinary derivative
(`derivWithin_of_mem_nhds`), and at `t = 0` it is the one-sided (right) derivative, which is the
only meaningful choice since `IsRicciFlow G T` controls `G` only on `[0, T)`. -/
noncomputable def reactOp [T2Space M] (G : ℝ → SMet I M) (t : ℝ) (x : M) (k : ℕ) :
    (Fin (k + 4) → TField (I := I) (M := M)) → M → ℝ :=
  fun F y =>
    derivWithin (fun s => ckt (G s) k F y) (Set.Ioi 0) t
      - ∑ m : Fin (Module.finrank ℝ E),
          ckt (G t) (k + 2)
            (Fin.cons (smoothExt x (onFrame (G t) x m))
              (Fin.cons (smoothExt x (onFrame (G t) x m)) F)) y

/-- **The ladder predicate for the reaction**: the `j`-th jet of `R_k` at `(t,x)` is bounded by
`C j · Shape_{k+j}` times the metric norms of the `k + 4 + j` vectors.  `j = 0` is the target's
reaction bound (`ladderAt_zero`); the constant is a *function of the jet order* `C : ℕ → ℝ` (it has
to be: the product rule makes the constants grow like `2^j`). -/
def LadderAt [T2Space M] (G : ℝ → SMet I M) (t : ℝ) (x : M) (k : ℕ) (C : ℕ → ℝ) : Prop :=
  JetBnd (G t) x (reactOp (I := I) (M := M) G t x k) k C

/-- **The `j = 0` jet of the reaction is the reaction itself**: the target's reaction bound is the
`j = 0` instance of the ladder. -/
theorem ladderAt_zero [T2Space M] {G : ℝ → SMet I M} {t : ℝ} {x : M} {k : ℕ}
    {C : ℕ → ℝ} (h : LadderAt G t x k C) (F : Fin (k + 4) → TField (I := I) (M := M))
    (hF : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (F i)) :
    |reactOp (I := I) (M := M) G t x k F x|
      ≤ C 0 * Shape (G t) x k
          * ∏ r : Fin (k + 4), Real.sqrt ((G t).inner x (F r x) (F r x)) :=
  h 0 F hF

/-- **Monotonicity of the ladder in its constant.** -/
theorem ladderAt_mono [T2Space M] {G : ℝ → SMet I M} {t : ℝ} {x : M} {k : ℕ}
    {C C' : ℕ → ℝ} (h : LadderAt G t x k C) (hCC' : ∀ j, C j ≤ C' j) :
    LadderAt G t x k C' := by
  intro j Gs hGs
  refine le_trans (h j Gs hGs) ?_
  have hS : 0 ≤ Shape (G t) x (k + j) := Shape_nonneg (G t) x (k + j)
  have hP : 0 ≤ ∏ r : Fin (k + 4 + j),
      Real.sqrt ((G t).inner x (Gs r x) (Gs r x)) :=
    Finset.prod_nonneg fun r _ => Real.sqrt_nonneg _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hCC' j) hS) hP

/-! ## The packing glue between the tower and `covKRm` -/

/-- **The packing bridge**: the tower `ckt g k` on a packed tuple of smooth extensions is the
`(0,k+4)`-tensor `covKRm` on the unpacked tuple (the first `k` slots are the differentiation
directions).  Immediate from `Work.Diff.EXT.Kpt_eq_covKRm_packed` (`Kpt g x k w` is
`ckt g k (fun s => smoothExt x (w s)) x` by definition). -/
theorem covKRm_eq_ckt_of_packed [T2Space M] (g : SMet I M) (x : M) (k : ℕ)
    (w : Fin (k + 4) → TangentSpace I x) :
    covKRm g x k (fun r : Fin k => w (Fin.castAdd 4 r))
        (w (Fin.natAdd k 0)) (w (Fin.natAdd k 1)) (w (Fin.natAdd k 2)) (w (Fin.natAdd k 3))
      = ckt g k (fun s => smoothExt x (w s)) x :=
  (Kpt_eq_covKRm_packed g x k w).symm

/-- **The packing bridge in the form used by the target**: with `w := Fin.append u ![a,b,c,d]`,
`covKRm g x k u a b c d` is the tower `ckt g k` on the smooth extensions of the concatenated tuple.
`Fin.append_left`/`Fin.append_right` evaluate the components of `w`. -/
theorem covKRm_eq_ckt_append [T2Space M] (g : SMet I M) (x : M) (k : ℕ)
    (u : Fin k → TangentSpace I x) (a b c d : TangentSpace I x) :
    covKRm g x k u a b c d
      = ckt g k (fun s => smoothExt x (Fin.append u ![a, b, c, d] s)) x := by
  rw [← covKRm_eq_ckt_of_packed g x k (Fin.append u ![a, b, c, d])]
  simp

end Work.Diff.EXT
