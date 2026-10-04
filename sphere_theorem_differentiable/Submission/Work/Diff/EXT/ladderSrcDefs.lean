import Mathlib
import Submission.Work.Diff.EXT.ladderEfDefs
import Submission.Work.Diff.EXT.reactDefs
import Submission.Work.Diff.EXT.towerReactDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The two source operators of the reaction-ladder step

`Work.Diff.EXT.reactOpEfD Ef G t k` is the level-`k` reaction `R_k = ∂ₜ⁺(∇^k Rm) − Δ(∇^k Rm)`
of a Ricci-flow family `G`, with the one-sided time derivative and the rough Laplacian traced in a
frame *field* `Ef` which is smooth and orthonormal near the base point (`IsFrameNear`).

Writing

* `dtOpD G t k` for the operator `F ↦ ∂ₜ⁺(ckk (G ·) k F ·)` (the one-sided time derivative of the
  tower), and
* `lapOpE Ef g k` for the operator `F ↦ ∑_m ckt g (k+2) (Ef m, Ef m, F)` (the rough Laplacian of
  the tower traced in `Ef`),

the reaction is `reactOpEfD Ef G t k = dtOpD G t k − lapOpE Ef (G t) k` (definitionally), and the
ladder step

`jetAll j (k+5) (R_{k+1}) − jetAll (j+1) (k+4) (R_k)`,

after rewriting `jetAll (j+1) (k+4) (R_k) = jetAll j (k+5) (extStep g R_k)`
(`Work.Diff.EXT.jetAll_extStep`), is the `j`-th jet of the **source operator**

`Src_k := R_{k+1} − extStep g R_k
        = (dtOpD G t (k+1) − extStep g (dtOpD G t k)) + (lapOpE Ef g (k+1) − extStep g (lapOpE Ef g k))`.

The two summands are the two sources of the ladder step:

* `srcConnvar` — the **connection-variation source** `(∂ₜ∇)(∇^k Rm)`: the first variation of the
  Levi-Civita connection, contracted with the level-`k` tower (a level-`k+1` object);
* `srcLapComm` — the **Weitzenböck source** `[Δ,∇](∇^k Rm)`: the commutator of the rough Laplacian
  with the covariant derivative, contracted with the level-`k` tower (a level-`k+1` object).

Both are *tower-level* objects: they do not mention the reaction `R_k` itself, and for both one has
an explicit pointwise identity in terms of the tower and the curvature, of the form "a metric
contraction of two tower components whose levels add up to `k+1`".  Consequently (the classical
reaction estimate) their `j`-th jets are bounded by `C_{k,j} · Shape (G t) x (k+1+j)` times the
product of the metric norms of the `k+5+j` arguments, where
`Shape g x m = ∑_{i ≤ m} √f_i √f_{m−i}`, `f_i = curvNormK g x i = |∇^i Rm|²`
(`Work.Diff.EXT.Shape`).

This module only *defines* the four operators; the two bounds are proved in the modules
`Submission/Work/Diff/EXT/evolX/connVar_src_jets.lean` and
`Submission/Work/Diff/EXT/evolX/lapComm_src_jets.lean`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- **The one-sided time-derivative operator of the tower**: `dtOpD G t k F y` is
`∂ₜ⁺(ckt (G ·) k F y)`, the `s`-derivative within `Ioi 0` of the tower along the metric family `G`.
On `0 < t` this is the ordinary derivative; at `t = 0` it is the right derivative, which is the only
meaningful choice since `IsRicciFlow G T` controls `G` only on `[0, T)`. -/
noncomputable def dtOpD [T2Space M] (G : ℝ → SMet I M) (t : ℝ) (k : ℕ) :
    (Fin (k + 4) → TField (I := I) (M := M)) → M → ℝ :=
  fun F y => derivWithin (fun s => ckt (G s) k F y) (Set.Ioi 0) t

/-- **The rough Laplacian of the tower, traced in the frame field `Ef`**: the operator
`F ↦ ∑_m ckt g (k+2) (Ef m, Ef m, F)`.  For `Ef` orthonormal near the base point this is the honest
`Δ(∇^k Rm)` near that point (`Work.Diff.EXT.IsFrameNear`). -/
noncomputable def lapOpE [T2Space M]
    (Ef : Fin (Module.finrank ℝ E) → TField (I := I) (M := M))
    (g : SMet I M) (k : ℕ) :
    (Fin (k + 4) → TField (I := I) (M := M)) → M → ℝ :=
  fun F y => ∑ m : Fin (Module.finrank ℝ E),
      ckt g (k + 2) (Fin.cons (Ef m) (Fin.cons (Ef m) F)) y

/-- The reaction is the difference of the two operators (definitional). -/
theorem reactOpEfD_eq_sub [T2Space M]
    (Ef : Fin (Module.finrank ℝ E) → TField (I := I) (M := M))
    (G : ℝ → SMet I M) (t : ℝ) (k : ℕ) :
    reactOpEfD (I := I) (M := M) Ef G t k
      = dtOpD (I := I) (M := M) G t k - lapOpE (I := I) (M := M) Ef (G t) k := rfl

/-- **The connection-variation source** of the ladder step: the `∂ₜ`-defect
`dtOpD G t (k+1) − extStep (G t) (dtOpD G t k)`.  By the differentiability of one recursion step of
the tower in time (`Work.Diff.EXT.ckt_step_tderiv`) it is (up to the two-sidedness of the time
derivative) minus the contraction of the connection-variation tensor `∂ₜ∇` with the level-`k`
tower, i.e. a level-`k+1` tower expression. -/
noncomputable def srcConnvar [T2Space M] (G : ℝ → SMet I M) (t : ℝ) (k : ℕ) :
    (Fin (k + 5) → TField (I := I) (M := M)) → M → ℝ :=
  dtOpD (I := I) (M := M) G t (k + 1) - extStep (I := I) (M := M) (G t) (dtOpD (I := I) (M := M) G t k)

/-- **The Weitzenböck source** of the ladder step: the Laplacian–derivative commutator
`lapOpE Ef g (k+1) − extStep g (lapOpE Ef g k)`.  By the tower recursion it is *exactly*
`∑_m [ ckt g (k+3) (Ef m, Ef m, X, F) − ckt g (k+3) (X, Ef m, Ef m, F) ]`, which by the two swap
identities of the tower (`Work.Diff.EXT.ckt_sub_swap`, `Work.Diff.EXT.ckt_swap23`) is a level-`k+1`
curvature-action expression. -/
noncomputable def srcLapComm [T2Space M]
    (Ef : Fin (Module.finrank ℝ E) → TField (I := I) (M := M))
    (g : SMet I M) (k : ℕ) :
    (Fin (k + 5) → TField (I := I) (M := M)) → M → ℝ :=
  lapOpE (I := I) (M := M) Ef g (k + 1) - extStep (I := I) (M := M) g (lapOpE (I := I) (M := M) Ef g k)

end Work.Diff.EXT
