import Mathlib
import Submission.Work.Diff.EXT.reactDefs
import Submission.Work.Diff.EXT.evolCompKFix_all
import Submission.Work.Diff.EXT.Kpt_eq_covKRm_packed

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The reaction of the `k`-th order Shi estimate, with the Laplacian traced in a frame *field*

## Why a new operator is needed

`Work.Diff.EXT.reactOp` (`Submission/Work/Diff/EXT/evolCompKFixReact_all.lean`) defines the reaction
`R_k = ∂ₛ(∇^k Rm) − Δ(∇^k Rm)` by tracing the rough Laplacian in the fields
`smoothExt x (onFrame (G t) x m)`, the `Classical.epsilon`-chosen extensions of the frame *at the
base point* `x`, and then states the ladder invariant
`LadderAt G t x k C = JetBnd (G t) x (reactOp G t x k) k C`, i.e. a bound on **all jets** of that
operator at `x`.

The *value* at `x` is right: the tower's second derivative along a field `D` is
`∇_D∇_D T (y) = Hess T (D y, D y)` (independent of the extension), so at `x` — where
`D_m x = onFrame (G t) x m` is orthonormal — the traced sum is the rough Laplacian
`∑_m Hess T (e_m, e_m) = ΔT(x)`.  The **jets are not**: at a nearby point `y` the traced sum is
`∑_m Hess T (D_m y, D_m y)`, which equals `ΔT(y)` only when the *values* `D_m y` are orthonormal,
and for the extensions above that fails for `y ≠ x`.  The defect is
`∑_{p,q} (C^{pq} − δ^{pq}) Hess T (e_p, e_q)` with `C^{pq} = ∑_m D_m^p D_m^q`: it vanishes at `x`,
but its first derivative — which enters the first jet of `reactOp` — contains the terms
`2 ∑_m Hess T (∇_v D_m, e_m)` involving the **covariant derivatives of the arbitrary
`Classical.epsilon` extensions**, about which nothing is known (and nothing can be: they are fixed
but arbitrary).  So `LadderAt(0,1)` — hence the whole ladder of that route — is not provable as
stated; the obstruction is not the mathematics of Shi's estimate but the choice of extensions.

## The repair

Trace the Laplacian in a frame *field* `Ef` which is smooth and `g`-orthonormal on a
**neighbourhood** of `x` (`IsFrameNear g x Ef`).  Then for `y` near `x` the traced sum *is*
`ΔT(y)`, so the operator defined here agrees with the honest reaction near `x`: its jets are the
honest jets of `R_k`, and its value at `x` is `∂ₛ(∇^k Rm)(x) − Δ(∇^k Rm)(x)`.  Such `Ef` exist
(`Work.Diff.EXT.evolX.exists_isFrameNear`, a Gram–Schmidt construction in a chart).

## Content of this module

* `IsFrameNear g x Ef` — `Ef` is smooth and `g`-orthonormal near `x`;
* `reactOpEf Ef G t k` — the reaction operator of the Ricci flow `G` at time `t` and level `k`,
  with the Laplacian traced in `Ef`;
* `LadderForm G t x Ef k j C` — the ladder invariant at level `k` and jet order `j`: every value of
  the `j`-th covariant derivative of `R_k` at `x`, on any tuple of `k+4+j` tangent vectors, is
  bounded by `C · Shape (k+j)` times the metric norms of the tuple.  (The tuple is carried as
  `w : Fin N` together with the length equation `N = k+4+j`, so that the two sides of the
  recursion `(k+1,j) ← (k,j+1)` — which have the same total length but different summands — can be
  compared on one tuple.)

The assembly `Work.Diff.EXT.evolCompK_all_tower` runs the ladder induction on this operator, with
the three pieces
`Work.Diff.EXT.evolX.ladderEf_base` (the level-`0` case, all jets, from the pointwise level-`0`
evolution identity and `reaction0_jets`),
`Work.Diff.EXT.evolX.ladderEf_step` (the recursion `R_{k+1} = ∇R_k + B_k` at the level of jets) and
`Work.Diff.EXT.evolX.ladderEf_to_react` (the conversion of the `j = 0` ladder into
`EvolCompKFixReact k`).
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

/-- **A smooth field family which is a `g`-orthonormal frame near `x`.** -/
def IsFrameNear [T2Space M] (g : SMet I M) (x : M)
    (Ef : Fin (Module.finrank ℝ E) → TField (I := I) (M := M)) : Prop :=
  (∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (Ef i)) ∧
    (∀ᶠ y in 𝓝 x, IsONFrame g y (fun i => Ef i y))

/-- **The reaction operator of the `k`-th order Shi estimate**, with the rough Laplacian traced in
the frame field `Ef`: `R_k = ∂ₛ(∇^k Rm) − ∑_m ∇_{Ef m}∇_{Ef m}(∇^k Rm)`.  For `Ef` smooth and
orthonormal near `x` this agrees with the honest reaction `∂ₛ(∇^k Rm) − Δ(∇^k Rm)` near `x`. -/
noncomputable def reactOpEf [T2Space M]
    (Ef : Fin (Module.finrank ℝ E) → TField (I := I) (M := M))
    (G : ℝ → SMet I M) (t : ℝ) (k : ℕ) :
    (Fin (k + 4) → TField (I := I) (M := M)) → M → ℝ :=
  fun F y =>
    deriv (fun s => ckt (G s) k F y) t
      - ∑ m : Fin (Module.finrank ℝ E),
          ckt (G t) (k + 2) (Fin.cons (Ef m) (Fin.cons (Ef m) F)) y

/-- **The ladder invariant of the reaction at level `k` and jet order `j`.**  `LadderForm G t x Ef k j C`
says: `C ≥ 0` and, for every `N` with `N = k + 4 + j` and every tuple `w : Fin N → TₓM`, the `j`-th
covariant derivative of the level-`k` reaction at `x`, evaluated on the `Classical.epsilon`
extensions of the entries of `w`, is bounded by `C · Shape (G t) x (k+j)` times the product of the
metric norms of the entries. -/
def LadderForm [T2Space M] (G : ℝ → SMet I M) (t : ℝ) (x : M)
    (Ef : Fin (Module.finrank ℝ E) → TField (I := I) (M := M)) (k j : ℕ) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ (N : ℕ) (hN : N = k + 4 + j) (w : Fin N → TangentSpace I x),
    |jetAll (G t) j (k + 4) (reactOpEf Ef G t k)
        (fun r : Fin (k + 4 + j) => smoothExt x (w (Fin.cast hN.symm r))) x|
      ≤ C * Shape (G t) x (k + j)
          * Finset.univ.prod
              (fun r : Fin N => Real.sqrt ((G t).inner x (w r) (w r)))

end Work.Diff.EXT
