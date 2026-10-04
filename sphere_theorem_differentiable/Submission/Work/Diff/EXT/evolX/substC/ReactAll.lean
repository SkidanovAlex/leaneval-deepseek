import Mathlib
import Submission.Work.Diff.EXT.ladderEfDefs
import Submission.Work.Diff.EXT.reactOpDefs
import Submission.Work.Diff.EXT.reactDefs
import Submission.Work.Diff.EXT.evolCompKFix_all
import Submission.Work.Diff.EXT.ladderEfD_base
import Submission.Work.Diff.EXT.evolX.substC.LadderStep
import Submission.Work.Diff.EXT.ladderEfDToReact

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `evolCompKFixReact_all` (copy of the W-chain version)

The last link of the independent chain `substC.Assembly` → … → `substC.ReactAll`; it provides
`∀ k ≥ 1, EvolCompKFixReact k` to `Work.Diff.EXT.evolK_of_flow` without depending on
`Work.Diff.EXT.evolCompKFixReact_all` (i.e. without `substOpJetsW`).
-/

namespace Work.Diff.EXT

/-!
# The sharp `k`-th order Shi reaction estimate for all `k ≥ 1`

`Work.Diff.EXT.EvolCompKFixReact k` (`Submission/Work/Diff/EXT/evolCompKFix_all.lean`) is the
*sharp* (classical) `k`-th order Shi reaction estimate: for each `k ≥ 1` there is `C ≥ 0` such that
along every Ricci flow `G` on `[0,T)`, at every `t ∈ Ico 0 T`, every `x`, and every choice of
vectors `u : Fin k → TₓM`, `a b c d`, the component `s ↦ covKRm (G s) x k u a b c d` has a right
derivative `D` (within `Ico 0 T`) with

`D ≤ lapCovKRm (G t) x k u a b c d + C · (∑_{i+j=k} √f_i √f_j) · ∏‖·‖`,  `f_j = curvNormK (G t) x j`.

It is *sharper* than `Work.Diff.EXT.EvolCompKFix k`; `Work.Diff.EXT.sum_sqrt_le` /
`evolCompKFix_of_reaction` (both proved) convert it into `EvolCompKFix k`, hence into `EvolK`,
`ShiBounds` and the extension contract.

## The proof architecture: the frame-field reaction ladder

Write `T_k := ∇^k Rm` (the tower `Work.Diff.EXT.ckt`) and `R_k := ∂ₜ⁺ T_k − Δ T_k` for the
*reaction*, where `∂ₜ⁺` is the one-sided time derivative (`derivWithin … (Set.Ioi 0)`) and the
Laplacian is traced in a frame *field* `Ef` which is smooth and orthonormal on a *neighbourhood* of
the base point (`Work.Diff.EXT.IsFrameNear`); the operator is `Work.Diff.EXT.reactOpEfD` and the
invariant is `Work.Diff.EXT.LadderEfD`.  (Both corrections are necessary; see
`Submission/Work/Diff/EXT/towerReactDefs.lean` and `ladderEfDefs.lean`.  In particular tracing the
Laplacian in the `Classical.epsilon` extensions of a frame of `TₓM` gives the honest value at `x`
but *not* the honest jets, so the naive `LadderAt` of `reactOp` is unprovable as stated.)

The classical identity `∂ₜ∇^k Rm = Δ∇^kRm + ∑_{i+j=k} ∇^iRm ∗ ∇^jRm` says that `R_k` is a sum of
metric contractions of *two* jets whose levels add to `k`, so

`|∇^j R_k| ≤ C_j · Shape (k+j) · ∏‖·‖`  (the ladder).

The ladder is run by the two-parameter recursion `(k,j) ← (k−1, j+1)`: with `R_{k+1} = ∇R_k + B_k`
(`B_k = (∂ₜ∇)(T_k) − [Δ,∇](T_k)` the explicit Weitzenböck/connection-variation terms) one has
`∇^j R_{k+1} = ∇^{j+1}R_k + ∇^j B_k`, so the induction hypothesis is needed for *all* `j` at the
lower level, and it terminates at the explicit quadratic level-`0` reaction `R_0 = Q(Rm)`, whose
jets are bounded jet by jet.  The two atoms of this recursion are

* `Work.Diff.EXT.ladderEfD_base` — the level-`0` reaction with *all* jets (`R_0 = Q(Rm)`, i.e. the
  quadratic reaction `reactionFormAt reactionMap` transported along the pointwise level-`0`
  evolution identity; the jet bound is the delegated `Work.Diff.EXT.reaction0_jets`);
* `Work.Diff.EXT.ladderEfD_step` — the recursion atom `R_{k+1} − ∇R_k = B_k` differentiated `j`
  times, bounded by `C · Shape (k+1+j)`.

The *bookkeeping* that turns the two atoms into the ladder at every level (`ladderEfD_all_atomsC`
below) and the *packaging* of the `j = 0` ladder into `EvolCompKFixReact k`
(`Work.Diff.EXT.ladderEfDToReact`) are the remaining pieces; the packaging uses the trace identity
`Work.Diff.EXT.evolX.ladderEf_trace`, the frame-field existence
`Work.Diff.EXT.evolX.isFrameNear_exists`, the packing bridge
`Work.Diff.EXT.covKRm_eq_ckt_append` and the differentiability of the tower component along the
flow (`Work.Diff.EXT.covKRm_derivWithin`).
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

/-- **Reindexing of a finite product along `Fin.cast`.** -/
theorem prod_fin_castC {N M : ℕ} (h : M = N) (f : Fin N → ℝ) :
    (∏ r : Fin M, f (Fin.cast h r)) = ∏ r : Fin N, f r := by
  subst h
  simp

/-- **The ladder, from its two atoms** (`ladderEfD_base` and `ladderEfD_step`).

This is the two-parameter induction `(k+1, j) ← (k, j+1)`: the step atom bounds the difference
`∇^j R_{k+1} − ∇^{j+1}R_k` by `C₂ · Shape (k+1+j)`, the induction hypothesis at level `k` and jet
order `j+1` bounds `∇^{j+1}R_k` by `C₁ · Shape (k+1+j)`, and the triangle inequality adds the two
constants.  The constants are per `(k,j)`, which is what the recursion needs (they must *not* be
uniform in `j`: the product rule makes them grow like `2^j`). -/
theorem ladderEfD_all_atomsC [I.Boundaryless] [T2Space M] [CompactSpace M] :
    ∀ k j : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T → ∀ t ∈ Set.Ico 0 T, ∀ x : M,
      ∀ (Ef : Fin (Module.finrank ℝ E) → TField (I := I) (M := M)),
      IsFrameNear (G t) x Ef → LadderEfD G t x Ef k j C := by
  intro k
  induction k with
  | zero => exact ladderEfD_base (I := I) (M := M)
  | succ k ih =>
    intro j
    obtain ⟨C₁, hC₁, h₁⟩ := ih (j + 1)
    obtain ⟨C₂, hC₂, h₂⟩ := ladderEfD_stepC (I := I) (M := M) k j
    refine ⟨C₁ + C₂, by linarith, ?_⟩
    intro G T hflow t ht x Ef hEf
    have hA0 := (h₁ G T hflow t ht x Ef hEf).2
    have hB0 := h₂ G T hflow t ht x Ef hEf
    refine ⟨by linarith, ?_⟩
    intro N hN w
    have hN₂ : N = k + 4 + (j + 1) := by omega
    have hA := hA0 N hN₂ w
    have hB := hB0 N hN.symm hN₂.symm w
    set PP : ℝ := ∏ r : Fin N, Real.sqrt ((G t).inner x (w r) (w r)) with hPP
    have hS : Shape (G t) x (k + (j + 1)) = Shape (G t) x ((k + 1) + j) := by
      congr 1
      omega
    rw [hS] at hA
    set AA : ℝ := jetAll (G t) j ((k + 1) + 4) (reactOpEfD (I := I) (M := M) Ef G t (k + 1))
        (fun r : Fin ((k + 1) + 4 + j) => smoothExt x (w (Fin.cast hN.symm r))) x with hAA
    set BB : ℝ := jetAll (G t) (j + 1) (k + 4) (reactOpEfD (I := I) (M := M) Ef G t k)
        (fun r : Fin (k + 4 + (j + 1)) => smoothExt x (w (Fin.cast hN₂.symm r))) x with hBB
    have hsplit : |AA| ≤ |AA - BB| + |BB| := by
      have h := abs_add_le (AA - BB) BB
      rwa [sub_add_cancel] at h
    calc |AA| ≤ |AA - BB| + |BB| := hsplit
      _ ≤ C₂ * Shape (G t) x ((k + 1) + j) * PP + C₁ * Shape (G t) x ((k + 1) + j) * PP :=
          add_le_add hB hA
      _ = (C₁ + C₂) * Shape (G t) x ((k + 1) + j) * PP := by ring

/-- **The requested statement**: the sharp `k`-th order Shi reaction estimate
`Work.Diff.EXT.EvolCompKFixReact k` for all `k ≥ 1`, assembled from the ladder induction
`ladderEfD_all_atomsC` (whose atoms are `Work.Diff.EXT.ladderEfD_base` and
`Work.Diff.EXT.ladderEfD_step`) and the packaging `Work.Diff.EXT.ladderEfDToReact`. -/
theorem evolCompKFixReact_allC
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M] :
    ∀ k : ℕ, 1 ≤ k → Work.Diff.EXT.EvolCompKFixReact (I := I) (M := M) k :=
  fun k hk => ladderEfDToReact (I := I) (M := M) k hk
    (ladderEfD_all_atomsC (I := I) (M := M) k)

end Work.Diff.EXT
