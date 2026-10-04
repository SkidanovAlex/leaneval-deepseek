import Mathlib
import Submission.Work.Diff.EXT.ConnCov.aTowerMovingDefs
import Submission.Work.Diff.EXT.covKAExt_tensorial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# From the `smoothExt`-value bound to the monotone slot bound (`Bnd1`)

`Work.Diff.EXT.ATower.ValBound G t m τ C` bounds the value-level operator
`valOp τ x v a b c = τ (smoothExt x (v i)) (smoothExt x a) (smoothExt x b) (smoothExt x c) x`
on *pointwise* vectors at `x` by `C` times the product of the `G t`-norms of the `m + 3` vectors.
The `ConnCov` machinery (`Work.Diff.EXT.ConnCov.aTower_moving_bound`) works with the *monotone* slot
bound `AMB.Bnd1 G t τ C`, which bounds `τ F x` for **arbitrary smooth** slot fields `F` by
`C * ∏_j (1 + ‖F_j x‖_{G t})`.

The passage between the two is exactly the *tensoriality* of the tower, plus the elementary product
estimate `∏ √a_j ≤ ∏ (1 + √a_j)`:

* `pack_tower_eq_valOp` — the packed tower evaluated on a smooth tuple of fields equals the value-level
  operator evaluated on the *values* of those fields.  This is `Work.Diff.EXT.covKAExt_tensorial`
  (`covKAExt = tower (lcOf (G 0)) (aOf G t)` definitionally), applied to the two tuples
  `F` and `smoothExt x (F x)`, which agree at `x` by `smoothExt_apply`;
* `Fin.prod_univ_add` + `Fin.prod_univ_three` split the product over `Fin (m+3)` into the product
  over the `m` direction slots and the three value slots, so that `ValBound` applies verbatim;
* `Finset.prod_le_prod₀` upgrades `√a ≤ 1 + √a` factorwise (all factors nonnegative), and `0 ≤ C`
  (`hC`) preserves the inequality.

This is the lemma `Work.Diff.EXT.ConnCov.bnd1_of_valBound`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ConnCov

section Kit

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-- **The packed tower on a smooth tuple is the value-level operator on the values of the tuple.**

`AMB.pack τ F x` evaluates `τ` on the `m` direction fields `F ∘ castAdd` and the three value fields
`F (natAdd m ·)`; `valOp τ x v a b c` evaluates `τ` on the *canonical smooth extensions*
`smoothExt x ·` of the pointwise vectors.  Since `covKAExt G t m` (which the tower is, definitionally)
is tensorial in all slots, the two agree as soon as the tuples agree at `x`, which they do by
`smoothExt_apply`. -/
theorem pack_tower_eq_valOp
    (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) (m : ℕ)
    (x : M) (F : Fin (m + 3) → Work.Diff.EXT.ATower.TF (I := I) (M := M))
    (hF : ∀ j, Work.Diff.EXT.ATower.SmE I M (F j)) :
    AMB.pack (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
        (fun _ => Work.Diff.EXT.aOf G t) m) F x
      = Work.Diff.EXT.ATower.valOp (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
          (fun _ => Work.Diff.EXT.aOf G t) m) x
        (fun i : Fin m => F (Fin.castAdd 3 i) x)
        (F (Fin.natAdd m 0) x) (F (Fin.natAdd m 1) x) (F (Fin.natAdd m 2) x) := by
  have hT := Work.Diff.EXT.covKAExt_tensorial (I := I) (M := M) hLC G t m x
    (fun i : Fin m => F (Fin.castAdd 3 i))
    (fun i : Fin m => Submission.Diff.smoothExt x (F (Fin.castAdd 3 i) x))
    (F (Fin.natAdd m 0)) (Submission.Diff.smoothExt x (F (Fin.natAdd m 0) x))
    (F (Fin.natAdd m 1)) (Submission.Diff.smoothExt x (F (Fin.natAdd m 1) x))
    (F (Fin.natAdd m 2)) (Submission.Diff.smoothExt x (F (Fin.natAdd m 2) x))
    (fun i => hF (Fin.castAdd 3 i)) (fun i => Work.Diff.GE.smoothExt_cmdiff x _)
    (hF (Fin.natAdd m 0)) (Work.Diff.GE.smoothExt_cmdiff x _)
    (hF (Fin.natAdd m 1)) (Work.Diff.GE.smoothExt_cmdiff x _)
    (hF (Fin.natAdd m 2)) (Work.Diff.GE.smoothExt_cmdiff x _)
    (fun i => (Work.Diff.GE.smoothExt_apply x _).symm) (Work.Diff.GE.smoothExt_apply x _).symm
    (Work.Diff.GE.smoothExt_apply x _).symm (Work.Diff.GE.smoothExt_apply x _).symm
  rw [Work.Diff.EXT.ConnCov.AMB.pack_apply,
    Work.Diff.EXT.ATower.tower_eq_covKAExt (I := I) (M := M) G t m]
  exact hT

end Kit

theorem bnd1_of_valBound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M) (t : ℝ)
    {m : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (h : Work.Diff.EXT.ATower.ValBound G t m
      (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
        (fun _ => Work.Diff.EXT.aOf G t) m) C) :
    Work.Diff.EXT.ConnCov.AMB.Bnd1 G t
      (Work.Diff.EXT.ConnCov.AMB.pack (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
        (fun _ => Work.Diff.EXT.aOf G t) m)) C := by
  intro F x hF
  rw [pack_tower_eq_valOp (I := I) (M := M) hLC G t m x F hF]
  have hval := h x (fun i : Fin m => F (Fin.castAdd 3 i) x) (F (Fin.natAdd m 0) x)
    (F (Fin.natAdd m 1) x) (F (Fin.natAdd m 2) x)
  have hprod : (∏ j : Fin (m + 3), Real.sqrt ((G t).inner x (F j x) (F j x)))
      = (∏ i : Fin m,
            Real.sqrt ((G t).inner x (F (Fin.castAdd 3 i) x) (F (Fin.castAdd 3 i) x)))
        * Real.sqrt ((G t).inner x (F (Fin.natAdd m 0) x) (F (Fin.natAdd m 0) x))
        * Real.sqrt ((G t).inner x (F (Fin.natAdd m 1) x) (F (Fin.natAdd m 1) x))
        * Real.sqrt ((G t).inner x (F (Fin.natAdd m 2) x) (F (Fin.natAdd m 2) x)) := by
    rw [Fin.prod_univ_add]
    rw [Fin.prod_univ_three]
    ring
  calc |Work.Diff.EXT.ATower.valOp (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
          (fun _ => Work.Diff.EXT.aOf G t) m) x
        (fun i : Fin m => F (Fin.castAdd 3 i) x) (F (Fin.natAdd m 0) x)
        (F (Fin.natAdd m 1) x) (F (Fin.natAdd m 2) x)|
      ≤ C * (∏ i : Fin m,
              Real.sqrt ((G t).inner x (F (Fin.castAdd 3 i) x) (F (Fin.castAdd 3 i) x)))
          * Real.sqrt ((G t).inner x (F (Fin.natAdd m 0) x) (F (Fin.natAdd m 0) x))
          * Real.sqrt ((G t).inner x (F (Fin.natAdd m 1) x) (F (Fin.natAdd m 1) x))
          * Real.sqrt ((G t).inner x (F (Fin.natAdd m 2) x) (F (Fin.natAdd m 2) x)) := hval
    _ = C * (∏ j : Fin (m + 3), Real.sqrt ((G t).inner x (F j x) (F j x))) := by
        rw [hprod]; ring
    _ ≤ C * ∏ j : Fin (m + 3), (1 + Real.sqrt ((G t).inner x (F j x) (F j x))) := by
        apply mul_le_mul_of_nonneg_left _ hC
        refine Finset.prod_le_prod₀ (fun j _ => Real.sqrt_nonneg _) (fun j _ => ?_)
        have hs := Real.sqrt_nonneg ((G t).inner x (F j x) (F j x))
        linarith

end Work.Diff.EXT.ConnCov
