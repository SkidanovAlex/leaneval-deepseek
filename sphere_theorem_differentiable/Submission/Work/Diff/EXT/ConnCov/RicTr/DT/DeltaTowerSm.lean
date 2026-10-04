import Mathlib
import Submission.Work.Diff.EXT.ConnCov.RicTr.DT.HAuxKernel

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace Work.Diff.EXT.ConnCov.RicTr.DT

open Work.Diff.EXT.ATower Work.Diff.EXT.ConnCov.DT

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- Smoothness of a one-slot update of a tuple of smooth fields (the `T2Space`-free copy of
`Work.Diff.EXT.ConnCov.DT.smE_update_aux`). -/
theorem smE_update_aux' {k : ℕ} {v : Fin k → ATower.TF (I := I) (M := M)} (i : Fin k)
    {W : ATower.TF (I := I) (M := M)} (hv : ∀ j, SmE I M (v j)) (hW : SmE I M W) :
    ∀ j, SmE I M (Function.update v i W j) := by
  intro j
  by_cases h : j = i
  · rw [h, Function.update_self]; exact hW
  · rw [Function.update_of_ne h (f := v)]; exact hv j

/-- Smoothness of the δ-tower on smooth fields.

This is the same induction as `Work.Diff.EXT.ConnCov.DT.deltaTower_sm` of `HAuxKernel`, but with
the (unused) `[T2Space M]` hypothesis of that statement removed: none of the ingredients
(`ATower.lcOf_apply_smE`, `ContMDiffAt.sum_section`, `ContMDiffAt.sub_section`) needs it. -/
theorem deltaTower_sm_nT2
    (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) :
    ∀ j : ℕ, VOpSm (I := I) (M := M) (deltaTower G t j) := by
  intro j
  induction j with
  | zero =>
      intro v X Y hv hX hY
      change SmE I M (fun y : M =>
        (lcOf (G t)) X y (Y y) - (lcOf (G 0)) X y (Y y))
      intro x
      exact ((lcOf_apply_smE hLC (G t) X Y hX hY) x).sub_section
        ((lcOf_apply_smE hLC (G 0) X Y hX hY) x)
  | succ j ih =>
      intro v X Y hv hX hY
      have hv' : ∀ i : Fin j, SmE I M (v i.succ) := fun i => hv i.succ
      have hv0 : SmE I M (v 0) := hv 0
      have hU : ∀ i : Fin j, SmE I M (fun y => (lcOf (G 0)) (v i.succ) y (v 0 y)) :=
        fun i => lcOf_apply_smE hLC (G 0) (v i.succ) (v 0) (hv i.succ) hv0
      change SmE I M (fun x : M =>
        (lcOf (G 0)) (deltaTower G t j (fun i : Fin j => v i.succ) X Y) x (v 0 x)
          - (∑ i : Fin j, deltaTower G t j
              (Function.update (fun j' : Fin j => v j'.succ) i
                (fun y => (lcOf (G 0)) (v i.succ) y (v 0 y))) X Y x)
          - deltaTower G t j (fun i : Fin j => v i.succ)
              (fun y => (lcOf (G 0)) X y (v 0 y)) Y x
          - deltaTower G t j (fun i : Fin j => v i.succ) X
              (fun y => (lcOf (G 0)) Y y (v 0 y)) x)
      intro x
      have h1 := (lcOf_apply_smE hLC (G 0)
        (deltaTower G t j (fun i : Fin j => v i.succ) X Y) (v 0)
        (ih _ X Y hv' hX hY) hv0) x
      have h2 : ContMDiffAt I I.tangent ∞ (T% (fun y : M => ∑ i : Fin j,
          deltaTower G t j
            (Function.update (fun j' : Fin j => v j'.succ) i
              (fun y => (lcOf (G 0)) (v i.succ) y (v 0 y))) X Y y)) x :=
        ContMDiffAt.sum_section (s := (Finset.univ : Finset (Fin j)))
          (fun i _ => (ih _ X Y (smE_update_aux' i hv' (hU i)) hX hY) x)
      have h3 := (ih _ _ Y hv' (lcOf_apply_smE hLC (G 0) X (v 0) hX hv0) hY) x
      have h4 := (ih _ X _ hv' hX (lcOf_apply_smE hLC (G 0) Y (v 0) hY hv0)) x
      exact ((h1.sub_section h2).sub_section h3).sub_section h4

theorem DeltaTowerSm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) :
    ∀ (j : ℕ) (v : Fin j → (y : M) → TangentSpace I y) (X Y : (y : M) → TangentSpace I y),
      (∀ i, Work.Diff.EXT.ATower.SmE I M (v i)) → Work.Diff.EXT.ATower.SmE I M X →
      Work.Diff.EXT.ATower.SmE I M Y →
      Work.Diff.EXT.ATower.SmE I M (Work.Diff.EXT.ConnCov.DT.deltaTower G t j v X Y) :=
  fun j v X Y hv hX hY => deltaTower_sm_nT2 hLC G t j v X Y hv hX hY

end Work.Diff.EXT.ConnCov.RicTr.DT
