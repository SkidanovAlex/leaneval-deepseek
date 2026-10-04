import Mathlib
import Submission.Work.Diff.EXT.evolX.connVarPairDefs
import Submission.Work.Diff.EXT.evolX.ladderPlumb
import Submission.Work.Diff.EXT.jetSmoothDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- NOTE (importer): the original header also carried
--   `import Submission.Work.Diff.EXT.evolX.connVar_pair_jets`
-- which is *not* needed by the proof below (the smoothness route does not use the jet bound of
-- `connVar_pair_jets`).  That module is left out because its import closure currently contains a
-- work-in-progress file of a colleague (`connVarTraceDefs`, imported by `connVar_pair_trace`);
-- a consumer that wants the bound should import `connVar_pair_jets` explicitly.

/-!
# `JetSmoothOp` for the connection-variation pairing of a Ricci flow

The target `Work.Diff.EXT.evolX.cvPairOp_jetSmoothOp`: the operator

`cvPairOp G t = fun (Z : Fin 3 → TField) (y : M) ↦ ⟪dLC G t (Z 0) (Z 1) y, Z 2 y⟫`

— the pairing of the first variation `∂ₜ∇ = dLC G t` of the Levi-Civita connection along the Ricci
flow `G`, contracted with a test field — satisfies the regularity predicate
`Work.Diff.EXT.JetSmoothOp (G t) 3 (cvPairOp G t) x` (`Submission/Work/Diff/EXT/jetSmoothDefs.lean`):
all its `jetAll`-jets are mdifferentiable near `x`.

## Proof

The same two-step argument as for the rough Laplacian (`opJetSmooth_lapOpE`), the tower
(`ckt_jetSmoothOp`) and the contracted tower with `dLC` inserted
(`jetSmoothOp_substOp_VdLC`):

* the value of the operator on a tuple of smooth fields is `C^∞`: the section
  `y ↦ dLC G t (F 0) (F 1) y` is smooth (`Work.Diff.Evol.cv_dLC_smooth`, from the joint smoothness
  of the flow on the open interval `Ioo 0 T`), and the metric pairing of two smooth sections is
  smooth (`Work.Diff.Evol.cv_metric_pairing_at`);
* all the jets of a `C^∞` value operator are `C^∞`
  (`Work.Diff.EXT.evolX.jetAll_contMDiff_of_base`), which gives `JetSmoothOp` after replacing `C^∞`
  by `MDifferentiableAt`.
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.evolX

set_option maxHeartbeats 800000

theorem cvPairOp_jetSmoothOp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (hLV : Submission.Diff.LCVariation I M)
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hflow : Submission.Diff.IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (x : M) :
    Work.Diff.EXT.JetSmoothOp (I := I) (M := M) (G t) 3
      (Work.Diff.EXT.evolX.cvPairOp (I := I) (M := M) G t) x := by
  have hJopen : IsOpen (Set.Ioo (0 : ℝ) T) := isOpen_Ioo
  have hJs : Submission.Diff.JointSmooth G (Set.Ioo (0 : ℝ) T) :=
    hflow.1.mono (Set.prod_mono Set.Ioo_subset_Ico_self (subset_refl _))
  -- The value of the pairing on a tuple of smooth fields is `C^∞`.
  have hbase : ∀ F : Fin 3 → Work.Diff.EXT.TField (I := I) (M := M),
      (∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F i)) →
      CMDiff ∞ (Work.Diff.EXT.evolX.cvPairOp (I := I) (M := M) G t F) := by
    intro F hF y
    have hA : CMDiff ∞ (T% (fun y : M => Submission.Diff.dLC G t (F 0) (F 1) y)) :=
      fun z => Work.Diff.Evol.cv_dLC_smooth (I := I) (M := M) hLC hLV hJopen hJs ht
        (F 0) (F 1) (hF 0) (hF 1) z
    show ContMDiffAt I 𝓘(ℝ,ℝ) ∞ (fun y : M =>
      (G t).inner y (Submission.Diff.dLC G t (F 0) (F 1) y) (F 2 y)) y
    exact Work.Diff.Evol.cv_metric_pairing_at (I := I) (M := M) hA (hF 2) y
  -- All the jets of a `C^∞` value operator are `C^∞`, hence `JetSmoothOp`.
  filter_upwards with y
  intro l F hF
  exact ((Work.Diff.EXT.evolX.jetAll_contMDiff_of_base (I := I) (M := M) hLC (G t)
      (K := 3) (S := Work.Diff.EXT.evolX.cvPairOp (I := I) (M := M) G t) hbase l F hF)).contMDiffAt.mdifferentiableAt
    (by simp)

end Work.Diff.EXT.evolX
