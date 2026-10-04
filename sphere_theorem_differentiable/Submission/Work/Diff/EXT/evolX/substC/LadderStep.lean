import Mathlib
import Submission.Work.Diff.EXT.ladderEfDefs
import Submission.Work.Diff.EXT.reactDefs
import Submission.Work.Diff.EXT.towerReactDefs
import Submission.Work.Diff.EXT.lapComm_tower
import Submission.Work.Diff.EXT.jetSmoothDefs
import Submission.Work.Diff.EXT.evolX.substC.ConnVarSrcJets
import Submission.Work.Diff.EXT.evolX.substC.LapCommSrc
import Submission.Work.Diff.EXT.evolX.opJetSmooth_dtOpD
import Submission.Work.Diff.EXT.evolX.opJetSmooth_lapOpE

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The reaction-ladder step, on the bypass assembly

This is a copy of `Submission/Work/Diff/EXT/ladderEfD_step.lean` in which the Weitzenböck source
bound is taken from `Work.Diff.EXT.lapComm_src_jetsWC`
(`Submission/Work/Diff/EXT/evolX/lapCommBypass.lean`) instead of the (uncompilable)
`Work.Diff.EXT.evolX.lapComm_src_jets`.  Everything else is unchanged.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-!
# `ladderEfD_step` (copy of the W-chain version)

Part of the independent chain `substC.Assembly` → … → `substC.ReactAll` feeding
`Work.Diff.EXT.evolK_of_flow`.
-/

namespace Work.Diff.EXT

theorem ladderEfD_stepC
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (k j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (G : ℝ → Submission.Diff.SMet I M) (T : ℝ), Submission.Diff.IsRicciFlow G T →
        ∀ t ∈ Set.Ico 0 T, ∀ x : M,
        ∀ Ef : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M),
          Work.Diff.EXT.IsFrameNear (I := I) (M := M) (G t) x Ef →
        ∀ (N : ℕ) (h1 : (k + 1 + 4) + j = N) (h2 : (k + 4) + (j + 1) = N)
          (w : Fin N → TangentSpace I x),
          |Work.Diff.EXT.jetAll (G t) j (k + 1 + 4)
              (Work.Diff.EXT.reactOpEfD (I := I) (M := M) Ef G t (k + 1))
              (fun r : Fin ((k + 1 + 4) + j) => Submission.Diff.smoothExt x (w (Fin.cast h1 r))) x
            - Work.Diff.EXT.jetAll (G t) (j + 1) (k + 4)
              (Work.Diff.EXT.reactOpEfD (I := I) (M := M) Ef G t k)
              (fun r : Fin ((k + 4) + (j + 1)) => Submission.Diff.smoothExt x (w (Fin.cast h2 r))) x|
          ≤ C * Work.Diff.EXT.Shape (G t) x ((k + 1) + j)
              * Finset.univ.prod (fun r : Fin N => Real.sqrt ((G t).inner x (w r) (w r))) := by
  obtain ⟨C₁, hC₁, h₁⟩ := evolX.connVarSrcJetsC (I := I) (M := M) k j
  obtain ⟨C₂, hC₂, h₂⟩ := evolX.lapComm_src_jetsWC (I := I) (M := M) k j
  refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, ?_⟩
  intro G T hflow t ht x Ef hEf N h1 h2 w
  set T₁ : Fin ((k + 1 + 4) + j) → TField (I := I) (M := M) :=
    fun r => Submission.Diff.smoothExt x (w (Fin.cast h1 r)) with hT₁
  set T₂ : Fin ((k + 4) + (j + 1)) → TField (I := I) (M := M) :=
    fun r => Submission.Diff.smoothExt x (w (Fin.cast h2 r)) with hT₂
  have hsm₁ : ∀ r : Fin ((k + 1 + 4) + j), SmoothF (T₁ r) :=
    fun r => Work.Diff.GE.smoothExt_cmdiff (I := I) (M := M) x (w (Fin.cast h1 r))
  have hsm₂ : ∀ r : Fin ((k + 4) + (j + 1)), SmoothF (T₂ r) :=
    fun r => Work.Diff.GE.smoothExt_cmdiff (I := I) (M := M) x (w (Fin.cast h2 r))
  have hX : jetAll (G t) j (k + 1 + 4) (reactOpEfD (I := I) (M := M) Ef G t (k + 1)) T₁ x
      = jetAll (G t) j (k + 1 + 4) (dtOpD (I := I) (M := M) G t (k + 1)) T₁ x
        - jetAll (G t) j (k + 1 + 4)
            (lapOpE (I := I) (M := M) Ef (G t) (k + 1)) T₁ x :=
    (jetAll_sub_of_JetSmoothOp (I := I) (M := M) (g := G t)
      (K := (k + 1) + 4)
      (S := dtOpD (I := I) (M := M) G t (k + 1))
      (S' := lapOpE (I := I) (M := M) Ef (G t) (k + 1)) x
      (evolX.opJetSmooth_dtOpD (I := I) (M := M) (k + 1) G T hflow t ht x)
      (evolX.opJetSmooth_lapOpE (I := I) (M := M) (k + 1) (G t) x Ef hEf.1)
      j T₁ hsm₁).eq_of_nhds
  have hY : jetAll (G t) (j + 1) (k + 4) (reactOpEfD (I := I) (M := M) Ef G t k) T₂ x
      = jetAll (G t) (j + 1) (k + 4) (dtOpD (I := I) (M := M) G t k) T₂ x
        - jetAll (G t) (j + 1) (k + 4) (lapOpE (I := I) (M := M) Ef (G t) k) T₂ x :=
    (jetAll_sub_of_JetSmoothOp (I := I) (M := M) (g := G t)
      (K := k + 4)
      (S := dtOpD (I := I) (M := M) G t k)
      (S' := lapOpE (I := I) (M := M) Ef (G t) k) x
      (evolX.opJetSmooth_dtOpD (I := I) (M := M) k G T hflow t ht x)
      (evolX.opJetSmooth_lapOpE (I := I) (M := M) k (G t) x Ef hEf.1)
      (j + 1) T₂ hsm₂).eq_of_nhds
  have hA := h₁ G T hflow t ht x Ef hEf N h1 h2 w
  have hB := h₂ G T hflow t ht x Ef hEf N h1 h2 w
  rw [hX, hY]
  have htri : |(jetAll (G t) j (k + 1 + 4) (dtOpD (I := I) (M := M) G t (k + 1)) T₁ x
        - jetAll (G t) j (k + 1 + 4) (lapOpE (I := I) (M := M) Ef (G t) (k + 1)) T₁ x)
      - (jetAll (G t) (j + 1) (k + 4) (dtOpD (I := I) (M := M) G t k) T₂ x
        - jetAll (G t) (j + 1) (k + 4) (lapOpE (I := I) (M := M) Ef (G t) k) T₂ x)|
      ≤ C₁ * Shape (G t) x ((k + 1) + j)
          * Finset.univ.prod (fun r : Fin N => Real.sqrt ((G t).inner x (w r) (w r)))
        + C₂ * Shape (G t) x ((k + 1) + j)
          * Finset.univ.prod (fun r : Fin N => Real.sqrt ((G t).inner x (w r) (w r))) := by
    have hrearr : (jetAll (G t) j (k + 1 + 4) (dtOpD (I := I) (M := M) G t (k + 1)) T₁ x
          - jetAll (G t) j (k + 1 + 4) (lapOpE (I := I) (M := M) Ef (G t) (k + 1)) T₁ x)
        - (jetAll (G t) (j + 1) (k + 4) (dtOpD (I := I) (M := M) G t k) T₂ x
          - jetAll (G t) (j + 1) (k + 4) (lapOpE (I := I) (M := M) Ef (G t) k) T₂ x)
        = (jetAll (G t) j (k + 1 + 4) (dtOpD (I := I) (M := M) G t (k + 1)) T₁ x
            - jetAll (G t) (j + 1) (k + 4) (dtOpD (I := I) (M := M) G t k) T₂ x)
          - (jetAll (G t) j (k + 1 + 4) (lapOpE (I := I) (M := M) Ef (G t) (k + 1)) T₁ x
            - jetAll (G t) (j + 1) (k + 4) (lapOpE (I := I) (M := M) Ef (G t) k) T₂ x) := by
      ring
    rw [hrearr]
    refine le_trans ?_ (add_le_add hA hB)
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le
      (jetAll (G t) j (k + 1 + 4) (dtOpD (I := I) (M := M) G t (k + 1)) T₁ x
        - jetAll (G t) (j + 1) (k + 4) (dtOpD (I := I) (M := M) G t k) T₂ x)
      (-(jetAll (G t) j (k + 1 + 4) (lapOpE (I := I) (M := M) Ef (G t) (k + 1)) T₁ x
        - jetAll (G t) (j + 1) (k + 4) (lapOpE (I := I) (M := M) Ef (G t) k) T₂ x))
  refine le_trans htri (le_of_eq ?_)
  ring

end Work.Diff.EXT
