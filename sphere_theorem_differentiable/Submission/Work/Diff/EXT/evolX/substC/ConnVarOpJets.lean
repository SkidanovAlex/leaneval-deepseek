import Mathlib
import Submission.Work.Diff.EXT.evolX.connVarDefs
import Submission.Work.Diff.EXT.evolX.connVarOp_jets_assembly
import Submission.Work.Diff.EXT.evolX.substC.Assembly
import Submission.Work.Diff.EXT.evolX.connVar_pair_jets
import Submission.Work.Diff.EXT.evolX.connVarPairDefs
import Submission.Work.Diff.EXT.evolX.towerJets
import Submission.Work.Diff.EXT.evolX.ckt_jetSmoothOp
import Submission.Work.Diff.EXT.evolX.cvPairOp_jetSmoothOp
import Submission.Work.Diff.EXT.evolX.jetAll_neg_of_JetSmoothOp
import Submission.Work.Diff.EXT.jetSmoothDefs
import Submission.Work.Diff.T.lc_smooth
import Submission.Work.Diff.T.lc_variation
import Submission.Work.EXT.lcSmooth_noBoundary

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `connVarOp_jets` (copy of the W-chain version, using the local assembly `substC.substOp_jets_le_C`)

See `Submission/Work/Diff/EXT/evolX/substC/` for the whole independent chain
`substC.Assembly` → `substC.ConnVarOpJets` → `substC.ConnVarSrcJets` → `substC.LadderStep` →
`substC.ReactAll`, which feeds `Work.Diff.EXT.evolK_of_flow` without depending on
`Work.Diff.EXT.evolX.substOpJetsW`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.evolX

/-- The vector-valued operator `pairOp g (vdlcOp G t)` is the connection-variation pairing
`cvPairOp G t` of `Submission/Work/Diff/EXT/evolX/connVarPairDefs.lean`. -/
theorem pairOp_vdlcOp_eq_cvPairOpC
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) :
    pairOp (I := I) (M := M) (G t) (vdlcOp (I := I) (M := M) G t)
      = cvPairOp (I := I) (M := M) G t :=
  rfl

/-- **The jet bound for the connection-variation operator** (the connection-variation source of the
reaction ladder of the `k`-th order Shi estimate).  It is assembled in
`Submission/Work/Diff/EXT/evolX/connVarOp_jets_assembly.lean` from the per-summand contraction
bound `Work.Diff.EXT.evolX.substOp_jets_le_v2` (with the vector-valued operator `∂ₜ∇ = vdlcOp`,
whose pairing strength is `Work.Diff.EXT.evolX.connVar_pair_jets`) and the jet calculus of the
finite sum. -/
theorem connVarOp_jetsC
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (k j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (G : ℝ → Submission.Diff.SMet I M) (T : ℝ), Submission.Diff.IsRicciFlow G T →
        ∀ t ∈ Set.Ioo 0 T, ∀ x : M,
        ∀ (F : Fin ((k + 5) + j) → Work.Diff.EXT.TField (I := I) (M := M)),
          (∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F i)) →
          |Work.Diff.EXT.jetAll (G t) j (k + 5)
              (Work.Diff.EXT.evolX.connVarOp (I := I) (M := M) G t k) F x|
            ≤ C * Work.Diff.EXT.Shape (G t) x (k + 1 + j)
                * ∏ r : Fin ((k + 5) + j),
                    Real.sqrt ((G t).inner x (F r x) (F r x)) := by
  have hLC : Submission.Diff.LCSmooth I M := Work.EXT.lcSmooth_noBoundary (I := I) (M := M)
  have hLV : Submission.Diff.LCVariation I M := Work.Diff.T.lc_variation (I := I) (M := M) hLC
  -- the negation rule of the jets (proved by the `connVar_src` chapter)
  have hneg : JetNegRule (I := I) (M := M) := fun g S x hS jj F hF =>
    Work.Diff.EXT.evolX.jetAll_neg_of_JetSmoothOp (I := I) (M := M) hLC hS jj F hF
  -- the pairing strength of `∂ₜ∇` (one constant per jet order, from `connVar_pair_jets`)
  set CV : ℕ → ℝ := fun a => Classical.choose (connVar_pair_jets (I := I) (M := M) a) with hCVdef
  have hCV : ∀ a, 0 ≤ CV a :=
    fun a => (Classical.choose_spec (connVar_pair_jets (I := I) (M := M) a)).1
  -- the per-summand contraction bound
  have hsubst : ConnVarSubstBound (I := I) (M := M) k j CV := by
    intro G T hflow t ht x s F hF
    have hV : StrongAt (I := I) (M := M) (G t) x 1 CV
        (pairOp (I := I) (M := M) (G t) (vdlcOp (I := I) (M := M) G t)) := by
      intro a G' hG'
      have h := (Classical.choose_spec (connVar_pair_jets (I := I) (M := M) a)).2
        G T hflow t ht x G' hG'
      rw [pairOp_vdlcOp_eq_cvPairOpC]
      exact h
    have hVs : Work.Diff.EXT.JetSmoothOp (I := I) (M := M) (G t) 3
        (pairOp (I := I) (M := M) (G t) (vdlcOp (I := I) (M := M) G t)) x := by
      rw [pairOp_vdlcOp_eq_cvPairOpC]
      exact cvPairOp_jetSmoothOp (I := I) (M := M) hLC hLV hflow ht x
    have hTs : Work.Diff.EXT.JetSmoothOp (I := I) (M := M) (G t) (k + 4)
        (Work.Diff.EXT.ckt (I := I) (M := M) (G t) k) x :=
      jetSmoothOp_ckt (I := I) (M := M) hLC (G t) x k
    have htw : StrongAt (I := I) (M := M) (G t) x k (fun _ => (1 : ℝ))
        (Work.Diff.EXT.ckt (I := I) (M := M) (G t) k) :=
      strongAt_ckt (I := I) (M := M) (G t) x k
    simpa only [mul_one] using substC.substOp_jets_le_C (I := I) (M := M) hLC k s (fun _ => (1 : ℝ)) CV
      (fun _ => zero_le_one) hCV (G t) x (vdlcOp (I := I) (M := M) G t)
      htw hV hTs hVs j F hF
  exact connVarOp_jets_of_subst (I := I) (M := M) hneg k j CV hCV hsubst

end Work.Diff.EXT.evolX
