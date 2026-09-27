import Mathlib
import Submission.Work.Drive.hdenseDesignData
import Submission.Work.Drive.hdenseNodeRows
import Submission.Work.Drive.exists_classRowFamily

/-!
# STATUS of this node (the `hdense` wall node) — read `HDENSE_STATUS.md` and `URGENT_hdenseOneT_build_break.md`

The target below is **unchanged** (byte-identical to the delegation, one `sorry`).  The node's own proof
cannot be written until three things are done (details in the two files above):

1. **`hdenseOneT.lean` does not build** (duplicate `T6GenAtDBox`, line 141, vs the `abbrev` of the same
   name in `T6GenAtD.lean:135`), which blocks `germDataAt`, `hdense_identity_of_designTripleAt` and
   `dense_T6GenAtDBox_design` — the three inputs of steps (E3)/(E4).  Fix: delete one of the two
   declarations (they are definitionally equal).  *Owner: the H3 lane; not edited here.*
2. **The import cycle**: `hdenseOneT`, `exists_meet3Hyp_rot_local_of_opens`, `germDataAt`,
   `hdense_identity_of_designTripleAt` and `eventually_DiamFamRegBox` still import *this* file, only for
   the declarations that now live in `Submission/Work/Drive/hdenseDesignData.lean` (moved there in the
   session of 2026-09-26); they must import that module instead.
3. **`Submission/Work/Drive/exists_designTripleAt_blockT6.lean`** (the (E4) producer, this lane's
   assignment) has to be written; `HDENSE_STATUS.md`, addendum 2, lists its exact `Pcond` inputs.

Once those are done the node's proof is the lead's (E5): `exists_germDataAt` for the germ data,
`hdense_identity_of_designTripleAt` at the (E4) parameter `t`, then `sideGerm_indep` at the six angles
of `{a, a+c', -a, c', -(a+c'), -c'}`, then `subset_closure`.
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology BigOperators

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

set_option maxHeartbeats 4000000


/-- **The `hdense` input of the germ route**: the germ side value satisfies the functional identity on a dense set of triples.  Verbatim the `hdense` hypothesis of `Work.Drive.parityCore_of_sideGerm` (`sideGerm.lean:170`), with the chart data that is obtainable (`IsPlaneChart` plus injectivity) instead of its `hdisj`/`IsChartData`.  With its sibling `hn2` (`Drive/hn2_sideGerm_reference`) and the already-unconditional `Work.Drive.sideGerm_localconst_of_planeChart_unconditional`, the assembly `Work.Drive.parityCore_of_sideGerm` then yields `Work.Drive.ParityCore γ` — the wall `Work.Drive.chainParity` behind `Work.Drive.orderWitnessExists`.

Route: the same triple count as `hn2` but with the triple chosen **generically** rather than at one reference triple, so each block identity is available on a dense set (`HN2_REFERENCE_STATUS.md` §2, `CHAINPARITY_REDUCTION.md` §1).  The bricks are the assembly lane's: `Submission/Work/Drive/hdenseAssembly.lean`, the triple engine `Work.Drive.odd_sum_topBdryMeet_clampedSweeps_of_planes`, the transport `Work.Drive.odd_topBdryMeet_zero_iff_coreSideCount_mul` (`transportThreeLevel.lean`, proved — note it carries about twenty design inputs per block), the level bridge and the genericity/density of the good triples (`SWEEP_TRIPLE_GENERIC_STATUS.md`).  Careful: `hdenseAssembly` works with three distinct levels while this statement fixes a single `c`, so level-independence has to be carried explicitly.  The imports listed are only the starting point — add whatever the assembly lane needs.

**Statement update (project lead, `NOTES_LEAD_hdense.md` §6, session of 2026-09-26).**  The hypothesis
`hdisjZc` — whole-plane disjointness of the chart's disk from its rotation, for the angles in `Zc γ` —
has been **added** to the statement.  The reason: the transport `T6`'s avoidances of the design
(`hδcut`, the `havoid` fields of the two `T5` deformation families, the separation of the `x 2 = 0`
shadow face) are *not* consequences of `IsPlaneChart` plus injectivity; they need the whole-plane
disjointness, which is a property of the chart lane's *output*
(`Work.Drive.exists_planeChart_chartDisk_disjoint_capSection`, proved), not of an arbitrary plane
chart.  All consumers of the node in this workspace (`hdenseOneT.lean`,
`parityCore_of_germInputs.lean`) are written against this form, and every warning above about
`hdisj`/`IsChartData` remains valid: the disjointness is what makes the counting route's avoidances
available, and only its *chart-side* form `hdisjZc` is obtainable. -/
theorem hdense_sideGerm {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    (hγinj : Function.Injective γ)
    {Q : ℂ → Work.Drive.CappingSpace} (hQ : Work.Drive.IsPlaneChart γ hγne Q) {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → Work.Drive.CappingSpace → Work.Drive.CappingSpace) (c : ℝ)
    (hΞ : Work.Drive.ChartPert Q m Ξ) (hc : 0 < c)
    (hcbot : ∀ p ∈ Work.Drive.chartDisk Q, c < Work.Drive.levelOf p)
    (hdisjZc : ∀ w : UnitAddCircle, w ∈ Work.Drive.Zc γ →
      Disjoint (Work.Drive.chartDisk Q) (Work.Drive.rotCapping w '' Work.Drive.chartDisk Q)) :
    ∀ a c' : UnitAddCircle, a ∈ Work.Drive.Zc γ → c' ∈ Work.Drive.Zc γ → a + c' ∈ Work.Drive.Zc γ →
      (a, c') ∈ closure {q : UnitAddCircle × UnitAddCircle |
        q.1 ∈ Work.Drive.Zc γ ∧ q.2 ∈ Work.Drive.Zc γ ∧ q.1 + q.2 ∈ Work.Drive.Zc γ ∧
          Work.Drive.sideGerm Ξ Q c q.1 * Work.Drive.sideGerm Ξ Q c (q.1 + q.2)
            + Work.Drive.sideGerm Ξ Q c (-q.1) * Work.Drive.sideGerm Ξ Q c q.2
            + Work.Drive.sideGerm Ξ Q c (-(q.1 + q.2)) * Work.Drive.sideGerm Ξ Q c (-q.2) = 1} := by
  exact hdense_sideGerm_of_classRowFamily hγinj hQ Ξ c hΞ hc hcbot hdisjZc
    (fun a c' ha hc' hac => exists_classRowFamily hγinj hQ hc hcbot hdisjZc a c' ha hc' hac)

end

end Work.Drive
