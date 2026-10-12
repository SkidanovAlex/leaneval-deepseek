import ChallengeDeps
import Submission.Work.BoseB1Cube.nomRowSqWindowRow
import Submission.Work.BoseSWE.F4d_Node
import Submission.Work.BoseSWE.lightBoxENode_holds
import Submission.Work.BoseSWE.massiveRegularNode_holds
import Submission.Work.BoseSWE.nomRowLinWindowRowE_of_normNodeE
import Submission.Work.BoseSWE.perBoxFNomE_inBox_of_windowRowsE
import Submission.Work.BoseSWE.perBoxFNomMuE_of_inBoxRowE_proved
import Submission.Work.BoseSWE.regularSR2Node_holds
import Submission.Work.BoseSWE.sr2LocalNode_holds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseSWE.Final` — the subproject `BoseSWE`'s deliverable

    `Work.BoseSWE.nodeB1B_final : Work.BoseBoxFix.NodeB1B v h J`

for every `v : E3 → ℝ` with `ScatSol v`, `0 ≤ v`, `MemLp v 1`, radial, `tsupport v ⊆ ball 0 R`
(`0 < R`) and `0 < a v`, and every real `J`.  This is FS `thm:aprioribounds` (the §5 node of the
root assembly), obtained **without** the hole/edge node `Work.BoseB1Cube.SmallWinHolePD`: the
vanishing slack `ErrE v C μ n = C·(a v)·μ·n·d^80` is carried through the small-window row
(`Work.BoseSWE.SmallWinPropE`) and absorbed by the a-priori ledger's error slot at the far end.

The composition (each step is a theorem in this directory):

```
SmallWinPropE          ⟸ sr2LocalNode_holds (N1) + regularSR2Node_holds (N2)
                          + massiveRegularNode_holds (N2′) + lightBoxENode_holds (E)
                          [Work.BoseSWE.smallWinPropE_of_nodes, PROVED in Defs]
NormNodeE              ⟸ SmallWinPropE            [normNodeE_of_smallWinPropE, PROVED in Defs]
NomRowLinWindowRowE    ⟸ NormNodeE                [nomRowLinWindowRowE_of_normNodeE]
PerBoxFNomE (in-box)   ⟸ NomRowLinWindowRowE + Work.BoseB1Cube.NomRowSqWindowRow (PROVED)
                                                  [perBoxFNomE_inBox_of_windowRowsE]
PerBoxFNomMuE          ⟸ the in-box row          [perBoxFNomMuE_of_inBoxRowE_proved]
NodeB1B                ⟸ PerBoxFNomMuE            [Work.BoseSWE.nodeB1B_of_perBoxFNomMuE]
```
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseSWE

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **THE DELIVERABLE.**  The frozen §5 node `Work.BoseBoxFix.NodeB1B v h J` (FS
`thm:aprioribounds`) from the `E`-route: no hole/edge node is used, only the four box-region nodes
of `Submission/Work/BoseSWE/BRIEF.md` and the PROVED downstream chain. -/
theorem nodeB1B_final {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < _root_.BoseGases.a v) (J : ℝ) :
    Work.BoseBoxFix.NodeB1B v h J := by
  -- ## 1. the four box-region nodes give the small-window row with the vanishing slack
  have hE : SmallWinPropE v h :=
    smallWinPropE_of_nodes (v := v) h hav
      (sr2LocalNode_holds h hv hv1 hvrad hR hv_supp hav)
      (regularSR2Node_holds h hv hv1 hvrad hR hv_supp hav)
      (massiveRegularNode_holds h hv hv1 hvrad hR hv_supp hav)
      (lightBoxENode_holds h hv hv1 hvrad hR hv_supp hav)
  -- ## 2. the normalised row with the slack
  have hN : NormNodeE v h :=
    normNodeE_of_smallWinPropE (v := v) h hv hv1 hvrad hR hv_supp hav hE
  -- ## 3. piece C with the slack
  have hC : NomRowLinWindowRowE v h R :=
    nomRowLinWindowRowE_of_normNodeE (v := v) h hv hv1 hvrad hR hv_supp hav hN
  -- ## 4. the two windowed rows at the descent's constants: piece C at `Cn = 4`,
  --    piece A (`Work.BoseB1Cube.nomRowSqWindowRow`, PROVED) at `Cn = 8`
  obtain ⟨εg, Cg, hεg, hCg, hGRP₀⟩ := hC 4 (by norm_num)
  obtain ⟨εr, Cr, hεr, hCr, hREM₀⟩ :=
    Work.BoseB1Cube.nomRowSqWindowRow (v := v) h hv hv1 hvrad hR hv_supp hav 8 (by norm_num)
  obtain ⟨ε₁, hε₁pos, hε₁le, hIn⟩ :=
    perBoxFNomE_inBox_of_windowRowsE (v := v) h hv hv1 hvrad hR hv_supp hav
      (Cn := 4) (ε₀ := min εg εr) (C := Cr) (CE := Cg) (by norm_num)
      (lt_min hεg hεr) hCr hCg
      (fun μ hAdm n' Ψ u hu hΨ hsupp h1 h2 =>
        hGRP₀ μ (Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)) n' Ψ u hu hΨ hsupp h1 h2)
      (fun μ hAdm n' Ψ u hu hΨ hsupp h2 =>
        hREM₀ μ (Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)) n' Ψ u hu hΨ hsupp
          (by linarith [h2]))
  -- ## 5. piece B (arity passage) gives the one-slot row for every box state
  exact nodeB1B_of_perBoxFNomMuE (v := v) (J := J) h hv hv1 hvrad hR hv_supp hav
    (perBoxFNomMuE_of_inBoxRowE_proved (v := v) h hv hv1 hvrad hR hv_supp hav
      hε₁pos hCr hCg hIn)

end Work.BoseSWE

#print axioms Work.BoseSWE.nodeB1B_final
