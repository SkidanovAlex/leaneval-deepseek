import Mathlib
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG5.Reindex3

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-- The coordinate selection `Fin (p+1) → Fin (p+(n+1)+1)` that keeps the `p` parameter
coordinates together with the last (value) coordinate, skipping the `n+1` fibre variables.
In other words `x ↦ x ∘ iotaPin p n` is the projection `ℝ^{p+(n+1)+1} → ℝ^{p+1}` that
forgets the fibre coordinates. -/
private def iotaPin (p n : ℕ) : Fin (p + 1) → Fin (p + (n + 1) + 1) :=
  Fin.lastCases (Fin.last (p + (n + 1))) (fun j : Fin p => Fin.castSucc (Fin.castAdd (n + 1) j))

/-- The graph of a family that is constant in the fibre coordinates is the pullback of the
graph of the parameter function along the projection `iotaPin`. -/
private theorem famGraph_const_eq_coordPre (p n : ℕ) (pt : (Fin p → ℝ) → ℝ) :
    CG.famGraph (fun (l : Fin p → ℝ) (_ : Fin (n + 1) → ℝ) => pt l)
      = Work.WilG5.coordPre (iotaPin p n) (graphOf pt) := by
  ext z
  simp only [CG.famGraph, graphOf, Work.WilG5.coordPre, Set.mem_ofPred_eq,
    Function.comp_apply, Fin.init_def, iotaPin]
  rw [Fin.lastCases_last]
  simp only [Fin.lastCases_castSucc]

theorem FamGraphConstPtMem (S : WilkiesDesign.SOMin) {p n A0 D : ℕ}
    {pt : (Fin p → ℝ) → ℝ} (hpt : WilkiesDesign.graphOf pt ∈ S.Ω A0 D (p + 1)) :
    WilkiesDesign.CG.famGraph (fun (l : Fin p → ℝ) (_ : Fin (n + 1) → ℝ) => pt l) ∈
      S.Ω (A0 + 64 * ((p + (n + 1) + 1) + (p + 1)) + 64)
        (D + 32 * ((p + (n + 1) + 1) + (p + 1)) + 32) (p + (n + 1) + 1) := by
  have h := Work.WilG5.coordPre_mem (S := S) (m := p + 1) (N := p + (n + 1) + 1)
    (F := A0) (D := D) (ι := iotaPin p n) (A := WilkiesDesign.graphOf pt) hpt
  rw [famGraph_const_eq_coordPre p n pt]
  exact h

end Work.WilkG4c
