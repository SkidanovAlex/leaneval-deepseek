import Mathlib
import Submission.Work.PinchLemma3.ClosedDiscA.windingSpan_union_le_sup_of_isPathConnected_inter
import Submission.Work.PinchLemma3.ClosedDiscA.finrank_windingSpan_union_le_of_pieces_of_components
import Submission.Work.SurgeryInvariance.Span.union_eq_sup

/-!
# The finrank bound `≤ 1` for a union with at most two gates

`Work.Drive.Final.finrank_windingSpan_union_le_one_of_two_gates`: if `A` and `E` are regions of
the torus `F = P.carrier` which are open in the carrier, path connected and inessential
(`WindingSpan P A = WindingSpan P E = ⊥`), and if their intersection is covered by at most two
connected components `C_a`, `C_b` of `A ∩ E` (of which `C_a` is path connected, as recorded by
the hypothesis `h2`), then

  `finrank ℚ W(A ∪ E) ≤ 1`.

Two facts make this true.

* Every connected component of `A ∩ E` is path connected: `A ∩ E` is open in the surface `F`,
  which is locally path connected, so its components are path connected
  (`isPathConnected_connectedComponentIn_carrier`).  Hence the two gates `C_a`, `C_b` of `h2` are
  honest (possibly empty) path connected pieces.
* If `b ∉ A ∩ E`, or if `C_a = C_b`, then `A ∩ E = C_a` is itself path connected and the one-gate
  subadditivity `windingSpan_union_le_sup_of_isPathConnected_inter` gives `W(A ∪ E) ≤ ⊥`.
  Otherwise the two gates are disjoint and cover `A ∩ E`, so the two-gate criterion
  `exists_ne_zero_inf_span_le_of_intersection_pair_general` exhibits a line `ℚ ∙ v` with
  `W(A ∪ E) ⊓ ℚ ∙ v ≤ W(A) ⊔ W(E) = ⊥`, and the linear algebra
  `finrank_le_one_of_inf_span_le_bot` concludes `finrank W(A ∪ E) ≤ 1`.
-/

open LeanEval.KnotTheory.PardonDistortion Set

namespace Work.Drive.Final

-- `hAconn` and `hEconn` are part of the requested interface but are not needed by the argument.
set_option linter.unusedVariables false

theorem finrank_windingSpan_union_le_one_of_two_gates {P : Work.CoreTopology.ParamTorus} {A E : Set LeanEval.KnotTheory.PardonDistortion.R3} (hAc : A ⊆ P.carrier) (hEc : E ⊆ P.carrier) (hA : Work.SurgeryInvariance.IsOpenInCarrier P A) (hE : Work.SurgeryInvariance.IsOpenInCarrier P E) (hAconn : IsPathConnected A) (hEconn : IsPathConnected E) (hWA : Work.SurgeryInvariance.WindingSpan P A = ⊥) (hWE : Work.SurgeryInvariance.WindingSpan P E = ⊥) (h2 : ∃ a b : LeanEval.KnotTheory.PardonDistortion.R3, IsPathConnected (A ∩ E ∩ connectedComponentIn (A ∩ E) a) ∧ (A ∩ E) ⊆ connectedComponentIn (A ∩ E) a ∪ connectedComponentIn (A ∩ E) b) : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (A ∪ E)) ≤ 1 := by
  classical
  obtain ⟨a, b, hpc, hcov⟩ := h2
  -- `A ∩ E` is open in the carrier, and its two gates lie in `A ∩ E`
  have hABC : A ∩ E ⊆ P.carrier := fun x hx => hAc hx.1
  have hABop : Work.SurgeryInvariance.IsOpenInCarrier P (A ∩ E) :=
    Work.SurgeryInvariance.isOpenInCarrier_inter P hA hE
  have hC₁sub : connectedComponentIn (A ∩ E) a ⊆ A ∩ E := connectedComponentIn_subset _ _
  have hC₂sub : connectedComponentIn (A ∩ E) b ⊆ A ∩ E := connectedComponentIn_subset _ _
  -- the first gate is path connected (it is `A ∩ E ∩ C_a`, and `C_a ⊆ A ∩ E`)
  have hpc₁ : IsPathConnected (connectedComponentIn (A ∩ E) a) := by
    have h := hpc
    rw [Set.inter_eq_right.mpr hC₁sub] at h
    exact h
  -- the case in which `A ∩ E` is a single gate
  have single : A ∩ E = connectedComponentIn (A ∩ E) a →
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (A ∪ E)) ≤ 1 := by
    intro hinter
    have hpcAE : IsPathConnected (A ∩ E) := by
      rw [hinter]
      exact hpc₁
    have hle := Work.PinchLemma3.ClosedDiscA.windingSpan_union_le_sup_of_isPathConnected_inter
      (P := P) (A := A) (B := E) hAc hEc hA hE hpcAE
    rw [hWA, hWE, sup_bot_eq] at hle
    have h0 : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (A ∪ E)) = 0 := by
      rw [le_bot_iff.mp hle, finrank_bot]
    omega
  by_cases hbC : b ∈ A ∩ E
  · -- the second gate is a genuine component of `A ∩ E`, hence path connected
    have hpc₂ : IsPathConnected (connectedComponentIn (A ∩ E) b) :=
      Work.PinchLemma3.ClosedDiscA.isPathConnected_connectedComponentIn_carrier
        (P := P) hABop hABC hbC
    by_cases heq : connectedComponentIn (A ∩ E) a = connectedComponentIn (A ∩ E) b
    · -- the two gates coincide: the intersection is the single gate `C_a`
      refine single ?_
      refine Subset.antisymm ?_ hC₁sub
      intro x hx
      rcases hcov hx with h | h
      · exact h
      · rw [heq]; exact h
    · -- the two gates are disjoint path connected pieces covering `A ∩ E`
      have hdisj : Disjoint (connectedComponentIn (A ∩ E) a)
          (connectedComponentIn (A ∩ E) b) := by
        refine Set.disjoint_left.mpr ?_
        intro x hx₁ hx₂
        exact heq ((connectedComponentIn_eq hx₁).trans (connectedComponentIn_eq hx₂).symm)
      have hunion : A ∩ E = connectedComponentIn (A ∩ E) a ∪ connectedComponentIn (A ∩ E) b :=
        Subset.antisymm hcov (Set.union_subset hC₁sub hC₂sub)
      obtain ⟨v, hvne, hvle⟩ :=
        Work.PinchLemma3.ClosedDiscA.exists_ne_zero_inf_span_le_of_intersection_pair_general
          (P := P) (A := A) (B := E) hAc hEc hA hE hWA hWE
          (fun x hx => hAc (hC₁sub hx).1) (fun x hx => hEc (hC₂sub hx).2)
          (Work.PinchLemma3.ClosedDiscA.isOpenInCarrier_connectedComponentIn
            (P := P) hABop hABC a)
          (Work.PinchLemma3.ClosedDiscA.isOpenInCarrier_connectedComponentIn
            (P := P) hABop hABC b)
          hpc₁ hpc₂ hdisj hunion
      rw [hWA, hWE, sup_bot_eq] at hvle
      exact Work.PinchLemma3.ClosedDiscA.finrank_le_one_of_inf_span_le_bot hvne hvle
  · -- `b ∉ A ∩ E`: the second gate is empty, so the intersection is the single gate `C_a`
    refine single ?_
    refine Subset.antisymm ?_ hC₁sub
    intro x hx
    rcases hcov hx with h | h
    · exact h
    · rw [connectedComponentIn_eq_empty hbC] at h
      exact h.elim

end Work.Drive.Final
