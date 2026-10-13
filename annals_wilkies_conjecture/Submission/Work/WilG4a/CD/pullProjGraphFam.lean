import Mathlib
import Submission.Work.WilG4a.CD.graphFamParamDefs

namespace Work.WilG4a.CD

/-- Unfolding of the pullback of `paramGraph Ψ` along the coordinate map `pullIdxA`:
on the ambient space with layout `(u, x, y, v)` it is the condition `v = Ψ u`. -/
theorem mem_pullIdxA_paramGraph (k p : ℕ) (Ψ : (Fin k → ℝ) → (Fin p → ℝ))
    (z : Fin ((k + 1 + 1) + p) → ℝ) :
    z ∘ pullIdxA k p ∈ paramGraph Ψ ↔
      ∀ j : Fin p, z (Fin.natAdd (k + 1 + 1) j) =
        Ψ (fun i : Fin k => z (Fin.castAdd p (Fin.castSucc (Fin.castSucc i)))) j := by
  simp only [paramGraph, Set.mem_ofPred_eq, Function.comp_def,
    pullIdxA_natAdd, pullIdxA_castAdd]

/-- Unfolding of the pullback of `graphFam f` along the coordinate map `pullIdxB`:
on the ambient space with layout `(u, x, y, v)` it is the condition `y = f v x`. -/
theorem mem_pullIdxB_graphFam (k p : ℕ) (f : (Fin p → ℝ) → ℝ → ℝ)
    (z : Fin ((k + 1 + 1) + p) → ℝ) :
    z ∘ pullIdxB k p ∈ Work.WilG4a.graphFam f ↔
      z (Fin.castAdd p (Fin.last (k + 1))) =
        f (fun j : Fin p => z (Fin.natAdd (k + 1 + 1) j))
          (z (Fin.castAdd p (Fin.castSucc (Fin.last k)))) := by
  rw [Work.WilG4a.mem_graphFam]
  simp only [Function.comp_def, pullIdxB_last, pullIdxB_castSucc_castSucc,
    pullIdxB_castSucc_last]

theorem pullProjGraphFam (k p : ℕ) (f : (Fin p → ℝ) → ℝ → ℝ)
    (Ψ : (Fin k → ℝ) → (Fin p → ℝ)) :
    Work.WilG0.projLastIter (k + 1 + 1) p
        ({z : Fin ((k + 1 + 1) + p) → ℝ |
            z ∘ Work.WilG4a.CD.pullIdxA k p ∈ Work.WilG4a.CD.paramGraph Ψ} ∩
         {z : Fin ((k + 1 + 1) + p) → ℝ |
            z ∘ Work.WilG4a.CD.pullIdxB k p ∈ Work.WilG4a.graphFam f})
      = Work.WilG4a.graphFam (fun (u : Fin k → ℝ) (x : ℝ) => f (Ψ u) x) := by
  rw [Work.WilG0.projLastIter_eq]
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨v, hA, hB⟩
    rw [Work.WilG4a.mem_graphFam]
    have hA' := (mem_pullIdxA_paramGraph k p Ψ
      (Work.WilG0.snocIt (k + 1 + 1) p w v)).mp hA
    have hB' := (mem_pullIdxB_graphFam k p f
      (Work.WilG0.snocIt (k + 1 + 1) p w v)).mp hB
    simp only [Work.WilG0.snocIt_natAdd, Work.WilG0.snocIt_castAdd] at hA' hB'
    have hv : v = Ψ (fun i : Fin k => w (Fin.castSucc (Fin.castSucc i))) := funext hA'
    rw [hv] at hB'
    exact hB'
  · intro hw
    rw [Work.WilG4a.mem_graphFam] at hw
    refine ⟨Ψ (fun i : Fin k => w (Fin.castSucc (Fin.castSucc i))), ?_, ?_⟩
    · rw [mem_pullIdxA_paramGraph]
      intro j
      simp only [Work.WilG0.snocIt_natAdd, Work.WilG0.snocIt_castAdd]
    · rw [mem_pullIdxB_graphFam]
      simp only [Work.WilG0.snocIt_natAdd, Work.WilG0.snocIt_castAdd]
      exact hw

end Work.WilG4a.CD
