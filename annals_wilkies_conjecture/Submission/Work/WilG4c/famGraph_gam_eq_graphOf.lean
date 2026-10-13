import Mathlib
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.Wilkies.Defs

namespace Work.WilG4c

/-- The graph of the `j`-th coordinate of the curve `γ`, read as a `famGraph` in the
`(l, x)`-splitting of `Fin (p+1)`, is the graph of the same coordinate read off an arbitrary
`u : Fin (p+1) → ℝ`.  (Purely a `Fin`-bookkeeping identity; no `Ω`.) -/
theorem famGraph_gam_eq_graphOf (p n : ℕ) (γ : (Fin p → ℝ) → ℝ → (Fin n → ℝ)) (j : Fin n) :
    WilkiesDesign.CG.famGraph (fun (l : Fin p → ℝ) (x : Fin 1 → ℝ) => γ l (x 0) j)
      = WilkiesDesign.graphOf (fun u : Fin (p + 1) → ℝ =>
          γ (fun i : Fin p => u (Fin.castSucc i)) (u (Fin.last p)) j) := by
  ext x
  simp only [WilkiesDesign.CG.famGraph, WilkiesDesign.graphOf, Set.mem_ofPred_eq]
  have h1 : (fun i : Fin p => Fin.init x (Fin.castAdd 1 i)) =
      (fun i : Fin p => Fin.init x i.castSucc) := by
    funext i; rw [show (Fin.castAdd 1 i : Fin (p + 1)) = i.castSucc from rfl]
  have h2 : Fin.init x (Fin.natAdd p (0 : Fin 1)) = Fin.init x (Fin.last p) := by
    rw [show (Fin.natAdd p (0 : Fin 1) : Fin (p + 1)) = Fin.last p from by
      ext; simp [Fin.natAdd]]
  rw [h1, h2]

end Work.WilG4c
