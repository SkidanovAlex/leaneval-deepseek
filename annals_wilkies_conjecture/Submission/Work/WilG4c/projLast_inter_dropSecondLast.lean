import Mathlib
import Submission.Work.WilG4c.ClampDefs

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-- Membership in the graph of a family member, in terms of `Fin.init`: the value coordinate
(the last one) is `f` applied to the initial `p` coordinates (`l`) and the next `m`
coordinates (`u`). -/
theorem famGraph_apply {p m : ℕ} (f : (Fin p → ℝ) → (Fin m → ℝ) → ℝ)
    (w : Fin (p + m + 1) → ℝ) :
    w ∈ WilkiesDesign.CG.famGraph f ↔
      w (Fin.last (p + m)) = f (fun i : Fin p => (Fin.init w) (Fin.castAdd m i))
        (fun j : Fin m => (Fin.init w) (Fin.natAdd p j)) := by
  simp [WilkiesDesign.CG.famGraph, WilkiesDesign.graphOf]

theorem projLast_inter_dropSecondLast {p m : ℕ} (f : (Fin p → ℝ) → (Fin m → ℝ) → ℝ) :
    WilkiesDesign.projLast
        ({z : Fin ((p + m) + 2) → ℝ |
            z ∘ Work.WilG4c.dropSecondLast (p + m) ∈ WilkiesDesign.CG.famGraph f} ∩
          Work.WilG4c.clampRel (p + m))
      = WilkiesDesign.CG.famGraph
          (fun l u => if f l u ∈ Set.Ioo (0 : ℝ) 1 then f l u else (1 / 2 : ℝ)) := by
  ext x
  simp only [WilkiesDesign.projLast, Set.mem_ofPred_eq, Set.mem_inter_iff, mem_clampRel,
    dropSecondLast_comp_snoc, Fin.snoc_castSucc, Fin.snoc_last, Fin.init_snoc,
    famGraph_apply]
  constructor
  · rintro ⟨t, rfl, h⟩; exact h
  · intro h; exact ⟨_, rfl, h⟩

end Work.WilG4c
