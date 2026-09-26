import Mathlib
import Submission.Work.SG.sgTauDefs

namespace Work.SG.Tau

/-- General accumulator form of `wfold_mem`: folding a valid word of generator indices through
right multiplication, starting from any `a ∈ sgClose gens k [sgOne]`, lands in
`sgClose gens (k + w.length) [sgOne]` (one closure round per letter). -/
theorem foldl_wfold_mem (gens : List (List ℤ × List ℚ)) (w : List ℕ)
    (h : ∀ i ∈ w, i < gens.length) :
    ∀ (k : ℕ) (a : List ℤ × List ℚ), a ∈ sgClose gens k [sgOne] →
      w.foldl (fun a i => sgMulPair a (gens.getD i sgOne)) a
        ∈ sgClose gens (k + w.length) [sgOne] := by
  induction w with
  | nil =>
      intro k a ha
      simpa using ha
  | cons i rest ih =>
      intro k a ha
      have hi : i < gens.length := h i (List.mem_cons_self ..)
      have hrest : ∀ j ∈ rest, j < gens.length := fun j hj => h j (List.mem_cons_of_mem _ hj)
      have hg : gens.getD i sgOne ∈ gens := by
        rw [List.getD_eq_getElem gens sgOne hi]
        exact List.getElem_mem hi
      have ha' : sgMulPair a (gens.getD i sgOne) ∈ sgClose gens (k + 1) [sgOne] := by
        rw [mem_sgClose_succ, mem_sgF]
        exact Or.inr ⟨a, ha, gens.getD i sgOne, hg, rfl⟩
      have hstep := ih hrest (k + 1) (sgMulPair a (gens.getD i sgOne)) ha'
      simp only [List.foldl_cons, List.length_cons]
      have hidx : (k + 1) + rest.length = k + (rest.length + 1) := by omega
      rw [hidx] at hstep
      exact hstep

theorem wfold_mem (gens : List (List ℤ × List ℚ)) :
    ∀ w : List ℕ, (∀ i ∈ w, i < gens.length) → wfold gens w ∈ sgClose gens w.length [sgOne] := by
  intro w h
  have h' := foldl_wfold_mem gens w h 0 sgOne (mem_sgClose_self 0 (List.mem_singleton_self sgOne))
  simpa [wfold] using h'

end Work.SG.Tau
