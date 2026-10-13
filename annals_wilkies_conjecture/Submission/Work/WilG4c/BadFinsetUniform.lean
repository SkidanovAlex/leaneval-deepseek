import Mathlib
import Submission.Work.WilG4c.iterDir_perm
import Submission.Work.WilG4c.Engine

namespace Work.WilG4c

theorem BadFinsetUniform {n r : ℕ} (G : (Fin (n + 1) → ℝ) → ℝ)
    (hs : ∀ L : List (Fin (n + 1)), L.length ≤ r →
      ∃ s : Finset ℝ, ∀ x ∈ Work.WilkG4c.I, x ∉ (s : Set ℝ) →
        BddAbove ((fun y => |Work.WilkG4c.iterDir L G (Work.WilkG4c.pt x y)|) ''
          {y : Fin n → ℝ | y ∈ WilkiesDesign.openCube n ∧
            Work.WilkG4c.pt x y ∈ interior {z | ContDiffAt ℝ L.length G z}})) :
    ∃ B : Finset ℝ, ∀ L : List (Fin (n + 1)), L.length ≤ r →
      ∀ x ∈ Work.WilkG4c.I, x ∉ (B : Set ℝ) →
        BddAbove ((fun y => |Work.WilkG4c.iterDir L G (Work.WilkG4c.pt x y)|) ''
          {y : Fin n → ℝ | y ∈ WilkiesDesign.openCube n ∧
            Work.WilkG4c.pt x y ∈ interior {z | ContDiffAt ℝ L.length G z}}) := by
  classical
  -- There are only finitely many lists of length `≤ r`, so we may take the union of the
  -- exceptional finite sets attached to each of them.
  choose s hs' using hs
  refine ⟨(List.finite_length_le (Fin (n + 1)) r).toFinset.biUnion
    (fun L => if h : L.length ≤ r then s L h else ∅), ?_⟩
  intro L hL x hx hxB
  refine hs' L hL x hx fun hxs => hxB ?_
  refine Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨L, ?_, ?_⟩)
  · exact (Set.Finite.mem_toFinset _).mpr hL
  · rw [dite_eq_left hL]; exact hxs

end Work.WilG4c
