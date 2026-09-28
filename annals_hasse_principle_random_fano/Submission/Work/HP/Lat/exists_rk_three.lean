import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Lat.mem_span_pair_of_not_linIndep
import Submission.Work.HP.Lat.exists_single_notMem_span_pair

namespace Work.HP.Lat

open Work.HP

/-- Two `ℤ`-linearly independent vectors of `ℤ^ι` (`card ι ≥ 3`) are contained in a sublattice of
rank three.

Suggested route: choose `j` such that `x`, `y`, `Pi.single j 1` are `ℤ`-independent (possible since
`card ι ≥ 3` and `x,y` span a plane), and take `L = Submodule.span ℤ {x, y, Pi.single j 1}`; then
`L` has rank three (`LinearIndependent.finrank_span_eq_card`) and contains `x` and `y`. -/
theorem exists_rk_three {ι : Type*} [Fintype ι] (x y : ι → ℤ)
    (h : LinearIndependent ℤ ![x, y]) (hcard : 3 ≤ Fintype.card ι) :
    ∃ L : Submodule ℤ (ι → ℤ), rk L = 3 ∧ x ∈ L ∧ y ∈ L := by
  classical
  -- Over `ℚ` the two vectors `x, y` span a space of dimension at most two, so some coordinate
  -- basis vector `e_j` escapes it.
  obtain ⟨j, hj⟩ :=
    exists_single_notMem_span_pair (fun i => (x i : ℚ)) (fun i => (y i : ℚ)) hcard
  -- Both the cast of `Pi.single j 1` and `Pi.single j (1 : ℚ)` are the same vector of `ℚ^ι`.
  have hcast :
      (fun i => (((Pi.single j (1 : ℤ) : ι → ℤ)) i : ℚ)) = (Pi.single j (1 : ℚ) : ι → ℚ) := by
    ext i
    by_cases hi : i = j
    · subst hi; simp
    · have h1 : (Pi.single j (1 : ℤ) : ι → ℤ) i = 0 :=
        Pi.single_eq_of_ne (M := fun _ => ℤ) hi 1
      have h2 : (Pi.single j (1 : ℚ) : ι → ℚ) i = 0 :=
        Pi.single_eq_of_ne (M := fun _ => ℚ) hi 1
      rw [h1, h2]; simp
  -- Hence `x, y, e_j` are `ℤ`-linearly independent.
  have hLI : LinearIndependent ℤ ![x, y, (Pi.single j (1 : ℤ) : ι → ℤ)] := by
    by_contra hcon
    have hmem := mem_span_pair_of_not_linIndep x y (Pi.single j (1 : ℤ) : ι → ℤ) h hcon
    exact hj (hcast ▸ hmem)
  refine ⟨Submodule.span ℤ (Set.range ![x, y, (Pi.single j (1 : ℤ) : ι → ℤ)]), ?_, ?_, ?_⟩
  · rw [rk, finrank_span_eq_card hLI, Fintype.card_fin]
  · exact Submodule.subset_span ⟨0, by simp⟩
  · exact Submodule.subset_span ⟨1, by simp⟩

end Work.HP.Lat
