import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux
import Submission.Work.HP.dmin_le_exists_prim
import Submission.Work.HP.exists_prim_super
import Submission.Work.HP.Lat.exists_rk_two
import Submission.Work.HP.Lat.detL_ge_one

/-!
# A primitive rank-`2` lattice through a single vector

`𝔡₂({x}) = dmin 2 {x}` is the least determinant of a rank-`2` sublattice of `ℤ^ι` containing the
nonzero vector `x`.  If it is at most `D`, then there is a **primitive** rank-`2` sublattice `L ∋ x`
with `detL L ≤ D + 1`.

The argument mirrors `dmin_le_exists_prim` (the pair version): the defining set of determinants is
nonempty, since `x ≠ 0` and `card ι ≥ 2` (so `x` extends to an independent pair, `Lat.exists_rk_two`)
and bounded below by `0` (`Lat.detL_ge_one`), so `csInf_lt_iff` produces a rank-`2` lattice
`L ∋ x` with `detL L < D + 1`; replacing it by its saturation (`exists_prim_super`) keeps the rank
and does not increase the determinant (`detL_le_of_le_of_rank_eq`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Work.HP.FM3

theorem dmin_two_singleton_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : 2 ≤ Fintype.card ι) (x : ι → ℤ) (hx : x ≠ 0) (D : ℝ) (hD : Work.HP.dmin 2 {x} ≤ D) :
    ∃ L : Submodule ℤ (ι → ℤ), Work.HP.IsPrimLat L ∧ Work.HP.rk L = 2 ∧ x ∈ L ∧
      Work.HP.detL L ≤ D + 1 := by
  classical
  set S : Set ℝ := {E : ℝ | ∃ L : Submodule ℤ (ι → ℤ),
    Work.HP.rk L = 2 ∧ ({x} : Set (ι → ℤ)) ⊆ L ∧ Work.HP.detL L = E} with hS
  have hne : S.Nonempty := by
    obtain ⟨L, hrank, hxL⟩ := Work.HP.Lat.exists_rk_two x hx hcard
    refine ⟨Work.HP.detL L, L, hrank, ?_, rfl⟩
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact hxL
  have hbd : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro e ⟨L, -, -, hdet⟩
    rw [← hdet]
    exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (Work.HP.Lat.detL_ge_one L)
  have hDs : sInf S ≤ D := by
    rw [hS]
    exact hD
  have hlt : sInf S < D + 1 := lt_of_le_of_lt hDs (by linarith)
  obtain ⟨e, ⟨L, hrank, hsub, hdet⟩, helt⟩ := (csInf_lt_iff hbd hne).mp hlt
  obtain ⟨P, hLP, hPprim, hPrank⟩ := Work.HP.exists_prim_super L
  have hxL : x ∈ L := hsub (by simp)
  refine ⟨P, hPprim, by rw [hPrank, hrank], hLP hxL, ?_⟩
  have hmono := Work.HP.detL_le_of_le_of_rank_eq hLP (by rw [hPrank, hrank])
  rw [← hdet] at helt
  linarith

end Work.HP.FM3
