import Mathlib
import Submission.Work.SSSR.Serre.E0SimplexDefs
import Submission.Work.RatHurewicz.Bridge.H_faces
import Submission.Work.SSSR.RatHurewicz.Bridge.exists_collapse_simplex
import Submission.Work.SSSR.Stems.Cubical.CubeFace
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Simplicial
open scoped Simplicial Topology unitInterval
namespace Work.SSSR.Serre

noncomputable section

open Work.SSSR.RatHurewicz.Bridge
open Work.SSSR.Stems.Cubical
open Work.SSSR.RatHurewicz
/-- **The cumulative-coordinate map sends the cube boundary into the simplicial boundary.**

If some coordinate of `t : I^m` is `0` or `1`, then some coordinate of `H m t` vanishes:
`Hfun m t j = Pnat m t j * (1 - tval m t j)`, `Pnat m t j = ∏_{i<j} t_i`; if `t i = 0` then
`Pnat m t (i+1) = 0`, and if `t i = 1` then `1 - tval m t i = 0`. -/
theorem H_mem_simplexBdry (m : ℕ) (t : IC m) (ht : t ∈ Cube.boundary (Fin m)) :
    ∃ j : Fin (m + 1), H m t j = 0 := by
  obtain ⟨i, hi | hi⟩ := ht
  · -- `t i = 0`: the coordinate `i+1` of the image vanishes
    refine ⟨⟨i.val + 1, by omega⟩, ?_⟩
    rw [H_apply, Hfun]
    have hzero : Pnat m t (i.val + 1) = 0 := by
      rw [Pnat]
      refine Finset.prod_eq_zero
        (show i.val ∈ Finset.range (i.val + 1) from Finset.mem_range.mpr (Nat.lt_succ_self _)) ?_
      rw [tval_of_lt _ i.isLt, show (⟨i.val, i.isLt⟩ : Fin m) = i from rfl, hi]
      norm_num
    rw [hzero, zero_mul]
  · -- `t i = 1`: the coordinate `i` of the image vanishes
    refine ⟨⟨i.val, by omega⟩, ?_⟩
    rw [H_apply, Hfun]
    have hone : tval m t i.val = 1 := by
      rw [tval_of_lt _ i.isLt, show (⟨i.val, i.isLt⟩ : Fin m) = i from rfl, hi]
      norm_num
    rw [hone, sub_self, mul_zero]

end

end Work.SSSR.Serre
