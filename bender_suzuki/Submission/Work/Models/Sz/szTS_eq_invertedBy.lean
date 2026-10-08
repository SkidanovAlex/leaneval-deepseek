import Mathlib
import Submission.Work.Models.Port.BenderPairModels
import Submission.Work.Models.Abstract.ModelData

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Models.Sz

/-- The Weyl element `w` inverts every element of the maximal torus `T`: the torus is exactly
`J(T,w) = {x ∈ T | w x w⁻¹ = x⁻¹}`.  One inclusion is by definition of `invertedBy`; the other
unfolds `T = (szTgHom n).range.subgroupOf (SzModel n)` and uses `szWgM_conj_szTgM`. -/
theorem szTS_eq_invertedBy (n : ℕ) :
    (Submission.Sz.szTS n : Set (LeanEval.GroupTheory.Defs.SzModel n)) =
      Submission.Blueprint.invertedBy (Submission.Sz.szTS n) (Submission.Sz.szWgM n) := by
  apply Set.Subset.antisymm
  · intro x hx
    refine ⟨hx, ?_⟩
    obtain ⟨y, hy⟩ := Subgroup.mem_subgroupOf.mp hx
    have hxM : x = Submission.Sz.szTgM n y :=
      Subtype.ext (by simpa [Submission.Sz.szTgM] using hy.symm)
    have hinv : (Submission.Sz.szTgM n y)⁻¹ = Submission.Sz.szTgM n y⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_inv, Submission.Sz.szTgM_coe]
      exact (map_inv (Submission.Sz.szTgHom n) y).symm
    rw [hxM, hinv]
    exact Submission.Sz.szWgM_conj_szTgM n y
  · intro x hx
    exact hx.1

end Work.Models.Sz
