import Mathlib
import Submission.Work.Frobenius.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Frobenius.Basic

open scoped Pointwise

/-- If `H` is a Frobenius complement then `H` is self-normalizing.

Indeed, if `g` normalizes `H` then `H^g = H`; were `g ∉ H` the trivial-intersection
property of a Frobenius complement would give `H ∩ H^g = 1`, i.e. `H = 1`,
contradicting nontriviality. The reverse inclusion `H ≤ N_G(H)` is standard. -/
theorem normalizer_eq_of_isFrobeniusComplement {G : Type*} [Group G] {H : Subgroup G}
    (hH : IsFrobeniusComplement H) : Subgroup.normalizer (H : Set G) = H := by
  refine le_antisymm ?_ Subgroup.le_normalizer
  intro g hg
  by_contra hgn
  -- `g` normalizes `H`, so conjugating `H` by `g` does not change it.
  have hconj : (MulAut.conj g • H : Subgroup G) = H := by
    ext x
    rw [Work.Frobenius.mem_conj_smul_iff]
    have hn := (Subgroup.mem_set_normalizer_iff.mp hg) (g⁻¹ * x * g)
    rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at hn
  -- But `g ∉ H`, so the Frobenius complement condition forces `H ∩ H^g = 1`.
  have hti := hH.ti g hgn
  rw [hconj, inf_idem] at hti
  exact hH.ne_bot hti

end Work.Frobenius.Basic
