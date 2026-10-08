import Mathlib
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.irreducible_character_mem_Irr
import Submission.Work.CharCore.norm_char_eq_iff_isScalar
import Submission.Work.CharCore.charKernel_subgroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Characters equal to their degree force the identity

If `ρ` is a complex representation of a finite group `G` and `g : G` satisfies
`ρ.character g = ρ.character 1` (i.e. the character value at `g` equals the degree), then
`ρ g = 1`.

Indeed `ρ.character g = trace (ρ g)` and `ρ.character 1 = finrank ℂ V`, while `ρ g` has finite
order (`(ρ g) ^ |G| = 1`).  The linear-algebra input
`Work.CharCore.eq_one_of_trace_eq_finrank` then gives `ρ g = 1`.
-/

namespace Work.CharCore

theorem eq_one_of_character_eq_degree {G : Type*} [Group G] [Fintype G] {V : Type*}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    (h : ρ.IsIrreducible) (g : G) (hg : ρ.character g = ρ.character 1) : ρ g = 1 := by
  -- the trace of `ρ g` equals the dimension
  have htr : LinearMap.trace ℂ V (ρ g) = (Module.finrank ℂ V : ℂ) := by
    rw [← Representation.char_one ρ]
    exact hg
  -- `ρ g` has finite order
  have hpow : (ρ g) ^ (Fintype.card G) = 1 := by
    rw [← map_pow ρ g (Fintype.card G), pow_card_eq_one, map_one]
  exact eq_one_of_trace_eq_finrank (ρ g) (Fintype.card_pos_iff.mpr ⟨1⟩) hpow htr

end Work.CharCore
