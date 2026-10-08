import Mathlib
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.star_char

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.CharCore.star_Irr`

For an irreducible complex character `χ` of a finite group `G` and any `g : G`,

`starRingEnd ℂ (χ g) = χ g⁻¹`.

This is the character-level form of `Work.CharCore.star_char`: `χ` is the character of a
simple submodule `N` of the group algebra `ℂ[G]`, and `star_char` applies to
`submoduleRep N`.
-/

namespace Work.CharCore

theorem star_Irr {G : Type*} [Group G] [Fintype G] (χ : G → ℂ) (hχ : χ ∈ Irr G) (g : G) :
    starRingEnd ℂ (χ g) = χ g⁻¹ := by
  obtain ⟨N, -, rfl⟩ := exists_mem_irrSubmodules_of_mem_Irr hχ
  exact star_char (submoduleRep N) g

end Work.CharCore
