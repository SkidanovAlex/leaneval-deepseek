import Mathlib
import Submission.Work.Clifford.cfInner_eq_ite_of_mem_Irr
import Submission.Work.Clifford.autChar_mem_Irr
import Submission.Work.Clifford.conjFun_mem_Irr
import Submission.Work.Clifford.Orbit

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Clifford.cfInner_orbitSum_self`

The orbit sum `orbitSum N θ = ∑_{φ ∈ charOrbit N θ} φ` of an irreducible character `θ` of a
normal subgroup `N ⊴ G` pairs to `1` against `θ`:

`⟪orbitSum N θ, θ⟫ = 1`.

The orbit of `θ` consists of irreducible characters (conjugation by `g ∈ G` is the twist of `θ`
by the automorphism `x ↦ g x g⁻¹` of `N`, and `Irr` is stable under twists —
`Work.Clifford.autChar_mem_Irr`); by orthonormality of the irreducible characters
(`Work.Clifford.cfInner_eq_ite_of_mem_Irr`) every term of the sum vanishes except the one with
`φ = θ`, and `θ` is always in its own orbit.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Classical

namespace Work.Clifford

variable {G : Type*} [Group G] [Fintype G]
variable {N : Subgroup G} [N.Normal]

theorem cfInner_orbitSum_self {G : Type*} [Group G] [Fintype G] {N : Subgroup G} [N.Normal]
    [Fintype N] {θ : N → ℂ} (hθ : θ ∈ Work.Clifford.Irr N) :
    Work.Clifford.cfInner (Work.Clifford.orbitSum N θ) θ = 1 := by
  -- Every element of the orbit of `θ` is irreducible.
  have hmem : ∀ φ ∈ charOrbit N θ, φ ∈ Irr N := by
    intro φ hφ
    obtain ⟨g, rfl⟩ := mem_charOrbit.mp hφ
    exact conjFun_mem_Irr g hθ
  -- The orbit sum is the pointwise sum of the orbit.
  have hdecomp : orbitSum N θ = ∑ φ ∈ charOrbit N θ, φ := by
    funext n
    simp only [orbitSum, Finset.sum_apply]
  -- Orthonormality of the irreducible characters: only `φ = θ` contributes.
  have hterm : ∀ φ ∈ charOrbit N θ, cfInner φ θ = if φ = θ then (1 : ℂ) else 0 :=
    fun φ hφ => cfInner_eq_ite_of_mem_Irr (hmem φ hφ) hθ
  rw [hdecomp, cfInner_sum_left, Finset.sum_congr rfl hterm, Finset.sum_eq_single θ]
  · simp
  · intro φ _ hne
    simp [hne]
  · intro hnot
    exact absurd (theta_mem_charOrbit θ) hnot

end Work.Clifford

