import Mathlib
import Submission.Work.Clifford.All
import Submission.Work.CharCore.Main

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Hering.AppVII.part2_orbitSum_norm`

The orbit sum `orbitSum N θ = ∑_{φ ∈ charOrbit N θ} φ` of an irreducible character `θ` of a
normal subgroup `N ⊴ G` has norm `|charOrbit N θ|` with respect to the inner product
`Work.Clifford.cfInner` on functions `N → ℂ`:

`⟪orbitSum N θ, orbitSum N θ⟫ = |charOrbit N θ|`.

Indeed `orbitSum N θ` is the sum of the *distinct* irreducible characters in the orbit of `θ`
(conjugation by `g ∈ G` is the twist of `θ` by the automorphism `x ↦ g x g⁻¹` of `N`, and
`Irr` is stable under twists — `Work.Clifford.charOrbit_subset_Irr`), and the irreducible
characters are orthonormal (`Work.Clifford.cfInner_eq_ite_of_mem_Irr`).  Expanding the inner
product, only the terms of the orbit can contribute, and each contributes exactly `1`:

`⟪orbitSum N θ, orbitSum N θ⟫ = ∑_{φ ∈ charOrbit N θ} ⟪orbitSum N θ, φ⟫
  = ∑_{φ ∈ charOrbit N θ} 1 = |charOrbit N θ|`,

using `Work.Clifford.cfInner_orbitSum_eq_ite` for the second equality.
-/

noncomputable section

open Classical

namespace Work.Hering.AppVII

theorem part2_orbitSum_norm {G : Type*} [Group G] [Fintype G] {N : Subgroup G} [N.Normal]
    [Fintype ↥N] {θ : ↥N → ℂ} (hθ : θ ∈ Work.Clifford.Irr ↥N) :
    Work.Clifford.cfInner (Work.Clifford.orbitSum N θ) (Work.Clifford.orbitSum N θ)
      = (((Work.Clifford.charOrbit N θ).card : ℕ) : ℂ) := by
  classical
  -- Every member of the orbit of `θ` is irreducible.
  have hsub : ∀ ψ ∈ Work.Clifford.charOrbit N θ, ψ ∈ Work.Clifford.Irr ↥N :=
    Work.Clifford.charOrbit_subset_Irr hθ
  -- The orbit sum is the sum of the orbit.
  have hdecomp : Work.Clifford.orbitSum N θ
      = ∑ ψ ∈ Work.Clifford.charOrbit N θ, ψ := Work.Clifford.orbitSum_eq_sum θ
  -- Expand the inner product in its second argument (and only there).
  nth_rewrite 2 [hdecomp]
  rw [Work.Clifford.cfInner_sum_right]
  -- Each orbit member pairs to `1` against the orbit sum; nothing else occurs.
  trans ∑ ψ ∈ Work.Clifford.charOrbit N θ, (1 : ℂ)
  · refine Finset.sum_congr rfl fun ψ hψ => ?_
    rw [Work.Clifford.cfInner_orbitSum_eq_ite hθ (hsub ψ hψ)]
    simp [hψ]
  · simp

end Work.Hering.AppVII
