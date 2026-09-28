import Mathlib
import Submission.Work.HP.Q44Child.SuperDefs
import Submission.Work.HP.Q44Child.SuperAux
import Submission.Work.HP.Q44Child.SuperInj
import Submission.Work.HP.Q44Child.basis_ext

namespace Work.HP.Q44Child

open Module

/-- **Counting rank-`3` superlattices.**  Uniformly in the rank-`2` primitive lattice
`Λ ⊆ ℤ^5`, the number of rank-`3` lattices `L ⊇ Λ` with `detL L ≤ T * detL Λ` is
`O(T^3 detL Λ)`.

The proof maps such an `L` to the generator `u` of the rank-`1` subgroup `π(L) ≤ π(ℤ^5)`,
where `π` is the orthogonal projection onto the orthogonal complement of the real span of
`Λ`; the norm of `u` is `detL L / detL Λ ≤ T`, and `L` is recovered from `u` by primitivity.
Counting the points of the projected lattice `Γ = π(ℤ^5) ⊆ W` of covolume `1/detL Λ`,
which has covering radius at most `√5/2`, gives the bound. -/
theorem superlattice_count :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : Submodule ℤ (Fin 5 → ℤ)), Work.HP.rk Λ = 2 →
      Work.HP.IsPrimLat Λ → ∀ T : ℝ, 1 ≤ T →
      (({L : Submodule ℤ (Fin 5 → ℤ) |
          Λ ≤ L ∧ Work.HP.rk L = 3 ∧ Work.HP.detL L ≤ T * Work.HP.detL Λ} :
        Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ)
        ≤ C * T ^ 3 * Work.HP.detL Λ := by
  refine ⟨1000, by norm_num, ?_⟩
  intro Λ hΛrk hpr T hT
  obtain ⟨b, hb, hli, h5⟩ := basis_ext Λ hΛrk hpr
  exact ncard_Sset_le hb hli h5 hΛrk hpr hT

end Work.HP.Q44Child
