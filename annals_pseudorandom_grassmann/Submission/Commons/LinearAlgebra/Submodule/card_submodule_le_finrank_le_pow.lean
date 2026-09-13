import Mathlib
import Submission.Commons.LinearAlgebra.Submodule.card_submodule_finrank_le_pow

namespace Commons.LinearAlgebra.Submodule

open Module

/-- The number of `i`-dimensional submodules of `V` lying inside a fixed submodule `U` is
bounded by `|K| ^ (i * (finrank U - i) + i)`.  This is the relative version of
`card_submodule_finrank_le_pow`, obtained by transporting the count along the bijection
`T ↦ T.map U.subtype` between submodules of `U` and submodules of `V` that are `≤ U`. -/
theorem card_submodule_le_finrank_le_pow {K : Type*} [Field K] [Fintype K]
    {V : Type*} [AddCommGroup V] [Module K V] [Finite V] (U : Submodule K V) (i : ℕ) :
    Nat.card {W : Submodule K V // W ≤ U ∧ Module.finrank K W = i}
      ≤ Nat.card K ^ (i * (Module.finrank K U - i) + i) := by
  have hle : ∀ T : Submodule K U, T.map U.subtype ≤ U := by
    intro T x hx
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  let F : {T : Submodule K U // Module.finrank K T = i} →
      {W : Submodule K V // W ≤ U ∧ Module.finrank K W = i} :=
    fun T => ⟨T.1.map U.subtype, hle T.1, by
      rw [Submodule.finrank_map_subtype_eq U T.1, T.2]⟩
  have hcard : Nat.card {W : Submodule K V // W ≤ U ∧ Module.finrank K W = i}
      = Nat.card {T : Submodule K U // Module.finrank K T = i} := by
    refine (Nat.card_congr (Equiv.ofBijective F ?_)).symm
    constructor
    · rintro ⟨T1, hT1⟩ ⟨T2, hT2⟩ h
      have hmap : T1.map U.subtype = T2.map U.subtype := by
        simpa [F] using congrArg Subtype.val h
      exact Subtype.ext (Submodule.map_injective_of_injective
        (Submodule.subtype_injective U) hmap)
    · rintro ⟨W, hWU, hWfin⟩
      refine ⟨⟨Submodule.comap U.subtype W, ?_⟩, ?_⟩
      · rw [← Submodule.finrank_map_subtype_eq U (Submodule.comap U.subtype W),
          Submodule.map_comap_subtype, inf_eq_right.mpr hWU, hWfin]
      · apply Subtype.ext
        show (Submodule.comap U.subtype W).map U.subtype = W
        rw [Submodule.map_comap_subtype, inf_eq_right.mpr hWU]
  rw [hcard]
  exact card_submodule_finrank_le_pow (K := K) (V := U) i

end Commons.LinearAlgebra.Submodule
