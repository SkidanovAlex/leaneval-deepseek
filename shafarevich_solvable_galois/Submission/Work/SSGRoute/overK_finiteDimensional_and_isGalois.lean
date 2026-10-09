import Mathlib
import Submission.Work.SSGRoute.overK
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open _root_.SSGRoute

/-- The field `↥(overK K N hKN)` is definitionally the same subtype as `↥N`, and the two `ℚ`-algebra
structures coincide; hence Galois-ness over `ℚ` transfers across the identity. -/
theorem isGalois_overK_over_rat (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K]
    (N : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ N]
    [IsGalois ℚ N] (hKN : K ≤ N) :
    IsGalois ℚ ↥(overK K N hKN) :=
  IsGalois.of_algEquiv (AlgEquiv.refl : (↥N) ≃ₐ[ℚ] (↥(overK K N hKN)))

/-- `overK K N hKN` is finite dimensional over `↥K`: this is the tower formula
`[N : ℚ] = [K : ℚ] * [N : K]` together with finiteness of `[N : ℚ]`. -/
theorem finiteDimensional_overK (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K]
    (N : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ N]
    [IsGalois ℚ N] (hKN : K ≤ N) :
    FiniteDimensional ↥K (overK K N hKN) := by
  have : FiniteDimensional ℚ ↥(overK K N hKN) := (inferInstance : FiniteDimensional ℚ ↥N)
  have h := Module.finrank_mul_finrank ℚ ↥K ↥(overK K N hKN)
  have h2 : 0 < Module.finrank ℚ ↥K * Module.finrank ↥K ↥(overK K N hKN) := by
    rw [h]; exact Module.finrank_pos
  exact FiniteDimensional.of_finrank_pos (Nat.pos_of_mul_pos_left h2)

theorem overK_finiteDimensional_and_isGalois (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] (N : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ N]
    [IsGalois ℚ N] (hKN : K ≤ N) :
    FiniteDimensional ↥K (overK K N hKN) ∧ IsGalois ↥K (overK K N hKN) := by
  refine ⟨finiteDimensional_overK K N hKN, ?_⟩
  have : IsGalois ℚ ↥(overK K N hKN) := isGalois_overK_over_rat K N hKN
  exact IsGalois.tower_top_of_isGalois ℚ ↥K ↥(overK K N hKN)

end Work.SSGRoute
