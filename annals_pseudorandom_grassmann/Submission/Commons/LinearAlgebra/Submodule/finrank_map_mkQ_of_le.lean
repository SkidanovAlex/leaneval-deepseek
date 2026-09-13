import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace Commons.LinearAlgebra.Submodule

open Module

noncomputable section

/-- If `A ≤ B` are submodules of a finite-dimensional space `V`, the image of `B` under the
quotient map `V → V ⧸ A` has dimension `finrank B - finrank A`.

Proof: restrict `A.mkQ` to `B`; its range is `map A.mkQ B` and its kernel is `A` (as a submodule
of `B`), so the rank-nullity theorem applies. -/
theorem finrank_map_mkQ_of_le {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] (A B : Submodule K V) (h : A ≤ B) :
    Module.finrank K (Submodule.map A.mkQ B) = Module.finrank K B - Module.finrank K A := by
  classical
  let g : B →ₗ[K] (V ⧸ A) := A.mkQ.comp B.subtype
  have hker_eq : LinearMap.ker g = A.comap B.subtype := by
    dsimp [g]
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have hker_finrank : Module.finrank K (LinearMap.ker g) = Module.finrank K A := by
    rw [hker_eq]
    exact LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe (p := A) (q := B) h)
  have hrange_eq : LinearMap.range g = Submodule.map A.mkQ B := by
    dsimp [g]
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hranknullity := LinearMap.finrank_range_add_finrank_ker g
  rw [hrange_eq, hker_finrank] at hranknullity
  exact Nat.eq_sub_of_add_eq hranknullity

end

end Commons.LinearAlgebra.Submodule
