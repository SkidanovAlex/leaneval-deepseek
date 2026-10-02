import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Thom

/-- For every `m : ℕ`, the complex Euclidean space of dimension `m + 1` is linearly
isometric (hence continuously linearly equivalent) to the product of the complex
Euclidean spaces of dimensions `m` and `1`. -/
theorem exists_continuousLinearEquiv_euclideanSpace_prod (m : ℕ) :
    Nonempty ((EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin 1)) ≃L[ℂ] EuclideanSpace ℂ (Fin (m + 1))) :=
  ⟨(EuclideanSpace.finAddEquivProd (𝕜 := ℂ) (n := m) (m := 1)).symm⟩

end Work.Thom
