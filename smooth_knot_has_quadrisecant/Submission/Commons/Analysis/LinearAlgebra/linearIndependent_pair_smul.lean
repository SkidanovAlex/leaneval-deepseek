import Mathlib

namespace Commons.Analysis.LinearAlgebra

/-- Scaling two linearly independent vectors by nonzero scalars preserves
their linear independence. -/
theorem linearIndependent_pair_smul {F : Type*} [Field F] {M : Type*} [AddCommGroup M] [Module F M]
    {x y : M} {c d : F} (hc : c ≠ 0) (hd : d ≠ 0)
    (h : LinearIndependent F ![x, y]) : LinearIndependent F ![c • x, d • y] := by
  let w : Fin 2 → Fˣ := ![Units.mk0 c hc, Units.mk0 d hd]
  have hw : LinearIndependent F (w • (![x, y] : Fin 2 → M)) := LinearIndependent.units_smul h w
  convert hw using 1
  funext i
  fin_cases i <;> simp [w]

end Commons.Analysis.LinearAlgebra
