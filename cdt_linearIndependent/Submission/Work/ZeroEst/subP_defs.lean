import Mathlib

/-!
# `Work.ZeroEst.subP_defs` — the substitution `X ↦ X + c` on `ℚ[X]`
-/

namespace Work.ZeroEst

open Polynomial

/-- The substitution `X ↦ X + c` as a ring homomorphism of `ℚ[X]`. -/
noncomputable def subP (c : ℚ) : Polynomial ℚ →+* Polynomial ℚ :=
  Polynomial.eval₂RingHom Polynomial.C (Polynomial.X + Polynomial.C c)

end Work.ZeroEst
