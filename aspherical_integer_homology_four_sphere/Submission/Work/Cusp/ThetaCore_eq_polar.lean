import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- The core chart `ThetaCore` is exactly the polar chart `ThetaPolar` written in Cartesian
coordinates: both have the same radial coordinate `r = (ThetaPolar v p y) 0`, the same angle
`θ = (ThetaPolar v p y) 1` and the same `w`-coordinates, and `ThetaCore` replaces `(r,θ)` by
`(r cos θ, r sin θ)`. -/
theorem ThetaCore_eq_polar (v : Fin 5) (p y : E2) :
    ThetaCore v p y = !₂[(ThetaPolar v p y) 0 * Real.cos ((ThetaPolar v p y) 1),
      (ThetaPolar v p y) 0 * Real.sin ((ThetaPolar v p y) 1), (ThetaPolar v p y) 2,
      (ThetaPolar v p y) 3] := by
  simp [ThetaCore, ThetaPolar]

end Work.Cusp
