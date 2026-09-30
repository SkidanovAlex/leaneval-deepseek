import Mathlib
import Submission.Work.RTOwed.cuspCert.tsetCoverData

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOwed.cuspCert

theorem cubeLookup :
    (∀ b : Fin 48, Work.Cusp.cubeOfMod (Work.Cusp.cubeCusp b) (Work.Cusp.cubeCorner b) = b) ∧
    (∀ (a : Fin 48) (e : Fin 8), Work.Cusp.cubeOfMod (Work.Cusp.cubeCusp a)
        (fun i : Fin 3 => Work.Cusp.cubeCorner a i + Work.RTOwed.cuspCert.satOf e i) =
      Work.RTOwed.cuspCert.covB a e) ∧
    (∀ (w : Fin 24) (c : ZMod 2), ∃ a : Fin 48,
      Work.RTOwed.cubeVert a = w ∧ Work.RTOwed.cubeBit a = c) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

end Work.RTOwed.cuspCert
