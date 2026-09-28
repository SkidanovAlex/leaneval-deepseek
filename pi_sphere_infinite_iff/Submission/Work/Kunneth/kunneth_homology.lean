import Mathlib
import Submission.Work.Kunneth.homology_tpC_homSum
import Submission.Work.Kunneth.homology_tpC_sumShift

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The Künneth theorem for homology

Combining

* `Work.Kunneth.homology_tpC_homSum` — tensoring with the splitting `D ≃ homSum D` does not
  change homology, and
* `Work.Kunneth.homology_tpC_sumShift` — for a flat family `M`, the homology of
  `tpC C (sumShift M)` is `⊕_{p+q=n} H_p(C) ⊗ M q`,

we obtain the **Künneth theorem for homology**: for a chain complex `D` of `ℤ`-modules whose terms
and homology are free,

`Hₙ(C ⊗ D) ≅ ⨁_{p+q=n} H_p(C) ⊗ H_q(D)`,
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- **The Künneth theorem for homology.**  If the terms and the homology of `D` are projective
(free) `ℤ`-modules, then `Hₙ(C ⊗ D) ≅ ⨁_{p+q=n} H_p(C) ⊗ H_q(D)`: the target is the degree-`n`
module of the tensor product of the two *homology* complexes `homSum C`, `homSum D`, i.e.
`⨁_{p+q=n} H_p(C) ⊗ H_q(D)` (the differential of that complex being zero). -/
theorem kunneth_homology (C D : ChainComplex (ModuleCat ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (n : ℕ) :
    Nonempty (CategoryTheory.Iso ((Work.Kunneth.tpC C D).homology n)
      ((Work.Kunneth.tpC (Work.Kunneth.homSum C) (Work.Kunneth.homSum D)).X n)) := by
  obtain ⟨e₁⟩ := homology_tpC_homSum C D hD hH n
  have hflat : ∀ q, Module.Flat ℤ ↥(D.homology q) := fun q => by
    haveI := hH q
    exact Module.Flat.of_projective
  obtain ⟨e₂⟩ := homology_tpC_sumShift C (fun q => D.homology q) hflat n
  exact ⟨e₁ ≪≫ e₂⟩

end

end Work.Kunneth
