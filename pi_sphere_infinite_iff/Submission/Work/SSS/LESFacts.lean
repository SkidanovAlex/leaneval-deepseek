import Mathlib
import Submission.Work.SSS.baseRowDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The long exact sequence of a saturated filtration, in explicit form

For the short exact sequence `0 → F_s → F_{s+1} → F_{s+1}/F_s → 0` of the filtration `ξ`, this file
records the exactness of the associated long exact sequence in homology in the explicit form used by
the bottom row argument:

* `range_jF_eq_ker_kF` : exactness at `E¹_{s+1,t}`;
* `range_kF_eq_ker_incF` : exactness at `H_{s+t}(F_s)`;
* `ker_jF_eq_range_incF` : exactness at `H_{(s+1)+t}(F_{s+1})`.
-/

set_option autoImplicit false

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits

variable {C : ChainComplex (ModuleCat ℤ) ℕ}

/-- Exactness at `E¹_{s+1,t} = H_{(s+1)+t}(F_{s+1}/F_s)`: the image of `j` is the kernel of `k`. -/
theorem range_jF_eq_ker_kF (ξ : Filtration C) (s t : ℕ) :
    LinearMap.range (jF ξ (s + 1) t).hom = LinearMap.ker (kF ξ s t).hom := by
  have h := (ShortComplex.ShortExact.homology_exact₃ (sesF_shortExact ξ s) ((s + 1) + t) (s + t)
    (by simp [ComplexShape.down]; omega)).moduleCat_range_eq_ker
  dsimp only [jF, kF]
  exact h

/-- Exactness at `H_{s+t}(F_s)`: the image of the connecting map `k` is the kernel of the map
induced by `F_s → F_{s+1}`. -/
theorem range_kF_eq_ker_incF (ξ : Filtration C) (s t : ℕ) :
    LinearMap.range (kF ξ s t).hom =
      LinearMap.ker (HomologicalComplex.homologyMap (incF ξ.F s) (s + t)).hom := by
  have h := (ShortComplex.ShortExact.homology_exact₁ (sesF_shortExact ξ s) ((s + 1) + t) (s + t)
    (by simp [ComplexShape.down]; omega)).moduleCat_range_eq_ker
  dsimp only [kF]
  exact h

/-- Exactness at `H_{(s+1)+t}(F_{s+1})`: the kernel of `j` is the image of the map induced by
`F_s → F_{s+1}`. -/
theorem ker_jF_eq_range_incF (ξ : Filtration C) (s t : ℕ) :
    LinearMap.ker (jF ξ (s + 1) t).hom =
      LinearMap.range (HomologicalComplex.homologyMap (incF ξ.F s) ((s + 1) + t)).hom := by
  have h := (ShortComplex.ShortExact.homology_exact₂ (sesF_shortExact ξ s) ((s + 1) + t)
    ).moduleCat_range_eq_ker
  dsimp only [jF]
  exact h.symm

end Work.SSS
