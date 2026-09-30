import Submission.Work.Homology.Basic
import Submission.Work.Homology.Pairs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Degree zero homology, and the homology of a point
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Homology

noncomputable section

/-- `H_0` of a path-connected space is the coefficient ring. -/
def singHomologyZeroIsoOfPathConnected (R : ModuleCat ℤ) (X : TopCat) [PathConnectedSpace X] :
    singHomology R 0 X ≅ R :=
  @asIso _ _ _ _ (X.singularHomology₀ε R) (inferInstance : IsIso (X.singularHomology₀ε R))

/-- `H_k` of a point vanishes for `k ≥ 1`. -/
theorem isZero_singHomology_point (R : ModuleCat ℤ) (k : ℕ) :
    IsZero (singHomology R (k + 1) (TopCat.of PUnit)) :=
  isZero_singularHomologyFunctor_of_totallyDisconnectedSpace (ModuleCat ℤ) (k + 1) R
    (TopCat.of PUnit) (by omega)

/-- The zero module is `IsZero`. -/
theorem isZero_moduleCat_of_subsingleton (M : ModuleCat ℤ) [Subsingleton M] : IsZero M :=
  ModuleCat.isZero_iff_subsingleton.mpr ‹Subsingleton M›

/-- `H_0` of a point is the coefficient ring. -/
def singHomologyPointZero (R : ModuleCat ℤ) :
    singHomology R 0 (TopCat.of PUnit) ≅ R :=
  singHomologyZeroIsoOfPathConnected R _

/-- `H_k` of a point is `R` for `k = 0` and `0` otherwise. -/
def singHomologyPoint (R : ModuleCat ℤ) (k : ℕ) :
    singHomology R k (TopCat.of PUnit) ≅ (if k = 0 then R else ModuleCat.of ℤ PUnit) := by
  rcases k with _ | k
  · simpa using singHomologyPointZero R
  · have h0 : IsZero (singHomology R (k + 1) (TopCat.of PUnit)) := isZero_singHomology_point R k
    have h1 : IsZero (ModuleCat.of ℤ PUnit) := isZero_moduleCat_of_subsingleton _
    simpa using h0.iso h1

/-- `H_k` of a point with integer coefficients: `ℤ` in degree `0`, `0` otherwise. -/
def intHomologyPoint (k : ℕ) :
    LeanEval.Topology.intHomology k (TopCat.of PUnit) ≅
      (if k = 0 then ModuleCat.of ℤ ℤ else ModuleCat.of ℤ PUnit) := by
  rw [intHomology_eq]
  simpa using singHomologyPoint ZMod k

end

end Work.Homology
