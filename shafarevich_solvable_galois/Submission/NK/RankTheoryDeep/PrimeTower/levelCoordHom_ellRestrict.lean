import Mathlib
import Submission.NK.RankTheoryDeep.PrimeTower.LevelCoords
import Submission.NK.RankTheoryDeep.PrimeTower.expHom_levelRestrict
import Submission.NK.RankTheoryDeep.levelCoordHom_ellRestrict
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Naturality of the `ℓ`-adic level coordinates under the transition maps `ellRestrict`

The `ℓ`-generalisation of `NK.RankTheoryDeep.levelCoordHom_ellRestrict`: the `n`-th coordinate
character of the `N`-th level of the `ℓ`-adic cyclotomic tower
(`NK.RankTheoryDeep.PrimeTower.levelCoordHom ℓ Ω n N`) is compatible with the transition maps
`NK.Reconstruct.ellRestrict ℓ` of Shimizu's projective system.

The proof is the verbatim `ℓ`-generalisation of the `ℓ = 2` case: the only genuinely new input is
the restatement in this namespace of `redPrime_comp_unitRed`, namely that the reduction `redPrime`
to the prime `towerPrime ℓ (n - 1)` factors through the reduction `unitRed` to the intermediate
level `towerMod ℓ n`.  Everything else (the naturality of the cyclotomic exponent
`NK.RankTheoryDeep.PrimeTower.expHom_levelRestrict`, and the functoriality of the abelianisation
`NK.RankTheoryDeep.ab_lift_comp_map`, `ab_lift_comp_hom`) is `ℓ`-agnostic and imported.
-/

attribute [local instance 10] DivisionRing.toRatAlgebra

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace NK.RankTheoryDeep.PrimeTower

/-! ## The reductions of the unit groups -/

/-- **The reduction `redPrime` factors through `unitRed`** (`ℓ`-version of
`NK.RankTheoryDeep.redPrime_comp_unitRed`): reducing the cyclotomic exponent of the `N`-th level
to the prime `towerPrime ℓ (n - 1)` is the same as reducing it first to the level `towerMod ℓ n` and
then to `towerPrime ℓ (n - 1)` — both are the reduction `ℤ/towerMod ℓ N → ℤ/towerPrime ℓ (n - 1)`
(`ZMod.unitsMap_comp`). -/
theorem redPrime_comp_unitRed (ℓ : ℕ) [Fact ℓ.Prime] {n N : ℕ} (hn : 1 ≤ n) (hN : n ≤ N) :
    (redPrime ℓ (by omega : n - 1 < n)).comp (unitRed ℓ hN)
      = redPrime ℓ (by omega : n - 1 < N) := by
  rw [show redPrime ℓ (by omega : n - 1 < n)
        = ZMod.unitsMap (towerPrime_dvd_towerMod ℓ (by omega : n - 1 < n)) from rfl,
    show unitRed ℓ hN = ZMod.unitsMap (towerMod_dvd_of_le ℓ hN) from rfl,
    show redPrime ℓ (by omega : n - 1 < N)
        = ZMod.unitsMap (towerPrime_dvd_towerMod ℓ (by omega : n - 1 < N)) from rfl]
  rw [ZMod.unitsMap_comp]

/-! ## The coordinate character is compatible with the transition maps -/

/-- **The `n`-th coordinate character of the `ℓ`-adic tower is compatible with `ellRestrict`**:
restricting the `ℓ`-part of the abelianisation of the `N`-th cyclotomic level to the `n`-th level
and reading off the `n`-th cyclotomic coordinate is the same as reading off the `n`-th coordinate
of the `N`-th level directly.

This is the coherence condition along the tower of cyclotomic levels which lets the coordinate
characters `n ≤ N` descend to the limit `Γ_ℚ` (`NK.Reconstruct.Gamma`). -/
theorem levelCoordHom_ellRestrict (ℓ : ℕ) [Fact ℓ.Prime] (Ω : Type*) [Field Ω] [Algebra ℚ Ω]
    [IsGalois ℚ Ω] [IsSepClosure ℚ Ω] {n N : ℕ} (hn : 1 ≤ n) (hN : n ≤ N) :
    (levelCoordHom ℓ Ω n n hn le_rfl).comp
        (NK.Reconstruct.ellRestrict ℓ (cycLevel ℓ Ω n) (cycLevel ℓ Ω N)
          (cycLevel_mono ℓ Ω hN)) =
      levelCoordHom ℓ Ω n N hn hN := by
  have hred : (redPrime ℓ (by omega : n - 1 < n)).comp (unitRed ℓ hN)
      = redPrime ℓ (by omega : n - 1 < N) := redPrime_comp_unitRed ℓ hn hN
  have hcp : (coordPrime ℓ n n hn le_rfl).comp (unitRed ℓ hN) = coordPrime ℓ n N hn hN := by
    rw [show coordPrime ℓ n n hn le_rfl
          = (cycSurj ℓ n hn).comp (redPrime ℓ (by omega : n - 1 < n)) from rfl,
      show coordPrime ℓ n N hn hN
          = (cycSurj ℓ n hn).comp (redPrime ℓ (by omega : n - 1 < N)) from rfl]
    rw [MonoidHom.comp_assoc, hred]
  ext x
  change coordPrime ℓ n n hn le_rfl
      (Abelianization.lift (expHom ℓ Ω n)
        ((NK.Reconstruct.ellRestrict ℓ (cycLevel ℓ Ω n) (cycLevel ℓ Ω N)
            (cycLevel_mono ℓ Ω hN) x :
          NK.Reconstruct.LevelEllPart (cycLevel ℓ Ω n).L ℓ) :
          NK.Reconstruct.LevelAbelianization (cycLevel ℓ Ω n).L))
    = coordPrime ℓ n N hn hN
        (Abelianization.lift (expHom ℓ Ω N)
          ((x : NK.Reconstruct.LevelEllPart (cycLevel ℓ Ω N).L ℓ) :
            NK.Reconstruct.LevelAbelianization (cycLevel ℓ Ω N).L))
  rw [show ((NK.Reconstruct.ellRestrict ℓ (cycLevel ℓ Ω n) (cycLevel ℓ Ω N)
          (cycLevel_mono ℓ Ω hN) x :
          NK.Reconstruct.LevelEllPart (cycLevel ℓ Ω n).L ℓ) :
          NK.Reconstruct.LevelAbelianization (cycLevel ℓ Ω n).L)
      = Abelianization.map (NK.Reconstruct.levelRestrictHom (cycLevel ℓ Ω n) (cycLevel ℓ Ω N)
          (cycLevel_mono ℓ Ω hN))
          ((x : NK.Reconstruct.LevelEllPart (cycLevel ℓ Ω N).L ℓ) :
            NK.Reconstruct.LevelAbelianization (cycLevel ℓ Ω N).L) from by
        rw [NK.Reconstruct.ellRestrict_coe]; rfl]
  rw [NK.RankTheoryDeep.ab_lift_comp_map_apply]
  rw [show (expHom ℓ Ω n).comp (NK.Reconstruct.levelRestrictHom (cycLevel ℓ Ω n)
        (cycLevel ℓ Ω N) (cycLevel_mono ℓ Ω hN))
      = (unitRed ℓ hN).comp (expHom ℓ Ω N) from expHom_levelRestrict ℓ Ω hN]
  rw [NK.RankTheoryDeep.ab_lift_comp_hom_apply]
  rw [show (coordPrime ℓ n n hn le_rfl).comp ((unitRed ℓ hN).comp (expHom ℓ Ω N))
      = (coordPrime ℓ n N hn hN).comp (expHom ℓ Ω N) from by
        rw [← MonoidHom.comp_assoc, hcp]]
  rw [← NK.RankTheoryDeep.ab_lift_comp_hom_apply]

end NK.RankTheoryDeep.PrimeTower
