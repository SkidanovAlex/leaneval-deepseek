import Mathlib
import Submission.NK.RankTheoryDeep.TowerArc
import Submission.NK.RankTheoryDeep.expHom_levelRestrict

/-!
# Naturality of the level coordinates under the transition maps `ellRestrict`

This file proves that the `n`-th coordinate character of the `N`-th cyclotomic level
(`NK.RankTheoryDeep.levelCoordHom`, the cyclotomic exponent reduced mod `q (n - 1)` and pushed
through the cyclic surjection `cycSurj n`) is **compatible with the transition maps** of Shimizu's
projective system: restricting the `2`-part `Γ_{M_N,2} = ℓ-part(Gal(ℚ(ζ_{towerMod N})/ℚ)^{ab})` to
the smaller level `ℚ(ζ_{towerMod n})` and then taking the `n`-th coordinate is the same as taking
the `n`-th coordinate of the `N`-th level directly:

```
levelCoordHom Ω n n hn le_rfl ∘ ellRestrict 2 (cycLevel Ω n) (cycLevel Ω N) (cycLevel_mono Ω)
  = levelCoordHom Ω n N hn hN.
```

This is the coherence condition that makes the coordinates `n ≤ N` a compatible family along the
projective system, so that they descend to the limit `Γ_ℚ` (`NK.Reconstruct.Gamma`); it is one of
the inputs of `NK.RankTheoryDeep.gamma_surjection_ellTower`.

The proof has two ingredients:

* **`NK.RankTheoryDeep.expHom_levelRestrict`** (in the imported module of the same name) —
  the naturality of the cyclotomic exponent
  (`NK.RankTheoryDeep.expHom`) under restriction of automorphisms: restricting
  `σ ∈ Gal(ℚ(ζ_{towerMod N})/ℚ)` to `ℚ(ζ_{towerMod n})` reduces its exponent through the reduction
  `unitRed` of the unit groups.  The subtlety is that the primitive roots `towerZeta Ω n` and
  `towerZeta Ω N` are chosen *independently* by `Classical.choose`; the proof uses that
  `towerZeta Ω n = (towerZeta Ω N) ^ j` for some `j`, since `towerMod n ∣ towerMod N` and hence
  every `towerMod n`-th root of unity is a `towerMod N`-th root of unity.  The exponent then
  multiplies by `j`, and the reduction is the same on both sides.
* **`redPrime_comp_unitRed`** — the reduction `redPrime` to the prime `q (n - 1)` factors through
  the reduction `unitRed` to the intermediate level `towerMod n`, by `ZMod.unitsMap_comp`.

Together with the functoriality of the abelianisation (`Abelianization.lift` vs.
`Abelianization.map`, `NK.RankTheoryDeep.ab_lift_comp_map`, `ab_lift_comp_hom`) this gives the
statement over the `2`-primary parts.  (The naturality statement itself is proved in
`Submission/Work/RankTheoryDeep/expHom_levelRestrict.lean`; the present file only records the extra
input `redPrime` vs. `unitRed` needed for the composite coordinates.)
-/

attribute [local instance 10] DivisionRing.toRatAlgebra

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace NK.RankTheoryDeep

open NK.Reconstruct

universe u

/-! ## The abelianisation: `lift` against `map` and against a postcomposition -/

/-- **`Abelianization.lift` against `Abelianization.map`**: lifting a homomorphism `f` from the
larger group `H` and then precomposing with the abelianisation of `g : G →* H` is the same as
lifting the composite `f ∘ g`. -/
theorem ab_lift_comp_map (G H : Type*) [Group G] [Group H] (A : Type*) [CommGroup A]
    (f : H →* A) (g : G →* H) :
    (Abelianization.lift f).comp (Abelianization.map g) = Abelianization.lift (f.comp g) := by
  apply Abelianization.hom_ext
  ext x
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply,
    Abelianization.lift_apply_of, Abelianization.map_of, Abelianization.lift_apply_of]
  rfl

/-- **`Abelianization.lift` against a postcomposition**: postcomposing the lift of `g` with a
homomorphism `f` into a commutative group is the same as lifting the composite `f ∘ g`. -/
theorem ab_lift_comp_hom (G : Type*) [Group G] (A B : Type*) [CommGroup A] [CommGroup B]
    (f : A →* B) (g : G →* A) :
    f.comp (Abelianization.lift g) = Abelianization.lift (f.comp g) := by
  apply Abelianization.hom_ext
  ext x
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply,
    Abelianization.lift_apply_of, Abelianization.lift_apply_of]
  rfl

/-- The pointwise form of `ab_lift_comp_map`. -/
theorem ab_lift_comp_map_apply {G H : Type*} [Group G] [Group H] {A : Type*} [CommGroup A]
    (f : H →* A) (g : G →* H) (y : Abelianization G) :
    Abelianization.lift f (Abelianization.map g y) = Abelianization.lift (f.comp g) y :=
  DFunLike.congr_fun (ab_lift_comp_map G H A f g) y

/-- The pointwise form of `ab_lift_comp_hom`. -/
theorem ab_lift_comp_hom_apply {G : Type*} [Group G] {A B : Type*} [CommGroup A] [CommGroup B]
    (f : A →* B) (g : G →* A) (y : Abelianization G) :
    f (Abelianization.lift g y) = Abelianization.lift (f.comp g) y :=
  DFunLike.congr_fun (ab_lift_comp_hom G A B f g) y

/-! ## The reductions of the unit groups -/

/-- **The reduction `redPrime` factors through `unitRed`**: reducing the cyclotomic exponent of the
`N`-th level to the prime `q (n - 1)` is the same as reducing it first to the level `towerMod n`
and then to `q (n - 1)` — both are the reduction `ℤ/towerMod N → ℤ/q (n - 1)`
(`ZMod.unitsMap_comp`). -/
theorem redPrime_comp_unitRed {n N : ℕ} (hn : 1 ≤ n) (hN : n ≤ N) :
    (redPrime (by omega : n - 1 < n)).comp (unitRed hN) = redPrime (by omega : n - 1 < N) := by
  rw [show redPrime (by omega : n - 1 < n)
        = ZMod.unitsMap (towerPrime_dvd_towerMod (by omega : n - 1 < n)) from rfl,
    show unitRed hN = ZMod.unitsMap (towerMod_dvd_of_le hN) from rfl,
    show redPrime (by omega : n - 1 < N)
        = ZMod.unitsMap (towerPrime_dvd_towerMod (by omega : n - 1 < N)) from rfl]
  rw [ZMod.unitsMap_comp]

/-! ## The coordinate character is compatible with the transition maps -/

/-- **The `n`-th coordinate character is compatible with `ellRestrict`**: restricting the `2`-part
of the abelianisation of the `N`-th cyclotomic level to the `n`-th level and reading off the `n`-th
cyclotomic coordinate is the same as reading off the `n`-th coordinate of the `N`-th level
directly.

This is the coherence condition along the tower of cyclotomic levels which lets the coordinate
characters `n ≤ N` descend to the limit `Γ_ℚ` (`NK.Reconstruct.Gamma`). -/
theorem levelCoordHom_ellRestrict (Ω : Type*) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    {n N : ℕ} (hn : 1 ≤ n) (hN : n ≤ N) :
    (NK.RankTheoryDeep.levelCoordHom Ω n n hn le_rfl).comp
        (NK.Reconstruct.ellRestrict 2 (NK.RankTheoryDeep.cycLevel Ω n)
          (NK.RankTheoryDeep.cycLevel Ω N) (NK.RankTheoryDeep.cycLevel_mono Ω hN)) =
      NK.RankTheoryDeep.levelCoordHom Ω n N hn hN := by
  have hred : (redPrime (by omega : n - 1 < n)).comp (unitRed hN)
      = redPrime (by omega : n - 1 < N) := redPrime_comp_unitRed hn hN
  have hcp : (coordPrime n n hn le_rfl).comp (unitRed hN) = coordPrime n N hn hN := by
    rw [show coordPrime n n hn le_rfl
          = (cycSurj n hn).comp (redPrime (by omega : n - 1 < n)) from rfl,
      show coordPrime n N hn hN
          = (cycSurj n hn).comp (redPrime (by omega : n - 1 < N)) from rfl]
    rw [MonoidHom.comp_assoc, hred]
  ext x
  change coordPrime n n hn le_rfl
      (Abelianization.lift (expHom Ω n)
        ((ellRestrict 2 (cycLevel Ω n) (cycLevel Ω N) (cycLevel_mono Ω hN) x :
          LevelEllPart (cycLevel Ω n).L 2) : LevelAbelianization (cycLevel Ω n).L))
    = coordPrime n N hn hN
        (Abelianization.lift (expHom Ω N)
          ((x : LevelEllPart (cycLevel Ω N).L 2) : LevelAbelianization (cycLevel Ω N).L))
  rw [show ((ellRestrict 2 (cycLevel Ω n) (cycLevel Ω N) (cycLevel_mono Ω hN) x :
          LevelEllPart (cycLevel Ω n).L 2) : LevelAbelianization (cycLevel Ω n).L)
      = Abelianization.map (levelRestrictHom (cycLevel Ω n) (cycLevel Ω N) (cycLevel_mono Ω hN))
          ((x : LevelEllPart (cycLevel Ω N).L 2) : LevelAbelianization (cycLevel Ω N).L) from by
        rw [ellRestrict_coe]; rfl]
  rw [ab_lift_comp_map_apply]
  rw [show (expHom Ω n).comp (levelRestrictHom (cycLevel Ω n) (cycLevel Ω N) (cycLevel_mono Ω hN))
      = (unitRed hN).comp (expHom Ω N) from expHom_levelRestrict Ω hN]
  rw [ab_lift_comp_hom_apply]
  rw [show (coordPrime n n hn le_rfl).comp ((unitRed hN).comp (expHom Ω N))
      = (coordPrime n N hn hN).comp (expHom Ω N) from by
        rw [← MonoidHom.comp_assoc, hcp]]
  rw [← ab_lift_comp_hom_apply]

end NK.RankTheoryDeep
