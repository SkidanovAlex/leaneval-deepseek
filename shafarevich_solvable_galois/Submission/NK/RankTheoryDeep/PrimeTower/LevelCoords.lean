import Mathlib
import Submission.NK.RankTheoryDeep.PrimeTower.Defs
import Submission.NK.RankTheoryDeep.PrimeTower.towerPrime_ell_pow_dvd_sub_one
import Submission.NK.RankTheoryDeep.PrimeTower.towerPrime_coprime
import Submission.NK.RankTheoryDeep.exists_surjective_hom_zmod_of_cyclic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The coordinate characters of the ℓ-adic cyclotomic tower

The ℓ-generalisation of the last part of `Submission/Work/RankTheoryDeep/TowerArc.lean`: the cyclic
surjection `cycSurj` from `(ℤ/q (n-1))^×` onto `ℤ/ℓ^n` (using that `(ℤ/q)^×` is cyclic of order
`q - 1`, divisible by `ℓ ^ n` by `NK.RankTheoryDeep.PrimeTower.towerPrime_ell_pow_dvd_sub_one`),
and the coordinate characters `coordPrime`, `levelCoordHom` of a level, together with the joint
characters `jointHom`, `jointLevelHom`.
-/

attribute [local instance 10] DivisionRing.toRatAlgebra

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace NK.RankTheoryDeep.PrimeTower

open scoped Pointwise

universe u

/-- **The divisibility of the unit-group orders used to build the cyclic surjection**: the order
`towerPrime ℓ (n - 1) - 1` of `(ℤ/q (n-1))^×` is divisible by `ℓ ^ n`. -/
theorem cycSurj_dvd (ℓ : ℕ) [Fact ℓ.Prime] {n : ℕ} (hn : 1 ≤ n) :
    ℓ ^ n ∣ Nat.card (ZMod (towerPrime ℓ (n - 1)))ˣ := by
  haveI : Fact (towerPrime ℓ (n - 1)).Prime := ⟨towerPrime_prime ℓ (n - 1)⟩
  haveI : NeZero (towerPrime ℓ (n - 1)) := ⟨(towerPrime_prime ℓ (n - 1)).ne_zero⟩
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.totient_prime (towerPrime_prime ℓ (n - 1))]
  have h := towerPrime_ell_pow_dvd_sub_one ℓ (n - 1)
  rwa [Nat.sub_add_cancel hn] at h

/-- **The `n`-th cyclic surjection**: the cyclic group `(ℤ/q (n - 1))^×` of order divisible by
`ℓ ^ n` maps onto `ℤ/ℓ ^ n`. -/
noncomputable def cycSurj (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) (hn : 1 ≤ n) :
    (ZMod (towerPrime ℓ (n - 1)))ˣ →* Multiplicative (ZMod (ℓ ^ n)) := by
  haveI : Fact (towerPrime ℓ (n - 1)).Prime := ⟨towerPrime_prime ℓ (n - 1)⟩
  exact Classical.choose (NK.RankTheoryDeep.exists_surjective_hom_zmod_of_cyclic (cycSurj_dvd ℓ hn))

theorem cycSurj_surjective (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) (hn : 1 ≤ n) :
    Function.Surjective (cycSurj ℓ n hn) := by
  haveI : Fact (towerPrime ℓ (n - 1)).Prime := ⟨towerPrime_prime ℓ (n - 1)⟩
  exact Classical.choose_spec
    (NK.RankTheoryDeep.exists_surjective_hom_zmod_of_cyclic (cycSurj_dvd ℓ hn))

section Level

variable (ℓ : ℕ) [Fact ℓ.Prime]
variable (Ω : Type u) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

/-- **The `n`-th coordinate character of the `N`-th level**: reduce the cyclotomic exponent of an
automorphism mod `q (n - 1)` and apply the cyclic surjection onto `ℤ/ℓ ^ n`. -/
noncomputable def coordPrime (n N : ℕ) (hn : 1 ≤ n) (hN : n ≤ N) :
    (ZMod (towerMod ℓ N))ˣ →* Multiplicative (ZMod (ℓ ^ n)) :=
  (cycSurj ℓ n hn).comp (redPrime ℓ (by omega : n - 1 < N))

/-- **The `n`-th coordinate of the `N`-th level**, on the ℓ-part of the abelianisation of
`Gal(ℚ(ζ_{towerMod ℓ N})/ℚ)`. -/
noncomputable def levelCoordHom (n N : ℕ) (hn : 1 ≤ n) (hN : n ≤ N) :
    NK.Reconstruct.LevelEllPart (cycLevel ℓ Ω N).L ℓ →* Multiplicative (ZMod (ℓ ^ n)) :=
  ((coordPrime ℓ n N hn hN).comp (Abelianization.lift (expHom ℓ Ω N))).comp (Subgroup.subtype _)

/-- **The joint coordinate character of the `N`-th level**: the product of the coordinate
characters `1, …, N`. -/
noncomputable def jointHom (N : ℕ) :
    Gal(↥(cycLevel ℓ Ω N).L/ℚ) →*
      (∀ n : Fin N, Multiplicative (ZMod (ℓ ^ (n.val + 1)))) where
  toFun σ n := coordPrime ℓ (n.val + 1) N (by omega) (by omega) (expHom ℓ Ω N σ)
  map_one' := by
    funext n
    rw [Pi.one_apply, map_one, map_one]
  map_mul' σ τ := by
    funext n
    rw [Pi.mul_apply, map_mul, map_mul]

/-- **The joint coordinate map of the `N`-th level**, on the ℓ-part of the abelianisation. -/
noncomputable def jointLevelHom (N : ℕ) :
    NK.Reconstruct.LevelEllPart (cycLevel ℓ Ω N).L ℓ →*
      (∀ n : Fin N, Multiplicative (ZMod (ℓ ^ (n.val + 1)))) :=
  (Abelianization.lift (jointHom ℓ Ω N)).comp (Subgroup.subtype _)

end Level

end NK.RankTheoryDeep.PrimeTower
