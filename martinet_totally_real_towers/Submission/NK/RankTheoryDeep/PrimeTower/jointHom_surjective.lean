import Mathlib
import Submission.NK.RankTheoryDeep.PrimeTower.LevelCoords
import Submission.NK.RankTheoryDeep.PrimeTower.expHom_surjective
import Submission.NK.RankTheoryDeep.PrimeTower.towerPrime_coprime
import Submission.NK.RankTheoryDeep.jointHom_surjective

/-!
# Surjectivity of the joint coordinate map of the ℓ-adic cyclotomic tower

The ℓ-generalisation of `NK.RankTheoryDeep.jointHom_surjective`.  `jointHom ℓ Ω N` is the
product, over `n : Fin N`, of the coordinate characters `coordPrime ℓ (n.val + 1) N` of the
`N`-th cyclotomic level of `Ω` composed with the cyclotomic exponent map `expHom ℓ Ω N`.

Given `x : ∏_{n < N} ℤ/ℓ^{n+1}`:

* for each `n : Fin N` choose a lift `v n ∈ (ℤ/towerPrime ℓ n)^×` with `cycSurj ℓ (n+1) (v n) = x n`
  (`cycSurj_surjective`);
* lift the family `v` to a unit `u ∈ (ℤ/towerMod ℓ N)^×` reducing to `v n` modulo every
  `towerPrime ℓ n` (`tower_units_reduction` below — `surjective_units_reduction_prod` plus the
  transport of units along the identification `∏_{i<N} towerPrime ℓ i = towerMod ℓ N`);
* realise `u` by an automorphism `σ` (`expHom_surjective`).

The only technical point is again the bookkeeping of the *equal but not syntactically identical*
moduli `∏_{i : Fin N} towerPrime ℓ i` and `towerMod ℓ N`, handled by the ℓ-agnostic helper
`NK.RankTheoryDeep.units_map_castHom_ringEquivCongr`.
-/

-- the same local instance priority as in `Defs`/`LevelCoords`, so that `Algebra ℚ ↥L` for an
-- intermediate field `L` is resolved by `IntermediateField.algebra'` and the types below match
-- those of `jointHom` and `redPrime`.
attribute [local instance 10] DivisionRing.toRatAlgebra

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace NK.RankTheoryDeep.PrimeTower

/-- **Chinese remainder theorem for the tower of primes, in the form needed by `redPrime`.**

Every family of units `v i ∈ (ℤ/towerPrime ℓ i)^×`, `i < N`, is the family of reductions of a
single unit `u ∈ (ℤ/towerMod ℓ N)^×`: `redPrime ℓ i.isLt u = v i` for all `i : Fin N`. -/
lemma tower_units_reduction (ℓ : ℕ) [Fact ℓ.Prime] (N : ℕ)
    (v : (i : Fin N) → (ZMod (towerPrime ℓ (i : ℕ)))ˣ) :
    ∃ u : (ZMod (towerMod ℓ N))ˣ, ∀ i : Fin N, redPrime ℓ i.isLt u = v i := by
  -- the two forms of the modulus of the `N`-th level agree
  have hmod : (∏ i : Fin N, towerPrime ℓ (i : ℕ)) = towerMod ℓ N :=
    (Finset.prod_range (f := fun i => towerPrime ℓ i)).symm
  have hne₀ : (∏ i : Fin N, towerPrime ℓ (i : ℕ)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i _
    exact (towerPrime_prime ℓ (i : ℕ)).ne_zero
  haveI : NeZero (∏ i : Fin N, towerPrime ℓ (i : ℕ)) := ⟨hne₀⟩
  haveI : NeZero (towerMod ℓ N) := ⟨towerMod_ne_zero ℓ N⟩
  -- the Chinese remainder theorem for the units of the univ-product
  have hCRT : ∃ u : (ZMod (∏ i : Fin N, towerPrime ℓ (i : ℕ)))ˣ,
      ∀ i : Fin N, Units.map ↑(ZMod.castHom
          (Finset.dvd_prod_of_mem (fun j : Fin N => towerPrime ℓ (j : ℕ))
            (Finset.mem_univ i)) (ZMod (towerPrime ℓ (i : ℕ)))) u = v i := by
    obtain ⟨u, hu⟩ := NK.RankTheoryDeep.surjective_units_reduction_prod
      (fun i : Fin N => towerPrime ℓ (i : ℕ))
      (fun i => (towerPrime_prime ℓ (i : ℕ)).ne_zero)
      (fun i j hij => towerPrime_coprime ℓ (fun h => hij (Fin.ext h))) v
    exact ⟨u, fun i => congrFun hu i⟩
  obtain ⟨u₀, hu₀⟩ := hCRT
  -- transport the unit to the modulus `towerMod ℓ N`; the reductions are unaffected
  refine ⟨Units.map (ZMod.ringEquivCongr hmod).toMonoidHom u₀, fun i => ?_⟩
  show Units.map (ZMod.castHom (towerPrime_dvd_towerMod ℓ i.isLt)
        (ZMod (towerPrime ℓ (i : ℕ)))).toMonoidHom
      (Units.map (ZMod.ringEquivCongr hmod).toMonoidHom u₀) = v i
  rw [NK.RankTheoryDeep.units_map_castHom_ringEquivCongr hmod
    (Finset.dvd_prod_of_mem (fun j : Fin N => towerPrime ℓ (j : ℕ)) (Finset.mem_univ i))
    (towerPrime_dvd_towerMod ℓ i.isLt) u₀]
  exact hu₀ i

/-- **The joint coordinate map of the `N`-th ℓ-adic cyclotomic level is surjective.**

For every family `x n ∈ ℤ/ℓ^{n+1}` (`n < N`) there is an automorphism `σ` of
`ℚ(ζ_{towerMod ℓ N})` whose cyclotomic exponent, reduced modulo the `i`-th tower prime and pushed
through the cyclic surjection `(ℤ/towerPrime ℓ i)^× ↠ ℤ/ℓ^{i+1}`, is `x i` for every `i < N`. -/
theorem jointHom_surjective (ℓ : ℕ) [Fact ℓ.Prime] (Ω : Type*) [Field Ω] [Algebra ℚ Ω]
    [IsGalois ℚ Ω] [IsSepClosure ℚ Ω] (N : ℕ) :
    Function.Surjective (jointHom ℓ Ω N) := by
  intro x
  -- the prescribed ℓ-power coordinates, lifted to the cyclic components
  have h1 : ∀ i : Fin N, ∃ w : (ZMod (towerPrime ℓ (i : ℕ)))ˣ,
      cycSurj ℓ ((i : ℕ) + 1) (by omega) w = x i := fun i =>
    cycSurj_surjective ℓ ((i : ℕ) + 1) (by omega) (x i)
  choose v hv using h1
  -- one unit of `ℤ/towerMod ℓ N` reducing to all of them (CRT)
  obtain ⟨u, hu⟩ := tower_units_reduction ℓ N v
  -- and one automorphism realising that unit (cyclotomic exponent)
  obtain ⟨σ, hσ⟩ := expHom_surjective ℓ Ω N u
  refine ⟨σ, ?_⟩
  funext n
  show coordPrime ℓ ((n : ℕ) + 1) N (by omega) (by omega) (expHom ℓ Ω N σ) = x n
  rw [hσ]
  unfold coordPrime
  simp only [MonoidHom.comp_apply]
  rw [hu n]
  exact hv n

end NK.RankTheoryDeep.PrimeTower
