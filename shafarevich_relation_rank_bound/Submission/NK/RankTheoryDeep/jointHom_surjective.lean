import Mathlib
import Submission.NK.RankTheoryDeep.TowerArc
import Submission.NK.RankTheoryDeep.expHom_surjective

/-!
# Surjectivity of the joint coordinate map of the cyclotomic tower

`NK.RankTheoryDeep.jointHom Ω N` is the product, over `n : Fin N`, of the coordinate characters
of the `N`-th cyclotomic level `ℚ(ζ_{towerMod N})` of `Ω`:

```
jointHom Ω N σ n = coordPrime (n + 1) N ⋯ ⋯ (expHom Ω N σ),
coordPrime n N ⋯ ⋯ = (cycSurj n ⋯).comp (redPrime ⋯) ,
```

i.e. the cyclotomic exponent of `σ` (an element of `(ℤ/towerMod N)^×`, `expHom`), reduced
modulo the `n`-th tower prime `towerPrime n` (`redPrime`), and pushed through the cyclic
surjection `(ℤ/towerPrime n)^× ↠ ℤ/2^{n+1}` (`cycSurj`).

**The theorem.** `jointHom Ω N` is surjective onto `∏_{n < N} ℤ/2^{n+1}`.

This is the group-theoretic heart of the construction of the surjection
`Γ_ℚ ↠ ∏_n ℤ/2^n` (`NK.RankTheoryDeep.gamma_surjection_ellTower`): every compatible family
of `2`-power coordinates is realised simultaneously by a single automorphism of the `N`-th
level. The mathematics is the multiplicativity of the cyclotomic exponent over the tower of
pairwise coprime prime fields,

`(ℤ/towerMod N)^× ≅ ∏_{i < N} (ℤ/towerPrime i)^×`   (CRT),

combined with the surjectivity of the exponent map `expHom Ω N : Gal(ℚ(ζ_{towerMod N})/ℚ) →
(ℤ/towerMod N)^×` (`expHom_surjective`) and of each cyclic coordinate `cycSurj`
(`cycSurj_surjective`).

Concretely, given `x : ∏_{n<N} ℤ/2^{n+1}`:

* for each `n : Fin N` choose a lift `v n ∈ (ℤ/towerPrime n)^×` with `cycSurj (n+1) (v n) = x n`
  (`cycSurj_surjective`);
* lift the family `v` to a unit `u ∈ (ℤ/towerMod N)^×` reducing to `v n` modulo every
  `towerPrime n` (`tower_units_reduction` below — this is `ZMod.prodEquivPi` plus the transport
  of units along the identification `∏_{i<N} towerPrime i = towerMod N`);
* realise `u` by an automorphism `σ` (`expHom_surjective`).

The only technical point is the bookkeeping of the *equal but not syntactically identical*
moduli `∏_{i : Fin N} towerPrime i` (the form in which the Chinese remainder theorem
`NK.RankTheoryDeep.surjective_units_reduction_prod` is stated) and `towerMod N`
(the form in which `redPrime` is stated); this is handled by
`units_map_castHom_ringEquivCongr`, which uses `ZMod.ringEquivCongr_val` (`ZMod.cast`, hence
every reduction `redPrime`, is computed from `ZMod.val`, and `ringEquivCongr` preserves `val`).
-/

namespace NK.RankTheoryDeep

set_option linter.style.haveILetI false

/-- **Reductions commute with the transport of `ZMod` along an equality of moduli.**

If `h : A = B` identifies the moduli, the ring equivalence `ZMod.ringEquivCongr h : ZMod A ≃+* ZMod B`
induces a group isomorphism of unit groups, and the reduction of units along any divisor `m` of
both moduli is compatible with it: for `ha : m ∣ A`, `hb : m ∣ B` and `u : (ZMod A)ˣ`,

`red(Units.map (ringEquivCongr h) u) = red u`.

Both reductions are computed by `ZMod.cast`, which only sees `ZMod.val`, and `ringEquivCongr`
preserves `ZMod.val` (`ZMod.ringEquivCongr_val`). -/
lemma units_map_castHom_ringEquivCongr {A B : ℕ} [NeZero A] [NeZero B] (h : A = B) {m : ℕ}
    (ha : m ∣ A) (hb : m ∣ B) (u : (ZMod A)ˣ) :
    Units.map (ZMod.castHom hb (ZMod m)).toMonoidHom
        (Units.map (ZMod.ringEquivCongr h).toMonoidHom u)
      = Units.map (ZMod.castHom ha (ZMod m)).toMonoidHom u := by
  apply Units.ext
  simp only [Units.coe_map]
  change ZMod.castHom hb (ZMod m) ((ZMod.ringEquivCongr h) (↑u : ZMod A))
      = ZMod.castHom ha (ZMod m) (↑u : ZMod A)
  rw [ZMod.castHom_apply, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.cast_eq_val,
    ZMod.ringEquivCongr_val]

/-- **Chinese remainder theorem for the tower of primes, in the form needed by `redPrime`.**

Every family of units `v i ∈ (ℤ/towerPrime i)^×`, `i < N`, is the family of reductions of a single
unit `u ∈ (ℤ/towerMod N)^×`:
`redPrime i.isLt u = v i` for all `i : Fin N`.

This is `NK.RankTheoryDeep.surjective_units_reduction_prod` (the CRT for units, stated for the
modulus `∏ i : Fin N, towerPrime i`) transported along the identification
`∏ i : Fin N, towerPrime i = towerMod N` of `Finset.prod_range`. -/
lemma tower_units_reduction (N : ℕ) (v : (i : Fin N) → (ZMod (towerPrime (i : ℕ)))ˣ) :
    ∃ u : (ZMod (towerMod N))ˣ, ∀ i : Fin N, redPrime i.isLt u = v i := by
  -- the two forms of the modulus of the `N`-th level agree
  have hmod : (∏ i : Fin N, towerPrime (i : ℕ)) = towerMod N :=
    (Finset.prod_range towerPrime).symm
  have hne₀ : (∏ i : Fin N, towerPrime (i : ℕ)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i _
    exact (towerPrime_prime (i : ℕ)).ne_zero
  haveI : NeZero (∏ i : Fin N, towerPrime (i : ℕ)) := ⟨hne₀⟩
  haveI : NeZero (towerMod N) := ⟨towerMod_ne_zero N⟩
  -- the Chinese remainder theorem for the units of the univ-product
  have hCRT : ∃ u : (ZMod (∏ i : Fin N, towerPrime (i : ℕ)))ˣ,
      ∀ i : Fin N, Units.map ↑(ZMod.castHom
          (Finset.dvd_prod_of_mem (fun j : Fin N => towerPrime (j : ℕ))
            (Finset.mem_univ i)) (ZMod (towerPrime (i : ℕ)))) u = v i := by
    obtain ⟨u, hu⟩ := surjective_units_reduction_prod (fun i : Fin N => towerPrime (i : ℕ))
      (fun i => (towerPrime_prime (i : ℕ)).ne_zero)
      (fun i j hij => towerPrime_coprime (fun h => hij (Fin.ext h))) v
    exact ⟨u, fun i => congrFun hu i⟩
  obtain ⟨u₀, hu₀⟩ := hCRT
  -- transport the unit to the modulus `towerMod N`; the reductions are unaffected
  refine ⟨Units.map (ZMod.ringEquivCongr hmod).toMonoidHom u₀, fun i => ?_⟩
  show Units.map (ZMod.castHom (towerPrime_dvd_towerMod i.isLt) (ZMod (towerPrime (i : ℕ)))).toMonoidHom
      (Units.map (ZMod.ringEquivCongr hmod).toMonoidHom u₀) = v i
  rw [units_map_castHom_ringEquivCongr hmod
    (Finset.dvd_prod_of_mem (fun j : Fin N => towerPrime (j : ℕ)) (Finset.mem_univ i))
    (towerPrime_dvd_towerMod i.isLt) u₀]
  exact hu₀ i

/-- **The joint coordinate map of the `N`-th cyclotomic level is surjective.**

For every family `x n ∈ ℤ/2^{n+1}` (`n < N`) there is an automorphism `σ` of `ℚ(ζ_{towerMod N})`
whose cyclotomic exponent, reduced modulo the `i`-th tower prime and pushed through the cyclic
surjection `(ℤ/towerPrime i)^× ↠ ℤ/2^{i+1}`, is `x i` for every `i < N`. -/
theorem jointHom_surjective (Ω : Type*) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (N : ℕ) : Function.Surjective (NK.RankTheoryDeep.jointHom Ω N) := by
  intro x
  -- the prescribed `2`-power coordinates, lifted to the cyclic components
  have h1 : ∀ i : Fin N, ∃ w : (ZMod (towerPrime (i : ℕ)))ˣ,
      cycSurj ((i : ℕ) + 1) (by omega) w = x i := fun i =>
    cycSurj_surjective ((i : ℕ) + 1) (by omega) (x i)
  choose v hv using h1
  -- one unit of `ℤ/towerMod N` reducing to all of them (CRT)
  obtain ⟨u, hu⟩ := tower_units_reduction N v
  -- and one automorphism realising that unit (cyclotomic exponent)
  obtain ⟨σ, hσ⟩ := expHom_surjective Ω N u
  refine ⟨σ, ?_⟩
  funext n
  show coordPrime ((n : ℕ) + 1) N (by omega) (by omega) (expHom Ω N σ) = x n
  rw [hσ]
  unfold coordPrime
  simp only [MonoidHom.comp_apply]
  rw [hu n]
  exact hv n

end NK.RankTheoryDeep
