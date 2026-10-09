import Mathlib
import Submission.NK.RankTheoryDeep.ProductRank
import Submission.NK.RankTheoryDeep.fermat_prime_dvd_sub_one
import Submission.NK.RankTheoryDeep.exists_surjective_hom_zmod_of_cyclic
import Submission.NK.RankTheoryDeep.surjective_units_reduction_prod
import Submission.NK.RankTheoryDeep.autToPow_castHom_pow
import Submission.NK.Reconstruct.All
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `2`-adic tower of cyclotomic levels inside a separable closure of `ℚ`

This file sets up the *arithmetic* vocabulary of
`NK.RankTheoryDeep.gamma_surjection_ellTower`: the tower of primes `q n` with `2 ^ (n + 1) ∣ q n - 1`
(the least prime factors of the Fermat numbers, `NK.RankTheoryDeep.towerPrime`), the cyclotomic
levels `ℚ(ζ_{q 0 ⋯ q (N - 1)})` of `Ω` (`NK.RankTheoryDeep.cycLevel`), the exponent maps
`Gal(ℚ(ζ_m)/ℚ) →* (ℤ/m)^×` (`NK.RankTheoryDeep.expHom`), and the reductions
`(ℤ/m)^× → (ℤ/m')^×` for `m' ∣ m` (`NK.RankTheoryDeep.unitRed`).

The main arithmetic statements are

* `NK.RankTheoryDeep.towerPrime_two_pow_dvd_sub_one` — `2 ^ (n + 1) ∣ q n - 1`;
* `NK.RankTheoryDeep.cycLevel_mono` — the levels are nested;
* `NK.RankTheoryDeep.expHom_levelRestrict` — **the naturality of the cyclotomic exponent**:
  restricting an automorphism of the level `N` to a smaller level reduces the exponent.

The file also prepares the `ℤ_2`-module structure of the coordinates
(`NK.RankTheoryDeep.cycSurj`, `NK.RankTheoryDeep.coordPrime`,
`NK.RankTheoryDeep.levelCoord`).
-/

attribute [local instance 10] DivisionRing.toRatAlgebra

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace NK.RankTheoryDeep

open scoped Pointwise
open Polynomial

universe u

/-! ## The tower of primes and the moduli of the levels -/

/-- **The `n`-th prime of the tower**: the least prime factor of the Fermat number `2 ^ 2 ^ n + 1`.

Every prime divisor `q` of `2 ^ (2 ^ n) + 1` satisfies `ord_q 2 = 2 ^ (n + 1)`, hence
`2 ^ (n + 1) ∣ q - 1`; the Fermat numbers are pairwise coprime, so the primes obtained this way
for distinct `n` are distinct. -/
def towerPrime (n : ℕ) : ℕ := (2 ^ 2 ^ n + 1).minFac

theorem towerPrime_dvd (n : ℕ) : towerPrime n ∣ 2 ^ 2 ^ n + 1 := Nat.minFac_dvd _

theorem towerPrime_prime (n : ℕ) : (towerPrime n).Prime := by
  refine Nat.minFac_prime ?_
  have h : 0 < 2 ^ 2 ^ n := pow_pos (by norm_num) _
  omega

theorem towerPrime_ne_one (n : ℕ) : towerPrime n ≠ 1 := (towerPrime_prime n).ne_one

/-- **`2 ^ (n + 1) ∣ towerPrime n - 1`**: the order of `2` modulo a prime divisor of the Fermat
number `2 ^ (2 ^ n) + 1` is exactly `2 ^ (n + 1)`. -/
theorem towerPrime_two_pow_dvd_sub_one (n : ℕ) : 2 ^ (n + 1) ∣ towerPrime n - 1 :=
  fermat_prime_dvd_sub_one (towerPrime_prime n) (towerPrime_dvd n)

/-- **The tower primes are pairwise distinct**, being distinct prime divisors of pairwise coprime
Fermat numbers. -/
theorem towerPrime_injective : Function.Injective towerPrime := by
  intro m n hmn
  by_contra hne
  have hcop : Nat.Coprime (2 ^ 2 ^ m + 1) (2 ^ 2 ^ n + 1) :=
    Nat.coprime_fermatNumber_fermatNumber hne
  have h1 : towerPrime m ∣ 2 ^ 2 ^ m + 1 := towerPrime_dvd m
  have h2 : towerPrime m ∣ 2 ^ 2 ^ n + 1 := by rw [hmn]; exact towerPrime_dvd n
  have h3 : towerPrime m ∣ Nat.gcd (2 ^ 2 ^ m + 1) (2 ^ 2 ^ n + 1) := Nat.dvd_gcd h1 h2
  rw [hcop] at h3
  have h4 : 1 < towerPrime m := (towerPrime_prime m).one_lt
  have h5 : towerPrime m ≤ 1 := Nat.le_of_dvd (by norm_num) h3
  omega

/-- Distinct tower primes are coprime. -/
theorem towerPrime_coprime {i j : ℕ} (h : i ≠ j) : Nat.Coprime (towerPrime i) (towerPrime j) := by
  refine ((towerPrime_prime i).coprime_iff_not_dvd).mpr fun hdvd => h ?_
  have heq : towerPrime j = towerPrime i :=
    ((towerPrime_prime j).dvd_iff_eq (towerPrime_prime i).ne_one).mp hdvd
  exact towerPrime_injective heq.symm

/-- **The modulus of the `N`-th level**: the product of the first `N` tower primes. -/
def towerMod (N : ℕ) : ℕ := ∏ i ∈ Finset.range N, towerPrime i

theorem towerMod_zero : towerMod 0 = 1 := by simp [towerMod]

theorem towerMod_succ (N : ℕ) : towerMod (N + 1) = towerMod N * towerPrime N := by
  simp [towerMod, Finset.prod_range_succ]

theorem towerMod_pos (N : ℕ) : 0 < towerMod N :=
  Finset.prod_pos fun i _ => (towerPrime_prime i).pos

theorem towerMod_ne_zero (N : ℕ) : towerMod N ≠ 0 := (towerMod_pos N).ne'

theorem towerPrime_dvd_towerMod {i N : ℕ} (h : i < N) : towerPrime i ∣ towerMod N :=
  Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr h)

theorem towerMod_dvd_of_le {n N : ℕ} (h : n ≤ N) : towerMod n ∣ towerMod N := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.add_succ, towerMod_succ]
      exact dvd_mul_of_dvd_left (ih (Nat.le_add_right n k)) _

/-! ## The cyclotomic levels of `Ω` -/

section Level

variable (Ω : Type u) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

/-- **A separable closure of `ℚ` contains a primitive `m`-th root of unity** for every `m > 0`. -/
theorem exists_isPrimitiveRoot_towerMod (N : ℕ) : ∃ ζ : Ω, IsPrimitiveRoot ζ (towerMod N) := by
  haveI : NeZero (towerMod N) := ⟨towerMod_ne_zero N⟩
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : PerfectField ℚ := PerfectField.ofCharZero
  haveI : IsAlgClosure ℚ Ω := inferInstance
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed (R := ℚ) (K := Ω)
  have hdeg : (Polynomial.cyclotomic (towerMod N) Ω).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic]
    simp only [ne_eq, Nat.cast_eq_zero]
    exact (Nat.totient_pos).mpr (towerMod_pos N) |>.ne'
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic (towerMod N) Ω) hdeg
  exact ⟨ζ, (isRoot_cyclotomic_iff_charZero (towerMod_pos N)).mp hζ⟩

/-- A chosen primitive `towerMod N`-th root of unity in `Ω`. -/
noncomputable def towerZeta (N : ℕ) : Ω := Classical.choose (exists_isPrimitiveRoot_towerMod Ω N)

theorem towerZeta_isPrimitiveRoot (N : ℕ) :
    IsPrimitiveRoot (towerZeta Ω N) (towerMod N) :=
  Classical.choose_spec (exists_isPrimitiveRoot_towerMod Ω N)

/-- **The `N`-th cyclotomic level** `ℚ(ζ_{towerMod N})` of `Ω`, as a finite Galois number-field
level. -/
noncomputable def cycLevel (N : ℕ) : NK.Reconstruct.FrobLevel ℚ Ω := by
  haveI : NeZero (towerMod N) := ⟨towerMod_ne_zero N⟩
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : Algebra.IsIntegral ℚ Ω := (IsSepClosure.separable.isAlgebraic).isIntegral
  haveI hcyc := (towerZeta_isPrimitiveRoot Ω N).intermediateField_adjoin_isCyclotomicExtension ℚ
  refine ⟨IntermediateField.adjoin ℚ ({towerZeta Ω N} : Set Ω), ?_, ?_, ?_⟩
  · exact IsCyclotomicExtension.finiteDimensional ({towerMod N} : Set ℕ) ℚ _
  · exact (IsCyclotomicExtension.isGalois ({towerMod N} : Set ℕ) ℚ _).to_normal
  · exact IsCyclotomicExtension.numberField ({towerMod N} : Set ℕ) ℚ _

theorem cycLevel_L (N : ℕ) :
    (cycLevel Ω N).L = IntermediateField.adjoin ℚ ({towerZeta Ω N} : Set Ω) := rfl

/-- The chosen primitive root, viewed in the level `ℚ(ζ_{towerMod N})`. -/
noncomputable def towerZetaL (N : ℕ) : ↥(cycLevel Ω N).L :=
  ⟨towerZeta Ω N,
    IntermediateField.subset_adjoin ℚ {towerZeta Ω N} (Set.mem_singleton (towerZeta Ω N))⟩

theorem towerZetaL_isPrimitiveRoot (N : ℕ) :
    IsPrimitiveRoot (towerZetaL Ω N) (towerMod N) :=
  (IsPrimitiveRoot.coe_submonoidClass_iff (N := (cycLevel Ω N).L)).mp
    (towerZeta_isPrimitiveRoot Ω N)

/-- **The cyclotomic levels are nested**: for `n ≤ N` the field `ℚ(ζ_{towerMod n})` is a subfield of
`ℚ(ζ_{towerMod N})`, since `towerMod n ∣ towerMod N` and every `towerMod n`-th root of unity is a
power of a primitive `towerMod N`-th root of unity. -/
theorem cycLevel_mono {n N : ℕ} (h : n ≤ N) :
    (cycLevel Ω n).L ≤ (cycLevel Ω N).L := by
  rw [cycLevel_L, cycLevel_L]
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  obtain ⟨k, hk⟩ := towerMod_dvd_of_le h
  haveI : NeZero (towerMod N) := ⟨towerMod_ne_zero N⟩
  have hpow : (towerZeta Ω n) ^ (towerMod N) = 1 := by
    rw [hk, pow_mul, (towerZeta_isPrimitiveRoot Ω n).pow_eq_one, one_pow]
  obtain ⟨i, -, hi⟩ :=
    IsPrimitiveRoot.eq_pow_of_pow_eq_one (towerZeta_isPrimitiveRoot Ω N) hpow
  rw [← hi]
  have hmem : towerZeta Ω N ∈ IntermediateField.adjoin ℚ ({towerZeta Ω N} : Set Ω) :=
    IntermediateField.mem_adjoin_of_mem ℚ (Set.mem_singleton (towerZeta Ω N))
  simpa using IntermediateField.pow_mem (IntermediateField.adjoin ℚ ({towerZeta Ω N} : Set Ω))
    hmem (i : ℤ)

/-- **The cyclotomic exponent map** `Gal(ℚ(ζ_m)/ℚ) →* (ℤ/m)^×`: the automorphism `σ` is sent to
the exponent `a` with `σ ζ = ζ ^ a`. -/
noncomputable def expHom (N : ℕ) :
    Gal(↥(cycLevel Ω N).L/ℚ) →* (ZMod (towerMod N))ˣ := by
  haveI : NeZero (towerMod N) := ⟨towerMod_ne_zero N⟩
  exact (towerZetaL_isPrimitiveRoot Ω N).autToPow ℚ

/-- The defining property of the cyclotomic exponent map: `σ ζ = ζ ^ (expHom σ)`. -/
theorem expHom_spec (N : ℕ) (σ : Gal(↥(cycLevel Ω N).L/ℚ)) :
    (towerZetaL Ω N) ^ ((expHom Ω N σ : ZMod (towerMod N))).val = σ (towerZetaL Ω N) := by
  haveI : NeZero (towerMod N) := ⟨towerMod_ne_zero N⟩
  exact IsPrimitiveRoot.autToPow_spec ℚ (towerZetaL_isPrimitiveRoot Ω N) σ

/-- **The reductions of the unit groups**: for `towerMod n ∣ towerMod N`, the ring reduction
`ℤ/towerMod N → ℤ/towerMod n` on units. -/
noncomputable def unitRed {n N : ℕ} (h : n ≤ N) :
    (ZMod (towerMod N))ˣ →* (ZMod (towerMod n))ˣ :=
  Units.map (ZMod.castHom (towerMod_dvd_of_le h) (ZMod (towerMod n))).toMonoidHom

/-- The reduction `(ZMod (towerMod N))ˣ → (ZMod (towerPrime i))ˣ` for `i < N`. -/
noncomputable def redPrime {i N : ℕ} (h : i < N) :
    (ZMod (towerMod N))ˣ →* (ZMod (towerPrime i))ˣ :=
  Units.map (ZMod.castHom (towerPrime_dvd_towerMod h) (ZMod (towerPrime i))).toMonoidHom

/-- **The divisibility of the unit-group orders used to build the cyclic surjection.** -/
theorem cycSurj_dvd {n : ℕ} (hn : 1 ≤ n) : 2 ^ n ∣ Nat.card (ZMod (towerPrime (n - 1)))ˣ := by
  haveI : Fact (towerPrime (n - 1)).Prime := ⟨towerPrime_prime (n - 1)⟩
  haveI : NeZero (towerPrime (n - 1)) := ⟨(towerPrime_prime (n - 1)).ne_zero⟩
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.totient_prime (towerPrime_prime (n - 1))]
  have h := towerPrime_two_pow_dvd_sub_one (n - 1)
  rwa [Nat.sub_add_cancel hn] at h

/-- **The `n`-th cyclic surjection**: the cyclic group `(ℤ/q (n - 1))^×` of order divisible by
`2 ^ n` maps onto `ℤ/2 ^ n`. -/
noncomputable def cycSurj (n : ℕ) (hn : 1 ≤ n) :
    (ZMod (towerPrime (n - 1)))ˣ →* Multiplicative (ZMod (2 ^ n)) := by
  haveI : Fact (towerPrime (n - 1)).Prime := ⟨towerPrime_prime (n - 1)⟩
  exact Classical.choose (exists_surjective_hom_zmod_of_cyclic (cycSurj_dvd hn))

theorem cycSurj_surjective (n : ℕ) (hn : 1 ≤ n) : Function.Surjective (cycSurj n hn) := by
  haveI : Fact (towerPrime (n - 1)).Prime := ⟨towerPrime_prime (n - 1)⟩
  exact Classical.choose_spec (exists_surjective_hom_zmod_of_cyclic (cycSurj_dvd hn))

/-- **The `n`-th coordinate character of the `N`-th level**: reduce the cyclotomic exponent of an
automorphism mod `q (n - 1)` and apply the cyclic surjection onto `ℤ/2 ^ n`. -/
noncomputable def coordPrime (n N : ℕ) (hn : 1 ≤ n) (hN : n ≤ N) :
    (ZMod (towerMod N))ˣ →* Multiplicative (ZMod (2 ^ n)) :=
  (cycSurj n hn).comp (redPrime (by omega))

/-- **The `n`-th coordinate of the `N`-th level**, on the `2`-part of the abelianisation of
`Gal(ℚ(ζ_{towerMod N})/ℚ)`: the cyclotomic exponent, reduced mod `q (n - 1)` and pushed through
the cyclic surjection. -/
noncomputable def levelCoordHom (n N : ℕ) (hn : 1 ≤ n) (hN : n ≤ N) :
    NK.Reconstruct.LevelEllPart (cycLevel Ω N).L 2 →* Multiplicative (ZMod (2 ^ n)) :=
  ((coordPrime n N hn hN).comp (Abelianization.lift (expHom Ω N))).comp (Subgroup.subtype _)

/-- **The joint coordinate character of the `N`-th level**: the product of the coordinate
characters `1, …, N`. -/
noncomputable def jointHom (N : ℕ) :
    Gal(↥(cycLevel Ω N).L/ℚ) →*
      (∀ n : Fin N, Multiplicative (ZMod (2 ^ (n.val + 1)))) where
  toFun σ n := coordPrime (n.val + 1) N (by omega) (by omega) (expHom Ω N σ)
  map_one' := by
    funext n
    rw [Pi.one_apply, map_one, map_one]
  map_mul' σ τ := by
    funext n
    rw [Pi.mul_apply, map_mul, map_mul]

/-- **The joint coordinate map of the `N`-th level**, on the `2`-part of the abelianisation. -/
noncomputable def jointLevelHom (N : ℕ) :
    NK.Reconstruct.LevelEllPart (cycLevel Ω N).L 2 →*
      (∀ n : Fin N, Multiplicative (ZMod (2 ^ (n.val + 1)))) :=
  (Abelianization.lift (jointHom Ω N)).comp (Subgroup.subtype _)


end Level

end NK.RankTheoryDeep
