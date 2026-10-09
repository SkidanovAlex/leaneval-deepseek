import Mathlib
import Submission.NK.Reconstruct.All
import Submission.NK.RankTheoryDeep.exists_surjective_hom_zmod_of_cyclic
import Submission.NK.RankTheoryDeep.surjective_units_reduction_prod
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The ℓ-adic cyclotomic tower of primes, for an arbitrary prime `ℓ`

This file sets up the *arithmetic and cyclotomic vocabulary* of the generalisation of
`NK.RankTheoryDeep.gamma_surjection_ellTower` from `ℓ = 2` to an arbitrary prime `ℓ`.

The tower of primes used for `ℓ = 2` (`NK.RankTheoryDeep.towerPrime`, the least prime factor of
the Fermat number `2 ^ 2 ^ n + 1`) is replaced by the uniform construction

  `towerNum ℓ k = ∑_{i < ℓ} ℓ ^ (i * ℓ ^ (k - 1))`  (the `k`-th "geometric number"),

whose prime factors `p` satisfy `orderOf (ℓ : ZMod p) = ℓ ^ k`, hence `ℓ ^ k ∣ p - 1`.  For
`ℓ = 2`, `k = n + 1` this is exactly the Fermat number `2 ^ (2 ^ n) + 1`.  The values
`towerNum ℓ k` for distinct `k` are pairwise coprime, so the primes `towerPrime ℓ n` obtained as
least prime factors are pairwise distinct.

The rest of the file is the verbatim ℓ-generalisation of the level vocabulary of
`Submission/Work/RankTheoryDeep/TowerArc.lean`: the cyclotomic levels `cycLevel ℓ Ω N`,
the cyclotomic exponent maps `expHom ℓ Ω N`, and the reductions `unitRed`, `redPrime`.
-/

attribute [local instance 10] DivisionRing.toRatAlgebra

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace NK.RankTheoryDeep.PrimeTower

open scoped Pointwise
open Polynomial

universe u

/-! ## The tower numbers and the tower primes -/

/-- **The `k`-th geometric number of the ℓ-adic tower**: `∑_{i < ℓ} ℓ ^ (i * ℓ ^ (k - 1))`.

Its prime divisors `p` satisfy `orderOf (ℓ : ZMod p) = ℓ ^ k` (see
`NK.RankTheoryDeep.PrimeTower.towerNum_prime_orderOf`), so that `ℓ ^ k ∣ p - 1`.  For `ℓ = 2`
and `k = n + 1` this is the Fermat number `2 ^ (2 ^ n) + 1`. -/
def towerNum (ℓ k : ℕ) : ℕ := ∑ i ∈ Finset.range ℓ, ℓ ^ (i * ℓ ^ (k - 1))

/-- **The `n`-th prime of the ℓ-adic tower**: the least prime factor of `towerNum ℓ (n + 1)`.

It satisfies `ℓ ^ (n + 1) ∣ towerPrime ℓ n - 1`, and distinct `n` give distinct primes. -/
def towerPrime (ℓ n : ℕ) : ℕ := (towerNum ℓ (n + 1)).minFac

/-- **The modulus of the `N`-th level**: the product of the first `N` tower primes. -/
def towerMod (ℓ N : ℕ) : ℕ := ∏ i ∈ Finset.range N, towerPrime ℓ i

section Arith

variable (ℓ : ℕ) [Fact ℓ.Prime]

theorem towerNum_pos (k : ℕ) : 0 < towerNum ℓ k := by
  rw [towerNum]
  exact Finset.sum_pos' (fun i _ => Nat.zero_le _)
    ⟨0, Finset.mem_range.mpr (Fact.out : ℓ.Prime).pos, by simp⟩

theorem towerNum_one_lt (k : ℕ) : 1 < towerNum ℓ k := by
  have hℓ2 : 2 ≤ ℓ := (Fact.out : ℓ.Prime).two_le
  have hmem : 1 ∈ Finset.range ℓ := Finset.mem_range.mpr hℓ2
  have hle : ℓ ^ (1 * ℓ ^ (k - 1)) ≤ towerNum ℓ k := by
    rw [towerNum]
    exact Finset.single_le_sum (f := fun i => ℓ ^ (i * ℓ ^ (k - 1)))
      (fun i _ => Nat.zero_le _) hmem
  have hexp : ℓ ^ (k - 1) ≠ 0 := pow_ne_zero _ (by omega : ℓ ≠ 0)
  have h1 : ℓ ^ 1 ≤ ℓ ^ (1 * ℓ ^ (k - 1)) := by
    rw [one_mul]
    exact Nat.pow_le_pow_right (by omega) (Nat.one_le_iff_ne_zero.mpr hexp)
  have h2 : 2 ≤ ℓ ^ 1 := by rw [pow_one]; exact hℓ2
  have h3 : 2 ≤ towerNum ℓ k := le_trans h2 (le_trans h1 hle)
  omega

theorem towerNum_ne_one (k : ℕ) : towerNum ℓ k ≠ 1 := (towerNum_one_lt ℓ k).ne'

theorem towerPrime_dvd (n : ℕ) : towerPrime ℓ n ∣ towerNum ℓ (n + 1) := Nat.minFac_dvd _

theorem towerPrime_prime (n : ℕ) : (towerPrime ℓ n).Prime :=
  Nat.minFac_prime (towerNum_ne_one ℓ (n + 1))

theorem towerPrime_ne_one (n : ℕ) : towerPrime ℓ n ≠ 1 := (towerPrime_prime ℓ n).ne_one

theorem towerPrime_pos (n : ℕ) : 0 < towerPrime ℓ n := (towerPrime_prime ℓ n).pos

theorem towerPrime_two_le (n : ℕ) : 2 ≤ towerPrime ℓ n := (towerPrime_prime ℓ n).two_le

theorem towerMod_zero : towerMod ℓ 0 = 1 := by simp [towerMod]

theorem towerMod_succ (N : ℕ) : towerMod ℓ (N + 1) = towerMod ℓ N * towerPrime ℓ N := by
  simp [towerMod, Finset.prod_range_succ]

theorem towerMod_pos (N : ℕ) : 0 < towerMod ℓ N :=
  Finset.prod_pos fun i _ => (towerPrime_prime ℓ i).pos

theorem towerMod_ne_zero (N : ℕ) : towerMod ℓ N ≠ 0 := (towerMod_pos ℓ N).ne'

theorem towerPrime_dvd_towerMod {i N : ℕ} (h : i < N) : towerPrime ℓ i ∣ towerMod ℓ N :=
  Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr h)

/-- **`towerNum ℓ k` is `1` modulo `ℓ`**: all the terms `i ≥ 1` of the defining sum are
multiples of `ℓ`, and the term `i = 0` equals `1`. -/
theorem exists_towerNum_eq (k : ℕ) : ∃ M : ℕ, towerNum ℓ k = 1 + ℓ * M := by
  have hℓpos : 0 < ℓ := (Fact.out : ℓ.Prime).pos
  have hmem : 0 ∈ Finset.range ℓ := Finset.mem_range.mpr hℓpos
  have hdiv : ∀ i ∈ (Finset.range ℓ).erase 0, ℓ ∣ ℓ ^ (i * ℓ ^ (k - 1)) := by
    intro i hi
    have hi0 : i ≠ 0 := Finset.ne_of_mem_erase hi
    have h1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
    have h2 : i * ℓ ^ (k - 1) ≠ 0 :=
      Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by omega))
    exact dvd_pow_self ℓ h2
  obtain ⟨M, hM⟩ : ∃ M, ∑ i ∈ (Finset.range ℓ).erase 0, ℓ ^ (i * ℓ ^ (k - 1)) = ℓ * M :=
    Finset.dvd_sum hdiv
  refine ⟨M, ?_⟩
  rw [towerNum, ← Finset.sum_erase_add (Finset.range ℓ)
    (fun i => ℓ ^ (i * ℓ ^ (k - 1))) hmem, hM, zero_mul, pow_zero]
  omega

/-- **`ℓ` does not divide `towerNum ℓ k`** (for `ℓ` prime): `towerNum ℓ k ≡ 1` modulo `ℓ`. -/
theorem not_dvd_towerNum (k : ℕ) : ¬ ℓ ∣ towerNum ℓ k := by
  obtain ⟨M, hM⟩ := exists_towerNum_eq ℓ k
  have hmod : towerNum ℓ k % ℓ = 1 := by
    rw [hM, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by have := (Fact.out : ℓ.Prime).one_lt; omega)
  intro h
  rw [Nat.mod_eq_zero_of_dvd h] at hmod
  omega

/-- **The geometric form of `towerNum` in `ZMod p`**: it is the geometric sum of ratio
`ℓ ^ (ℓ ^ (k - 1))`. -/
theorem cast_towerNum (k p : ℕ) :
    ((towerNum ℓ k : ZMod p))
      = ∑ i ∈ Finset.range ℓ, ((ℓ : ZMod p) ^ (ℓ ^ (k - 1))) ^ i := by
  rw [towerNum, Nat.cast_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [Nat.cast_pow, mul_comm, pow_mul]

/-- **The geometric-sum identity for `towerNum`** (for `k ≥ 1`): multiplying the geometric sum by
`ℓ ^ (ℓ ^ (k - 1)) - 1` gives `ℓ ^ (ℓ ^ k) - 1`. -/
theorem cast_towerNum_mul {k : ℕ} (hk : 1 ≤ k) (p : ℕ) :
    ((towerNum ℓ k : ZMod p)) * ((ℓ : ZMod p) ^ (ℓ ^ (k - 1)) - 1)
      = (ℓ : ZMod p) ^ (ℓ ^ k) - 1 := by
  have hexp : ℓ ^ (k - 1) * ℓ = ℓ ^ k := by rw [← pow_succ, Nat.sub_add_cancel hk]
  rw [cast_towerNum, geom_sum_mul, ← pow_mul, hexp]

theorem towerMod_dvd_of_le {n N : ℕ} (h : n ≤ N) : towerMod ℓ n ∣ towerMod ℓ N := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.add_succ, towerMod_succ]
      exact dvd_mul_of_dvd_left (ih (Nat.le_add_right n k)) _

end Arith

/-! ## The cyclotomic levels of `Ω` -/

section Level

variable (ℓ : ℕ) [Fact ℓ.Prime]
variable (Ω : Type u) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

/-- **A separable closure of `ℚ` contains a primitive `towerMod ℓ N`-th root of unity.** -/
theorem exists_isPrimitiveRoot_towerMod (N : ℕ) :
    ∃ ζ : Ω, IsPrimitiveRoot ζ (towerMod ℓ N) := by
  haveI : NeZero (towerMod ℓ N) := ⟨towerMod_ne_zero ℓ N⟩
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : PerfectField ℚ := PerfectField.ofCharZero
  haveI : IsAlgClosure ℚ Ω := inferInstance
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed (R := ℚ) (K := Ω)
  have hdeg : (Polynomial.cyclotomic (towerMod ℓ N) Ω).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic]
    simp only [ne_eq, Nat.cast_eq_zero]
    exact (Nat.totient_pos).mpr (towerMod_pos ℓ N) |>.ne'
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic (towerMod ℓ N) Ω) hdeg
  exact ⟨ζ, (isRoot_cyclotomic_iff_charZero (towerMod_pos ℓ N)).mp hζ⟩

/-- A chosen primitive `towerMod ℓ N`-th root of unity in `Ω`. -/
noncomputable def towerZeta (N : ℕ) : Ω :=
  Classical.choose (exists_isPrimitiveRoot_towerMod ℓ Ω N)

theorem towerZeta_isPrimitiveRoot (N : ℕ) :
    IsPrimitiveRoot (towerZeta ℓ Ω N) (towerMod ℓ N) :=
  Classical.choose_spec (exists_isPrimitiveRoot_towerMod ℓ Ω N)

/-- **The `N`-th cyclotomic level** `ℚ(ζ_{towerMod ℓ N})` of `Ω`. -/
noncomputable def cycLevel (N : ℕ) : NK.Reconstruct.FrobLevel ℚ Ω := by
  haveI : NeZero (towerMod ℓ N) := ⟨towerMod_ne_zero ℓ N⟩
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : Algebra.IsIntegral ℚ Ω := (IsSepClosure.separable.isAlgebraic).isIntegral
  haveI hcyc := (towerZeta_isPrimitiveRoot ℓ Ω N).intermediateField_adjoin_isCyclotomicExtension ℚ
  refine ⟨IntermediateField.adjoin ℚ ({towerZeta ℓ Ω N} : Set Ω), ?_, ?_, ?_⟩
  · exact IsCyclotomicExtension.finiteDimensional ({towerMod ℓ N} : Set ℕ) ℚ _
  · exact (IsCyclotomicExtension.isGalois ({towerMod ℓ N} : Set ℕ) ℚ _).to_normal
  · exact IsCyclotomicExtension.numberField ({towerMod ℓ N} : Set ℕ) ℚ _

theorem cycLevel_L (N : ℕ) :
    (cycLevel ℓ Ω N).L = IntermediateField.adjoin ℚ ({towerZeta ℓ Ω N} : Set Ω) := rfl

/-- The chosen primitive root, viewed in the level `ℚ(ζ_{towerMod ℓ N})`. -/
noncomputable def towerZetaL (N : ℕ) : ↥(cycLevel ℓ Ω N).L :=
  ⟨towerZeta ℓ Ω N,
    IntermediateField.subset_adjoin ℚ {towerZeta ℓ Ω N}
      (Set.mem_singleton (towerZeta ℓ Ω N))⟩

theorem towerZetaL_isPrimitiveRoot (N : ℕ) :
    IsPrimitiveRoot (towerZetaL ℓ Ω N) (towerMod ℓ N) :=
  (IsPrimitiveRoot.coe_submonoidClass_iff (N := (cycLevel ℓ Ω N).L)).mp
    (towerZeta_isPrimitiveRoot ℓ Ω N)

/-- **The cyclotomic levels are nested.** -/
theorem cycLevel_mono {n N : ℕ} (h : n ≤ N) :
    (cycLevel ℓ Ω n).L ≤ (cycLevel ℓ Ω N).L := by
  rw [cycLevel_L, cycLevel_L]
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  obtain ⟨k, hk⟩ := towerMod_dvd_of_le ℓ h
  haveI : NeZero (towerMod ℓ N) := ⟨towerMod_ne_zero ℓ N⟩
  have hpow : (towerZeta ℓ Ω n) ^ (towerMod ℓ N) = 1 := by
    rw [hk, pow_mul, (towerZeta_isPrimitiveRoot ℓ Ω n).pow_eq_one, one_pow]
  obtain ⟨i, -, hi⟩ :=
    IsPrimitiveRoot.eq_pow_of_pow_eq_one (towerZeta_isPrimitiveRoot ℓ Ω N) hpow
  rw [← hi]
  have hmem : towerZeta ℓ Ω N ∈ IntermediateField.adjoin ℚ ({towerZeta ℓ Ω N} : Set Ω) :=
    IntermediateField.mem_adjoin_of_mem ℚ (Set.mem_singleton (towerZeta ℓ Ω N))
  simpa using IntermediateField.pow_mem (IntermediateField.adjoin ℚ ({towerZeta ℓ Ω N} : Set Ω))
    hmem (i : ℤ)

/-- **The cyclotomic exponent map** `Gal(ℚ(ζ_m)/ℚ) →* (ℤ/m)^×`. -/
noncomputable def expHom (N : ℕ) :
    Gal(↥(cycLevel ℓ Ω N).L/ℚ) →* (ZMod (towerMod ℓ N))ˣ := by
  haveI : NeZero (towerMod ℓ N) := ⟨towerMod_ne_zero ℓ N⟩
  exact (towerZetaL_isPrimitiveRoot ℓ Ω N).autToPow ℚ

theorem expHom_spec (N : ℕ) (σ : Gal(↥(cycLevel ℓ Ω N).L/ℚ)) :
    (towerZetaL ℓ Ω N) ^ ((expHom ℓ Ω N σ : ZMod (towerMod ℓ N))).val
      = σ (towerZetaL ℓ Ω N) := by
  haveI : NeZero (towerMod ℓ N) := ⟨towerMod_ne_zero ℓ N⟩
  exact IsPrimitiveRoot.autToPow_spec ℚ (towerZetaL_isPrimitiveRoot ℓ Ω N) σ

/-- **The reductions of the unit groups.** -/
noncomputable def unitRed {n N : ℕ} (h : n ≤ N) :
    (ZMod (towerMod ℓ N))ˣ →* (ZMod (towerMod ℓ n))ˣ :=
  Units.map (ZMod.castHom (towerMod_dvd_of_le ℓ h) (ZMod (towerMod ℓ n))).toMonoidHom

/-- The reduction `(ZMod (towerMod ℓ N))ˣ → (ZMod (towerPrime ℓ i))ˣ` for `i < N`. -/
noncomputable def redPrime {i N : ℕ} (h : i < N) :
    (ZMod (towerMod ℓ N))ˣ →* (ZMod (towerPrime ℓ i))ˣ :=
  Units.map (ZMod.castHom (towerPrime_dvd_towerMod ℓ h) (ZMod (towerPrime ℓ i))).toMonoidHom

end Level

end NK.RankTheoryDeep.PrimeTower
