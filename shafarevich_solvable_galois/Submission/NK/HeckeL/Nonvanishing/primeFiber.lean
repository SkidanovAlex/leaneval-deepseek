import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Submission.NK.Chebotarev.IsFrobAtOrderOfEqInertiaDeg
import Submission.NK.HeckeL.Zeta
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain
open scoped BigOperators Classical nonZeroDivisors

noncomputable section

namespace NK.HeckeL.Nonvanishing

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-! ## The prime below a prime -/

/-- The prime of `𝓞 K` below a nonzero prime of `𝓞 L`. -/
noncomputable def underPrime (𝔮 : PrimeIdeal L) : PrimeIdeal K :=
  ⟨𝔮.asIdeal.under (𝓞 K), Ideal.IsPrime.under (𝓞 K) 𝔮.asIdeal,
    Ideal.under_ne_bot (𝓞 K) 𝔮.ne_bot⟩

@[simp]
theorem underPrime_asIdeal (𝔮 : PrimeIdeal L) :
    (underPrime (K := K) 𝔮).asIdeal = 𝔮.asIdeal.under (𝓞 K) := rfl

theorem underPrime_eq_iff {𝔮 : PrimeIdeal L} {𝔭 : PrimeIdeal K} :
    underPrime 𝔮 = 𝔭 ↔ 𝔮.asIdeal.LiesOver 𝔭.asIdeal := by
  rw [Ideal.liesOver_iff]
  exact ⟨fun h => by rw [← h]; rfl, fun h => HeightOneSpectrum.ext h.symm⟩

theorem underPrime_eq_iff' {𝔮 : PrimeIdeal L} {𝔭 : PrimeIdeal K} :
    𝔭 = underPrime 𝔮 ↔ 𝔮.asIdeal.LiesOver 𝔭.asIdeal := by
  rw [eq_comm, underPrime_eq_iff]

theorem underPrime_liesOver (𝔮 : PrimeIdeal L) :
    𝔮.asIdeal.LiesOver (underPrime (K := K) 𝔮).asIdeal :=
  ⟨rfl⟩

theorem liesOver_eq_of_liesOver {𝔮 : PrimeIdeal L} {𝔭 Q : PrimeIdeal K}
    (h : 𝔮.asIdeal.LiesOver 𝔭.asIdeal) (hQ : 𝔮.asIdeal.LiesOver Q.asIdeal) : Q = 𝔭 :=
  HeightOneSpectrum.ext
    (((Ideal.liesOver_iff 𝔮.asIdeal Q.asIdeal).mp hQ).trans
      ((Ideal.liesOver_iff 𝔮.asIdeal 𝔭.asIdeal).mp h).symm)

/-! ## The fibre of the places of `L` over a place of `K` -/

/-- The primes of `𝓞 L` lying above a fixed prime `𝔭` of `𝓞 K`, as a subtype of `PrimeIdeal L`.
Defined through `underPrime` so that a fibre is literally `{𝔮 // underPrime 𝔮 = 𝔭}`. -/
abbrev primesOverPrime (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (𝔭 : PrimeIdeal K) : Type _ :=
  {𝔮 : PrimeIdeal L // underPrime (K := K) 𝔮 = 𝔭}

/-- The same fibre, described by `Ideal.LiesOver`. -/
abbrev primesOverPrimeLiesOver (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (𝔭 : PrimeIdeal K) : Type _ :=
  {𝔮 : PrimeIdeal L // 𝔮.asIdeal.LiesOver 𝔭.asIdeal}

noncomputable def primesOverPrimeEquivLiesOver (𝔭 : PrimeIdeal K) :
    primesOverPrime K L 𝔭 ≃ primesOverPrimeLiesOver K L 𝔭 :=
  Equiv.subtypeEquivRight fun _ => underPrime_eq_iff

/-- The fibre `primesOverPrime K L 𝔭` is the same as Mathlib's `𝔭.asIdeal.primesOver 𝓞 L`. -/
noncomputable def primesOverPrimeEquivMathlib (𝔭 : PrimeIdeal K) :
    primesOverPrimeLiesOver K L 𝔭 ≃ ↥(𝔭.asIdeal.primesOver (𝓞 L)) where
  toFun 𝔮 := ⟨𝔮.1.asIdeal, ⟨𝔮.1.isPrime, 𝔮.2⟩⟩
  invFun q := ⟨⟨q.1, q.2.1, fun hbot => by
    have h : 𝔭.asIdeal = Ideal.under (𝓞 K) q.1 := (Ideal.liesOver_iff q.1 𝔭.asIdeal).mp q.2.2
    rw [hbot, Ideal.under_bot] at h
    exact 𝔭.ne_bot h⟩, q.2.2⟩
  left_inv 𝔮 := by ext; rfl
  right_inv q := by ext; rfl

noncomputable instance instFintypePrimesOverPrime (𝔭 : PrimeIdeal K) :
    Fintype (primesOverPrime K L 𝔭) :=
  Fintype.ofEquiv _ ((primesOverPrimeEquivLiesOver (K := K) (L := L) 𝔭).trans
    (primesOverPrimeEquivMathlib (K := K) (L := L) 𝔭)).symm

theorem natCard_primesOverPrime (𝔭 : PrimeIdeal K) :
    Nat.card (primesOverPrime K L 𝔭) = Fintype.card ↥(𝔭.asIdeal.primesOver (𝓞 L)) :=
  Nat.card_eq_fintype_card.trans
    (Fintype.card_congr
      ((primesOverPrimeEquivLiesOver (K := K) (L := L) 𝔭).trans
        (primesOverPrimeEquivMathlib (K := K) (L := L) 𝔭)))

/-! ## Primes avoiding a modulus -/

/-- The primes of `𝓞 L` which do not lie above any prime of the modulus `S`. -/
abbrev primesOutside (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (S : Finset (PrimeIdeal K)) : Type _ :=
  {𝔮 : PrimeIdeal L // ∀ Q ∈ S, ¬ 𝔮.asIdeal.LiesOver Q.asIdeal}

theorem zetaUnramified_eq_tprod_primesOutside (S : Finset (PrimeIdeal K)) (s : ℝ) :
    zetaUnramified K L S s =
      ∏' 𝔮 : primesOutside K L S,
        (1 - (((Ideal.absNorm 𝔮.1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ :=
  tprod_congr_subtype (fun 𝔮 : PrimeIdeal L =>
      (1 - (((Ideal.absNorm 𝔮.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹) fun 𝔮 => Iff.rfl

/-- A prime of `L` above a prime of `K` outside `S` avoids the modulus `S`. -/
theorem liesOver_subset_of_notMem {S : Finset (PrimeIdeal K)} {𝔮 : PrimeIdeal L} {𝔭 : PrimeIdeal K}
    (h𝔭 : 𝔭 ∉ S) (h : 𝔮.asIdeal.LiesOver 𝔭.asIdeal) :
    ∀ Q ∈ S, ¬ 𝔮.asIdeal.LiesOver Q.asIdeal := by
  intro Q hQ hQlies
  exact h𝔭 ((liesOver_eq_of_liesOver h hQlies).symm ▸ hQ)

/-- Avoiding a modulus `S` is the same as the prime below not lying in `S`. -/
theorem not_liesOver_iff_underPrime_notMem {S : Finset (PrimeIdeal K)} {𝔮 : PrimeIdeal L} :
    (∀ Q ∈ S, ¬ 𝔮.asIdeal.LiesOver Q.asIdeal) ↔ underPrime (K := K) 𝔮 ∉ S := by
  constructor
  · intro h hmem
    exact h (underPrime 𝔮) hmem (underPrime_liesOver 𝔮)
  · intro h Q hQ hQlies
    exact h ((underPrime_eq_iff (𝔮 := 𝔮) (𝔭 := Q)).mpr hQlies ▸ hQ)

end NK.HeckeL.Nonvanishing
