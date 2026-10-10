import Mathlib.Algebra.CharZero.Infinite
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.NK.Chebotarev.IsFrobAtOrderOfEqInertiaDeg
import Submission.NK.HeckeL.Zeta
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace NK.HeckeL.Product

open NumberField IsDedekindDomain

/-- **The Euler factor at a prime of `K` which is unramified in a Galois extension `L/K`.**

If every prime `𝔮` of `L` lying over `𝔭` is unramified over `𝔭`, then the product, over the primes
of `L` above `𝔭`, of the local Euler factors `(1 - N𝔮^{-s})^{-1}` is the `g`-th power of the
`f`-th power of the local Euler factor of `𝔭`, where

* `f = orderOf (frobAtPrime 𝔭)` is the inertia degree of `𝔭`, i.e. the order of the Frobenius
  at `𝔭` (`NK.Chebotarev.IsFrobAtOrderOfEqInertiaDeg`), and
* `g = Nat.card Gal(L/K) / f` is the number of primes of `L` above `𝔭`.

Indeed every prime `𝔮` above `𝔭` has residue degree `f` and `N𝔮 = N𝔭 ^ f`, and the fundamental
identity `g · e · f = [L : K]` together with `e = 1` gives `g = [L : K] / f`. -/
theorem zeta_eulerFactor_liesOver {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (𝔭 : NK.HeckeL.PrimeIdeal K)
    (hunr : ∀ 𝔮 : NK.HeckeL.PrimeIdeal L, 𝔮.asIdeal.LiesOver 𝔭.asIdeal →
      𝔮.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) (s : ℝ) :
    ∏ P : 𝔭.asIdeal.primesOver (NumberField.RingOfIntegers L),
        (1 - (((Ideal.absNorm P.1 : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ =
      ((1 - (((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ) ^
        orderOf (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭))⁻¹) ^
      (Nat.card Gal(L/K) / orderOf (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭)) := by
  classical
  -- Abbreviate the right hand side, so that the goal becomes `∏ ... = c ^ _`.
  set c : ℂ := (1 - (((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ) ^
        orderOf (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭))⁻¹ with hc
  -- A prime of `L` above `𝔭`, together with a Frobenius at it.  The chosen Frobenius at `𝔭` is
  -- this Frobenius element, and its order is the inertia degree at `𝔭`.
  have hex : ∃ σ : Gal(L/K), NK.Chebotarev.IsFrobAtPrime (K := K) (L := L) 𝔭 σ :=
    NK.Chebotarev.exists_isFrobAtPrime (K := K) (L := L) 𝔭
  have hfrob : NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭 = hex.choose := by
    rw [NK.Chebotarev.frobAtPrime, dif_pos hex]
  obtain ⟨P₀, hP₀lies, hP₀frob⟩ := hex.choose_spec
  haveI : P₀.asIdeal.IsPrime := P₀.isPrime
  haveI : P₀.asIdeal.LiesOver 𝔭.asIdeal := hP₀lies
  have hfeq : orderOf (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) =
      P₀.asIdeal.inertiaDeg (𝓞 K) := by
    rw [hfrob]
    exact NK.Chebotarev.IsFrobAtOrderOfEqInertiaDeg hP₀lies (hunr P₀ hP₀lies) hP₀frob
  haveI : 𝔭.asIdeal.IsPrime := 𝔭.isPrime
  -- `𝔭` is unramified in `L`, so its ramification index and inertia degree in `L` are
  -- `1` and `f = orderOf (frobAtPrime 𝔭)` respectively.
  have he : Ideal.ramificationIdxIn 𝔭.asIdeal (𝓞 L) = 1 := by
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx 𝔭.asIdeal P₀.asIdeal (Gal(L/K))]
    exact hunr P₀ hP₀lies
  have hfIn : Ideal.inertiaDegIn 𝔭.asIdeal (𝓞 L) = P₀.asIdeal.inertiaDeg (𝓞 K) :=
    Ideal.inertiaDegIn_eq_inertiaDeg 𝔭.asIdeal P₀.asIdeal (Gal(L/K))
  -- The fundamental identity: `g · e · f = [L : K]`.
  have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (A := 𝓞 K) (B := 𝓞 L)
    𝔭.asIdeal (Gal(L/K))
  have hcard : (𝔭.asIdeal.primesOver (𝓞 L)).ncard *
      orderOf (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) = Nat.card Gal(L/K) := by
    rw [hfIn, ← hfeq, he, one_mul] at hfund
    exact hfund
  have hfpos : 0 < orderOf (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) := orderOf_pos _
  -- Hence the number of primes above `𝔭` is `Nat.card Gal(L/K) / f`.
  have hquot : Nat.card Gal(L/K) / orderOf (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭)
      = (𝔭.asIdeal.primesOver (𝓞 L)).ncard := by
    rw [← hcard]
    exact Nat.mul_div_cancel _ hfpos
  -- Every prime `P` above `𝔭` has norm `N𝔭 ^ f` (here `Ideal.absNorm_pow_inertiaDeg`), the
  -- inertia degrees above `𝔭` being all equal.
  have hNR : ∀ P : 𝔭.asIdeal.primesOver (𝓞 L), Ideal.absNorm P.1 =
      Ideal.absNorm 𝔭.asIdeal ^
        orderOf (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) := by
    intro P
    have h1 := Ideal.absNorm_pow_inertiaDeg (R := 𝓞 K) (S := 𝓞 L) 𝔭.asIdeal P.1
    have h2 : P.1.inertiaDeg (𝓞 K) =
        orderOf (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) := by
      rw [hfeq]
      exact Ideal.inertiaDeg_eq_of_isGaloisGroup 𝔭.asIdeal P.1 P₀.asIdeal (Gal(L/K))
    rw [h2] at h1
    exact h1.symm
  -- The real/complex identities `(N𝔭 ^ f) ^ (-s) = (N𝔭 ^ (-s)) ^ f`.
  have hreal : (((Ideal.absNorm 𝔭.asIdeal ^
        orderOf (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) : ℕ) : ℝ) ^ (-s))
      = (((Ideal.absNorm 𝔭.asIdeal : ℝ)) ^ (-s)) ^
        orderOf (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) := by
    have hA : (0 : ℝ) ≤ (Ideal.absNorm 𝔭.asIdeal : ℝ) := Nat.cast_nonneg _
    rw [Nat.cast_pow]
    calc (((Ideal.absNorm 𝔭.asIdeal : ℝ)) ^
              orderOf (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭)) ^ (-s)
        = ((Ideal.absNorm 𝔭.asIdeal : ℝ) ^
            (((orderOf (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) : ℝ)) * (-s))) :=
          (Real.rpow_natCast_mul hA _ (-s)).symm
      _ = ((Ideal.absNorm 𝔭.asIdeal : ℝ) ^
            ((-s) * ((orderOf (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) : ℝ)))) := by
          rw [mul_comm]
      _ = ((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) ^
            orderOf (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) :=
          Real.rpow_mul_natCast hA (-s) _
  have hcomplex : ((((Ideal.absNorm 𝔭.asIdeal ^
          orderOf (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ)
      = ((((Ideal.absNorm 𝔭.asIdeal : ℝ)) ^ (-s) : ℝ) : ℂ) ^
        orderOf (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) := by
    rw [hreal, Complex.ofReal_pow]
  -- Hence all the factors are equal to `c`.
  have hconst : ∀ P : 𝔭.asIdeal.primesOver (𝓞 L),
      (1 - (((Ideal.absNorm P.1 : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ = c := by
    intro P
    rw [hNR P, hcomplex, hc]
  have hprod : ∏ P : 𝔭.asIdeal.primesOver (𝓞 L),
      (1 - (((Ideal.absNorm P.1 : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹
      = c ^ (𝔭.asIdeal.primesOver (𝓞 L)).ncard := by
    calc ∏ P : 𝔭.asIdeal.primesOver (𝓞 L),
            (1 - (((Ideal.absNorm P.1 : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹
        = ∏ _P : 𝔭.asIdeal.primesOver (𝓞 L), c := Finset.prod_congr rfl (fun P _ => hconst P)
      _ = c ^ Fintype.card (𝔭.asIdeal.primesOver (𝓞 L)) := Finset.prod_const c
      _ = c ^ (𝔭.asIdeal.primesOver (𝓞 L)).ncard := by rw [Set.fintypeCard_eq_ncard]
  rw [hquot]
  exact hprod

end NK.HeckeL.Product
