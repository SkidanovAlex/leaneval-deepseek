import Mathlib
import Submission.NK.CFTLib.ArtinReciprocityIdeal.LangDefs
import Submission.NK.CFTLib.ArtinReciprocityIdeal.frobAtPrime_prod_relNorm_eq_one
import Submission.NK.CFTLib.ArtinReciprocityIdeal.Basic
import Submission.NK.CFTLib.Arl.Defs

/-!
# The Artin symbol kills the norm group `𝔑(m)`

This file proves `NK.CFTLib.ArtinReciprocityIdeal.normRayLeKer`: for a finite abelian Galois
extension `L / K` of number fields and a modulus `m > 0` whose primes include all the primes
ramified in `L/K`, the Artin symbol `NK.CFTLib.Arl.artinSym` of every fractional ideal in the
norm group `normRay K L m = 𝔑(m)` is trivial.  This is Lang, *Algebraic Number Theory*, Chapter X
§2, property **A4** ("norms are killed by the Artin symbol"), in the ideal-theoretic form used by
the conductor theorem.

The mathematical content is the classical fact that the Artin symbol of a relative norm
`N_{L/K}𝔟` is trivial (equivalently, the Frobenius element at a prime `𝔭` of `K` has order the
inertia degree `f(𝔓|𝔭)`, so that the symbol of `𝔭^{f(𝔓|𝔭)} = N𝔓` is `1`).  The coprimality of the
ideal with `(m)` guarantees that all primes occurring in the norm are *unramified* — this is the
only place the hypothesis on `m` is used — and `artinSym` coincides with the ideal-theoretic
symbol `artinSymbol` there.

The proof is an induction on the ideal `𝔟` of `𝓞 L` (using `UniqueFactorizationMonoid`), the
multiplicativity of `artinSym` on the group of fractional ideals (`artinSym_mul`), and the
computation `relNorm 𝔓 = 𝔭 ^ f(𝔓|𝔭)` at a prime `𝔓`.

## Main result

* `NK.CFTLib.ArtinReciprocityIdeal.normRayLeKer`
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField nonZeroDivisors IsMulCommutative
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.ArtinReciprocityIdeal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative (Gal(L/K))]

/-- The Artin symbol of a fractional ideal, as a monoid homomorphism from the group `Frac K` of
fractional ideals to `Gal(L/K)`.  This is the only way in which the multiplicative properties of
`NK.CFTLib.Arl.artinSym` are used below. -/
noncomputable def artinSymFracHom (hcomm : ∀ a b : Gal(L/K), a * b = b * a) :
    Frac K →* Gal(L/K) where
  toFun A := NK.CFTLib.Arl.artinSym hcomm (A : FractionalIdeal (𝓞 K)⁰ K)
  map_one' := by
    rw [show ((1 : Frac K) : FractionalIdeal (𝓞 K)⁰ K) = 1 from Units.val_one]
    exact NK.CFTLib.Arl.artinSym_one hcomm
  map_mul' A B := by
    rw [show ((A * B : Frac K) : FractionalIdeal (𝓞 K)⁰ K)
        = (A : FractionalIdeal (𝓞 K)⁰ K) * (B : FractionalIdeal (𝓞 K)⁰ K)
        from Units.val_mul A B]
    exact NK.CFTLib.Arl.artinSym_mul hcomm (Units.ne_zero A) (Units.ne_zero B)

@[simp] lemma artinSymFracHom_apply (hcomm : ∀ a b : Gal(L/K), a * b = b * a) (A : Frac K) :
    artinSymFracHom (K := K) (L := L) hcomm A
      = NK.CFTLib.Arl.artinSym hcomm (A : FractionalIdeal (𝓞 K)⁰ K) := rfl

/-- The Artin symbol of the zero fractional ideal is trivial. -/
lemma artinSymFrac_zero (hcomm : ∀ a b : Gal(L/K), a * b = b * a) :
    NK.CFTLib.Arl.artinSym hcomm (0 : FractionalIdeal (𝓞 K)⁰ K) = 1 := by
  letI := NK.CFTLib.Arl.galCommMonoid hcomm
  unfold NK.CFTLib.Arl.artinSym
  rw [show NK.CFTLib.Arl.exps (0 : FractionalIdeal (𝓞 K)⁰ K) = 0 by
    ext 𝔭
    rw [NK.CFTLib.Arl.exps_apply, FractionalIdeal.count_zero, Finsupp.zero_apply]]
  exact Finsupp.prod_zero_index

/-- The Artin symbol is multiplicative in the exponent. -/
lemma artinSymFrac_pow (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    {A : FractionalIdeal (𝓞 K)⁰ K} (hA : A ≠ 0) (n : ℕ) :
    NK.CFTLib.Arl.artinSym hcomm (A ^ n) = NK.CFTLib.Arl.artinSym hcomm A ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact NK.CFTLib.Arl.artinSym_one hcomm
  | succ n ih =>
      rw [pow_succ, NK.CFTLib.Arl.artinSym_mul hcomm (pow_ne_zero n hA) hA, ih, pow_succ]

/-- **The Artin symbol kills the relative norm of an ideal coprime to `(m)`.**  If every prime
occurring in the ideal `I` of `𝓞 L` (equivalently, every prime of `L` dividing `(m)`) is coprime
to `(m)`, then the Artin symbol of the norm `N_{L/K} I` is trivial.  The induction is over the
factorisation of `I`; at a prime `𝔓` one computes `N 𝔓 = 𝔭^{f(𝔓|𝔭)}` and uses that the Frobenius
at an unramified `𝔭` has order `f(𝔓|𝔭)`. -/
lemma artinSymFrac_relNorm_eq_one (hcomm : ∀ a b : Gal(L/K), a * b = b * a) (m : ℕ)
    (hram : ∀ p : NK.Chebotarev.PrimeIdeal K,
      ¬ IsUnramified (K := K) (L := L) p → (m : 𝓞 K) ∈ p.asIdeal)
    (I : Ideal (𝓞 L))
    (hcop : ∀ 𝔮 : HeightOneSpectrum (𝓞 L), (m : 𝓞 L) ∈ 𝔮.asIdeal →
      FractionalIdeal.count L 𝔮 (I : FractionalIdeal (𝓞 L)⁰ L) = 0) :
    NK.CFTLib.Arl.artinSym hcomm
      ((Ideal.relNorm (𝓞 K) I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = 1 := by
  classical
  refine (UniqueFactorizationMonoid.induction_on_prime (P := fun I : Ideal (𝓞 L) =>
    (∀ 𝔮 : HeightOneSpectrum (𝓞 L), (m : 𝓞 L) ∈ 𝔮.asIdeal →
      FractionalIdeal.count L 𝔮 (I : FractionalIdeal (𝓞 L)⁰ L) = 0) →
    NK.CFTLib.Arl.artinSym hcomm
      ((Ideal.relNorm (𝓞 K) I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = 1) I ?_ ?_ ?_) hcop
  · intro _
    rw [Ideal.zero_eq_bot, Ideal.relNorm_bot, FractionalIdeal.coeIdeal_bot]
    exact artinSymFrac_zero hcomm
  · intro x hx _
    rw [Ideal.isUnit_iff.mp hx, Ideal.relNorm_top, FractionalIdeal.coeIdeal_top]
    exact NK.CFTLib.Arl.artinSym_one hcomm
  · intro a p ha hpprime iha hcop'
    have ha_bot : a ≠ ⊥ := fun h => ha (h.trans Ideal.zero_eq_bot.symm)
    have hp0 : p ≠ ⊥ := fun h => hpprime.ne_zero (h.trans Ideal.zero_eq_bot.symm)
    have hpIsPrime : p.IsPrime := (Ideal.prime_iff_isPrime hp0).mp hpprime
    let 𝔭 : HeightOneSpectrum (𝓞 L) := ⟨p, hpIsPrime, hp0⟩
    have h𝔭 : 𝔭.asIdeal = p := rfl
    have hmul_qa : ∀ 𝔮 : HeightOneSpectrum (𝓞 L), FractionalIdeal.count L 𝔮
        (((p * a : Ideal (𝓞 L)) : FractionalIdeal (𝓞 L)⁰ L))
        = FractionalIdeal.count L 𝔮 ((p : Ideal (𝓞 L)) : FractionalIdeal (𝓞 L)⁰ L)
          + FractionalIdeal.count L 𝔮 ((a : Ideal (𝓞 L)) : FractionalIdeal (𝓞 L)⁰ L) := by
      intro 𝔮
      rw [FractionalIdeal.coeIdeal_mul, FractionalIdeal.count_mul L 𝔮
        (FractionalIdeal.coeIdeal_ne_zero.mpr hp0) (FractionalIdeal.coeIdeal_ne_zero.mpr ha_bot)]
    have hcop_a : ∀ 𝔮 : HeightOneSpectrum (𝓞 L), (m : 𝓞 L) ∈ 𝔮.asIdeal →
        FractionalIdeal.count L 𝔮 (a : FractionalIdeal (𝓞 L)⁰ L) = 0 := by
      intro 𝔮 hmem
      have h1 := hcop' 𝔮 hmem
      have h2 := hmul_qa 𝔮
      have h3 := FractionalIdeal.count_coe_nonneg L 𝔮 p
      have h4 := FractionalIdeal.count_coe_nonneg L 𝔮 a
      linarith
    have hpm : (m : 𝓞 L) ∉ p := by
      intro hmem
      have h1 := hcop' 𝔭 (by rwa [h𝔭])
      have h2 := hmul_qa 𝔭
      have h3 : FractionalIdeal.count L 𝔭 ((p : Ideal (𝓞 L)) : FractionalIdeal (𝓞 L)⁰ L) = 1 := by
        rw [← h𝔭]
        exact FractionalIdeal.count_self L 𝔭
      have h4 := FractionalIdeal.count_coe_nonneg L 𝔭 a
      linarith
    have hnp : ((Ideal.relNorm (𝓞 K) p : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.mpr (fun h => hp0 ((Ideal.relNorm_eq_bot_iff).mp h))
    have hna : ((Ideal.relNorm (𝓞 K) a : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.mpr (fun h => ha_bot ((Ideal.relNorm_eq_bot_iff).mp h))
    rw [map_mul (Ideal.relNorm (𝓞 K)) p a, FractionalIdeal.coeIdeal_mul,
        NK.CFTLib.Arl.artinSym_mul hcomm hnp hna, iha hcop_a, mul_one]
    haveI : p.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hp0 hpIsPrime
    let q : Ideal (𝓞 K) := p.under (𝓞 K)
    haveI : p.LiesOver q := ⟨rfl⟩
    have hq_ne : q ≠ ⊥ := Ideal.under_ne_bot (𝓞 K) hp0
    have hq_prime : q.IsPrime := inferInstance
    haveI : q.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hq_ne hq_prime
    have hrelNorm : Ideal.relNorm (𝓞 K) p = q ^ p.inertiaDeg (𝓞 K) :=
      Ideal.relNorm_eq_pow_of_isMaximal p q
    have hunr : IsUnramified (K := K) (L := L) ⟨q, hq_prime, hq_ne⟩ := by
      by_contra hcon
      have hmq : (m : 𝓞 K) ∈ q := hram ⟨q, hq_prime, hq_ne⟩ hcon
      have hmp : (m : 𝓞 L) ∈ p := by
        have h := (Ideal.mem_under (𝓞 K) p).mp hmq
        simpa using h
      exact hpm hmp
    rw [hrelNorm, FractionalIdeal.coeIdeal_pow,
      artinSymFrac_pow hcomm (FractionalIdeal.coeIdeal_ne_zero.mpr hq_ne) (p.inertiaDeg (𝓞 K)),
      NK.CFTLib.Arl.artinSym_prime hcomm ⟨q, hq_prime, hq_ne⟩,
      ← orderOf_dvd_iff_pow_eq_one,
      orderOf_frobAtPrime_eq_inertiaDeg (K := K) (L := L) ⟨q, hq_prime, hq_ne⟩
        ⟨p, hpIsPrime, hp0⟩ (show p.LiesOver q from ⟨rfl⟩) hunr]

theorem normRayLeKer (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative (Gal(L/K))] (m : ℕ) (hm : 0 < m)
    (hram : ∀ p : NK.Chebotarev.PrimeIdeal K,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p →
      (m : NumberField.RingOfIntegers K) ∈ p.asIdeal) :
    ∀ A ∈ NK.CFTLib.ArtinReciprocityIdeal.normRay K L m,
      NK.CFTLib.Arl.artinSym (K := K) (L := L)
        (fun a b : Gal(L/K) => IsMulCommutative.is_comm.comm a b) A = 1 := by
  intro A hA
  let hcomm : ∀ a b : Gal(L/K), a * b = b * a := fun a b => IsMulCommutative.is_comm.comm a b
  let f : Frac K →* Gal(L/K) := artinSymFracHom hcomm
  have hle : normRay K L m ≤ f.ker := by
    rw [show normRay K L m = Subgroup.closure {A : Frac K |
        ∃ (I : Ideal (𝓞 L)) (hI : I ≠ ⊥),
          FracCoprime (K := L) m (idealUnit I hI) ∧
          A = idealUnit (Ideal.relNorm (𝓞 K) I)
                (fun h => hI ((Ideal.relNorm_eq_bot_iff).mp h))} from rfl]
    rw [Subgroup.closure_le]
    rintro A ⟨I, hI, hcop, rfl⟩
    show NK.CFTLib.Arl.artinSym hcomm
      ((Ideal.relNorm (𝓞 K) I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = 1
    exact artinSymFrac_relNorm_eq_one hcomm m hram I (fun 𝔮 hmem => hcop 𝔮 hmem)
  exact hle hA

end NK.CFTLib.ArtinReciprocityIdeal
