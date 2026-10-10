import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Submission.NK.NUV2.ARL.abelianWeakToStrong
import Submission.Work.SSGRoute.ZDataMup.CyclicCaseStatement
import Submission.Work.SSGRoute.ZDataMup.exists_isCyclic_fixingSubgroup_notMem
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The abelian case of the conductor drop from the cyclic case

For a finite **abelian** Galois extension `L/K` of number fields, a modulus `M > 0` whose prime
divisors are unramified in `L` (`hramM`) and for which the ideal-theoretic reciprocity law holds
(`hprincM`), and `b ∈ Kˣ` congruent to `1` modulo `M` at every ramified prime dividing `M`
(`hcong`) and totally positive (`hpos`), the Artin symbol of the principal ideal `(b)` is trivial.

The proof is the classical reduction of the abelian case to the cyclic one
(Lang, *Algebraic Number Theory*, Ch. X, Theorem 3):

* a nontrivial element of a finite abelian group is separated by a cyclic quotient; in field
  terms, `Work.SSGRoute.ZDataMup.exists_isCyclic_fixingSubgroup_notMem` produces a cyclic
  intermediate field `M` with `σ ∉ Gal(L/M)`;
* for such a cyclic `M/K` the hypothesis `h : CyclicCaseStatement` gives
  `artinSym_{M/K} (b·𝒪_M) = 1`;
* restricting `artinSym_{L/K} (b·𝒪_K)` to `M` gives `artinSym_{M/K} (b·𝒪_M)`, so `σ ∈ Gal(L/M)`:
  contradiction.

The restriction step needs the primes dividing `(b)` to be unramified in `L`, which is exactly
what `hcong` provides: at a ramified prime `𝔮 | (M)`, the congruence `b ≡ 1 mod 𝔮^{v_𝔮(M)}`
forces `b` to be a `𝔮`-adic unit, so `𝔮 ∤ (b)`.

The three all-important hypothesis transfers to the cyclic subextension `M/K` are
`NK.NUV2.ARL.ramificationIdxIn_eq_one_of_intermediateField` (unramifiedness descends),
`NK.NUV2.ARL.artinKillsPrincipal_of_intermediateField` (the reciprocity law descends to normal
subextensions) and the divisor relation `e(M/K) ∣ e(L/K)` for the congruence condition.
-/

namespace Work.SSGRoute.ZDataMup

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-- **The support of a principal ideal `(b)` avoids the ramified primes.**  Under the congruence
hypothesis `hcong` at the ramified primes dividing `(M)` and `hramM`, every prime `𝔮` ramified in
`L` is a `𝔮`-adic unit-divisor of `b`, i.e. `count K 𝔮 (b) = 0`.

The proof is local: at a ramified `𝔮` the modulus satisfies `(M : 𝓞 K) ∈ 𝔮`, so `hcong` gives
`v_𝔮(b - 1) ≤ v_𝔮(M) < 1`; hence `v_𝔮(b) = v_𝔮(1 + (b-1)) = v_𝔮(1) = 1`, i.e. `b` is a `𝔮`-adic
unit.  The `𝔮`-adic exponent of the principal fractional ideal `(b)` is the negative of
`log v_𝔮(b)` (`NK.GlobalCFT.IdeleClassGroup.count_spanSingleton_eq`). -/
theorem count_spanSingleton_eq_zero_of_ramified
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (M : ℕ)
    (hramM : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (M : NumberField.RingOfIntegers K) ∉ 𝔭.asIdeal →
      Ideal.ramificationIdxIn 𝔭.asIdeal (NumberField.RingOfIntegers L) = 1)
    (b : Kˣ)
    (hcong : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (M : NumberField.RingOfIntegers K) ∈ 𝔮.asIdeal →
      Ideal.ramificationIdxIn 𝔮.asIdeal (NumberField.RingOfIntegers L) ≠ 1 →
      Valued.v (algebraMap K (𝔮.adicCompletion K) ((b : Kˣ) : K) - 1)
        ≤ Valued.v ((M : ℕ) : 𝔮.adicCompletion K))
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hram : Ideal.ramificationIdxIn 𝔮.asIdeal (NumberField.RingOfIntegers L) ≠ 1) :
    FractionalIdeal.count K 𝔮
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
        ((b : Kˣ) : K)) = 0 := by
  -- a prime ramified in `L` divides `(M)`, by contraposition of `hramM`
  have hmem : (M : 𝓞 K) ∈ 𝔮.asIdeal := by
    by_contra h
    exact hram (hramM 𝔮 h)
  -- the congruence, transported to the global `𝔮`-adic valuation of `K`
  have hcongK : 𝔮.valuation K ((b : K) - 1) ≤ 𝔮.intValuation (M : 𝓞 K) := by
    have h1 := hcong 𝔮 hmem hram
    rw [← show algebraMap K (𝔮.adicCompletion K) ((b : K) - 1)
        = algebraMap K (𝔮.adicCompletion K) ((b : K)) - 1 by rw [map_sub, map_one]] at h1
    rw [Commons.NumberTheory.NumberField.Completion.valued_alg_eq 𝔮 ((b : K) - 1)] at h1
    rw [show ((M : ℕ) : 𝔮.adicCompletion K)
        = algebraMap K (𝔮.adicCompletion K) ((M : ℕ) : K) from (map_natCast _ M).symm,
      Commons.NumberTheory.NumberField.Completion.valued_alg_eq 𝔮 ((M : ℕ) : K),
      show ((M : ℕ) : K) = algebraMap (𝓞 K) K ((M : ℕ) : 𝓞 K) from (map_natCast _ M).symm,
      HeightOneSpectrum.valuation_of_algebraMap] at h1
    exact h1
  -- hence `b` is a `𝔮`-adic unit
  have hb : 𝔮.valuation K ((b : K)) = 1 := by
    have hlt : 𝔮.valuation K ((b : K) - 1) < 𝔮.valuation K (1 : K) := by
      rw [map_one]
      exact lt_of_le_of_lt hcongK
        ((HeightOneSpectrum.intValuation_lt_one_iff_mem 𝔮 (M : 𝓞 K)).mpr hmem)
    have h := Valuation.map_add_eq_of_lt_left (v := 𝔮.valuation K) (x := (1 : K))
      (y := (b : K) - 1) hlt
    rwa [map_one, show (1 : K) + ((b : K) - 1) = ((b : K)) by ring] at h
  -- and the `𝔮`-adic exponent of `(b)` is `- log v_𝔮(b) = 0`
  rw [NK.GlobalCFT.IdeleClassGroup.count_spanSingleton_eq 𝔮 (Units.ne_zero b), hb,
    WithZero.log_one, neg_zero]

/-- **Unramifiedness of the support is inherited by the cyclic subextension**: if `𝔭` is unramified
in `L`, it is unramified in `M` (contrapositive of
`NK.NUV2.ARL.ramificationIdxIn_eq_one_of_intermediateField`). -/
theorem ramificationIdxIn_ne_one_of_intermediateField
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (M : IntermediateField K L) [FiniteDimensional K M] [NumberField ↥M] [IsGalois K ↥M]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (h : Ideal.ramificationIdxIn 𝔭.asIdeal (NumberField.RingOfIntegers ↥M) ≠ 1) :
    Ideal.ramificationIdxIn 𝔭.asIdeal (NumberField.RingOfIntegers L) ≠ 1 :=
  fun h1 => h (NK.NUV2.ARL.ramificationIdxIn_eq_one_of_intermediateField (K := K) (L := L) M 𝔭 h1)

/-- **Restriction of the ideal-theoretic Artin symbol to a normal intermediate field.**  For
`K ⊆ M ⊆ L` with `L/K` finite Galois and `M/K` finite Galois, and a fractional ideal `A` of `K` all
of whose prime divisors are unramified in `L`, the restriction to `Gal(M/K)` of the Artin symbol
`artinSym A ∈ Gal(L/K)` is the Artin symbol of `A` in `Gal(M/K)`.

This is the prime-by-prime compatibility `(Frob_𝔭)|_M = Frob_𝔭` of the chosen Frobenius elements:
`artinSym` is the product over the support of `A` of `Frob_𝔭 ^ (count 𝔭 A)`, and at each prime in
the support both sides are Frobenius elements at `𝔭` in the extension `M/K`, hence equal by
uniqueness of the Frobenius in the abelian extension `M/K`. -/
theorem artinSym_restrictNormalHom_of_unramifiedSupport
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (M : IntermediateField K L) [FiniteDimensional K M] [NumberField ↥M] [IsGalois K ↥M]
    (hcommM : ∀ a b : Gal(↥M/K), a * b = b * a)
    (A : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    (hunr : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), FractionalIdeal.count K 𝔭 A ≠ 0 →
      Ideal.ramificationIdxIn 𝔭.asIdeal (𝓞 L) = 1) :
    AlgEquiv.restrictNormalHom (F := K) (K₁ := L) M
        (NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm A)
      = NK.CFTLib.Arl.artinSym (K := K) (L := ↥M) hcommM A := by
  classical
  -- the restriction of the Frobenius element of `L/K` at an unramified `𝔭` is the Frobenius
  -- element of `M/K` at `𝔭`
  have hfrob : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), Ideal.ramificationIdxIn 𝔭.asIdeal (𝓞 L) = 1 →
      AlgEquiv.restrictNormalHom (F := K) (K₁ := L) M
          (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭)
        = NK.Chebotarev.frobAtPrime (K := K) (L := ↥M) 𝔭 := by
    intro 𝔭 h𝔭
    -- unramifiedness of `𝔭` in `L`, in the prime-by-prime form
    have hunrL : ∀ P : NK.Chebotarev.PrimeIdeal L, P.asIdeal.LiesOver 𝔭.asIdeal →
        P.asIdeal.ramificationIdx (𝓞 K) = 1 := by
      intro P hP
      rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (A := 𝓞 K) (B := 𝓞 L)
        𝔭.asIdeal P.asIdeal (Gal(L/K))]
      exact h𝔭
    -- ... hence also in `M`, by multiplicativity of the ramification index in a tower
    have hunrM : ∀ Q : NK.Chebotarev.PrimeIdeal ↥M, Q.asIdeal.LiesOver 𝔭.asIdeal →
        Q.asIdeal.ramificationIdx (𝓞 K) = 1 := by
      intro Q hQ
      haveI : IsScalarTower (𝓞 K) (𝓞 ↥M) (𝓞 L) := inferInstance
      haveI : Module.Flat (𝓞 ↥M) (𝓞 L) := inferInstance
      obtain ⟨P, hP⟩ :=
        Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := ↥M) (L := L) Q
      haveI : P.asIdeal.LiesOver Q.asIdeal := hP
      have hPQ : P.asIdeal.LiesOver 𝔭.asIdeal :=
        Ideal.LiesOver.trans P.asIdeal Q.asIdeal 𝔭.asIdeal
      haveI := hPQ
      have htw := Ideal.ramificationIdx_tower (R := 𝓞 K) (S := 𝓞 ↥M) (T := 𝓞 L)
        Q.asIdeal P.asIdeal
      rw [hunrL P hPQ] at htw
      exact Nat.eq_one_of_mul_eq_one_right htw.symm
    -- both sides are Frobenius elements at `𝔭` in `M/K`, where the Frobenius is unique
    have h1 : NK.Chebotarev.IsFrobAtPrime (K := K) (L := ↥M) 𝔭
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) M
          (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭)) := by
      obtain ⟨P, hP, hPfrob⟩ :=
        NK.Chebotarev.isFrobAtPrime_frobAtPrime (K := K) (L := L) hcomm 𝔭 hunrL
      refine ⟨P.under (𝓞 ↥M), ?_, ?_⟩
      · refine ⟨?_⟩
        rw [NK.Chebotarev.under_asIdeal M P, Ideal.under_under]
        exact hP.over
      · exact NK.Chebotarev.IsFrobAtRestrictNormalHom (M := L) M hP hPfrob
    have h2 : NK.Chebotarev.IsFrobAtPrime (K := K) (L := ↥M) 𝔭
        (NK.Chebotarev.frobAtPrime (K := K) (L := ↥M) 𝔭) :=
      NK.Chebotarev.isFrobAtPrime_frobAtPrime (K := K) (L := ↥M) hcommM 𝔭 hunrM
    exact (NK.Chebotarev.ExistsUniqueIsFrobAtPrime (K := K) (L := ↥M) hcommM 𝔭 hunrM).unique
      h1 h2
  -- unfold the two Artin symbols as products over the support of `A`
  letI := NK.CFTLib.Arl.galCommMonoid hcomm
  letI := NK.CFTLib.Arl.galCommMonoid hcommM
  have hL : NK.CFTLib.Arl.artinSym hcomm A =
      ∏ 𝔭 ∈ (NK.CFTLib.Arl.exps A).support,
        (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) ^ ((NK.CFTLib.Arl.exps A) 𝔭) := by
    unfold NK.CFTLib.Arl.artinSym
    exact Finsupp.prod_of_support_subset (NK.CFTLib.Arl.exps A) le_rfl _
      (fun i _ => zpow_zero _)
  have hR : NK.CFTLib.Arl.artinSym hcommM A =
      ∏ 𝔭 ∈ (NK.CFTLib.Arl.exps A).support,
        (NK.Chebotarev.frobAtPrime (K := K) (L := ↥M) 𝔭) ^ ((NK.CFTLib.Arl.exps A) 𝔭) := by
    unfold NK.CFTLib.Arl.artinSym
    exact Finsupp.prod_of_support_subset (NK.CFTLib.Arl.exps A) le_rfl _
      (fun i _ => zpow_zero _)
  rw [hL, hR, map_prod]
  refine Finset.prod_congr rfl (fun 𝔭 h𝔭 => ?_)
  have hne : (NK.CFTLib.Arl.exps A) 𝔭 ≠ 0 := Finsupp.mem_support_iff.mp h𝔭
  have hm𝔭 : Ideal.ramificationIdxIn 𝔭.asIdeal (𝓞 L) = 1 :=
    hunr 𝔭 (by rwa [NK.CFTLib.Arl.exps_apply] at hne)
  rw [map_zpow, hfrob 𝔭 hm𝔭]

theorem abelian_of_cyclicCase (h : CyclicCaseStatement)
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (M : ℕ) (hM : 0 < M)
    (hramM : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (M : NumberField.RingOfIntegers K) ∉ 𝔭.asIdeal →
      Ideal.ramificationIdxIn 𝔭.asIdeal (NumberField.RingOfIntegers L) = 1)
    (hprincM : NK.CFTLib.artinKillsPrincipal K L M)
    (b : Kˣ)
    (hcong : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (M : NumberField.RingOfIntegers K) ∈ 𝔮.asIdeal →
      Ideal.ramificationIdxIn 𝔮.asIdeal (NumberField.RingOfIntegers L) ≠ 1 →
      Valued.v (algebraMap K (𝔮.adicCompletion K) ((b : Kˣ) : K) - 1)
        ≤ Valued.v ((M : ℕ) : 𝔮.adicCompletion K))
    (hpos : ∀ (w : NumberField.InfinitePlace K) (hw : w.IsReal),
      0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
            (algebraMap K w.Completion ((b : Kˣ) : K))) :
    NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
        ((b : Kˣ) : K)) = 1 := by
  classical
  -- `Gal(L/K)` is commutative, so `L/K` is an abelian (hence in particular Galois) extension
  haveI : IsMulCommutative Gal(L/K) := IsMulCommutative.of_comm hcomm
  haveI : IsAbelianGalois K L := {}
  set A : FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
    FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) ((b : Kˣ) : K) with hA
  by_contra hx
  -- a nontrivial element of the abelian Galois group is separated by a cyclic subextension
  obtain ⟨Mf, hMcyc, hMnot⟩ := exists_isCyclic_fixingSubgroup_notMem (K := K) (L := L) hcomm
    (NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm A) hx
  haveI : IsCyclic Gal(↥Mf/K) := hMcyc
  haveI : IsGalois K ↥Mf := inferInstance
  haveI : Normal K ↥Mf := inferInstance
  haveI : FiniteDimensional K ↥Mf := inferInstance
  haveI : NumberField ↥Mf := inferInstance
  have hcommMf : ∀ a b : Gal(↥Mf/K), a * b = b * a := fun a b => mul_comm' a b
  -- ## the hypotheses of the cyclic case for `Mf/K`
  have hramMf : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (M : 𝓞 K) ∉ 𝔭.asIdeal →
      Ideal.ramificationIdxIn 𝔭.asIdeal (𝓞 ↥Mf) = 1 :=
    fun 𝔭 h𝔭 => NK.NUV2.ARL.ramificationIdxIn_eq_one_of_intermediateField (K := K) (L := L)
      Mf 𝔭 (hramM 𝔭 h𝔭)
  have hprincMf : NK.CFTLib.artinKillsPrincipal K ↥Mf M :=
    NK.NUV2.ARL.artinKillsPrincipal_of_intermediateField (K := K) (L := L) Mf hramM hprincM
  have hcongMf : ∀ 𝔮 : HeightOneSpectrum (𝓞 K), (M : 𝓞 K) ∈ 𝔮.asIdeal →
      Ideal.ramificationIdxIn 𝔮.asIdeal (𝓞 ↥Mf) ≠ 1 →
      Valued.v (algebraMap K (𝔮.adicCompletion K) ((b : Kˣ) : K) - 1)
        ≤ Valued.v ((M : ℕ) : 𝔮.adicCompletion K) :=
    fun 𝔮 h𝔮 hram => hcong 𝔮 h𝔮
      (ramificationIdxIn_ne_one_of_intermediateField (K := K) (L := L) Mf 𝔮 hram)
  -- the cyclic case
  have hcyc : NK.CFTLib.Arl.artinSym (K := K) (L := ↥Mf) hcommMf A = 1 :=
    h (K := K) (L := ↥Mf) (hcomm := hcommMf) M hM hramMf hprincMf b hcongMf hpos
  -- ## the primes dividing `(b)` are unramified in `L`
  have hunr : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), FractionalIdeal.count K 𝔭 A ≠ 0 →
      Ideal.ramificationIdxIn 𝔭.asIdeal (𝓞 L) = 1 := by
    intro 𝔭 hc
    by_contra hram
    exact hc (hA ▸ count_spanSingleton_eq_zero_of_ramified (K := K) (L := L) M hramM b hcong 𝔭 hram)
  -- ## restriction of the Artin symbol to the cyclic subextension
  have hres : AlgEquiv.restrictNormalHom (F := K) (K₁ := L) Mf
      (NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm A)
      = NK.CFTLib.Arl.artinSym (K := K) (L := ↥Mf) hcommMf A :=
    artinSym_restrictNormalHom_of_unramifiedSupport (K := K) (L := L) hcomm Mf hcommMf A hunr
  rw [hcyc] at hres
  exact hMnot (by
    rw [← IntermediateField.restrictNormalHom_ker Mf]
    exact MonoidHom.mem_ker.mpr hres)

end Work.SSGRoute.ZDataMup
