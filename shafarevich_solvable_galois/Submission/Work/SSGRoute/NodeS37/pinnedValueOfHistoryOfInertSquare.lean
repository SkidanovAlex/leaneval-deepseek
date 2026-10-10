import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Int.Star
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.SSGRoute.NodeS37.evenCountAtNonEscapePrime
import Submission.Work.SSGRoute.NodeS37.killsLocalGroupAtSBlockConj
import Submission.Work.SSGRoute.P2Close.isSquare_of_mul_aut_eq_one
import Submission.Work.SSGRoute.P2Close.unitSquare
import Submission.Work.SSGRoute.PinnedTwin.coprimeRepresentative
import Submission.Work.SSGRoute.PinnedTwin.divisorRepresentative
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.antiInvariantPairingAux
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.oPairAt_sum_attach_eq_zero_of_kills
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.NodeS37

/-!
# The p. 16 diagonal value, with the inert squareness taken as an input

`pinnedValueOfHistoryOfInertSquare` is the arithmetic core of the `p = 2` recursion (see
`NOTE_pinnedValueOfHistoryOfInertSquare_design.md`): the pinned value of the stage class `b_m`
at the sibling of its own escape prime vanishes, for every involution `ρ ≠ 1`.  The one local
input which the statement leaves as a hypothesis is `hinert` (= the statement of
`Work.SSGRoute.NodeS37.inertSquareOfRhoFixed`, proved in the sibling module).

The two genuinely arithmetic pieces consumed by the assembly are recorded above the target:

* `divisorRepresentativeCoprime` — the Čebotarev representative `z = b·y²` with `div z = 𝔮·Q'²`,
  `Q' ≠ ρQ'`, `Q' ≠ ρ𝔮` and the coprimality `supp z ∩ supp (ρz) = ∅` (all ingredients are proved on
  disk: `exists_prime_in_class_not_fixed`, `count_mul_sq_of_classRepresentative`,
  `coprimeOfPrimeRepresentative`);
* `oPairAt_inertPrime_eq_zero` — the inert case of the dichotomy at a place laying over a
  `ρ`-fixed prime (the variant of the proved `PinnedTwin.oPairAtInvariantUnitAnti` in which the
  hypothesis `galLift K ρ • B = B` is weakened to `gesKConj K (galLift K ρ • B) B`).
-/

/-- **The representative normalisation of Schmidt--Wingberg p. 16** (Čebotarev + divisor
arithmetic): from `div(b) = 𝔮·A²` (odd at `𝔮`, even elsewhere) and `ρ𝔮 ≠ 𝔮`, produce `z = b·y²`
whose divisor is `𝔮·Q'²` with `Q' ≠ ρQ'`, `Q' ≠ ρ𝔮`, and whose support is disjoint from its
`ρ`-conjugate and misses `ρ𝔮`. -/
theorem divisorRepresentativeCoprime {k K : Type} [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (ρ : K ≃ₐ[k] K) (hρ2 : ρ ^ 2 = 1) (b : Kˣ)
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (heven : ∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K), P ≠ 𝔮 →
      Even (FractionalIdeal.count K P (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers K)) (b : K))))
    (hodd : Odd (FractionalIdeal.count K 𝔮 (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers K)) (b : K))))
    (hne : Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮 ≠ 𝔮) :
    ∃ z y : Kˣ, z = b * y ^ 2 ∧
      ∃ Q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        Commons.NumberTheory.NumberField.Completion.placeSmul ρ Q' ≠ Q' ∧
        Q' ≠ Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮 ∧
        (∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
          FractionalIdeal.count K P (FractionalIdeal.spanSingleton
            (nonZeroDivisors (NumberField.RingOfIntegers K)) (z : K))
            = FractionalIdeal.count K P
                ((𝔮.asIdeal : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K))
              + 2 * FractionalIdeal.count K P
                ((Q'.asIdeal : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K))) ∧
        (∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
          FractionalIdeal.count K P (FractionalIdeal.spanSingleton
            (nonZeroDivisors (NumberField.RingOfIntegers K)) (z : K)) ≠ 0 →
          FractionalIdeal.count K
            (Commons.NumberTheory.NumberField.Completion.placeSmul ρ P)
            (FractionalIdeal.spanSingleton
              (nonZeroDivisors (NumberField.RingOfIntegers K)) (z : K)) = 0) ∧
        FractionalIdeal.count K
          (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮)
          (FractionalIdeal.spanSingleton
            (nonZeroDivisors (NumberField.RingOfIntegers K)) (z : K)) = 0 := by
  classical
  -- the square root of the divisor of `b`
  obtain ⟨A, hA, hb⟩ :=
    Work.SSGRoute.ZDataTwo.TwoRec.exists_fractionalIdeal_count_eq (K := K) b 𝔮 heven hodd
  -- a Čebotarev prime in the class of `A`, not fixed by `ρ` and not `ρ𝔮`
  obtain ⟨Q', y, hQ', hQ'𝔮, hyA⟩ :=
    Work.SSGRoute.ZDataTwo.TwoRec.exists_prime_in_class_not_fixed (k := k) (K := K)
      ρ hρ2 A hA 𝔮 hne
  -- its count form
  have hy : ∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      FractionalIdeal.count K P A
        + FractionalIdeal.count K P (FractionalIdeal.spanSingleton
            (nonZeroDivisors (NumberField.RingOfIntegers K)) (y : K))
      = (if P = Q' then 1 else 0) :=
    Work.SSGRoute.PinnedTwin.count_eq_of_asIdeal_eq_mul (K := K) A hA Q' y hyA
  -- the divisor of `z = b y²` is `𝔮 · Q'²`
  have hcount : ∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      FractionalIdeal.count K P (FractionalIdeal.spanSingleton
          (nonZeroDivisors (NumberField.RingOfIntegers K)) (((b * y ^ 2 : Kˣ)) : K))
      = (if P = 𝔮 then 1 else 0) + 2 * (if P = Q' then 1 else 0) :=
    Work.SSGRoute.NodeS37.count_mul_sq_of_classRepresentative (K := K) 𝔮 Q' A b y hb hy
  -- and the coprimality
  have hcop := Work.SSGRoute.NodeS37.coprimeOfPrimeRepresentative (k := k) (L := K)
    ρ hρ2 b y 𝔮 Q' A hb hy hQ' hne hQ'𝔮
  refine ⟨b * y ^ 2, y, rfl, Q', hQ', hQ'𝔮, ?_, hcop.1, hcop.2⟩
  intro P
  rw [hcount P]
  have h1 : FractionalIdeal.count K P
      ((𝔮.asIdeal : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K))
      = (if P = 𝔮 then 1 else 0) := by
    rw [FractionalIdeal.count_maximal (R := NumberField.RingOfIntegers K) (K := K) P 𝔮]
    by_cases h : P = 𝔮
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg fun hc => h hc.symm]
  have h2 : FractionalIdeal.count K P
      ((Q'.asIdeal : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K))
      = (if P = Q' then 1 else 0) := by
    rw [FractionalIdeal.count_maximal (R := NumberField.RingOfIntegers K) (K := K) P Q']
    by_cases h : P = Q'
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg fun hc => h hc.symm]
  rw [h1, h2]

open scoped Pointwise NumberField

/-! ## The inert case at a place over a `ρ`-fixed prime of `K`

`PinnedTwin.oPairAtInvariantUnitAnti` assumes that the *place* is fixed by `galLift K ρ`; the
p. 16 `Σ`-step needs only that the *prime* of `K` below it is fixed (there are primes over a
`ρ`-fixed prime with no `galLift K ρ`-fixed place above them).  The whole chain
(`residueInvolution` → `unitSquare_residue_square` → `unitSquare`) consumes the place-level
fixedness only through the prime-level invariance `placeSmul ρ 𝔭 = 𝔭`, so the two lemmas below are
copies of the existing ones with that substitution. -/

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

private lemma galRestrict_apply_eq_smul_pin {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] {K : IntermediateField k Ω} [NumberField ↥K] (ρ : K ≃ₐ[k] K)
    (y : NumberField.RingOfIntegers ↥K) :
    (galRestrict (NumberField.RingOfIntegers k) k ↥K (NumberField.RingOfIntegers ↥K) ρ) y =
      ρ • y := by
  apply NumberField.RingOfIntegers.coe_injective
  rw [algebraMap_galRestrict_apply, algebraMap.smul', AlgEquiv.smul_def]

private lemma rhoTilde_mk_pin {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    {K : IntermediateField k Ω} [NumberField ↥K] (ρ : K ≃ₐ[k] K)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (y : NumberField.RingOfIntegers ↥K) :
    Ideal.Quotient.mk 𝔭.asIdeal
        ((galRestrict (NumberField.RingOfIntegers k) k ↥K
          (NumberField.RingOfIntegers ↥K) ρ :
          NumberField.RingOfIntegers ↥K ≃+* NumberField.RingOfIntegers ↥K) y)
      = Ideal.Quotient.mk 𝔭.asIdeal (ρ • y) := by
  have hbridge : ((galRestrict (NumberField.RingOfIntegers k) k ↥K
        (NumberField.RingOfIntegers ↥K) ρ :
        NumberField.RingOfIntegers ↥K ≃+* NumberField.RingOfIntegers ↥K) y)
      = (galRestrict (NumberField.RingOfIntegers k) k ↥K
        (NumberField.RingOfIntegers ↥K) ρ) y := rfl
  rw [hbridge, galRestrict_apply_eq_smul_pin (K := K) ρ y]

/-- **The involution induced on the residue field by a `ρ`-invariant prime** (the prime-level
version of `P2Close.residueInvolution`). -/
private theorem residueInvolutionOfPrimeFix {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ρ : K ≃ₐ[k] K) (hρ2 : ρ ^ 2 = 1)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (hfix : Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔭 = 𝔭)
    (hnontriv : ∃ x₀ : NumberField.RingOfIntegers ↥K,
      ¬ (IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 (ρ (x₀ : ↥K) - (x₀ : ↥K)) < 1)) :
    ∃ σbar : ((NumberField.RingOfIntegers ↥K) ⧸ 𝔭.asIdeal) ≃+*
        ((NumberField.RingOfIntegers ↥K) ⧸ 𝔭.asIdeal),
      (∀ y : NumberField.RingOfIntegers ↥K,
        σbar (Ideal.Quotient.mk 𝔭.asIdeal y) =
          Ideal.Quotient.mk 𝔭.asIdeal (ρ • y)) ∧
      σbar ^ 2 = 1 ∧ σbar ≠ 1 := by
  classical
  have hmap : Ideal.map
      ((galRestrict (NumberField.RingOfIntegers k) k ↥K (NumberField.RingOfIntegers ↥K) ρ :
        NumberField.RingOfIntegers ↥K ≃+* NumberField.RingOfIntegers ↥K) :
        NumberField.RingOfIntegers ↥K →+* NumberField.RingOfIntegers ↥K) 𝔭.asIdeal =
      𝔭.asIdeal := by
    have hPS : (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔭).asIdeal =
        𝔭.asIdeal := by
      rw [hfix]
    exact (Commons.NumberTheory.NumberField.Completion.placeSmul_asIdeal ρ 𝔭).symm.trans hPS
  set σbar : ((NumberField.RingOfIntegers ↥K) ⧸ 𝔭.asIdeal) ≃+*
      ((NumberField.RingOfIntegers ↥K) ⧸ 𝔭.asIdeal) :=
    Ideal.quotientEquiv 𝔭.asIdeal 𝔭.asIdeal
      (galRestrict (NumberField.RingOfIntegers k) k ↥K (NumberField.RingOfIntegers ↥K) ρ :
        NumberField.RingOfIntegers ↥K ≃+* NumberField.RingOfIntegers ↥K) hmap.symm
    with hσbar
  have hprop : ∀ y : NumberField.RingOfIntegers ↥K,
      σbar (Ideal.Quotient.mk 𝔭.asIdeal y) = Ideal.Quotient.mk 𝔭.asIdeal (ρ • y) := by
    intro y
    rw [hσbar, Ideal.quotientEquiv_mk]
    exact rhoTilde_mk_pin (K := K) ρ 𝔭 y
  refine ⟨σbar, hprop, ?_, ?_⟩
  · ext z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [pow_two, RingAut.mul_apply, RingAut.one_apply, hprop y, hprop (ρ • y)]
    have hfixy : ρ • (ρ • y) = y := by
      rw [← mul_smul, ← pow_two, hρ2, one_smul]
    rw [hfixy]
  · intro h1
    obtain ⟨x₀, hx₀⟩ := hnontriv
    refine hx₀ ?_
    have hmem : ρ • x₀ - x₀ ∈ 𝔭.asIdeal := by
      have hx : Ideal.Quotient.mk 𝔭.asIdeal (ρ • x₀) =
          Ideal.Quotient.mk 𝔭.asIdeal x₀ := by
        rw [← hprop x₀, h1, RingAut.one_apply]
      have hzero : Ideal.Quotient.mk 𝔭.asIdeal (ρ • x₀ - x₀) = 0 := by
        rw [map_sub, hx, sub_self]
      exact Ideal.Quotient.eq_zero_iff_mem.mp hzero
    have hv : (IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭)
        ((algebraMap (NumberField.RingOfIntegers ↥K) ↥K) (ρ • x₀ - x₀)) < 1 :=
      (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := ↥K) 𝔭
        (ρ • x₀ - x₀)).mpr hmem
    have hconv : (algebraMap (NumberField.RingOfIntegers ↥K) ↥K) (ρ • x₀ - x₀)
        = ρ ((algebraMap (NumberField.RingOfIntegers ↥K) ↥K) x₀) -
          (algebraMap (NumberField.RingOfIntegers ↥K) ↥K) x₀ := by
      rw [map_sub, algebraMap.smul', AlgEquiv.smul_def]
    rw [hconv] at hv
    exact hv

/-- **The unit case of the p. 16 inert squareness at prime level**: the image of a unit `x` which
is `ρ`-invariant (or `ρ`-anti-invariant) in the `𝔭`-adic completion is a square, granted only that
the prime `𝔭` is `ρ`-fixed (`P2Close.unitSquare` assumes the stronger `galLift K ρ • A = A`). -/
private theorem unitSquareOfPrimeFix {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ρ : K ≃ₐ[k] K) (hρ2 : ρ ^ 2 = 1)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (h2 : ¬ A.valuation (2 : Ω) < 1)
    (hfix : Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔭 = 𝔭)
    (hnontriv : ∃ x₀ : NumberField.RingOfIntegers ↥K,
      ¬ (IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 (ρ (x₀ : ↥K) - (x₀ : ↥K)) < 1))
    (hFF : ∀ (E : Type) [Field E] [Fintype E] (σ : E ≃+* E), σ ^ 2 = 1 → σ ≠ 1 →
      ringChar E ≠ 2 → (∀ y : E, σ y = y → IsSquare y) ∧ (∀ y : E, y * σ y = 1 → IsSquare y))
    (x : (↥K)ˣ) (hunit : A.valuation (algebraMap ↥K Ω (x : ↥K)) = 1)
    (hconj : Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) x = x ∨
      Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) x = x⁻¹) :
    ∃ c : (𝔭.adicCompletion ↥K)ˣ,
      Units.map (algebraMap ↥K (𝔭.adicCompletion ↥K)).toMonoidHom x = c ^ 2 := by
  classical
  obtain ⟨r, hrval, hrsq⟩ : ∃ r : NumberField.RingOfIntegers ↥K,
      IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 ((x : ↥K) - (r : ↥K)) < 1 ∧
      IsSquare (Ideal.Quotient.mk 𝔭.asIdeal r) := by
    obtain ⟨σbar, hσbar_mk, hσbar2, hσbar1⟩ :=
      residueInvolutionOfPrimeFix ρ hρ2 𝔭 hfix hnontriv
    -- `2` is nonzero in the residue field (the place is odd)
    have h2val : ¬ (IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 (2 : ↥K)) < 1 := by
      intro h
      exact h2 (by
        rw [← map_ofNat (algebraMap ↥K Ω) 2]
        exact (Work.SSGRoute.ZDataTwo.TwoRec.place_valuation_lt_one_iff A 𝔭 h𝔭 (2 : ↥K)).mpr h)
    have htwo_ne : (2 : 𝓞 ↥K ⧸ 𝔭.asIdeal) ≠ 0 := by
      have hcast : ((2 : 𝓞 ↥K) : ↥K) = (2 : ↥K) := by
        first
          | rfl
          | exact map_ofNat (algebraMap (𝓞 ↥K) ↥K) 2
          | (rw [NumberField.RingOfIntegers.coe_eq_algebraMap, map_ofNat]; rfl)
          | (push_cast; ring)
          | (norm_num)
      have h2mem : ¬ (2 : 𝓞 ↥K) ∈ 𝔭.asIdeal := by
        intro hmem
        refine h2val ?_
        have h := (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := ↥K) 𝔭
          (2 : 𝓞 ↥K)).mpr hmem
        first
          | (simpa using h)
          | (simpa only [hcast] using h)
          | (rwa [hcast] at h)
          | (exact h.trans_le (le_of_eq hcast))
      intro hzero
      have hzero' : Ideal.Quotient.mk 𝔭.asIdeal (2 : 𝓞 ↥K) = 0 := by
        first
          | (rw [map_ofNat (Ideal.Quotient.mk 𝔭.asIdeal) 2]; exact hzero)
          | (rw [show (2 : 𝓞 ↥K ⧸ 𝔭.asIdeal) =
                Ideal.Quotient.mk 𝔭.asIdeal (2 : 𝓞 ↥K) from by
                  first | (rw [map_ofNat]) | rfl] at hzero
             exact hzero)
      exact h2mem (Ideal.Quotient.eq_zero_iff_mem.mp hzero')
    have hchar : ringChar (𝓞 ↥K ⧸ 𝔭.asIdeal) ≠ 2 := by
      intro hc
      haveI : CharP (𝓞 ↥K ⧸ 𝔭.asIdeal) 2 := ringChar.of_eq hc
      exact htwo_ne (CharP.cast_eq_zero _ 2)
    obtain ⟨hFFfix, hFFanti⟩ :=
      Work.SSGRoute.P2Close.unitSquare_hFF_apply 𝔭 σbar hσbar2 hσbar1 hchar hFF
    -- write `x = n / s` with `s` a unit at `𝔭`
    have hxle : IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 (x : ↥K) ≤ 1 :=
      (Work.SSGRoute.ZDataTwo.TwoRec.place_valuation_le_one_iff A 𝔭 h𝔭 (x : ↥K)).mp
        (le_of_eq hunit)
    obtain ⟨n, d, hnd⟩ :=
      IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (K := ↥K) 𝔭 (x : ↥K)
        hxle
    set s : 𝓞 ↥K := (d : 𝓞 ↥K) with hs_def
    have hs_notMem : s ∉ 𝔭.asIdeal := by
      rw [hs_def]
      exact Ideal.mem_primeCompl_iff.mp d.2
    have hndK : (x : ↥K) * (s : ↥K) = (n : ↥K) := by
      simpa [hs_def] using hnd
    have hs_ne : Ideal.Quotient.mk 𝔭.asIdeal s ≠ 0 := by
      intro h
      exact hs_notMem (Ideal.Quotient.eq_zero_iff_mem.mp h)
    obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv (I := 𝔭.asIdeal)
      (a := Ideal.Quotient.mk 𝔭.asIdeal s) hs_ne
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective b
    have hts : Ideal.Quotient.mk 𝔭.asIdeal t * Ideal.Quotient.mk 𝔭.asIdeal s = 1 := by
      rw [ht, mul_comm]
      exact hb
    have hst' : Ideal.Quotient.mk 𝔭.asIdeal s * Ideal.Quotient.mk 𝔭.asIdeal t = 1 := by
      rw [mul_comm, hts]
    set r : 𝓞 ↥K := n * t with hr_def
    have hrn : Ideal.Quotient.mk 𝔭.asIdeal r =
        Ideal.Quotient.mk 𝔭.asIdeal n * Ideal.Quotient.mk 𝔭.asIdeal t := by
      rw [hr_def, map_mul]
    have hrs : Ideal.Quotient.mk 𝔭.asIdeal r * Ideal.Quotient.mk 𝔭.asIdeal s =
        Ideal.Quotient.mk 𝔭.asIdeal n := by
      rw [hrn, mul_assoc, hts, mul_one]
    -- the action of `ρ` on `x`
    have hrho : ρ (x : ↥K) = (x : ↥K) ∨ ρ (x : ↥K) = ((x : ↥K))⁻¹ := by
      have hconj'' : Units.map ρ.toMonoidHom x = x ∨ Units.map ρ.toMonoidHom x = x⁻¹ := by
        have hmap : Units.map
              (AlgEquiv.restrictNormalHom K (Work.SSGRoute.ZDataMup.galLift K ρ)).toMonoidHom x =
            Units.map ρ.toMonoidHom x := by
          rw [Work.SSGRoute.ZDataMup.galLift_spec K ρ]
        rcases hconj with h | h
        · left
          unfold Work.SSGRoute.H9.conjUnit at h
          rwa [hmap] at h
        · right
          unfold Work.SSGRoute.H9.conjUnit at h
          rwa [hmap] at h
      rcases hconj'' with h | h
      · left
        have h' := congrArg (fun u : (↥K)ˣ => (u : ↥K)) h
        simpa [Units.coe_map] using h'
      · right
        have h' := congrArg (fun u : (↥K)ˣ => (u : ↥K)) h
        simpa [Units.coe_map] using h'
    -- the two algebraic relations between `n` and `s` coming from the invariance of `x`
    have hrel_inv_K : ρ (x : ↥K) = (x : ↥K) →
        ρ (n : ↥K) * (s : ↥K) = (n : ↥K) * ρ (s : ↥K) := by
      intro hx
      have hm : ρ (n : ↥K) = ρ (x : ↥K) * ρ (s : ↥K) := by rw [← hndK, map_mul]
      rw [hm, hx]
      linear_combination (ρ (s : ↥K)) * hndK
    have hrel_anti_K : ρ (x : ↥K) = ((x : ↥K))⁻¹ →
        ρ (n : ↥K) * (n : ↥K) = ρ (s : ↥K) * (s : ↥K) := by
      intro hx
      have hm : ρ (n : ↥K) = ρ (x : ↥K) * ρ (s : ↥K) := by rw [← hndK, map_mul]
      have hxx : ρ (x : ↥K) * (x : ↥K) = 1 := by
        rw [hx, inv_mul_cancel₀ (Units.ne_zero x)]
      have hndK' : (n : ↥K) = (x : ↥K) * (s : ↥K) := hndK.symm
      rw [hm]
      linear_combination (ρ (x : ↥K) * ρ (s : ↥K)) * hndK' +
        (ρ (s : ↥K) * (s : ↥K)) * hxx
    have hn : (algebraMap (𝓞 ↥K) ↥K) (ρ • n : 𝓞 ↥K) = ρ (n : ↥K) :=
      integralClosure.coe_smul ρ n
    have hs : (algebraMap (𝓞 ↥K) ↥K) (ρ • s : 𝓞 ↥K) = ρ (s : ↥K) :=
      integralClosure.coe_smul ρ s
    have hrel_inv : ρ (x : ↥K) = (x : ↥K) →
        (ρ • n : 𝓞 ↥K) * s = n * (ρ • s : 𝓞 ↥K) := by
      intro hx
      apply NumberField.RingOfIntegers.coe_injective
      rw [map_mul, map_mul, hn, hs]
      exact hrel_inv_K hx
    have hrel_anti : ρ (x : ↥K) = ((x : ↥K))⁻¹ →
        (ρ • n : 𝓞 ↥K) * n = (ρ • s : 𝓞 ↥K) * s := by
      intro hx
      apply NumberField.RingOfIntegers.coe_injective
      rw [map_mul, map_mul, hn, hs]
      exact hrel_anti_K hx
    have hρs_ne : Ideal.Quotient.mk 𝔭.asIdeal (ρ • s) ≠ 0 := by
      rw [← hσbar_mk s]
      exact fun h => hs_ne (σbar.injective (by rw [h, map_zero]))
    refine ⟨r, ?_, ?_⟩
    · -- the congruence `x ≡ r (mod 𝔭)`
      have hst : Ideal.Quotient.mk 𝔭.asIdeal (s * t) = 1 := by
        rw [map_mul, mul_comm, hts]
      have hmem : (s * t - 1 : 𝓞 ↥K) ∈ 𝔭.asIdeal := by
        have h0 : Ideal.Quotient.mk 𝔭.asIdeal (s * t - 1) = 0 := by
          rw [map_sub, hst, map_one, sub_self]
        exact Ideal.Quotient.eq_zero_iff_mem.mp h0
      have hcoe1 : (algebraMap (𝓞 ↥K) ↥K) (s * t - 1) = (s : ↥K) * (t : ↥K) - 1 := by
        rw [map_sub, map_mul, map_one]
      have hlt : IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭
          ((s : ↥K) * (t : ↥K) - 1) < 1 := by
        have h2' := (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := ↥K) 𝔭
          (s * t - 1)).mpr hmem
        first
          | (simpa only [hcoe1] using h2')
          | (simpa using h2')
          | (convert h2' using 1; push_cast; ring)
      have hlt' : IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭
          (1 - (s : ↥K) * (t : ↥K)) < 1 := by
        have hneg : (1 : ↥K) - (s : ↥K) * (t : ↥K) = -((s : ↥K) * (t : ↥K) - 1) := by ring
        rw [hneg, Valuation.map_neg]
        exact hlt
      have hr1 : ((r : 𝓞 ↥K) : ↥K) = (n : ↥K) * (t : ↥K) := by
        rw [hr_def]
        rfl
      have hr' : ((r : 𝓞 ↥K) : ↥K) = (x : ↥K) * (s : ↥K) * (t : ↥K) := by
        rw [hr1, ← hndK]
      have hprod : (x : ↥K) - (r : ↥K) = (x : ↥K) * (1 - (s : ↥K) * (t : ↥K)) := by
        rw [hr']
        ring
      rw [hprod, map_mul]
      calc IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 (x : ↥K) *
              IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 (1 - (s : ↥K) * (t : ↥K))
          = IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 (1 - (s : ↥K) * (t : ↥K)) *
              IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 (x : ↥K) := mul_comm _ _
        _ ≤ IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 (1 - (s : ↥K) * (t : ↥K)) * 1 :=
            mul_le_mul_right hxle _
        _ = IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 (1 - (s : ↥K) * (t : ↥K)) :=
            mul_one _
        _ < 1 := hlt'
    · rcases hrho with hx | hx
      · -- invariant case: `σbar` fixes the class of `r`
        refine hFFfix (Ideal.Quotient.mk 𝔭.asIdeal r) ?_
        have hmkeq : Ideal.Quotient.mk 𝔭.asIdeal (ρ • n) * Ideal.Quotient.mk 𝔭.asIdeal s =
            Ideal.Quotient.mk 𝔭.asIdeal n * Ideal.Quotient.mk 𝔭.asIdeal (ρ • s) := by
          rw [← map_mul, ← map_mul, hrel_inv hx]
        have h1 : σbar (Ideal.Quotient.mk 𝔭.asIdeal r) * Ideal.Quotient.mk 𝔭.asIdeal (ρ • s) =
            Ideal.Quotient.mk 𝔭.asIdeal (ρ • n) := by
          rw [← hσbar_mk s, ← hσbar_mk n, ← map_mul, hrs]
        have h3 : (σbar (Ideal.Quotient.mk 𝔭.asIdeal r) * Ideal.Quotient.mk 𝔭.asIdeal s) *
              Ideal.Quotient.mk 𝔭.asIdeal (ρ • s) =
            Ideal.Quotient.mk 𝔭.asIdeal n * Ideal.Quotient.mk 𝔭.asIdeal (ρ • s) := by
          rw [mul_assoc, mul_comm (Ideal.Quotient.mk 𝔭.asIdeal s), ← mul_assoc, h1, hmkeq]
        have h4 : σbar (Ideal.Quotient.mk 𝔭.asIdeal r) * Ideal.Quotient.mk 𝔭.asIdeal s =
            Ideal.Quotient.mk 𝔭.asIdeal n := mul_right_cancel₀ hρs_ne h3
        exact mul_right_cancel₀ hs_ne (by rw [h4, hrs])
      · -- anti-invariant case: the class of `r` has norm one
        refine hFFanti (Ideal.Quotient.mk 𝔭.asIdeal r) ?_
        have hmkeq : Ideal.Quotient.mk 𝔭.asIdeal (ρ • n) * Ideal.Quotient.mk 𝔭.asIdeal n =
            Ideal.Quotient.mk 𝔭.asIdeal (ρ • s) * Ideal.Quotient.mk 𝔭.asIdeal s := by
          rw [← map_mul, ← map_mul, hrel_anti hx]
        have h1 : σbar (Ideal.Quotient.mk 𝔭.asIdeal r) * Ideal.Quotient.mk 𝔭.asIdeal (ρ • s) =
            Ideal.Quotient.mk 𝔭.asIdeal (ρ • n) := by
          rw [← hσbar_mk s, ← hσbar_mk n, ← map_mul, hrs]
        have h6 : Ideal.Quotient.mk 𝔭.asIdeal r * Ideal.Quotient.mk 𝔭.asIdeal (ρ • n) =
            Ideal.Quotient.mk 𝔭.asIdeal (ρ • s) := by
          rw [hrn]
          calc (Ideal.Quotient.mk 𝔭.asIdeal n * Ideal.Quotient.mk 𝔭.asIdeal t) *
                Ideal.Quotient.mk 𝔭.asIdeal (ρ • n)
              = Ideal.Quotient.mk 𝔭.asIdeal (ρ • n) * Ideal.Quotient.mk 𝔭.asIdeal n *
                  Ideal.Quotient.mk 𝔭.asIdeal t := by ring
            _ = Ideal.Quotient.mk 𝔭.asIdeal (ρ • s) * Ideal.Quotient.mk 𝔭.asIdeal s *
                  Ideal.Quotient.mk 𝔭.asIdeal t := by rw [hmkeq]
            _ = Ideal.Quotient.mk 𝔭.asIdeal (ρ • s) := by rw [mul_assoc, hst', mul_one]
        have h7 : Ideal.Quotient.mk 𝔭.asIdeal r * σbar (Ideal.Quotient.mk 𝔭.asIdeal r) *
              Ideal.Quotient.mk 𝔭.asIdeal (ρ • s) = Ideal.Quotient.mk 𝔭.asIdeal (ρ • s) := by
          rw [mul_assoc, h1, h6]
        exact mul_right_cancel₀ hρs_ne (by rw [h7, one_mul])
  -- `2` is a unit of the integers of the completion
  have h2val : ¬ (IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 (2 : ↥K)) < 1 := by
    intro h
    exact h2 (by
      rw [← map_ofNat (algebraMap ↥K Ω) 2]
      exact (Work.SSGRoute.ZDataTwo.TwoRec.place_valuation_lt_one_iff A 𝔭 h𝔭 (2 : ↥K)).mpr h)
  have h2unit : IsUnit (2 : 𝔭.adicCompletionIntegers ↥K) :=
    Work.SSGRoute.ZDataTwo.TwoRec.isUnit_two_adicCompletionIntegers_of_not_lt_one 𝔭 h2val
  have hcoe : ∀ y : ↥K, Valued.v (algebraMap ↥K (𝔭.adicCompletion ↥K) y) =
      IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 y := fun y =>
    Work.SSGRoute.NodeS37.valued_adicCompletion_eq 𝔭 y
  have hxle : IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 (x : ↥K) ≤ 1 :=
    (Work.SSGRoute.ZDataTwo.TwoRec.place_valuation_le_one_iff A 𝔭 h𝔭 (x : ↥K)).mp
      (le_of_eq hunit)
  have hmem : algebraMap ↥K (𝔭.adicCompletion ↥K) (x : ↥K) ∈ 𝔭.adicCompletionIntegers ↥K := by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    simp only [hcoe]
    exact hxle
  have hxnotlt : ¬ (IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 (x : ↥K)) < 1 := by
    intro h
    have h' := (Work.SSGRoute.ZDataTwo.TwoRec.place_valuation_lt_one_iff A 𝔭 h𝔭 (x : ↥K)).mpr h
    rw [hunit] at h'
    exact lt_irrefl 1 h'
  have hxnotlt' : ¬ (Valued.v (algebraMap ↥K (𝔭.adicCompletion ↥K) (x : ↥K)) < 1) := by
    simp only [hcoe]
    exact hxnotlt
  have hu : IsUnit (⟨algebraMap ↥K (𝔭.adicCompletion ↥K) (x : ↥K), hmem⟩ :
      𝔭.adicCompletionIntegers ↥K) := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hmem2
    refine hxnotlt' ?_
    have h :=
      (Commons.NumberTheory.NumberField.adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one
        𝔭 (⟨algebraMap ↥K (𝔭.adicCompletion ↥K) (x : ↥K), hmem⟩ :
          𝔭.adicCompletionIntegers ↥K)).mp hmem2
    simpa using h
  have hux : algebraMap (𝔭.adicCompletionIntegers ↥K) (𝔭.adicCompletion ↥K)
      (hu.unit : 𝔭.adicCompletionIntegers ↥K) =
      algebraMap ↥K (𝔭.adicCompletion ↥K) (x : ↥K) := by
    simp [IsUnit.unit_spec]
  have hr_mem : (hu.unit : 𝔭.adicCompletionIntegers ↥K) -
      algebraMap (𝓞 ↥K) (𝔭.adicCompletionIntegers ↥K) r ∈
      IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers ↥K) := by
    rw [Commons.NumberTheory.NumberField.adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one
      𝔭]
    change Valued.v (algebraMap (𝔭.adicCompletionIntegers ↥K) (𝔭.adicCompletion ↥K)
      ((hu.unit : 𝔭.adicCompletionIntegers ↥K) -
        algebraMap (𝓞 ↥K) (𝔭.adicCompletionIntegers ↥K) r)) < 1
    rw [map_sub, hux]
    have htower : ((algebraMap (𝓞 ↥K) (𝔭.adicCompletionIntegers ↥K) r :
          𝔭.adicCompletionIntegers ↥K) : 𝔭.adicCompletion ↥K) =
        algebraMap ↥K (𝔭.adicCompletion ↥K) (r : ↥K) := by
      rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply (R := 𝓞 ↥K)
        (K := ↥K) 𝔭 r]
      exact IsScalarTower.algebraMap_apply (𝓞 ↥K) ↥K (𝔭.adicCompletion ↥K) r
    rw [show algebraMap (𝔭.adicCompletionIntegers ↥K) (𝔭.adicCompletion ↥K)
          (algebraMap (𝓞 ↥K) (𝔭.adicCompletionIntegers ↥K) r) =
          algebraMap ↥K (𝔭.adicCompletion ↥K) (r : ↥K) from htower]
    rw [← map_sub]
    simp only [hcoe]
    exact hrval
  have hsq_res : IsSquare ((IsLocalRing.residue (𝔭.adicCompletionIntegers ↥K))
      (hu.unit : 𝔭.adicCompletionIntegers ↥K)) :=
    Work.SSGRoute.NodeS37.isSquare_residue_of_isSquare_mk 𝔭
      (hu.unit : 𝔭.adicCompletionIntegers ↥K) r hr_mem hrsq
  obtain ⟨c, hc⟩ :=
    Work.SSGRoute.NodeS37.exists_sq_of_residue_isSquare 𝔭 h2unit hu.unit hsq_res
  refine ⟨c, ?_⟩
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.coe_map, hc]
  exact hux.symm

/-- **A finite field with a nontrivial involution of odd characteristic: fixed elements and
norm-one elements are squares** (assembled from the two proved inputs). -/
private lemma involutionIsSquare_of_fintype_pin {E : Type*} [Field E] [Fintype E] (σ : E ≃+* E)
    (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1) (hchar : ringChar E ≠ 2) :
    (∀ y : E, σ y = y → IsSquare y) ∧ (∀ y : E, y * σ y = 1 → IsSquare y) := by
  haveI : Finite E := Fintype.finite (inferInstance : Fintype E)
  have hinv : Function.Involutive σ := fun z => by
    have h := congrArg (fun f : E ≃+* E => f z) hσ2
    simpa [pow_two] using h
  have hfix : ∀ y : E, σ y = y → IsSquare y :=
    fun y hy => Work.SSGRoute.NodeS37.isSquare_of_fixed_of_involution σ hinv hσ1 hy
  exact ⟨hfix, fun y hy => Work.SSGRoute.P2Close.isSquare_of_mul_aut_eq_one σ hσ2 hfix y hy⟩

theorem oPairAt_inertPrime_eq_zero {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (ρ : K ≃ₐ[k] K) (hρ1 : ρ ≠ 1) (hρ2 : ρ ^ 2 = 1)
    (a X : (↥K)ˣ)
    (ha : Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) a = a)
    (hX : Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) X = -X)
    (B : ValuationSubring Ω) (hB : SSGRoute.IsFinPlace k B)
    (hB2 : ¬ B.valuation (2 : Ω) < 1)
    (hfix : Work.SSGRoute.gesKConj K (Work.SSGRoute.ZDataMup.galLift K ρ • B) B)
    (hunr : ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.res k K σ = ρ → ¬ SSGRoute.IsInertia k B σ)
    (hvala : B.valuation (algebraMap ↥K Ω (a : ↥K)) = 1) :
    Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
      (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
      B hB (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a)
      (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ X) = 0 := by
  classical
  -- the `K`-prime below the place `B`
  let 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K) :=
    Work.SSGRoute.levelPrime k Ω B hB K
  have h𝔭 : B.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 :=
    NK.Reconstruct.primeOfLevel_spec B K (NK.Reconstruct.comap_level_ne_top hB K)
  -- the prime is `ρ`-fixed, because `galLift K ρ • B` is `K`-conjugate to `B`
  have hcomapeq : (Work.SSGRoute.ZDataMup.galLift K ρ • B).comap (algebraMap ↥K Ω) =
      B.comap (algebraMap ↥K Ω) :=
    Work.SSGRoute.ZConstruction.comap_eq_of_gesKConj (K := K) hfix
  have hcomapsmul : (Work.SSGRoute.ZDataMup.galLift K ρ • B).comap (algebraMap ↥K Ω) =
      ρ • (B.comap (algebraMap ↥K Ω)) :=
    Work.SSGRoute.NodeS37.comap_smul_eq_smul_comap B (Work.SSGRoute.ZDataMup.galLift K ρ) ρ
      (fun x => Work.SSGRoute.H9.galLift_apply_coe (K := K) ρ x)
  have hO : ρ • IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 := by
    rw [← h𝔭, ← hcomapsmul, hcomapeq]
  have hfix' : Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔭 = 𝔭 := by
    apply Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := ↥K)
    rw [← Commons.NumberTheory.RamificationInertia.smul_valuationSubringAtPrime_eq_map_galRestrict
      𝔭 (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔭) ρ
      (Commons.NumberTheory.NumberField.Completion.placeSmul_asIdeal ρ 𝔭)]
    exact hO
  -- the action of `ρ` on the residue field is nontrivial (from `hunr`)
  have hnontriv : ∃ x₀ : NumberField.RingOfIntegers ↥K,
      ¬ (IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 (ρ (x₀ : ↥K) - (x₀ : ↥K)) < 1) := by
    by_contra hcon
    push Not at hcon
    have hρmem : ρ ∈ Work.SSGRoute.levelInertiaOf k Ω B hB K := by
      intro x
      change ρ • x - x ∈ 𝔭.asIdeal
      rw [← IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := ↥K) 𝔭
        (ρ • x - x)]
      simpa only [NumberField.RingOfIntegers.coe_eq_algebraMap, map_sub, algebraMap.smul',
        AlgEquiv.smul_def] using hcon x
    have hIn : ρ ∈ (Work.SSGRoute.inertiaSub k Ω B).map (AlgEquiv.restrictNormalHom K) := by
      rw [Work.SSGRoute.inertiaSub_image_eq_levelInertia k Ω B hB K]
      exact hρmem
    obtain ⟨u, hu, huρ⟩ := Subgroup.mem_map.mp hIn
    exact hunr u huρ hu
  -- the finite-field input
  have hFF : ∀ (E : Type) [Field E] [Fintype E] (σ : E ≃+* E), σ ^ 2 = 1 → σ ≠ 1 →
      ringChar E ≠ 2 → (∀ y : E, σ y = y → IsSquare y) ∧ (∀ y : E, y * σ y = 1 → IsSquare y) :=
    fun E _ _ σ hσ2 hσ1 hchar => involutionIsSquare_of_fintype_pin σ hσ2 hσ1 hchar
  -- `a` is a square in the completion at `𝔭`
  have hsq := unitSquareOfPrimeFix ρ hρ2 B hB 𝔭 h𝔭 hB2 hfix' hnontriv hFF a hvala (Or.inl ha)
  -- hence its local `2`-power class is trivial
  have he : (Units.map (algebraMap ↥K (𝔭.adicCompletion ↥K)).toMonoidHom a)⁻¹ ∈
      NK.UchidaKummer.ellPowSubgroup (𝔭.adicCompletion ↥K) 2 := by
    obtain ⟨c, hc⟩ := hsq
    refine ⟨c⁻¹, ?_⟩
    rw [powMonoidHom_apply, pow_two]
    rw [show c⁻¹ * c⁻¹ = (Units.map (algebraMap ↥K (𝔭.adicCompletion ↥K)).toMonoidHom a)⁻¹
      from by rw [← mul_inv_rev, ← pow_two, ← hc]]
  have hloc : NK.UchidaKummer.localPowClass ↥K 2 𝔭 a = 1 :=
    Work.SSGRoute.localPowClass_eq_one_of_unit_component (K := ↥K) (p := 2) Nat.prime_two
      (𝔭 := 𝔭) (γ := a)
      (e := (Units.map (algebraMap ↥K (𝔭.adicCompletion ↥K)).toMonoidHom a)⁻¹) he
      (by rw [inv_inv])
  -- so the Kummer cochain of `a` kills the whole local group, and the pairing vanishes
  have hkill : ∀ u ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a u = 0 :=
    fun u hu => (Work.SSGRoute.ZSplit.nodeKummerCocharZMod_eq_zero_iff_localPowClass
      K ζ hζK hζ a B hB 𝔭 h𝔭).mpr hloc u hu
  exact Work.SSGRoute.ZDataTwo.TwoRec.oPairAt_eq_zero_of_killsLocalGroup
    (ζ := ζ) (hζ := hζ) (hζK := hζK) a X B hB hkill

/-- `conjUnit` of a lifted automorphism is the image of the unit. -/
private lemma conjUnit_galLift_eq_map_pin {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω] (ρ : K ≃ₐ[k] K) (x : (↥K)ˣ) :
    Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) x
      = Units.map ρ.toRingEquiv.toMonoidHom x := by
  rw [Work.SSGRoute.H9.conjUnit, Work.SSGRoute.ZDataMup.galLift_spec]
  rfl

/-- **The `𝔭`-count is invariant under negation of the generator.** -/
private lemma count_spanSingleton_neg_pin {K : Type} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (x : K) (hx : x ≠ 0) :
    FractionalIdeal.count K 𝔭 (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers K)) (-x))
      = FractionalIdeal.count K 𝔭 (FractionalIdeal.spanSingleton
          (nonZeroDivisors (NumberField.RingOfIntegers K)) x) := by
  have hzero : FractionalIdeal.count K 𝔭 (FractionalIdeal.spanSingleton
      (nonZeroDivisors (NumberField.RingOfIntegers K)) (((-1 : Kˣ) : K))) = 0 := by
    have h3 := Work.SSGRoute.ZDataTwo.TwoRec.count_spanSingleton_inv_unit (K := K) 𝔭 (-1 : Kˣ)
    rw [show ((-1 : Kˣ))⁻¹ = -1 from by ext; simp] at h3
    omega
  have h1 := Work.SSGRoute.ZDataTwo.TwoRec.count_spanSingleton_mul_unit (K := K) 𝔭 (-1 : Kˣ)
    (Units.mk0 x hx)
  rw [show ((-1 : Kˣ) * Units.mk0 x hx : Kˣ) = Units.mk0 (-x) (neg_ne_zero.mpr hx) from by
    ext; simp] at h1
  rw [Units.val_mk0, hzero, zero_add, Units.val_mk0] at h1
  exact h1

/-- **The Kummer cochain of `b·x²` is that of `b`** (the function-level form of
`ZConstruction.nodeKummerCocharZMod_mul_sq`). -/
private lemma nodeKummerCocharZMod_mul_sq_fun {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K) (b x : (↥K)ˣ) :
    Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (b * x ^ 2)
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b := by
  funext ψ
  by_cases hψ : ψ ∈ K.fixingSubgroup
  · rw [pow_two]
    exact Work.SSGRoute.ZConstruction.nodeKummerCocharZMod_mul_sq (K := K) ζ hζ hζK b x ψ hψ
  · rw [Work.SSGRoute.ZSplit.nodeKummerCocharZMod_of_notMem (K := K) (ζ := ζ) (hζK := hζK)
      (hζ := hζ) (β := b * x ^ 2) hψ,
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod_of_notMem (K := K) (ζ := ζ) (hζK := hζK)
      (hζ := hζ) (β := b) hψ]

/-! ## Auxiliary lemmas for the final assembly of `pinnedValueOfHistoryOfInertSquare` -/

/-- The square of a chosen lift of an involution lies in the fixing subgroup of `K`. -/
theorem galLift_sq_mem_fixingSubgroup {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (ρ : K ≃ₐ[k] K) (hρ2 : ρ ^ 2 = 1) :
    Work.SSGRoute.ZDataMup.galLift K ρ * Work.SSGRoute.ZDataMup.galLift K ρ
      ∈ K.fixingSubgroup := by
  rw [← IntermediateField.restrictNormalHom_ker K, MonoidHom.mem_ker, map_mul, ← pow_two,
    Work.SSGRoute.ZDataMup.galLift_spec, hρ2]

/-- **Symmetry of the local Kummer pairing of two Kummer cochains** at a finite place. -/
theorem oPairAt_comm_two_pin {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K) (α β : (↥K)ˣ)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) A hA
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β)
      = Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) A hA
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α) := by
  rw [Work.SSGRoute.ZDataTwo.TwoRec.oPairAt_eq_oPairGlob_two (K := K) ζ hζ hζK α β A hA,
    Work.SSGRoute.H9.oPairGlob_comm_two (K := K) (⟨ζ, hζK⟩ : ↥K)
      (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) α β A hA,
    ← Work.SSGRoute.ZDataTwo.TwoRec.oPairAt_eq_oPairGlob_two (K := K) ζ hζ hζK β α A hA]

/-- **The local Kummer pairing only depends on the `K`-class of the place** (its prime below). -/
theorem oPairAt_gesKConj_pin {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K) (α β : (↥K)ˣ)
    (A B : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (hB : SSGRoute.IsFinPlace k B)
    (h : Work.SSGRoute.gesKConj K A B) :
    Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) A hA
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β)
      = Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) B hB
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β) := by
  rw [Work.SSGRoute.ZDataTwo.TwoRec.oPairAt_eq_oPairGlob_two (K := K) ζ hζ hζK α β A hA,
    Work.SSGRoute.ZDataTwo.TwoRec.oPairGlob_eq_of_gesKConj (K := K) (k := k) (Ω := Ω) ζ hζ hζK
      α β A B hA hB h,
    ← Work.SSGRoute.ZDataTwo.TwoRec.oPairAt_eq_oPairGlob_two (K := K) ζ hζ hζK α β B hB]

/-- **A class of odd order at a prime of `K` off the escape prime and its sibling is a unit there.**
If `z = b·y²` with `b` of even order off `𝔮`, if `z` is coprime to its `ρ`-conjugate, and if the
anti-invariant switch `X = z - ρz` has *odd* order at the prime `𝔭` below the place `B`, then both
`z` and `ρz` are units at `B` and `X` lies in the maximal ideal there. -/
theorem localUnits_of_oddCountX {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ρ : K ≃ₐ[k] K) (hρ2 : ρ ^ 2 = 1) (b y z X : (↥K)ˣ) (hzy : z = b * y ^ 2)
    (hX : (X : ↥K) = (z : ↥K)
      - ((Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) z : (↥K)ˣ) : ↥K))
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (heven : ∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K), P ≠ 𝔮 →
      Even (FractionalIdeal.count ↥K P (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) (b : ↥K))))
    (hcop : ∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      FractionalIdeal.count ↥K P (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) (z : ↥K)) ≠ 0 →
      FractionalIdeal.count ↥K
        (Commons.NumberTheory.NumberField.Completion.placeSmul ρ P)
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          (z : ↥K)) = 0)
    (B : ValuationSubring Ω) (hB : SSGRoute.IsFinPlace k B)
    (h𝔭q : Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) B hB ≠ 𝔮)
    (h𝔭rq : Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) B hB
      ≠ Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮)
    (hcB : Odd (FractionalIdeal.count ↥K
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) B hB)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        (X : ↥K)))) :
    B.valuation (algebraMap ↥K Ω (z : ↥K)) = 1 ∧
    B.valuation (algebraMap ↥K Ω
      (((Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) z : (↥K)ˣ) : ↥K))) = 1 ∧
    B.valuation (algebraMap ↥K Ω (X : ↥K)) < 1 := by
  sorry

theorem pinnedValueOfHistoryOfInertSquare {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K Λ : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω] [FiniteDimensional k Λ] [IsGalois k Λ] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (2 : Ω) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (2 : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0)
    (s : Work.SSGRoute.ZDataTwo.TwoRec.St (K := K))
    (hs : ∀ n, Work.SSGRoute.ZDataTwo.TwoRec.PreTwo (K := K) Λ ζ hζ hζK S y n s)
    (hinert : ∀ (ρ : K ≃ₐ[k] K) (hρ1 : ρ ≠ 1) (hρ2 : ρ ^ 2 = 1)
      (a : (↥K)ˣ) (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
      (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
      (h𝔭 : A.comap (algebraMap ↥K Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
      (h2 : ¬ A.valuation (2 : Ω) < 1)
      (hfixA : Work.SSGRoute.ZDataMup.galLift K ρ • A = A)
      (hunram : ¬ SSGRoute.IsRamifiedIn k K A)
      (hafix : Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) a = a)
      (heven : ∃ d : (↥K)ˣ, IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 (a : ↥K)
        = (IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 (d : ↥K)) ^ 2),
      ∀ u ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a u = 0) :
    ∀ m : ℕ, ∀ ρ : K ≃ₐ[k] K, ρ ≠ 1 → ρ ^ 2 = 1 →
      Work.SSGRoute.NodeS35.pinValue (K := K) (p := 2) ζ hζ hζK
        (fun _ => ((s.f m).1, (s.f m).2))
        (fun _ => (hs (m + 1)).1 m (Nat.lt_succ_self m)) 0 ρ = 0 := by
  intro m ρ hρ1 hρ2
  classical
  -- ## the prefix invariant at the stage `m + 1`
  obtain ⟨hfin, hsplit, -, -, -, -, hinv, -, hnorm⟩ := hs (m + 1)
  have hm : m < m + 1 := Nat.lt_succ_self m
  set Q : ValuationSubring Ω := (s.f m).1 with hQdef
  set b : (↥K)ˣ := (s.f m).2 with hbdef
  have hQfin : SSGRoute.IsFinPlace k Q := hfin m hm
  have hQsplit : SSGRoute.IsSplitIn k K Q :=
    Work.SSGRoute.NodeS35.isSplitIn_of_le (K := K) (N := Λ) hKΛ (hsplit m hm)
  set A : ValuationSubring Ω := Work.SSGRoute.ZDataMup.siblingPlace K ρ Q with hAdef
  have hAfin : SSGRoute.IsFinPlace k A :=
    (SSGRoute.isFinPlace_smul_iff Q (Work.SSGRoute.ZDataMup.galLift K ρ)).mpr hQfin
  have hQA : ¬ Work.SSGRoute.gesKConj K Q A := by
    rw [hAdef]
    exact Work.SSGRoute.ZDataMup.siblingPlace_not_gesKConj (K := K) hρ1 hQsplit
  -- ## the `K`-prime below `Q`, and the divisor normalisation of `b`
  set 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K) :=
    Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) Q hQfin with h𝔮def
  have h𝔮spec : Q.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔮 :=
    Work.SSGRoute.ZDataMup.OddForm.oddPrime_spec (K := K) hQfin
  have heven : ∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      P ≠ 𝔮 → Even (FractionalIdeal.count ↥K P (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) (b : ↥K))) := by
    intro P hP
    rw [h𝔮def] at hP
    rw [hbdef]
    exact Work.SSGRoute.NodeS37.evenCountAtNonEscapePrime (K := K) (Λ := Λ) hKΛ ζ hζ hζK S y
      hy hyT s hs m P hP
  have hodd : Odd (FractionalIdeal.count ↥K 𝔮 (FractionalIdeal.spanSingleton
      (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) (b : ↥K))) := by
    obtain ⟨𝔮₀, h𝔮₀comap, h𝔮₀odd⟩ := hnorm m hm
    have h : 𝔮₀ = 𝔮 := by
      apply Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := ↥K)
      rw [← h𝔮₀comap, h𝔮spec]
    rw [hbdef, ← h]
    exact h𝔮₀odd
  -- ## the sibling is not `K`-conjugate to `Q`, so `ρ𝔮 ≠ 𝔮`
  have hneSib : Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮 ≠ 𝔮 := by
    intro hfix
    have hcomapA : A.comap (algebraMap ↥K Ω) = Q.comap (algebraMap ↥K Ω) := by
      have h1 : A.comap (algebraMap ↥K Ω) = ρ • (Q.comap (algebraMap ↥K Ω)) := by
        rw [hAdef, Work.SSGRoute.ZDataMup.siblingPlace]
        exact Work.SSGRoute.NodeS37.comap_smul_eq_smul_comap Q
          (Work.SSGRoute.ZDataMup.galLift K ρ) ρ
          (fun x => Work.SSGRoute.H9.galLift_apply_coe (K := K) ρ x)
      have h2 : ρ • (Q.comap (algebraMap ↥K Ω)) = Q.comap (algebraMap ↥K Ω) := by
        rw [h𝔮spec,
          Commons.NumberTheory.RamificationInertia.smul_valuationSubringAtPrime_eq_map_galRestrict
            𝔮 (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮) ρ
            (Commons.NumberTheory.NumberField.Completion.placeSmul_asIdeal ρ 𝔮),
          hfix]
      rw [h1, h2]
    obtain ⟨σ, hσ⟩ := Commons.RingTheory.Valuation.exists_smul_eq_of_comap_eq_isGalois
      (F := ↥K) (E := Ω) Q A hcomapA.symm
      (by rw [h𝔮spec]; exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top 𝔮)
    refine hQA ⟨((IntermediateField.fixingSubgroupEquiv K).symm σ : Ω ≃ₐ[k] Ω), ?_, ?_⟩
    · exact ((IntermediateField.fixingSubgroupEquiv K).symm σ).2
    · rw [← Work.SSGRoute.GrunwaldEscapeCore.gesSmulEqOfCoeEq K (φ := σ)
        (ψ := ((IntermediateField.fixingSubgroupEquiv K).symm σ : Ω ≃ₐ[k] Ω)) rfl Q]
      exact hσ
  -- ## the representative `z = b · yᵥ²` with `div z = 𝔮 · Q'²`
  obtain ⟨z, yv, hzy, Q', hQ'nfix, hQ'miss, hcount, hcop, hmissρ⟩ :=
    divisorRepresentativeCoprime (k := k) (K := ↥K) ρ hρ2 b 𝔮 heven hodd hneSib
  -- ## the conjugate units
  set bt : (↥K)ˣ := Units.map ρ.toRingEquiv.toMonoidHom b with hbt
  set rz : (↥K)ˣ := Units.map ρ.toRingEquiv.toMonoidHom z with hrz
  have hbtconj : Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) b = bt :=
    (conjUnit_galLift_eq_map_pin (K := K) ρ b).trans hbt.symm
  -- ## the Kummer cochains of `z` and `ρz` agree with those of `b` and `ρb`
  have hχz : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ z
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b := by
    rw [hzy]
    exact nodeKummerCocharZMod_mul_sq_fun (K := K) ζ hζ hζK b yv
  have hrzeq : rz = bt * (Units.map ρ.toRingEquiv.toMonoidHom yv) ^ 2 := by
    rw [hrz, hbt, hzy]
    simp only [map_mul, map_pow]
  have hχrz : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ rz
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt := by
    rw [hrzeq]
    exact nodeKummerCocharZMod_mul_sq_fun (K := K) ζ hζ hζK bt
      (Units.map ρ.toRingEquiv.toMonoidHom yv)
  -- ## the count of `z` at `𝔮` is odd, hence nonzero
  have hoddz : FractionalIdeal.count ↥K 𝔮 (FractionalIdeal.spanSingleton
      (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) (z : ↥K)) ≠ 0 := by
    rw [hcount 𝔮, FractionalIdeal.count_maximal (R := NumberField.RingOfIntegers ↥K) (K := ↥K)
      𝔮 𝔮, if_pos rfl]
    intro h0
    omega
  -- ## the switch `X := z - ρz`
  have hzne : (z : ↥K) - (rz : ↥K) ≠ 0 := by
    intro h0
    have hzeq : z = rz := Units.ext (sub_eq_zero.mp h0)
    have h1 : FractionalIdeal.count ↥K
        (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮)
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          (z : ↥K)) ≠ 0 := by
      rw [hzeq, hrz,
        Work.SSGRoute.NodeS37.count_placeSmul_eq_count (k := k) (L := ↥K) ρ z 𝔮]
      exact hoddz
    exact h1 (hcop 𝔮 hoddz)
  set X : (↥K)ˣ := Units.mk0 ((z : ↥K) - (rz : ↥K)) hzne with hXdef
  -- ## `ρ` acts on `↥K` as an involution (value form)
  have hρρ : ∀ x : ↥K, ρ (ρ x) = x := by
    intro x
    have h := congrArg (fun e : K ≃ₐ[k] K => e x) hρ2
    simpa [pow_two] using h
  have hrzval : ρ (rz : ↥K) = (z : ↥K) := by
    rw [hrz, Units.coe_map]
    exact hρρ (z : ↥K)
  have hzval : (rz : ↥K) = ρ (z : ↥K) := rfl
  -- ## the anti-invariance of `X`
  have hXanti : Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) X = -X := by
    refine Units.ext ?_
    rw [conjUnit_galLift_eq_map_pin (K := K) ρ X, Units.coe_map, hXdef, Units.val_mk0,
      Units.val_neg, Units.val_mk0]
    show ρ ((z : ↥K) - (rz : ↥K)) = -((z : ↥K) - (rz : ↥K))
    rw [map_sub, hrzval, ← hzval]
    ring
  -- ## the confinement of the stage class (outside its own escape prime)
  have hconfQ : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (¬ Work.SSGRoute.gesKConj K Q B) → ∀ u : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B u →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b u = 0 := by
    intro B hB hnc u hI
    by_cases huK : u ∈ K.fixingSubgroup
    · exact Work.SSGRoute.NodeS37.claimOfPreTwoConfined.claimOfPreTwoConfined (K := K) (Λ := Λ)
        hKΛ ζ hζ hζK S y hy hyT s hs m B hB hnc u huK hI
    · exact Work.SSGRoute.ZSplit.nodeKummerCocharZMod_of_notMem (K := K) (ζ := ζ) (hζK := hζK)
        (hζ := hζ) (β := b) huK
  -- ## the confinement of the conjugate class, and its involution-killing
  have hconfbt : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (¬ Work.SSGRoute.gesKConj K A B) → ∀ u : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B u →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt u = 0 := by
    have h := Work.SSGRoute.H9.CV2.hconf_conjUnit (K := K) ζ hζ hζK b ρ Q hconfQ
    rw [← hbt, ← hAdef] at h
    exact h
  have hinfb : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b c = 0 :=
    fun c hc hc2 => hinv m hm c hc hc2
  have hinfbt : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt c = 0 := by
    have h := Work.SSGRoute.H9.CV2.hinf_conjUnit (K := K) ζ hζ hζK b ρ hinfb
    rw [← hbt] at h
    exact h
  -- ## the place set `T' = krep K ({A, Q} ∪ T_X ∪ T_2)`
  obtain ⟨TX, hTXfin, -, hTXcover⟩ :=
    Work.SSGRoute.ZConstruction.exists_finset_covering_notUnit (K := K) X
  obtain ⟨T2, hT2fin, -, hT2cover⟩ :=
    Work.SSGRoute.ZConstruction.exists_finset_covering_notUnit (K := K)
      (Units.mk0 (2 : ↥K) (by norm_num))
  set TX2 : Finset (ValuationSubring Ω) := TX ∪ T2 with hTX2def
  set TXg : Finset (ValuationSubring Ω) :=
    TX2.image (fun B => Work.SSGRoute.ZDataMup.galLift K ρ • B) with hTXgdef
  set T0 : Finset (ValuationSubring Ω) := insert A (insert Q (TX2 ∪ TXg)) with hT0def
  have hTXgfin : ∀ B ∈ TXg, SSGRoute.IsFinPlace k B := by
    intro B hB
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hB
    rw [hTX2def] at hC
    rcases Finset.mem_union.mp hC with hC | hC
    · exact (SSGRoute.isFinPlace_smul_iff C (Work.SSGRoute.ZDataMup.galLift K ρ)).mpr
        (hTXfin C hC)
    · exact (SSGRoute.isFinPlace_smul_iff C (Work.SSGRoute.ZDataMup.galLift K ρ)).mpr
        (hT2fin C hC)
  set T' : Finset (ValuationSubring Ω) := Work.SSGRoute.H9.krep K T0 with hT'def
  have hT'fin : ∀ B ∈ T', SSGRoute.IsFinPlace k B := by
    intro B hB
    obtain ⟨B0, hB0, hconj⟩ :=
      Work.SSGRoute.H9.krep_mem_classes K T0 B (by rw [← hT'def]; exact hB)
    have hB0fin : SSGRoute.IsFinPlace k B0 := by
      rw [hT0def] at hB0
      rcases Finset.mem_insert.mp hB0 with h | h
      · rw [h]; exact hAfin
      · rcases Finset.mem_insert.mp h with h | h
        · rw [h]; exact hQfin
        · rcases Finset.mem_union.mp h with h' | h'
          · rw [hTX2def] at h'
            rcases Finset.mem_union.mp h' with h' | h'
            · exact hTXfin B0 h'
            · exact hT2fin B0 h'
          · exact hTXgfin B0 h'
    obtain ⟨τ, -, hτB⟩ := hconj
    exact (SSGRoute.isFinPlace_smul_iff B τ).mp (by rw [hτB]; exact hB0fin)
  have hT'disj : ∀ B ∈ T', ∀ C ∈ T',
      (∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ C ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ B) → B = C := by
    intro B hB C hC hform
    rw [hT'def] at hB hC
    exact Work.SSGRoute.H9.krep_disj K T0 B hB C hC
      ((Work.SSGRoute.H9.gesKConj_iff_smul_form B C).mpr hform)
  -- ## the confinement of the switch `X` outside `T'`
  have hconfX : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ C ∈ T', ¬ Work.SSGRoute.gesKConj K C B) →
      ∀ u : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B u →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ X u = 0 := by
    intro B hB hnc u hI
    have hunitX : B.valuation (algebraMap ↥K Ω (X : ↥K)) = 1 := by
      by_contra hne
      obtain ⟨C, hC, hCB⟩ := hTXcover B hB hne
      have hCT0 : C ∈ T0 := by
        rw [hT0def]; exact Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_union_left TXg (by
            rw [hTX2def]; exact Finset.mem_union_left T2 hC)))
      obtain ⟨C', hC', hC'C⟩ := Work.SSGRoute.H9.krep_covers K T0 C hCT0
      rw [← hT'def] at hC'
      exact hnc C' hC' (Work.SSGRoute.H9.swGesKConj_trans hC'C hCB)
    have hnot2 : ¬ B.valuation (2 : Ω) < 1 := by
      intro hlt
      have hlt' : B.valuation (algebraMap ↥K Ω
          ((Units.mk0 (2 : ↥K) (by norm_num) : (↥K)ˣ) : ↥K)) ≠ 1 := by
        rw [show ((Units.mk0 (2 : ↥K) (by norm_num) : (↥K)ˣ) : ↥K) = (2 : ↥K) from rfl,
          show algebraMap ↥K Ω ((2 : ↥K)) = (2 : Ω) from map_ofNat (algebraMap ↥K Ω) 2]
        exact ne_of_lt hlt
      obtain ⟨C, hC, hCB⟩ := hT2cover B hB hlt'
      have hCT0 : C ∈ T0 := by
        rw [hT0def]; exact Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_union_left TXg (by
            rw [hTX2def]; exact Finset.mem_union_right TX hC)))
      obtain ⟨C', hC', hC'C⟩ := Work.SSGRoute.H9.krep_covers K T0 C hCT0
      rw [← hT'def] at hC'
      exact hnc C' hC' (Work.SSGRoute.H9.swGesKConj_trans hC'C hCB)
    by_cases huK : u ∈ K.fixingSubgroup
    · exact Work.SSGRoute.ZDataTwo.TwoRec.killsInertia_of_unit_notTwo (K := K) ζ hζ hζK X B hB
        hnot2 hunitX u huK hI
    · exact Work.SSGRoute.ZSplit.nodeKummerCocharZMod_of_notMem (K := K) (ζ := ζ) (hζK := hζK)
        (hζ := hζ) (β := X) huK
  have hconfbt' : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ C ∈ T', ¬ Work.SSGRoute.gesKConj K C B) →
      ∀ u : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B u →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt u = 0 := by
    intro B hB hnc u hI
    refine hconfbt B hB ?_ u hI
    intro hconj
    obtain ⟨A', hA', hA'A⟩ := Work.SSGRoute.H9.krep_covers K T0 A
      (by rw [hT0def]; exact Finset.mem_insert_self A _)
    rw [← hT'def] at hA'
    exact hnc A' hA' (Work.SSGRoute.H9.swGesKConj_trans hA'A hconj)
  -- ## the multi-place product formula for the pair `(ρb, X)` over `T'`
  have hsum := Work.SSGRoute.ZDataTwo.TwoRec.oPairAt_sum_attach_eq_zero_of_kills (K := K)
    ζ hζ hζK bt X T' hT'fin hT'disj hconfbt' hconfX hinfbt
  -- ## `X` is a unit at the `𝔮`-class (`count_𝔮 X = 0`)
  have hcountz_pos : 0 < FractionalIdeal.count ↥K 𝔮 (FractionalIdeal.spanSingleton
      (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) (z : ↥K)) := by
    rw [hcount 𝔮,
      FractionalIdeal.count_maximal (R := NumberField.RingOfIntegers ↥K) (K := ↥K) 𝔮 𝔮,
      FractionalIdeal.count_maximal (R := NumberField.RingOfIntegers ↥K) (K := ↥K) 𝔮 Q',
      if_pos rfl]
    split_ifs with h <;> norm_num
  have hvalz : (IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔮) (z : ↥K) < 1 := by
    rw [Work.SSGRoute.GrunwaldEscapeCore.val_eq_exp_neg_count (K := ↥K) 𝔮 (Units.ne_zero z)]
    rw [show (1 : WithZero (Multiplicative ℤ)) = WithZero.exp (0 : ℤ) from rfl,
      WithZero.exp, WithZero.exp, WithZero.coe_lt_coe, Multiplicative.ofAdd_lt]
    omega
  have hcountrz : FractionalIdeal.count ↥K 𝔮 (FractionalIdeal.spanSingleton
      (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) (rz : ↥K)) = 0 := by
    have hpp : Commons.NumberTheory.NumberField.Completion.placeSmul ρ
        (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮) = 𝔮 :=
      Work.SSGRoute.ZDataTwo.TwoRec.placeSmul_placeSmul (K := ↥K) ρ hρ2 𝔮
    have htr := Work.SSGRoute.NodeS37.count_placeSmul_eq_count (k := k) (L := ↥K) ρ z
      (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮)
    rw [hpp, ← hrz] at htr
    exact htr.trans hmissρ
  have hvalrz : (IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔮) (rz : ↥K) = 1 := by
    rw [Work.SSGRoute.GrunwaldEscapeCore.val_eq_exp_neg_count (K := ↥K) 𝔮 (Units.ne_zero rz),
      hcountrz]
    norm_num [WithZero.exp]
  have hvalXq : (IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔮) (X : ↥K) = 1 := by
    have hlt : (IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔮) (z : ↥K)
        < (IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔮) (rz : ↥K) := by
      rw [hvalrz]; exact hvalz
    rw [Units.val_mk0 hzne,
      (IsDedekindDomain.HeightOneSpectrum.valuation ↑K 𝔮).map_sub_eq_of_lt_right hlt,
      hvalrz]
  have hcountX : FractionalIdeal.count ↥K 𝔮 (FractionalIdeal.spanSingleton
      (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) (X : ↥K)) = 0 := by
    refine (Work.SSGRoute.GrunwaldEscapeCore.valuation_eq_one_iff_count_eq_zero Q 𝔮 h𝔮spec
      X).mp ?_
    have hle : Q.valuation (algebraMap ↥K Ω (X : ↥K)) ≤ 1 :=
      (Work.SSGRoute.ZDataTwo.TwoRec.place_valuation_le_one_iff Q 𝔮 h𝔮spec (X : ↥K)).mpr
        (le_of_eq hvalXq)
    have hnotlt : ¬ Q.valuation (algebraMap ↥K Ω (X : ↥K)) < 1 := fun h =>
      absurd ((Work.SSGRoute.ZDataTwo.TwoRec.place_valuation_lt_one_iff Q 𝔮 h𝔮spec
        (X : ↑K)).mp h) (by rw [hvalXq]; exact lt_irrefl 1)
    exact le_antisymm hle (not_lt.mp hnotlt)
  sorry

end Work.SSGRoute.NodeS37
