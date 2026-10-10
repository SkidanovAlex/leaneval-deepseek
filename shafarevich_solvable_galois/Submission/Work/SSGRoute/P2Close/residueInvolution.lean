import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.NodeS37.inertSquareOfRhoFixed
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The involution induced on the residue field of a `ρ`-stable prime

Let `k` be a number field, `Ω` an algebraic closure of `k`, `K/k` a finite Galois intermediate
field, `A` a finite place of `Ω`, and `𝔭` the prime of `𝓞 K` below `A`.  If an involution
`ρ : K ≃ₐ[k] K` fixes the place `A` (through its chosen lift `galLift K ρ` to `Ω`) and acts
nontrivially on `𝓞 K / 𝔭`, then `ρ` induces a *nontrivial* involution `σbar` of the residue field
`𝓞 K / 𝔭`.

The mathematical content is:

* the fixedness of the place transports: `ρ • 𝒪_𝔭 = 𝒪_𝔭`, where `𝒪_𝔭` is the `𝔭`-valuation ring
  of `↥K` (`comap_smul_eq_smul_comap` and `h𝔭`);
* hence `ρ` fixes the prime `𝔭` itself, i.e. the induced automorphism of `𝓞 K` preserves `𝔭.asIdeal`
  (`smul_valuationSubringAtPrime_eq_map_galRestrict` + injectivity of `valuationSubringAtPrime`);
* so `ρ` descends to a ring automorphism `σbar` of `𝓞 K ⧸ 𝔭.asIdeal`, which is an involution because
  `ρ ^ 2 = 1`, and is nontrivial because `ρ` moves some element of `𝓞 K` modulo `𝔭`.
-/

open scoped Pointwise

namespace Work.SSGRoute.P2Close

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
  [IsSepClosure ↥K Ω]

/-- The action of `ρ` on `𝓞 K` is the restriction to `𝓞 K` of the automorphism `ρ` of `↥K`. -/
private lemma galRestrict_apply_eq_smul (ρ : K ≃ₐ[k] K) (y : NumberField.RingOfIntegers ↥K) :
    (galRestrict (NumberField.RingOfIntegers k) k ↥K (NumberField.RingOfIntegers ↥K) ρ) y =
      ρ • y := by
  apply NumberField.RingOfIntegers.coe_injective
  rw [algebraMap_galRestrict_apply, algebraMap.smul', AlgEquiv.smul_def]

/-- In the residue field, the class of the induced image of `y` is the class of `ρ • y`. -/
private lemma rhoTilde_mk (ρ : K ≃ₐ[k] K)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (y : NumberField.RingOfIntegers ↥K) :
    Ideal.Quotient.mk 𝔭.asIdeal
        ((galRestrict (NumberField.RingOfIntegers k) k ↥K (NumberField.RingOfIntegers ↥K) ρ :
          NumberField.RingOfIntegers ↥K ≃+* NumberField.RingOfIntegers ↥K) y)
      = Ideal.Quotient.mk 𝔭.asIdeal (ρ • y) := by
  have hbridge : ((galRestrict (NumberField.RingOfIntegers k) k ↥K
        (NumberField.RingOfIntegers ↥K) ρ :
        NumberField.RingOfIntegers ↥K ≃+* NumberField.RingOfIntegers ↥K) y)
      = (galRestrict (NumberField.RingOfIntegers k) k ↥K
        (NumberField.RingOfIntegers ↥K) ρ) y := rfl
  rw [hbridge, galRestrict_apply_eq_smul (K := K) ρ y]

theorem residueInvolution {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ρ : K ≃ₐ[k] K) (hρ2 : ρ ^ 2 = 1)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (hfixA : Work.SSGRoute.ZDataMup.galLift K ρ • A = A)
    (hnontriv : ∃ x₀ : NumberField.RingOfIntegers ↥K,
      ¬ (IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 (ρ (x₀ : ↥K) - (x₀ : ↥K)) < 1)) :
    ∃ σbar : ((NumberField.RingOfIntegers ↥K) ⧸ 𝔭.asIdeal) ≃+*
        ((NumberField.RingOfIntegers ↥K) ⧸ 𝔭.asIdeal),
      (∀ y : NumberField.RingOfIntegers ↥K,
        σbar (Ideal.Quotient.mk 𝔭.asIdeal y) =
          Ideal.Quotient.mk 𝔭.asIdeal (ρ • y)) ∧
      σbar ^ 2 = 1 ∧ σbar ≠ 1 := by
  classical
  -- The place `galLift K ρ • A = A` has the same trace on `↥K` as `A`, namely the `ρ`-image of
  -- the `𝔭`-valuation ring of `↥K`.
  have hcomap : ρ • (A.comap (algebraMap ↥K Ω)) = A.comap (algebraMap ↥K Ω) := by
    rw [← Work.SSGRoute.NodeS37.comap_smul_eq_smul_comap A
        (Work.SSGRoute.ZDataMup.galLift K ρ) ρ
        (fun x => Work.SSGRoute.H9.galLift_apply_coe (K := K) ρ x), hfixA]
  have hO : ρ • IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 := by
    rw [← h𝔭]
    exact hcomap
  -- Hence the prime below the place is fixed by `ρ`.
  have hplace : IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K
      (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔭) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 := by
    rw [← Commons.NumberTheory.RamificationInertia.smul_valuationSubringAtPrime_eq_map_galRestrict
      𝔭 (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔭) ρ
      (Commons.NumberTheory.NumberField.Completion.placeSmul_asIdeal ρ 𝔭)]
    exact hO
  have hfix : Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔭 = 𝔭 :=
    Commons.RingTheory.Valuation.valuationSubringAtPrime_injective hplace
  -- Therefore the induced automorphism of `𝓞 K` preserves the ideal `𝔭.asIdeal`.
  have hmap : Ideal.map
      ((galRestrict (NumberField.RingOfIntegers k) k ↥K (NumberField.RingOfIntegers ↥K) ρ :
        NumberField.RingOfIntegers ↥K ≃+* NumberField.RingOfIntegers ↥K) :
        NumberField.RingOfIntegers ↥K →+* NumberField.RingOfIntegers ↥K) 𝔭.asIdeal =
      𝔭.asIdeal := by
    -- `placeSmul_asIdeal` states the stability of `𝔭.asIdeal` in the coercion form of
    -- `galRestrict` used by `placeSmul`; the two coercion forms are definitionally equal.
    have hPS : (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔭).asIdeal = 𝔭.asIdeal := by
      rw [hfix]
    exact (Commons.NumberTheory.NumberField.Completion.placeSmul_asIdeal ρ 𝔭).symm.trans hPS
  -- The descent to the residue field.
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
    exact rhoTilde_mk (K := K) ρ 𝔭 y
  refine ⟨σbar, hprop, ?_, ?_⟩
  · -- `σbar` is an involution because `ρ ^ 2 = 1`.
    ext z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [pow_two, RingAut.mul_apply, RingAut.one_apply, hprop y, hprop (ρ • y)]
    have hfixy : ρ • (ρ • y) = y := by
      rw [← mul_smul, ← pow_two, hρ2, one_smul]
    rw [hfixy]
  · -- `σbar` is nontrivial by the hypothesis on `ρ`.
    intro h1
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

end Work.SSGRoute.P2Close
