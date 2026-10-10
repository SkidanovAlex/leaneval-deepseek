import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.H9.swChainConjDefs
import Submission.Work.SSGRoute.NodeS37.isSquare_of_fixed_of_involution
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `IsSquare (mk 𝔭 r)` for a `ρ`-fixed residue at an unramified `ρ`-fixed place

Let `k` be a number field, `Ω` an algebraic closure, `K / k` a finite Galois intermediate field with
`Ω` a separable closure of `K`.  Let `ρ : Gal(K/k)` be an involution `≠ 1`, `A` a finite place of
`Ω` over `k` fixed by the lift `galLift K ρ`, and let `𝔭` be the prime of `𝓞 K` below `A`.  Assume
`A` is unramified in `K/k`.  Then, for any `r : 𝓞 K` with `ρ • r - r ∈ 𝔭`, the residue class
`mk 𝔭 r` is a **square** in the residue field `𝓞 K ⧸ 𝔭`.

The mechanism is purely local.  `hfixA` forces `ρ` into the decomposition group of `𝔭`
(`decompositionSubgroup`), so `ρ` acts on the residue field `𝓞 K ⧸ 𝔭`; `hunram` forces this action
to be non-trivial (some `y` has `ρ y - y ∉ 𝔭`), and `ρ² = 1` makes it an involution.  The residue
field is finite, so the abstract finite-field statement
`NodeS37.isSquare_of_fixed_of_involution` (fixed elements of a finite field under a non-trivial
involution are squares) applies.
-/

open scoped Pointwise NumberField

namespace Work.SSGRoute.NodeS37

set_option linter.style.haveILetI false

/-- **The place `A` and its `K`-linear restriction.**  If `g` acts on `↥K` as `ρ`, then the
valuation ring of `g • A` pulled back to `↥K` is the image under `ρ` of the valuation ring of `A`
pulled back to `↥K`. -/
private lemma comap_smul_eq_smul_comap_aux {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {K : IntermediateField k Ω} (A : ValuationSubring Ω) (g : Ω ≃ₐ[k] Ω) (ρ : K ≃ₐ[k] K)
    (hg : ∀ x : K, g (x : Ω) = (ρ x : Ω)) :
    (g • A).comap (algebraMap K Ω) = ρ • (A.comap (algebraMap K Ω)) := by
  ext x
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_comap]
  have h1 : g⁻¹ • (algebraMap K Ω x) = algebraMap K Ω (ρ⁻¹ • x) := by
    rw [AlgEquiv.smul_def]
    have h2 : g ((algebraMap K Ω) (ρ⁻¹ • x)) = algebraMap K Ω x := by
      change g ((↑(ρ⁻¹ • x) : Ω)) = algebraMap K Ω x
      rw [hg]
      simp
    rw [← h2]
    exact AlgEquiv.symm_apply_apply g ((algebraMap K Ω) (ρ⁻¹ • x))
  rw [h1]

/-- **Unramifiedness forces `ρ` to act non-trivially on the residue field.**

If the finite place `A` (fixed by `galLift K ρ`) is unramified in `K/k`, then the nontrivial
involution `ρ` cannot act trivially on `𝓞 K ⧸ 𝔭`: there is `y` with `ρ • y - y ∉ 𝔭`. -/
theorem exists_smul_sub_notMem_of_unramified {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ρ : K ≃ₐ[k] K) (hρ1 : ρ ≠ 1)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (hunram : ¬ SSGRoute.IsRamifiedIn k K A) :
    ∃ y : NumberField.RingOfIntegers ↥K, ρ • y - y ∉ 𝔭.asIdeal := by
  classical
  -- identify the given prime with the level prime of `A` at the level `K`
  have hlev : Work.SSGRoute.levelPrime k Ω A hA K = 𝔭 :=
    Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
      (by rw [← NK.Reconstruct.primeOfLevel_spec A K (NK.Reconstruct.comap_level_ne_top hA K), h𝔭])
  -- `hunram` gives ramification index one over `k`
  have hram : 𝔭.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 := by
    rw [← hlev]
    exact Work.SSGRoute.ZDataTwo.ramificationIdx_levelPrime_eq_one_of_not_isRamifiedIn
      k Ω K A hA hunram
  -- hence the inertia subgroup of `Gal(↥K/k)` at `𝔭` is trivial
  haveI : (𝔭.asIdeal.under (NumberField.RingOfIntegers k)).IsPrime := inferInstance
  have hbot : Ideal.inertia (↥K ≃ₐ[k] ↥K) 𝔭.asIdeal = ⊥ :=
    (Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
      (𝔭.asIdeal.under (NumberField.RingOfIntegers k)) 𝔭.asIdeal).mpr hram
  by_contra hcon
  push_neg at hcon
  have hmem : ρ ∈ Ideal.inertia (↥K ≃ₐ[k] ↥K) 𝔭.asIdeal := hcon
  rw [hbot] at hmem
  exact hρ1 (Subgroup.mem_bot.mp hmem)

theorem isSquare_mk_of_rho_smul_sub_mem {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ρ : K ≃ₐ[k] K) (hρ1 : ρ ≠ 1) (hρ2 : ρ ^ 2 = 1)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (hfixA : Work.SSGRoute.ZDataMup.galLift K ρ • A = A)
    (hunram : ¬ SSGRoute.IsRamifiedIn k K A)
    (r : NumberField.RingOfIntegers ↥K) (hr : ρ • r - r ∈ 𝔭.asIdeal) :
    IsSquare (Ideal.Quotient.mk 𝔭.asIdeal r) := by
  classical
  -- (1) `ρ` lies in the decomposition group of `𝔭`, because it fixes `A` and acts on `K` as `ρ`.
  have hρD : ρ ∈ Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := k) 𝔭 := by
    refine (Commons.NumberTheory.NumberField.Completion.smul_valuationSubringAtPrime_eq_iff_mem_decompositionSubgroup (F := k) (E := ↥K) 𝔭 ρ).mp ?_
    have h1 : A.comap (algebraMap ↥K Ω) = ρ • (A.comap (algebraMap ↥K Ω)) := by
      rw [← comap_smul_eq_smul_comap_aux A (Work.SSGRoute.ZDataMup.galLift K ρ) ρ
        (fun y => Work.SSGRoute.H9.galLift_apply_coe ρ y), hfixA]
    rw [h𝔭] at h1
    exact h1.symm
  -- (2) `ρ` preserves the `𝔭`-adic valuation, hence the prime ideal `𝔭`.
  have hρval : ∀ y : ↥K, IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 (ρ y)
      = IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 y :=
    fun y => Commons.NumberTheory.NumberField.Completion.decompositionSubgroup_preserves_valuation
      (K := k) (L := ↥K) (w := 𝔭) hρD y
  -- (3) the ring endomorphism of `𝓞 K` induced by `ρ`.
  let ψ : NumberField.RingOfIntegers ↥K →+* NumberField.RingOfIntegers ↥K :=
    MulSemiringAction.toRingHom (↥K ≃ₐ[k] ↥K) (NumberField.RingOfIntegers ↥K) ρ
  have hψapply : ∀ x : NumberField.RingOfIntegers ↥K, ψ x = ρ • x :=
    fun x => MulSemiringAction.toRingHom_apply _ _ ρ x
  have hψcoe : ∀ x : NumberField.RingOfIntegers ↥K,
      ((ψ x : NumberField.RingOfIntegers ↥K) : ↥K) = ρ (x : ↥K) := by
    intro x
    rw [hψapply]
    rfl
  have hψmem : ∀ x : NumberField.RingOfIntegers ↥K, ψ x ∈ 𝔭.asIdeal ↔ x ∈ 𝔭.asIdeal := by
    intro x
    rw [← IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := ↥K) 𝔭 (ψ x),
      ← IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := ↥K) 𝔭 x]
    simp only [hψcoe x, hρval (x : ↥K)]
  have hψ2 : ∀ y : NumberField.RingOfIntegers ↥K, ψ (ψ y) = y := by
    intro y
    have h1 : ψ (ψ y) = ρ • (ρ • y) := by
      rw [hψapply, hψapply]
    rw [h1, ← mul_smul, ← pow_two, hρ2, one_smul]
  -- (4) the induced ring endomorphism of the residue field.
  haveI : Field (NumberField.RingOfIntegers ↥K ⧸ 𝔭.asIdeal) := Ideal.Quotient.field 𝔭.asIdeal
  let σ : (NumberField.RingOfIntegers ↥K ⧸ 𝔭.asIdeal) →+*
      (NumberField.RingOfIntegers ↥K ⧸ 𝔭.asIdeal) :=
    Ideal.Quotient.lift 𝔭.asIdeal
      ((Ideal.Quotient.mk 𝔭.asIdeal).comp ψ)
      (fun a ha => by
        rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
        exact (hψmem a).mpr ha)
  have hσmk : ∀ x : NumberField.RingOfIntegers ↥K,
      σ (Ideal.Quotient.mk 𝔭.asIdeal x) = Ideal.Quotient.mk 𝔭.asIdeal (ψ x) :=
    fun x => Ideal.Quotient.lift_mk _ _ _
  have hσinj : Function.Injective σ := by
    intro a b hab
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [hσmk, hσmk, Ideal.Quotient.eq] at hab
    have hab' : ψ (x - y) ∈ 𝔭.asIdeal := by
      rw [map_sub]
      exact hab
    rw [Ideal.Quotient.eq]
    exact (hψmem (x - y)).mp hab'
  haveI : Finite (NumberField.RingOfIntegers ↥K ⧸ 𝔭.asIdeal) :=
    Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum 𝔭
  let σe : (NumberField.RingOfIntegers ↥K ⧸ 𝔭.asIdeal) ≃+*
      (NumberField.RingOfIntegers ↥K ⧸ 𝔭.asIdeal) :=
    RingEquiv.ofBijective σ ⟨hσinj, Finite.surjective_of_injective hσinj⟩
  have hσemk : ∀ x : NumberField.RingOfIntegers ↥K,
      σe (Ideal.Quotient.mk 𝔭.asIdeal x) = Ideal.Quotient.mk 𝔭.asIdeal (ψ x) := by
    intro x
    change σ (Ideal.Quotient.mk 𝔭.asIdeal x) = Ideal.Quotient.mk 𝔭.asIdeal (ψ x)
    rw [hσmk]
  -- (5) the residue class of `r` is fixed by `σe`.
  have hfix : σe (Ideal.Quotient.mk 𝔭.asIdeal r) = Ideal.Quotient.mk 𝔭.asIdeal r := by
    rw [hσemk, Ideal.Quotient.eq, hψapply]
    exact hr
  -- (6) `σe` is an involution.
  have hinvol : Function.Involutive σe := by
    intro z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [hσemk, hσemk]
    congr 1
    exact hψ2 y
  -- (7) `σe` is nontrivial, by the unramifiedness witness.
  have hne : σe ≠ 1 := by
    obtain ⟨y, hy⟩ := exists_smul_sub_notMem_of_unramified ρ hρ1 A hA 𝔭 h𝔭 hunram
    intro h
    have h1 : σe (Ideal.Quotient.mk 𝔭.asIdeal y) = Ideal.Quotient.mk 𝔭.asIdeal y := by
      rw [h]; rfl
    rw [hσemk, Ideal.Quotient.eq, hψapply] at h1
    exact hy h1
  -- (8) the finite-field statement.  The `Field` instance is supplied concretely (so that its
  -- `toSemiring` unfolds to `Ideal.Quotient.semiring`, matching the instance used by `σe`).
  exact @isSquare_of_fixed_of_involution (NumberField.RingOfIntegers ↥K ⧸ 𝔭.asIdeal)
    (Ideal.Quotient.field 𝔭.asIdeal)
    (Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum 𝔭)
    σe hinvol hne (Ideal.Quotient.mk 𝔭.asIdeal r) hfix

end Work.SSGRoute.NodeS37
