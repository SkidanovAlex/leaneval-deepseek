import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.place_basics
import Submission.Work.SSGRoute.primeOfLevel_mem_iff_k
import Submission.Work.SSGRoute.ringOfIntegers_mem_of_isFinPlace_k
import Submission.Work.SSGRoute.exists_finiteDimensional_normal_fixingSubgroup_le
import Submission.NeukirchUchida.PrimeCorrespondence
import Submission.NeukirchUchida.Local.PlaceFromValuation
import Submission.NK.ResidueFrob.primeOfLevel_liesOver
import Submission.Work.LocalFields.finite_ramified_primes_extension
import Submission.Work.LocalFields.isUnramifiedAt_iff_ramificationIdxIn_eq_one
import Submission.Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
import Submission.Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

open scoped NumberField

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-! ## Auxiliary facts about places, levels and inertia

The finiteness statement below (`ramifiedPlaces_finite_k_aux`) needs the general-number-field
form of "the inertia of a place maps to the level inertia of the prime below it"
(`restrictNormalHom_mem_inertia_k`) and of "the level prime lies over the prime of the base field"
(`NK.ResidueFrob.primeOfLevel_liesOver`). -/

section Places

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]

/-- The image of an element of the ring of integers of a finite normal level under the restriction
of a `k`-automorphism of `Ω`: general form of
`Work.SSGRoute.restrictNormalHom_smul_coe`. -/
theorem restrictNormalHom_smul_coe_k (M : IntermediateField k Ω) [FiniteDimensional k M]
    [Normal k M] (σ : Ω ≃ₐ[k] Ω) (x : NumberField.RingOfIntegers ↥M) :
    ((AlgEquiv.restrictNormalHom ↥M (F := k) (K₁ := Ω) σ • x :
        NumberField.RingOfIntegers ↥M) : Ω) = σ (x : Ω) := by
  have h1 : ((AlgEquiv.restrictNormalHom ↥M (F := k) (K₁ := Ω) σ • x :
        NumberField.RingOfIntegers ↥M) : ↥M)
      = (AlgEquiv.restrictNormalHom ↥M (F := k) (K₁ := Ω) σ) (x : ↥M) := rfl
  rw [h1]
  rw [show (AlgEquiv.restrictNormalHom ↥M (F := k) (K₁ := Ω) σ) (x : ↥M)
      = AlgEquiv.restrictNormal σ ↥M (x : ↥M) from rfl]
  exact @AlgEquiv.restrictNormal_apply k _ Ω _ _ M _ σ (x : ↥M)

/-- **The inertia of a place maps to the ideal-theoretic inertia of the prime below it.**

General-number-field form of `Work.SSGRoute.mem_inertia_of_isInertia`. -/
theorem restrictNormalHom_mem_inertia_k [IsSepClosure k Ω]
    (M : IntermediateField k Ω) [FiniteDimensional k M] [Normal k M]
    (B : ValuationSubring Ω) (hB : SSGRoute.IsFinPlace k B)
    {σ : Ω ≃ₐ[k] Ω} (hσ : SSGRoute.IsInertia k B σ) :
    AlgEquiv.restrictNormalHom ↥M (F := k) (K₁ := Ω) σ ∈
      Ideal.inertia (↥M ≃ₐ[k] ↥M)
        (NK.Reconstruct.primeOfLevel B M (NK.Reconstruct.comap_level_ne_top hB M)).asIdeal := by
  rw [AddSubgroup.mem_inertia]
  intro x
  change (AlgEquiv.restrictNormalHom ↥M (F := k) (K₁ := Ω) σ • x - x) ∈
    (NK.Reconstruct.primeOfLevel B M (NK.Reconstruct.comap_level_ne_top hB M)).asIdeal
  rw [primeOfLevel_mem_iff_k k Ω B hB M]
  have h2 : algebraMap (NumberField.RingOfIntegers ↥M) Ω
      (AlgEquiv.restrictNormalHom ↥M (F := k) (K₁ := Ω) σ • x) = σ (x : Ω) :=
    restrictNormalHom_smul_coe_k M σ x
  rw [map_sub, h2]
  exact hσ.2 _ (ringOfIntegers_mem_of_isFinPlace_k k Ω B hB M x)

/-- A `k`-automorphism of `Ω` which does not fix a finite normal level `M` pointwise restricts to
a nontrivial element of `Gal(M/k)`. -/
theorem restrictNormalHom_ne_one_k (M : IntermediateField k Ω) [Normal k M]
    {σ : Ω ≃ₐ[k] Ω} (h : σ ∉ M.fixingSubgroup) :
    AlgEquiv.restrictNormalHom ↥M (F := k) (K₁ := Ω) σ ≠ 1 := by
  intro h1
  refine h ?_
  have h2 : σ ∈ (AlgEquiv.restrictNormalHom ↥M (F := k) (K₁ := Ω)).ker := MonoidHom.mem_ker.mpr h1
  rwa [IntermediateField.restrictNormalHom_ker (K := k) (L := Ω) M] at h2

/-- **A prime of a finite Galois extension of number fields with nontrivial inertia is
ramified**: an inertia subgroup inside the decomposition group is trivial exactly when the
ramification index of the prime below is `1`. -/
theorem not_isUnramifiedAt_of_inertia_ne_bot {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (v : Work.LocalFields.FinitePrime K) (w : Work.LocalFields.FinitePrime L)
    (hw : w.asIdeal.LiesOver v.asIdeal)
    (h : Ideal.inertia (L ≃ₐ[K] L) w.asIdeal ≠ ⊥) :
    ¬ Work.LocalFields.IsUnramifiedAt K w := by
  intro hbot
  apply h
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hxD : x ∈ Work.LocalFields.decompositionGroup K w :=
    Ideal.inertia_le_stabilizer w.asIdeal hx
  have hxI : (⟨x, hxD⟩ : Work.LocalFields.decompositionGroup K w) ∈
      Work.LocalFields.inertiaSubgroup K w := hx
  have h1 : (⟨x, hxD⟩ : Work.LocalFields.decompositionGroup K w) ∈ (⊥ :
      Subgroup (Work.LocalFields.decompositionGroup K w)) := hbot ▸ hxI
  exact congrArg Subtype.val (Subgroup.mem_bot.mp h1)

/-- **Only finitely many conjugacy classes of finite places of `Ω` ramify in a finite Galois
extension `N/k`.**  General-number-field form of `Work.SSGRoute.ramifiedPlaces_finite` (the case
`k = ℚ`) and of `Work.SSGRoute.ramifiedPlaces_finite_over_K`. -/
theorem ramifiedPlaces_finite_k_aux (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (N : IntermediateField k Ω) [FiniteDimensional k N] [IsGalois k N] :
    ∃ S : Finset (ValuationSubring Ω),
      (∀ A ∈ S, SSGRoute.IsFinPlace k A) ∧
      (∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B) ∧
      ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        SSGRoute.IsRamifiedIn k N B → ∃ A ∈ S, SSGRoute.IsConjPlace k A B := by
  classical
  haveI hSep : IsSepClosure k Ω := inferInstance
  haveI hNorm : Normal k N := (inferInstance : IsGalois k N).to_normal
  -- the finitely many primes of `k` below a prime of `N` ramified over `k`
  let V : Set (Work.LocalFields.FinitePrime k) :=
    {v | ∃ w : Work.LocalFields.FinitePrime ↥N,
        w.asIdeal.LiesOver v.asIdeal ∧ ¬ Work.LocalFields.IsUnramifiedAt k w}
  have hVfin : V.Finite :=
    Work.LocalFields.finite_ramified_primes_extension (K := k) (L := ↥N)
  refine ⟨hVfin.toFinset.image
    (fun v => (Submission.NeukirchUchida.placeOver (K₁ := k) (K₁' := Ω) v).1), ?_, ?_, ?_⟩
  · intro A hA
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hA
    show (Submission.NeukirchUchida.placeOver (K₁ := k) (K₁' := Ω) v).1.comap
        (algebraMap k Ω) ≠ ⊤
    rw [Submission.NeukirchUchida.placeOver_spec]
    exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top v
  · intro A hA B hB hconj
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨v', -, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨σ, hσ⟩ := hconj
    have hcomap : (Submission.NeukirchUchida.placeOver (K₁ := k) (K₁' := Ω) v).1.comap
          (algebraMap k Ω) =
        (Submission.NeukirchUchida.placeOver (K₁ := k) (K₁' := Ω) v').1.comap
          (algebraMap k Ω) := by
      rw [← hσ]
      exact (Commons.NumberTheory.NumberField.Valuation.comap_smul_algebraMap
        (Submission.NeukirchUchida.placeOver (K₁ := k) (K₁' := Ω) v).1 σ).symm
    rw [Submission.NeukirchUchida.placeOver_spec,
      Submission.NeukirchUchida.placeOver_spec] at hcomap
    obtain rfl : v = v' :=
      Commons.RingTheory.Valuation.valuationSubringAtPrime_injective hcomap
    rfl
  · intro B hB hram
    obtain ⟨σ, hσI, hσN⟩ := hram
    set P : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥N) :=
      NK.Reconstruct.primeOfLevel B N (NK.Reconstruct.comap_level_ne_top hB N) with hPdef
    have hLies : P.asIdeal.LiesOver (Submission.NeukirchUchida.primeOf B hB).asIdeal :=
      NK.ResidueFrob.primeOfLevel_liesOver (K := k) (K' := Ω) ⟨B, hB⟩ N
    have hmem : AlgEquiv.restrictNormalHom ↥N (F := k) (K₁ := Ω) σ ∈
        Ideal.inertia (↥N ≃ₐ[k] ↥N) P.asIdeal :=
      restrictNormalHom_mem_inertia_k N B hB hσI
    have hne : AlgEquiv.restrictNormalHom ↥N (F := k) (K₁ := Ω) σ ≠ 1 :=
      restrictNormalHom_ne_one_k N hσN
    have hnebot : Ideal.inertia (↥N ≃ₐ[k] ↥N) P.asIdeal ≠ ⊥ := by
      intro hbot
      exact hne (Subgroup.mem_bot.mp (hbot ▸ hmem))
    refine ⟨(Submission.NeukirchUchida.placeOver (K₁ := k) (K₁' := Ω)
      (Submission.NeukirchUchida.primeOf B hB)).1, ?_, ?_⟩
    · refine Finset.mem_image.mpr ⟨Submission.NeukirchUchida.primeOf B hB, ?_, rfl⟩
      rw [Set.Finite.mem_toFinset hVfin]
      exact ⟨P, hLies, not_isUnramifiedAt_of_inertia_ne_bot (K := k) (L := ↥N) _ _ hLies hnebot⟩
    · exact Submission.NeukirchUchida.exists_smul_eq_of_comap_eq' (K₁ := k) (K₁' := Ω)
        (Submission.NeukirchUchida.placeOver (K₁ := k) (K₁' := Ω)
          (Submission.NeukirchUchida.primeOf B hB)).2
        (by rw [Submission.NeukirchUchida.placeOver_spec,
          Submission.NeukirchUchida.primeOf_spec B hB])

end Places

/-- **Only finitely many places have nontrivial inertia for a locally constant cocycle.**

Let `k` be a number field, `Ω` an algebraic closure, `K/k` finite Galois, `M` a
`Gal(K/k)`-module (no finiteness needed), and `f : G_k → M` a locally constant crossed
homomorphism.  Then, up to conjugacy, there are only finitely many finite places `B` at which `f`
fails to vanish on the inertia subgroup `I_B`; equivalently there is a finite set `S` of pairwise
non-conjugate finite places such that every finite place `B` outside the conjugates of `S` satisfies
`f σ = 0` for all `σ ∈ I_B`.

*Why true*: `IsLocConstOn ⊤ f` gives an open subgroup `U ≤ G_k` with `f (g * u) = f g` for all
`g` and `u ∈ U`; the cocycle identity at `u * u'` (`u, u' ∈ U`) together with this constancy shows
`f u = 0` for every `u ∈ U` (as `f (u * u') = f u` while `f (u * u') = f u + res(u) • f u'`, and
`res(u) • f u' = 0` follows by the same identity with `u := u`, `u' := u`).  So `f` vanishes on the
fixed field `F = Ω^U` of the open subgroup `U`, which is finite over `k`; and `I_B ⊆ G_F = U`
whenever `B` is unramified in `F/k`.  Only finitely many places of `k` ramify in the finite
extension `F`, so the places where `f` can fail to vanish on `I_B` are finite up to conjugacy.

This is the finiteness input used by the reciprocity ("easy") half of
`Work.SSGRoute.pt_selmer_relaxed`: the reciprocity law `hrec` may be applied with a finite set of
places `S'` only if one knows that the places where the two global cocycles fail to vanish on
inertia can be finitely enumerated.  (The `k = ℚ` case is `Work.SSGRoute.ramifiedPlaces_finite`.) -/
theorem vanishingInertia_finite (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [DistribMulAction (K ≃ₐ[k] K) M]
    (f : (Ω ≃ₐ[k] Ω) → M)
    (hf : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ f)
    (hlc : SSGRoute.IsLocConstOn ⊤ f) :
    ∃ S : Finset (ValuationSubring Ω),
      (∀ A ∈ S, SSGRoute.IsFinPlace k A) ∧
      (∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B) ∧
      ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) →
        ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → f σ = 0 := by
  classical
  -- Step 1.  The locally constant cocycle is constant on the cosets of an open subgroup.
  obtain ⟨U, hUopen, hUc⟩ := hlc
  have hUc' : ∀ g : Ω ≃ₐ[k] Ω, ∀ u ∈ U, f (g * u) = f g :=
    fun g u hu => hUc g trivial u hu trivial
  -- Step 2.  `f` vanishes on `U`.
  have hfzero : ∀ u ∈ U, f u = 0 := by
    intro u hu
    have h1 : f (u * u) = f u + SSGRoute.res k K u • f u := hf u trivial u trivial
    have h2 : f (u * u) = f u := hUc' u u hu
    have h3 : SSGRoute.res k K u • f u = 0 := by
      have h4 : f u + (0 : M) = f u + SSGRoute.res k K u • f u := by
        rw [add_zero]
        exact (h1.symm.trans h2).symm
      exact (add_left_cancel h4).symm
    have h5 : f u = (SSGRoute.res k K u)⁻¹ • (SSGRoute.res k K u • f u) := by
      rw [← mul_smul, inv_mul_cancel, one_smul]
    rw [h5, h3, smul_zero]
  -- Step 3.  A finite Galois level whose fixing subgroup is contained in `U`.
  haveI : IsGalois k Ω := inferInstance
  obtain ⟨N, hNfin, hNnorm, hNle⟩ :=
    exists_finiteDimensional_normal_fixingSubgroup_le U hUopen
  haveI : FiniteDimensional k N := hNfin
  haveI : Normal k N := hNnorm
  -- Step 4.  The finitely many ramified places.
  obtain ⟨S, hSfin, hSdisj, hSram⟩ := ramifiedPlaces_finite_k_aux k Ω N
  refine ⟨S, hSfin, hSdisj, ?_⟩
  intro B hB hconj σ hσ
  have hnotram : ¬ SSGRoute.IsRamifiedIn k N B := by
    intro hram
    obtain ⟨A, hA, hc⟩ := hSram B hB hram
    exact (hconj A hA) hc
  have hσN : σ ∈ N.fixingSubgroup :=
    mem_fixingSubgroup_of_isInertia_of_not_isRamifiedIn N B hnotram σ hσ
  exact hfzero σ (hNle hσN)

end Work.SSGRoute.PT
