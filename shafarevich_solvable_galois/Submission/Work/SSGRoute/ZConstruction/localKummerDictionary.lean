import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.grunwald_kummer_idx
import Submission.Work.SSGRoute.GrunwaldTwoDefs
import Submission.NK.UchidaKummer.Defs
import Submission.NK.UchidaKummer.Kummer.localDeg_kummerField_eq_one_iff
import Submission.NK.UchidaKummer.API.splitsCompletely_iff_forall_localDeg_eq_one
import Submission.NK.Reconstruct.stabilizer_le_fixingSubgroup_iff_splitCompletely
import Submission.NK.GlobalCFTdeep.SecondInequality.finrank_kummerAdjoin
import Submission.NK.LocalAnabelian.Kummer.isGalois_kummerField_and_finrank
import Submission.NK.LocalAnabelian.Kummer.kummerField_eq_bot_of_mem_powSubgroup
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local Kummer dictionary

`Work.SSGRoute.local_kummer_dictionary`: for a number field `K`, a prime `p`, a primitive `p`-th
root of unity `ζ ∈ K`, a unit `a ∈ Kˣ`, a finite place `A` of a separable closure `Ω` of `K` and the
prime `𝔭` of `K` below it, the Kummer character of `a` (the global character `σ ↦ σ(√[p]a)/√[p]a`,
encoded as a `ZMod p`-valued cochain, `Work.SSGRoute.kummerCharZMod`) vanishes on the decomposition
group of `A` exactly when `a` is a local `p`-th power at `𝔭` (equivalently, when the local `p`-power
class `NK.UchidaKummer.localPowClass K p 𝔭 a` is trivial).

This is the "local Kummer dictionary" of the `SSGRoute` project: it is the translation step between
the arithmetic of the Kummer extension `K(a^{1/p})/K` (unramified / split / local degree conditions,
`NK.UchidaKummer.Kummer.localDeg_kummerField_eq_one_iff`) and the cochain language in which the
classes of Schmidt--Wingberg §4 are constructed.  It is the `p = 2` statement recorded as
`Work.SSGRoute.kummerChar_eq_zero_iff_local_powClass` in `Submission/Work/SSGRoute/`, here proved
for every prime `p` in the `ZMod p`-valued form.

## Proof

`N := K(a^{1/p})` (`NK.LocalAnabelian.kummerField`), a Galois extension of `K` of degree `p` (or
`N = ⊥` if `a` is a `p`-th power, the case in which both sides are trivial).  By construction of the
Kummer index, the character vanishes at `σ` exactly when `σ` fixes a `p`-th root `α` of `a`, i.e.
when `σ ∈ N.fixingSubgroup`; hence the left-hand side is `decomp A ≤ N.fixingSubgroup`, i.e. `A` is
split in `N`.  The bridge
`NK.Reconstruct.stabilizer_le_fixingSubgroup_iff_splitCompletely` and
`NK.UchidaKummer.API.splitsCompletely_iff_forall_localDeg_eq_one` turn this into "every prime above
`𝔭` in `N` has local degree `1`", and
`NK.UchidaKummer.Kummer.localDeg_kummerField_eq_one_iff` turns *that* into "`a` is a `p`-th power in
`K_𝔭`", i.e. into the triviality of the local `p`-power class.
-/

open scoped Pointwise IntermediateField

namespace Work.SSGRoute

open _root_.SSGRoute

noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]

/-- A chosen `p`-th root in `Ω` of `a ∈ Kˣ`, for a prime `p`. -/
noncomputable def kummerSqrtZMod (p : ℕ) [Fact p.Prime] (a : Kˣ) : Ω :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq (algebraMap K Ω (a : K)) (Fact.out : p.Prime).pos)

theorem kummerSqrtZMod_pow (p : ℕ) [Fact p.Prime] (a : Kˣ) :
    (kummerSqrtZMod (Ω := Ω) p a) ^ p = algebraMap K Ω (a : K) :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (algebraMap K Ω (a : K))
    (Fact.out : p.Prime).pos)

/-- The chosen `p`-th root, as a unit of `Ω`. -/
noncomputable def kummerSqrtUnitZMod (p : ℕ) [Fact p.Prime] (a : Kˣ) : Ωˣ :=
  Units.mk0 (kummerSqrtZMod (Ω := Ω) p a) (by
    intro h
    have h2 := kummerSqrtZMod_pow (Ω := Ω) p a
    rw [h, zero_pow (Fact.out : p.Prime).ne_zero] at h2
    exact (map_ne_zero (algebraMap K Ω)).mpr a.ne_zero h2.symm)

theorem kummerSqrtUnitZMod_pow (p : ℕ) [Fact p.Prime] (a : Kˣ) :
    kummerSqrtUnitZMod (Ω := Ω) p a ^ p = Units.map (algebraMap K Ω) a := by
  refine Units.ext ?_
  simp only [kummerSqrtUnitZMod, Units.val_mk0, Units.val_pow_eq_pow_val, Units.coe_map]
  exact kummerSqrtZMod_pow (Ω := Ω) p a

theorem kummerSqrtUnitZMod_coe (p : ℕ) [Fact p.Prime] (a : Kˣ) :
    (kummerSqrtUnitZMod (Ω := Ω) p a : Ω) = kummerSqrtZMod (Ω := Ω) p a := rfl

/-- **The global Kummer character of `a ∈ Kˣ`**, as a `ZMod p`-valued cochain on `Gal(Ω/K)`:
`σ ↦ σ(√[p]a)/√[p]a`, encoded through the Kummer index `Work.SSGRoute.kummerIdx`. -/
noncomputable def kummerCharZMod (p : ℕ) [Fact p.Prime] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (a : Kˣ) : (Ω ≃ₐ[K] Ω) → ZMod p :=
  fun σ => kummerIdx p hζ a (kummerSqrtUnitZMod (Ω := Ω) p a)
    (kummerSqrtUnitZMod_pow (Ω := Ω) p a) σ

@[simp] theorem kummerCharZMod_apply (p : ℕ) [Fact p.Prime] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (a : Kˣ) (σ : Ω ≃ₐ[K] Ω) :
    kummerCharZMod (Ω := Ω) p hζ a σ =
      kummerIdx p hζ a (kummerSqrtUnitZMod (Ω := Ω) p a)
        (kummerSqrtUnitZMod_pow (Ω := Ω) p a) σ := rfl

end

/-! ## The dictionary -/

section Dictionary

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  [IsAlgClosed Ω]

theorem local_kummer_dictionary (p : ℕ) [Fact p.Prime]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (a : Kˣ) :
    ((∀ σ : Ω ≃ₐ[↥K] Ω, σ ∈ SSGRoute.decomp (k := ↥K) A →
        kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ a σ = 0) ↔
      NK.UchidaKummer.localPowClass ↥K p 𝔭 a = 1) := by
  classical
  haveI hnumK : NumberField ↥K := Commons.NumberTheory.NumberField.numberField_of_intermediateField K
  haveI hsep : IsSepClosure ↥K Ω := ⟨inferInstance, inferInstance⟩
  set N : IntermediateField ↥K Ω := NK.LocalAnabelian.kummerField (K' := Ω) p a with hNdef
  haveI hfdN : FiniteDimensional ↥K N :=
    NK.GlobalCFTdeep.SecondInequality.finiteDimensional_kummerField (p := p) Fact.out hζ a
  haveI hnfN : NumberField ↥N := inferInstance
  -- the chosen `p`-th root and the identification `N = K⟮α⟯`
  have hα : ((kummerSqrtUnitZMod (Ω := Ω) p a : Ω)) ^ p = algebraMap ↥K Ω (a : ↥K) :=
    kummerSqrtZMod_pow (Ω := Ω) p a
  have hNgen : N = (↥K)⟮(kummerSqrtUnitZMod (Ω := Ω) p a : Ω)⟯ := by
    rw [hNdef]
    exact NK.UchidaKummer.Kummer.kummerField_eq_adjoin_simple p Fact.out hζ a hα
  have hmemN : (kummerSqrtUnitZMod (Ω := Ω) p a : Ω) ∈ N := by
    rw [hNgen]
    exact IntermediateField.mem_adjoin_simple_self _ _
  -- the character vanishes exactly on the fixing subgroup of `N`
  have hchar : ∀ σ : Ω ≃ₐ[↥K] Ω,
      kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ a σ = 0 ↔ σ ∈ N.fixingSubgroup := by
    intro σ
    constructor
    · intro hσ
      -- `σ` fixes the chosen root `α`
      have hfixα : σ (kummerSqrtUnitZMod (Ω := Ω) p a : Ω) =
          (kummerSqrtUnitZMod (Ω := Ω) p a : Ω) := by
        have h1 := kummerIdx_spec p hζ a (kummerSqrtUnitZMod (Ω := Ω) p a)
          (kummerSqrtUnitZMod_pow (Ω := Ω) p a) σ
        have h0 : kummerIdx p hζ a (kummerSqrtUnitZMod (Ω := Ω) p a)
            (kummerSqrtUnitZMod_pow (Ω := Ω) p a) σ = 0 := hσ
        have hz0 : (zr (isPrimitiveRoot_mappedRoot (E := Ω) p hζ))
            (Multiplicative.ofAdd (0 : ZMod p)) = 1 := map_one _
        rw [h0, hz0] at h1
        have h1' : Work.Kummer.kummerRatio σ (kummerSqrtUnitZMod (Ω := Ω) p a) = 1 := by
          simpa using h1
        have h2 : σ (kummerSqrtUnitZMod (Ω := Ω) p a : Ω) /
            (kummerSqrtUnitZMod (Ω := Ω) p a : Ω) = 1 := by
          rw [← Work.Kummer.kummerRatio_coe]
          exact congrArg (fun u : Ωˣ => (u : Ω)) h1'
        rw [div_eq_one_iff_eq (Units.ne_zero _)] at h2
        exact h2
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      rw [hNgen] at hx
      obtain ⟨r, s, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff ↥K x).mp hx
      rw [map_div₀,
        show σ ((Polynomial.aeval (kummerSqrtUnitZMod (Ω := Ω) p a : Ω)) r) =
          (Polynomial.aeval (σ (kummerSqrtUnitZMod (Ω := Ω) p a : Ω))) r from
          (Polynomial.aeval_algHom_apply (σ : Ω →ₐ[↥K] Ω) _ r).symm,
        show σ ((Polynomial.aeval (kummerSqrtUnitZMod (Ω := Ω) p a : Ω)) s) =
          (Polynomial.aeval (σ (kummerSqrtUnitZMod (Ω := Ω) p a : Ω))) s from
          (Polynomial.aeval_algHom_apply (σ : Ω →ₐ[↥K] Ω) _ s).symm,
        hfixα]
    · intro hσ
      refine kummerIdx_eq_zero_of_apply_eq p hζ a (kummerSqrtUnitZMod (Ω := Ω) p a)
        (kummerSqrtUnitZMod_pow (Ω := Ω) p a) σ ?_
      exact (IntermediateField.mem_fixingSubgroup_iff N σ).mp hσ _ hmemN
  rw [show (∀ σ : Ω ≃ₐ[↥K] Ω, σ ∈ SSGRoute.decomp (k := ↥K) A →
      kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ a σ = 0) ↔
      SSGRoute.IsSplitIn ↥K N A from
    ⟨fun h σ hσ => (hchar σ).mp (h σ hσ), fun h σ hσ => (hchar σ).mpr (h hσ)⟩]
  by_cases ha : a ∈ NK.LocalAnabelian.powSubgroup p ↥K
  · -- `a` is a global `p`-th power: both sides are trivial
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp (show a ∈ (powMonoidHom p : Kˣ →* Kˣ).range from ha)
    constructor
    · intro _
      rw [show a = u ^ p from hu.symm]
      rw [NK.UchidaKummer.localPowClass, MonoidHom.comp_apply, map_pow,
        QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff _).mpr (MonoidHom.mem_range.mpr
        ⟨Units.map (algebraMap ↥K (𝔭.adicCompletion ↥K)).toMonoidHom u, rfl⟩)
    · intro _ σ _
      have hbot : N = ⊥ := by
        rw [hNdef]
        exact NK.LocalAnabelian.Kummer.kummerField_eq_bot_of_mem_powSubgroup (K' := Ω) p
          Fact.out hζ ha
      rw [hbot, IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      simp only [IntermediateField.mem_bot] at hx
      obtain ⟨c, rfl⟩ := hx
      exact AlgEquiv.commutes σ c
  · -- the generic case: `N/K` is Galois
    haveI hNgal : IsGalois ↥K N :=
      (NK.LocalAnabelian.Kummer.isGalois_kummerField_and_finrank (K' := Ω) p Fact.out hζ a ha).1
    refine (NK.Reconstruct.stabilizer_le_fixingSubgroup_iff_splitCompletely
      (K := ↥K) (K' := Ω) (N := N) 𝔭 A h𝔭).trans ?_
    refine (NK.UchidaKummer.API.splitsCompletely_iff_forall_localDeg_eq_one
      (K := ↥K) (L := ↥N) 𝔭).trans ?_
    refine (NK.UchidaKummer.Kummer.localDeg_kummerField_eq_one_iff p Fact.out hζ a N
      (by rw [hNdef]) 𝔭).trans ?_
    constructor
    · rintro ⟨b, hb⟩
      rw [NK.UchidaKummer.localPowClass, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
      refine (QuotientGroup.eq_one_iff _).mpr (MonoidHom.mem_range.mpr ⟨b, ?_⟩)
      refine Units.ext ?_
      simpa using hb.symm
    · intro h
      rw [NK.UchidaKummer.localPowClass, MonoidHom.comp_apply, QuotientGroup.mk'_apply] at h
      obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp ((QuotientGroup.eq_one_iff _).mp h)
      refine ⟨b, ?_⟩
      have h2 := congrArg (fun u : (𝔭.adicCompletion ↥K)ˣ => (u : 𝔭.adicCompletion ↥K)) hb
      simpa using h2.symm

/-- **The `p = 2` form of the local Kummer dictionary.**  This is the statement recorded as
`Work.SSGRoute.kummerChar_eq_zero_iff_local_powClass` (the vocabulary of
`Work.SSGRoute.grunwald_surjective_two` and of the `p = 2` `z`-data), here proved: for the global
Kummer character `Work.SSGRoute.kummerChar` of `a ∈ Kˣ` attached to the square root of unity `ζ`,
vanishing on the decomposition group of `A` is equivalent to the triviality of the local `2`-power
class of `a` at the prime `𝔭` below `A`. -/
theorem local_kummer_dictionary_two (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (a : Kˣ) :
    ((∀ σ : Ω ≃ₐ[↥K] Ω, σ ∈ SSGRoute.decomp (k := ↥K) A →
        Work.SSGRoute.kummerChar (Ω := Ω) ζ hζ a σ = 0) ↔
      NK.UchidaKummer.localPowClass ↥K 2 𝔭 a = 1) := by
  have hchar_eq : ∀ σ : Ω ≃ₐ[↥K] Ω,
      Work.SSGRoute.kummerChar (Ω := Ω) ζ hζ a σ =
        kummerCharZMod (Ω := Ω) 2 (ζ := ζ) hζ a σ := by
    intro σ
    show kummerIdx 2 hζ a (Work.SSGRoute.kummerSqrt (Ω := Ω) a)
        (Work.SSGRoute.kummerSqrt_pow (Ω := Ω) a) σ =
      kummerIdx 2 hζ a (kummerSqrtUnitZMod (Ω := Ω) 2 a)
        (kummerSqrtUnitZMod_pow (Ω := Ω) 2 a) σ
    exact kummerIdx_congr 2 hζ a _ _ σ
  have hiff : ((∀ σ : Ω ≃ₐ[↥K] Ω, σ ∈ SSGRoute.decomp (k := ↥K) A →
        Work.SSGRoute.kummerChar (Ω := Ω) ζ hζ a σ = 0) ↔
      (∀ σ : Ω ≃ₐ[↥K] Ω, σ ∈ SSGRoute.decomp (k := ↥K) A →
        kummerCharZMod (Ω := Ω) 2 (ζ := ζ) hζ a σ = 0)) :=
    ⟨fun h σ hσ => by rw [← hchar_eq σ]; exact h σ hσ,
      fun h σ hσ => by rw [hchar_eq σ]; exact h σ hσ⟩
  exact hiff.trans (local_kummer_dictionary 2 K ζ hζ A hA 𝔭 h𝔭 a)

end Dictionary

end Work.SSGRoute
