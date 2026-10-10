import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.H9.swTwoPlacePairingTwo
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.NodeS37

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! ## Auxiliary lemmas

The target is the *Galois invariance* of the local Kummer pairing at `p = 2`: conjugating both the
place and the two Kummer classes by `galLift K τ` does not change the value.

The route is the `p = 2` *norm criterion* of `Work.SSGRoute.H9`:

* `oPairAt` of the Kummer cochains of `α`, `β` at `A` is `oPairGlob α β`
  (`oPair_toClass_eq_oPairGlob`);
* at `p = 2`, `oPairGlob α β = 0` iff the local component of `β` at the prime below `A` is a local
  norm from the Kummer level `K(α^{1/2})` (`oPairGlob_eq_zero_iff_mem_localNormSubgroup`), which for
  non-square `α` is representability by the norm form `X² - ᾱY²` over the completion
  (`mem_localNormSubgroup_iff_normForm`).

The norm form is transported along the canonical local isomorphism
`NK.GlobalCFT.Place.localRingEquiv τ 𝔭 : K_𝔭 ≃+* K_{τ𝔭}`, which sends `ᾱ` to `τᾱ` and the local
component of `β` to that of `τβ` — hence the invariance. -/

section Aux

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
  [IsSepClosure ↥K Ω]

/-! ### `ZMod 2` bookkeeping -/

private lemma zmodTwo_eq_one_of_ne_zero (x : ZMod 2) (hx : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact absurd rfl hx
  · rfl

private lemma zmodTwo_eq_of_iff_eq_zero {x y : ZMod 2} (h : (x = 0) ↔ (y = 0)) : x = y := by
  by_cases hx : x = 0
  · rw [hx, h.mp hx]
  · exact (zmodTwo_eq_one_of_ne_zero x hx).trans
      (zmodTwo_eq_one_of_ne_zero y (fun hh => hx (h.mpr hh))).symm

/-! ### The conjugate of a unit -/

/-- The conjugate unit is the image of `a` under `τ` (a group automorphism of `↥Kˣ`). -/
private lemma conjUnit_galLift_eq (τ : K ≃ₐ[k] K) (a : (↥K)ˣ) :
    Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K τ) a
      = Units.mapEquiv τ.toMulEquiv a := by
  rw [Work.SSGRoute.H9.conjUnit, Work.SSGRoute.ZDataMup.galLift_spec]
  rfl

/-- Conjugation preserves the subgroup of squares. -/
private lemma conjUnit_mem_powSubgroup_iff (τ : K ≃ₐ[k] K) (a : (↥K)ˣ) :
    Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K τ) a ∈
        NK.LocalAnabelian.powSubgroup 2 ↥K
      ↔ a ∈ NK.LocalAnabelian.powSubgroup 2 ↥K := by
  rw [conjUnit_galLift_eq]
  have hpow : ∀ b : (↥K)ˣ, b ∈ NK.LocalAnabelian.powSubgroup 2 ↥K ↔ ∃ d, d * d = b := by
    intro b
    simp only [NK.LocalAnabelian.powSubgroup, MonoidHom.mem_range, powMonoidHom_apply, pow_two]
  rw [hpow, hpow]
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨(Units.mapEquiv τ.toMulEquiv).symm d, ?_⟩
    have h1 : (Units.mapEquiv τ.toMulEquiv) ((Units.mapEquiv τ.toMulEquiv).symm d *
        (Units.mapEquiv τ.toMulEquiv).symm d) = d * d := by
      rw [map_mul, MulEquiv.apply_symm_apply]
    exact (Units.mapEquiv τ.toMulEquiv).injective (by rw [h1, hd])
  · rintro ⟨d, hd⟩
    exact ⟨Units.mapEquiv τ.toMulEquiv d, by rw [← map_mul, hd]⟩

/-! ### The prime of `↥K` below the conjugate place -/

/-- **`galLift K τ` acts on the valuation subrings of `↥K` through `τ`.** -/
private lemma comap_galLift_smul (τ : K ≃ₐ[k] K) (Q : ValuationSubring Ω) :
    (Work.SSGRoute.ZDataMup.galLift K τ • Q).comap (algebraMap ↥K Ω) =
      τ • (Q.comap (algebraMap ↥K Ω)) := by
  ext x
  have hpt : (Work.SSGRoute.ZDataMup.galLift K τ)⁻¹ • (algebraMap ↥K Ω x)
      = algebraMap ↥K Ω (τ⁻¹ • x) := by
    rw [AlgEquiv.smul_def, AlgEquiv.smul_def]
    rw [← Work.SSGRoute.algebraMap_restrictNormalHom (K := K)
      ((Work.SSGRoute.ZDataMup.galLift K τ)⁻¹) x]
    congr 1
    rw [map_inv, Work.SSGRoute.ZDataMup.galLift_spec]
  rw [ValuationSubring.mem_comap]
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  rw [ValuationSubring.mem_comap, hpt]

/-- **The prime of `𝓞 ↥K` below `galLift K τ • A` is the transport of the prime below `A`.** -/
private lemma hPrimeBelow_galLift_smul (τ : K ≃ₐ[k] K) (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A)
    (hA' : SSGRoute.IsFinPlace k (Work.SSGRoute.ZDataMup.galLift K τ • A)) :
    Work.SSGRoute.ZDataMup.LTRecFamHonest.hPrimeBelow (K := K)
        (Work.SSGRoute.ZDataMup.galLift K τ • A) hA'
      = NK.GlobalCFT.Place.smulHeightOneSpectrum τ
          (Work.SSGRoute.ZDataMup.LTRecFamHonest.hPrimeBelow (K := K) A hA) := by
  have hplace : Work.SSGRoute.ZDataMup.LTRecFamHonest.hPrimeBelow (K := K)
        (Work.SSGRoute.ZDataMup.galLift K τ • A) hA'
      = Commons.NumberTheory.NumberField.Completion.placeSmul τ
          (Work.SSGRoute.ZDataMup.LTRecFamHonest.hPrimeBelow (K := K) A hA) := by
    apply Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
      (R := NumberField.RingOfIntegers ↥K) (K := ↥K)
    rw [← Commons.NumberTheory.RamificationInertia.smul_valuationSubringAtPrime_eq_map_galRestrict
      (Work.SSGRoute.ZDataMup.LTRecFamHonest.hPrimeBelow (K := K) A hA)
      (Commons.NumberTheory.NumberField.Completion.placeSmul τ
        (Work.SSGRoute.ZDataMup.LTRecFamHonest.hPrimeBelow (K := K) A hA)) τ
      (Commons.NumberTheory.NumberField.Completion.placeSmul_asIdeal τ _)]
    rw [← Submission.NeukirchUchida.primeOf_spec A
        (Work.SSGRoute.ZConstruction.isFinPlace_of_isFinPlace_below (K := K) (A := A) hA),
      ← Submission.NeukirchUchida.primeOf_spec (Work.SSGRoute.ZDataMup.galLift K τ • A)
        (Work.SSGRoute.ZConstruction.isFinPlace_of_isFinPlace_below (K := K)
          (A := Work.SSGRoute.ZDataMup.galLift K τ • A) hA')]
    exact comap_galLift_smul (K := K) τ A
  rw [hplace, NK.GlobalCFT.Inclusion.globalCFT_placeSmul_eq_smulHeightOneSpectrum τ
    (Work.SSGRoute.ZDataMup.LTRecFamHonest.hPrimeBelow (K := K) A hA)]

/-! ### The local transports along `localRingEquiv` -/

/-- **The local component of a conjugate unit is the transport of the local component.** -/
private lemma localImageAt_conjUnit_galLift (τ : K ≃ₐ[k] K) (b : (↥K)ˣ)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K)) :
    NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
        (τ • (NK.GlobalCFT.Place.ofFinite 𝔭 : NK.GlobalCFT.Place ↥K))
        (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K τ) b)
      = Units.map (NK.GlobalCFT.Place.localRingEquiv τ
          (NK.GlobalCFT.Place.ofFinite 𝔭)).toMonoidHom
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) b) := by
  rw [NK.CFTLib.IdeleHasse.localImageAt, NK.CFTLib.IdeleHasse.localImageAt,
    show Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K τ) b
      = Units.map τ.toMulEquiv.toMonoidHom b from by
    rw [Work.SSGRoute.H9.conjUnit, Work.SSGRoute.ZDataMup.galLift_spec]]
  apply Units.ext
  simp only [Units.coe_map]
  change (algebraMap ↥K (NK.GlobalCFT.Place.localField ↥K
        (τ • NK.GlobalCFT.Place.ofFinite 𝔭))) (τ (b : ↥K))
    = (NK.GlobalCFT.Place.localRingEquiv τ (NK.GlobalCFT.Place.ofFinite 𝔭))
      ((algebraMap ↥K (NK.GlobalCFT.Place.localField ↥K
        (NK.GlobalCFT.Place.ofFinite 𝔭))) (b : ↥K))
  exact (NK.GlobalCFT.Place.localRingEquiv_algebraMap τ (NK.GlobalCFT.Place.ofFinite 𝔭)
    (b : ↥K)).symm

/-- **The element-level form of the previous transport.** -/
private lemma algebraMap_conjUnit_galLift (τ : K ≃ₐ[k] K) (a : (↥K)ˣ)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K)) :
    (algebraMap ↥K (NK.GlobalCFT.Place.localField ↥K
        (τ • (NK.GlobalCFT.Place.ofFinite 𝔭 : NK.GlobalCFT.Place ↥K))))
        ((Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K τ) a : (↥K)ˣ) : ↥K)
      = (NK.GlobalCFT.Place.localRingEquiv τ (NK.GlobalCFT.Place.ofFinite 𝔭))
          (algebraMap ↥K (NK.GlobalCFT.Place.localField ↥K (NK.GlobalCFT.Place.ofFinite 𝔭))
            (a : ↥K)) := by
  rw [show Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K τ) a
      = Units.map τ.toMulEquiv.toMonoidHom a from by
    rw [Work.SSGRoute.H9.conjUnit, Work.SSGRoute.ZDataMup.galLift_spec]]
  rw [Units.coe_map]
  exact (NK.GlobalCFT.Place.localRingEquiv_algebraMap τ (NK.GlobalCFT.Place.ofFinite 𝔭)
    (a : ↥K)).symm

/-! ### The norm-form transport -/

/-- **The element-level form of the local transport** (the coercion of the previous lemma). -/
private lemma localImageAt_conjUnit_galLift_coe (τ : K ≃ₐ[k] K) (b : (↥K)ˣ)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K)) :
    ((NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
        (τ • (NK.GlobalCFT.Place.ofFinite 𝔭 : NK.GlobalCFT.Place ↥K))
        (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K τ) b) :
          (NK.GlobalCFT.Place.localField ↥K
            (τ • (NK.GlobalCFT.Place.ofFinite 𝔭 : NK.GlobalCFT.Place ↥K)))ˣ) :
        NK.GlobalCFT.Place.localField ↥K
          (τ • (NK.GlobalCFT.Place.ofFinite 𝔭 : NK.GlobalCFT.Place ↥K)))
      = (NK.GlobalCFT.Place.localRingEquiv τ (NK.GlobalCFT.Place.ofFinite 𝔭))
          ((NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) b :
            (NK.GlobalCFT.Place.localField ↥K (NK.GlobalCFT.Place.ofFinite 𝔭))ˣ) :
            NK.GlobalCFT.Place.localField ↥K (NK.GlobalCFT.Place.ofFinite 𝔭)) := by
  have h := congrArg (fun u : (NK.GlobalCFT.Place.localField ↥K
      (τ • (NK.GlobalCFT.Place.ofFinite 𝔭 : NK.GlobalCFT.Place ↥K)))ˣ =>
        (u : NK.GlobalCFT.Place.localField ↥K
          (τ • (NK.GlobalCFT.Place.ofFinite 𝔭 : NK.GlobalCFT.Place ↥K))))
    (localImageAt_conjUnit_galLift (K := K) τ b 𝔭)
  simpa using h

/-- The norm form `X² - cY² = d` is transported along a ring isomorphism. -/
private theorem exists_normForm_map_iff {F F' : Type} [Field F] [Field F'] (φ : F ≃+* F')
    (c d : F) :
    (∃ u v : F, u ^ 2 - c * v ^ 2 = d) ↔ (∃ u v : F', u ^ 2 - φ c * v ^ 2 = φ d) := by
  constructor
  · rintro ⟨u, v, huv⟩
    exact ⟨φ u, φ v, by rw [← map_pow, ← map_pow, ← map_mul, ← map_sub, huv]⟩
  · rintro ⟨u, v, huv⟩
    refine ⟨φ.symm u, φ.symm v, ?_⟩
    apply φ.injective
    rw [map_sub, map_mul, map_pow, map_pow]
    simp only [RingEquiv.apply_symm_apply]
    exact huv

/-! ### The pairing of Kummer cochains is the pairing of the global units -/

/-- **`oPairAt` of the Kummer cochains of two global units is `oPairGlob` of those units.**  This is
`oPair_toClass_eq_oPairGlob` with the cocycle, local-constancy and character hypotheses supplied by
the Kummer cochain. -/
private theorem oPairAt_eq_oPairGlob_aux (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (α β : (↥K)ˣ) (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) A hA
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β)
      = Work.SSGRoute.ZDataMup.OddForm.oPairGlob (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
        hA α β := by
  rw [Work.SSGRoute.ZDataMup.OddForm.oPairAt]
  refine Work.SSGRoute.ZDataMup.OddForm.oPair_toClass_eq_oPairGlob (K := K) (p := 2) (k := k)
    (Ω := Ω) (ζ := (⟨ζ, hζK⟩ : ↥K))
    (hζ := Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) (hA := hA)
    _ _ α β ?_ ?_ ?_ ?_ ?_ ?_
  · intro g hg h hh
    rw [Work.SSGRoute.ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ α g hg h hh]
    have hg1 : SSGRoute.res k K g = 1 := by
      rw [← MonoidHom.mem_ker]
      rw [show (SSGRoute.res k K).ker = K.fixingSubgroup from
        IntermediateField.restrictNormalHom_ker K]
      exact hg
    rw [hg1, one_smul]
  · exact Work.SSGRoute.ZSplit.nodeKummerCocharZMod_locConst K ζ hζK hζ α
  · intro g hg h hh
    rw [Work.SSGRoute.ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ β g hg h hh]
    have hg1 : SSGRoute.res k K g = 1 := by
      rw [← MonoidHom.mem_ker]
      rw [show (SSGRoute.res k K).ker = K.fixingSubgroup from
        IntermediateField.restrictNormalHom_ker K]
      exact hg
    rw [hg1, one_smul]
  · exact Work.SSGRoute.ZSplit.nodeKummerCocharZMod_locConst K ζ hζK hζ β
  · intro σ hσ
    exact Work.SSGRoute.ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK)
      (hζ := hζ) (β := α) hσ
  · intro σ hσ
    exact Work.SSGRoute.ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK)
      (hζ := hζ) (β := β) hσ

/-- **The norm-form transfer along `localRingEquiv`.**  The two norm-form statements for the pair
`(conjUnit τ a, conjUnit τ b)` at the conjugate prime and for `(a, b)` at `𝔭` are equivalent. -/
private lemma normForm_transport (τ : K ≃ₐ[k] K) (a b : (↥K)ˣ)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K)) :
    (∃ u v : (NK.GlobalCFT.Place.smulHeightOneSpectrum τ 𝔭).adicCompletion ↥K,
        u ^ 2 - (algebraMap ↥K ((NK.GlobalCFT.Place.smulHeightOneSpectrum τ 𝔭).adicCompletion ↥K)
            ((Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K τ) a : (↥K)ˣ) : ↥K))
          * v ^ 2
          = ((NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
              (NK.GlobalCFT.Place.ofFinite (NK.GlobalCFT.Place.smulHeightOneSpectrum τ 𝔭))
              (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K τ) b) :
              ((NK.GlobalCFT.Place.smulHeightOneSpectrum τ 𝔭).adicCompletion ↥K)ˣ) :
              (NK.GlobalCFT.Place.smulHeightOneSpectrum τ 𝔭).adicCompletion ↥K))
      ↔ (∃ u v : 𝔭.adicCompletion ↥K,
        u ^ 2 - (algebraMap ↥K (𝔭.adicCompletion ↥K) (a : ↥K)) * v ^ 2
          = ((NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) b :
              (𝔭.adicCompletion ↥K)ˣ) : 𝔭.adicCompletion ↥K)) := by
  show (∃ u v : NK.GlobalCFT.Place.localField ↥K
          (τ • (NK.GlobalCFT.Place.ofFinite 𝔭 : NK.GlobalCFT.Place ↥K)),
        u ^ 2 - (algebraMap ↥K (NK.GlobalCFT.Place.localField ↥K
            (τ • (NK.GlobalCFT.Place.ofFinite 𝔭 : NK.GlobalCFT.Place ↥K)))
            ((Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K τ) a : (↥K)ˣ) : ↥K))
          * v ^ 2
          = ((NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
              (τ • (NK.GlobalCFT.Place.ofFinite 𝔭 : NK.GlobalCFT.Place ↥K))
              (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K τ) b) :
              (NK.GlobalCFT.Place.localField ↥K
                (τ • (NK.GlobalCFT.Place.ofFinite 𝔭 : NK.GlobalCFT.Place ↥K)))ˣ) :
              NK.GlobalCFT.Place.localField ↥K
                (τ • (NK.GlobalCFT.Place.ofFinite 𝔭 : NK.GlobalCFT.Place ↥K))))
      ↔ (∃ u v : NK.GlobalCFT.Place.localField ↥K (NK.GlobalCFT.Place.ofFinite 𝔭),
        u ^ 2 - (algebraMap ↥K (NK.GlobalCFT.Place.localField ↥K
            (NK.GlobalCFT.Place.ofFinite 𝔭)) (a : ↥K)) * v ^ 2
          = ((NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
              (NK.GlobalCFT.Place.ofFinite 𝔭) b :
              (NK.GlobalCFT.Place.localField ↥K (NK.GlobalCFT.Place.ofFinite 𝔭))ˣ) :
              NK.GlobalCFT.Place.localField ↥K (NK.GlobalCFT.Place.ofFinite 𝔭)))
  rw [algebraMap_conjUnit_galLift (K := K) τ a 𝔭,
    localImageAt_conjUnit_galLift_coe (K := K) τ b 𝔭]
  exact (exists_normForm_map_iff (NK.GlobalCFT.Place.localRingEquiv τ
      (NK.GlobalCFT.Place.ofFinite 𝔭))
    (algebraMap ↥K (NK.GlobalCFT.Place.localField ↥K (NK.GlobalCFT.Place.ofFinite 𝔭))
      (a : ↥K))
    ((NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) b :
        (NK.GlobalCFT.Place.localField ↥K (NK.GlobalCFT.Place.ofFinite 𝔭))ˣ) :
        NK.GlobalCFT.Place.localField ↥K (NK.GlobalCFT.Place.ofFinite 𝔭))).symm

end Aux

theorem oPairAt_smul_conj {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (a b : (↥K)ˣ) (τ : K ≃ₐ[k] K)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hA' : SSGRoute.IsFinPlace k (Work.SSGRoute.ZDataMup.galLift K τ • A))
    [FiniteDimensional ↥K ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) a)]
    [IsGalois ↥K ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) a)]
    [NumberField ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) a)]
    [FiniteDimensional ↥K ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2)
      (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K τ) a))]
    [IsGalois ↥K ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2)
      (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K τ) a))]
    [NumberField ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2)
      (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K τ) a))] :
    Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
        (Work.SSGRoute.ZDataMup.galLift K τ • A) hA'
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ
          (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K τ) a))
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ
          (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K τ) b))
      = Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
        A hA (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b) := by
  have hL := oPairAt_eq_oPairGlob_aux (K := K) (k := k) (Ω := Ω) ζ hζ hζK
    (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K τ) a)
    (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K τ) b)
    (Work.SSGRoute.ZDataMup.galLift K τ • A) hA'
  have hR := oPairAt_eq_oPairGlob_aux (K := K) (k := k) (Ω := Ω) ζ hζ hζK a b A hA
  rw [hL, hR]
  by_cases ha : a ∈ NK.LocalAnabelian.powSubgroup 2 ↥K
  · rw [Work.SSGRoute.H9.oPairGlob_eq_zero_of_mem_powSubgroup_fst (K := K) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
        (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K τ) a)
        (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K τ) b)
        (Work.SSGRoute.ZDataMup.galLift K τ • A) hA'
        ((conjUnit_mem_powSubgroup_iff (K := K) τ a).mpr ha),
      Work.SSGRoute.H9.oPairGlob_eq_zero_of_mem_powSubgroup_fst (K := K) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
        a b A hA ha]
  · have hna : Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K τ) a ∉
        NK.LocalAnabelian.powSubgroup 2 ↥K :=
      fun h => ha ((conjUnit_mem_powSubgroup_iff (K := K) τ a).mp h)
    refine zmodTwo_eq_of_iff_eq_zero ?_
    rw [Work.SSGRoute.H9.oPairGlob_eq_zero_iff_mem_localNormSubgroup (K := K) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
        (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K τ) a)
        (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K τ) b)
        (Work.SSGRoute.ZDataMup.galLift K τ • A) hA' hna,
      Work.SSGRoute.H9.oPairGlob_eq_zero_iff_mem_localNormSubgroup (K := K) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
        a b A hA ha]
    rw [Work.SSGRoute.H9.mem_localNormSubgroup_iff_normForm (K := K) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
        (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K τ) a)
        (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K τ) b)
        (Work.SSGRoute.ZDataMup.galLift K τ • A) hA' hna,
      Work.SSGRoute.H9.mem_localNormSubgroup_iff_normForm (K := K) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
        a b A hA ha]
    rw [hPrimeBelow_galLift_smul (K := K) τ A hA hA']
    exact normForm_transport (K := K) τ a b
      (Work.SSGRoute.ZDataMup.LTRecFamHonest.hPrimeBelow (K := K) A hA)

end Work.SSGRoute.NodeS37
