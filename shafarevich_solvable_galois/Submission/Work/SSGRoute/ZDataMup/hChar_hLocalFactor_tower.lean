import Mathlib
import Submission.Work.SSGRoute.ZDataMup.mupOddChar
import Submission.Work.SSGRoute.ZDataMup.mupOddLevel
import Submission.Work.SSGRoute.ZDataMup.LTRecFamHonest.LocalFactor
import Submission.Work.SSGRoute.ZDataMup.ArtinUniqueness.artinMap_restrictNormalHom_eq_abelian
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.surjective_of_frobAtPrime_unramified
import Submission.NK.NUV2.ARL.isOpenNorm
import Submission.NK.Chebotarev.FrobRestriction
import Submission.NK.Chebotarev.IsFrobAtRestrictNormalHomType
import Submission.NK.Chebotarev.ExistsUniqueIsFrobAtPrime
import Submission.NK.Chebotarev.LFunctions
import Submission.NK.CFTLib.Arl.eq_top_of_forall_isFrobAtPrime_of_notMem
import Submission.NK.CFTLib.exists_congruenceSubgroup_le_normImage
import Submission.Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
import Submission.NK.GlobalCFT.Norm.globalCFT_normIdeleHom_trans
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Level compatibility (`tower`) of the Kummer character against the local Artin factor

The descended Kummer character `OddForm.hChar` of `mupOddChar.lean` is defined at a Kummer level
`M ⊇ K(β^{1/p})`.  This file proves that the character is compatible with restriction to a
smaller level `L`, `K(β^{1/p}) ⊆ L ⊆ M`, along the local factor of the global Artin map:

`hChar_M (θ^M_A(ν)) = hChar_L (θ^L_A(ν))`,

i.e. `Work.SSGRoute.ZDataMup.hChar_hLocalFactor_tower`.

The proof has three ingredients.

1. `hChar` is pinned by its values on restrictions of elements of `Gal(Ω/K)`
   (`hChar_apply`), so the two sides can be compared as soon as the local factors are
   compatible under restriction:
   `hChar_restrictNormalHom_apply`.
2. The local factors are compatible because the *Artin maps* are: for `L ≤ M` intermediate
   fields of `Ω`, the restriction `Gal(↥M/F) → Gal(↥L/F)` carries the Artin map of `↥M` to the
   Artin map of `↥L` (`artinMap_restrictNormalHom_of_le`, the port of
   `ArtinUniqueness.artinMap_restrictNormalHom_eq_abelian` to the present setting where `L` and
   `M` are *both* intermediate fields of the same ambient `Ω`, so that `Algebra ↥L ↥M` is not an
   instance and has to be supplied by the caller).
3. The port needs the two transport lemmas
   `isUnramifiedIn_of_tower` (unramifiedness descends along a tower) and
   `frobAtPrime_restrictNormalHom_of_tower` (the restriction of a Frobenius is a Frobenius).
-/

open scoped NumberField
open NumberField IsDedekindDomain

namespace Work.SSGRoute.ZDataMup

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

/-! ## Transport of unramifiedness and of Frobenius elements along a tower -/

/-- **Unramifiedness descends along a tower of number fields.**  If `𝔭` is unramified in the
extension `M / F` of number fields and `F ⊆ L ⊆ M` is a tower, then `𝔭` is unramified in
`L / F`: the ramification indices multiply along the tower, and a prime of `M` above a prime of
`L` above `𝔭` witnesses that `e(𝔮 | 𝔭) = 1`. -/
theorem isUnramifiedIn_of_tower {F L M : Type} [Field F] [NumberField F] [Field L] [NumberField L]
    [Field M] [NumberField M] [Algebra F L] [Algebra L M] [Algebra F M]
    [IsScalarTower F L M] [FiniteDimensional F L] [FiniteDimensional L M] [FiniteDimensional F M]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (hunr : NK.HeckeL.IsUnramifiedIn (K := F) (L := M) 𝔭) :
    NK.HeckeL.IsUnramifiedIn (K := F) (L := L) 𝔭 := by
  intro 𝔮 h𝔮
  haveI : IsScalarTower (𝓞 F) (𝓞 L) (𝓞 M) := inferInstance
  haveI : Module.Flat (𝓞 L) (𝓞 M) := inferInstance
  obtain ⟨𝔮', h𝔮'⟩ :=
    Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := L) (L := M) 𝔮
  haveI : 𝔮'.asIdeal.LiesOver 𝔮.asIdeal := h𝔮'
  have h𝔮'𝔭 : 𝔮'.asIdeal.LiesOver 𝔭.asIdeal :=
    Ideal.LiesOver.trans 𝔮'.asIdeal 𝔮.asIdeal 𝔭.asIdeal
  have htw := Ideal.ramificationIdx_tower (R := 𝓞 F) (S := 𝓞 L) (T := 𝓞 M)
    𝔮.asIdeal 𝔮'.asIdeal
  rw [hunr 𝔮' h𝔮'𝔭] at htw
  exact Nat.eq_one_of_mul_eq_one_right htw.symm

/-- **The restriction of a Frobenius element along a tower of number fields.**  For a tower
`F ⊆ L ⊆ M` of number fields with `M / F` and `L / F` finite abelian Galois, and a prime `𝔭` of
`F` unramified in both, the restriction to `L` of the Frobenius element of `M / F` at `𝔭` is the
Frobenius element of `L / F` at `𝔭`. -/
theorem frobAtPrime_restrictNormalHom_of_tower {F L M : Type} [Field F] [NumberField F]
    [Field L] [NumberField L] [Field M] [NumberField M] [Algebra F L] [Algebra L M] [Algebra F M]
    [IsScalarTower F L M] [FiniteDimensional F L] [FiniteDimensional F M] [IsGalois F L]
    [IsGalois F M] (hcommL : ∀ a b : L ≃ₐ[F] L, a * b = b * a)
    (hcommM : ∀ a b : M ≃ₐ[F] M, a * b = b * a)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (hunrM : NK.HeckeL.IsUnramifiedIn (K := F) (L := M) 𝔭)
    (hunrL : NK.HeckeL.IsUnramifiedIn (K := F) (L := L) 𝔭) :
    AlgEquiv.restrictNormalHom (F := F) (K₁ := M) L
        (NK.Chebotarev.frobAtPrime (K := F) (L := M) 𝔭)
      = NK.Chebotarev.frobAtPrime (K := F) (L := L) 𝔭 := by
  classical
  have h1 : NK.Chebotarev.IsFrobAtPrime (K := F) (L := L) 𝔭
      (AlgEquiv.restrictNormalHom (F := F) (K₁ := M) L
        (NK.Chebotarev.frobAtPrime (K := F) (L := M) 𝔭)) := by
    obtain ⟨P, hP, hPfrob⟩ :=
      NK.Chebotarev.isFrobAtPrime_frobAtPrime (K := F) (L := M) hcommM 𝔭 hunrM
    refine ⟨P.under (𝓞 L), ?_, ?_⟩
    · refine ⟨?_⟩
      rw [NK.Chebotarev.under_asIdeal_type (E := L) (M := M) P, Ideal.under_under]
      exact hP.over
    · exact NK.Chebotarev.IsFrobAtRestrictNormalHomType (K := F) (E := L) (M := M) P
        (NK.Chebotarev.frobAtPrime (K := F) (L := M) 𝔭) hPfrob
  have h2 : NK.Chebotarev.IsFrobAtPrime (K := F) (L := L) 𝔭
      (NK.Chebotarev.frobAtPrime (K := F) (L := L) 𝔭) :=
    NK.Chebotarev.isFrobAtPrime_frobAtPrime (K := F) (L := L) hcommL 𝔭 hunrL
  exact (NK.Chebotarev.ExistsUniqueIsFrobAtPrime (K := F) (L := L) hcommL 𝔭 hunrL).unique h1 h2

/-! ## The descended Kummer character is compatible with restriction of the level -/

/-- **Level compatibility of the descended Kummer character.**  For `L ≤ M` intermediate fields
of `Ω` over `↥K` and the restriction homomorphism
`ρ : Gal(↥M/↥K) →* Gal(↥L/↥K)`, the character descended to the level `M` evaluated at `g` is the
character descended to the level `L` evaluated at `ρ g` (both levels containing the Kummer field
of `β`).

The hypothesis `[IsScalarTower ↥L ↥M Ω]` is what pins the algebra structure `↥L → ↥M` (which is
not an instance here, since `L` and `M` are two intermediate fields of the same ambient field) to
the inclusion `L ⊆ M`: it forces `algebraMap ↥L ↥M` to be the coercion. -/
theorem hChar_restrictNormalHom_apply {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω] {K : IntermediateField k Ω}
    [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K] [IsSepClosure ↥K Ω]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    {L M : IntermediateField ↥K Ω} [FiniteDimensional ↥K L] [IsGalois ↥K L]
    [FiniteDimensional ↥K M] [IsGalois ↥K M]
    [Algebra ↥L ↥M] [IsScalarTower ↥K ↥L ↥M] [IsScalarTower ↥L ↥M Ω]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (β : (↥K)ˣ)
    (hLM : L ≤ M) (hKL : NK.LocalAnabelian.kummerField (K' := Ω) p β ≤ L)
    (g : ↥M ≃ₐ[↥K] ↥M) :
    Work.SSGRoute.ZDataMup.OddForm.hChar (K := K) (p := p) ζ hζ β (le_trans hKL hLM) g =
      Work.SSGRoute.ZDataMup.OddForm.hChar (K := K) (p := p) ζ hζ β hKL
        (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := ↥M) ↥L g) := by
  classical
  obtain ⟨σ, hσ⟩ :=
    AlgEquiv.restrictNormalHom_surjective (F := ↥K) (E := Ω) (K₁ := ↥M) g
  rw [← hσ]
  rw [show (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := ↥M) ↥L)
        ((AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) ↥M) σ)
      = (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) ↥L) σ from
    (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply (K₁ := ↥L) (K₂ := ↥M) (F := ↥K)
      (K₃ := Ω) σ).symm]
  rw [Work.SSGRoute.ZDataMup.OddForm.hChar_apply (K := K) (p := p) ζ hζ β (le_trans hKL hLM) σ,
    Work.SSGRoute.ZDataMup.OddForm.hChar_apply (K := K) (p := p) ζ hζ β hKL σ]

/-! ## Level compatibility of the abelian Artin map, for two subfields of one ambient field -/

/-- **Level compatibility of the abelian idèlic Artin map** (Milne, *CFT*, Lemma 8.4(a)), in the
form needed when `L` and `M` are two intermediate fields of the *same* ambient field `Ω` over a
number field `F`.

If `M/F` is finite abelian Galois, `↥L ⊆ M` is a finite Galois subextension (the algebra structure
`↥L → ↥M` being supplied by the caller, e.g. `(Subsemiring.inclusion hLM).toAlgebra`), and
`Φ : 𝕀 F →* Gal(M/F)`, `Ψ : 𝕀 F →* Gal(L/F)` are Artin maps (kernel `N ⊔ principal`, Frobenius
normalised at every unramified prime), then the restriction of `Φ` to `Gal(L/F)` is `Ψ`.

This is the port of `ArtinUniqueness.artinMap_restrictNormalHom_eq_abelian` to this setting; the
only adaptations are that the restriction homomorphism is `AlgEquiv.restrictNormalHom` for the bare
tower `F ⊆ ↥L ⊆ ↥M`, that the norm monotonicity `N_{M/F} ≤ N_{L/F}` comes from
`NK.NUV2.ARL.normImage_le_of_tower`, and that the Frobenius comparison uses
`frobAtPrime_restrictNormalHom_of_tower`. -/
theorem artinMap_restrictNormalHom_of_le
    {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {L M : IntermediateField F Ω} [FiniteDimensional F L] [IsGalois F L] [NumberField ↥L]
    [FiniteDimensional F M] [IsGalois F M] [NumberField ↥M]
    [Algebra ↥L ↥M] [IsScalarTower F ↥L ↥M]
    (hcommL : ∀ a b : ↥L ≃ₐ[F] ↥L, a * b = b * a)
    (hcommM : ∀ a b : ↥M ≃ₐ[F] ↥M, a * b = b * a)
    (Φ : NK.GlobalCFT.Idele F →* (↥M ≃ₐ[F] ↥M))
    (hΦker : Φ.ker =
      NK.GlobalCFT.Idele.normImage F ↥M ⊔ NK.GlobalCFT.Idele.principalSubgroup F)
    (hΦfrob : ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
      NK.HeckeL.IsUnramifiedIn (K := F) (L := ↥M) Q →
      Φ (NK.HeckeL.ideleOfPrime F Q) = NK.Chebotarev.frobAtPrime (K := F) (L := ↥M) Q)
    (Ψ : NK.GlobalCFT.Idele F →* (↥L ≃ₐ[F] ↥L))
    (hΨker : Ψ.ker =
      NK.GlobalCFT.Idele.normImage F ↥L ⊔ NK.GlobalCFT.Idele.principalSubgroup F)
    (hΨfrob : ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
      NK.HeckeL.IsUnramifiedIn (K := F) (L := ↥L) Q →
      Ψ (NK.HeckeL.ideleOfPrime F Q) = NK.Chebotarev.frobAtPrime (K := F) (L := ↥L) Q) :
    (AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥M) ↥L).comp Φ = Ψ := by
  classical
  haveI hfdLM : FiniteDimensional ↥L ↥M := Module.Finite.right F ↥L ↥M
  -- `Φ` is surjective (its range contains every Frobenius element)
  have hsurjΦ : Function.Surjective Φ :=
    ArtinReciprocity.surjective_of_frobAtPrime_unramified hcommM Φ hΦfrob
  -- the kernel inclusion `N_{M/F} ⊆ N_{L/F}` (a norm from `M` is a norm from `L`)
  have hle : Φ.ker ≤ Ψ.ker := by
    rw [hΦker, hΨker]
    exact sup_le
      (le_trans (NK.NUV2.ARL.normImage_le_of_tower (K := F) (L := ↥L) (M := ↥M)) le_sup_left)
      le_sup_right
  -- the quotient map defined by `Ψ`, transported to `Gal(M/F)`
  let eΦ : (NK.GlobalCFT.Idele F ⧸ Φ.ker) ≃* (↥M ≃ₐ[F] ↥M) :=
    QuotientGroup.quotientKerEquivOfSurjective Φ hsurjΦ
  let LΨ : (NK.GlobalCFT.Idele F ⧸ Φ.ker) →* (↥L ≃ₐ[F] ↥L) :=
    QuotientGroup.lift Φ.ker Ψ hle
  let χ : (↥M ≃ₐ[F] ↥M) →* (↥L ≃ₐ[F] ↥L) := LΨ.comp eΦ.symm.toMonoidHom
  have hχ : ∀ x : NK.GlobalCFT.Idele F, χ (Φ x) = Ψ x := by
    intro x
    have h1 : eΦ (QuotientGroup.mk' Φ.ker x) = Φ x := rfl
    have h2 : LΨ (QuotientGroup.mk' Φ.ker x) = Ψ x := QuotientGroup.lift_mk' _ _ x
    calc χ (Φ x) = LΨ (eΦ.symm (Φ x)) := rfl
      _ = LΨ (eΦ.symm (eΦ (QuotientGroup.mk' Φ.ker x))) := by rw [h1]
      _ = LΨ (QuotientGroup.mk' Φ.ker x) := by rw [MulEquiv.symm_apply_apply]
      _ = Ψ x := h2
  -- `χ` and the restriction map agree on the Frobenius elements (Čebotarev)
  have hχρ : χ = AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥M) ↥L := by
    let T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :=
      NK.CFTLib.ExistsCongruence.ramPrimes (K := F) (L := ↥M)
    have hunrT : ∀ 𝔭, 𝔭 ∉ T → NK.HeckeL.IsUnramifiedIn (K := F) (L := ↥M) 𝔭 :=
      fun 𝔭 h𝔭 𝔮 h𝔮 =>
        NK.CFTLib.ExistsCongruence.ramificationIdx_eq_one_of_notMem_ramPrimes (K := F) (L := ↥M)
          h𝔭 h𝔮
    have hgen := NK.CFTLib.Arl.closure_isFrobAtPrime_of_notMem_eq_top (K := F) (L := ↥M) T
    have heqon : Set.EqOn (⇑χ)
        (⇑(AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥M) ↥L))
        {σ : (↥M ≃ₐ[F] ↥M) |
          ∃ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
            𝔭 ∉ T ∧ NK.Chebotarev.IsFrobAtPrime (K := F) (L := ↥M) 𝔭 σ} := by
      rintro σ ⟨𝔭, h𝔭T, hσ⟩
      have hunrM : NK.HeckeL.IsUnramifiedIn (K := F) (L := ↥M) 𝔭 := hunrT 𝔭 h𝔭T
      have hunrL : NK.HeckeL.IsUnramifiedIn (K := F) (L := ↥L) 𝔭 :=
        isUnramifiedIn_of_tower (F := F) (L := ↥L) (M := ↥M) 𝔭 hunrM
      have hσ' : NK.Chebotarev.frobAtPrime (K := F) (L := ↥M) 𝔭 = σ :=
        (NK.Chebotarev.isFrobAtPrime_iff_frobAtPrime_eq hcommM 𝔭 hunrM σ).mp hσ
      rw [← hσ']
      calc χ (NK.Chebotarev.frobAtPrime (K := F) (L := ↥M) 𝔭)
          = χ (Φ (NK.HeckeL.ideleOfPrime F 𝔭)) := by rw [hΦfrob 𝔭 hunrM]
        _ = Ψ (NK.HeckeL.ideleOfPrime F 𝔭) := hχ _
        _ = NK.Chebotarev.frobAtPrime (K := F) (L := ↥L) 𝔭 := hΨfrob 𝔭 hunrL
        _ = AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥M) ↥L
              (NK.Chebotarev.frobAtPrime (K := F) (L := ↥M) 𝔭) :=
            (frobAtPrime_restrictNormalHom_of_tower (F := F) (L := ↥L) (M := ↥M) hcommL hcommM
              𝔭 hunrM hunrL).symm
    have hEq := MonoidHom.eqOn_closure (f := χ)
      (g := AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥M) ↥L) heqon
    refine MonoidHom.ext fun σ => ?_
    exact hEq (by rw [hgen]; exact Subgroup.mem_top σ)
  -- conclusion
  refine MonoidHom.ext fun x => ?_
  rw [← hχρ]
  exact hχ x

end Work.SSGRoute.ZDataMup

namespace Work.SSGRoute.ZDataMup

set_option linter.style.haveILetI false

/-! ## The target: level compatibility of the Kummer character along the local factor -/

theorem hChar_hLocalFactor_tower {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω] {K : IntermediateField k Ω}
    [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K] [IsSepClosure ↥K Ω]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (β : (↥K)ˣ)
    {L M : IntermediateField ↥K Ω} [FiniteDimensional ↥K L] [IsGalois ↥K L] [NumberField ↥L]
    [FiniteDimensional ↥K M] [IsGalois ↥K M] [NumberField ↥M]
    (hLM : L ≤ M) (hKL : NK.LocalAnabelian.kummerField (K' := Ω) p β ≤ L)
    (hcommL : ∀ a b : ↥L ≃ₐ[↥K] ↥L, a * b = b * a)
    (hcommM : ∀ a b : ↥M ≃ₐ[↥K] ↥M, a * b = b * a) (ν : (↥K)ˣ) :
    Work.SSGRoute.ZDataMup.OddForm.hChar (K := K) (p := p) ζ hζ β (le_trans hKL hLM)
        (Work.SSGRoute.ZDataMup.LTRecFamHonest.hLocalFactor (K := K) A hA M
          (Work.SSGRoute.ZDataMup.oddArtin (K := K) M hcommM) ν) =
      Work.SSGRoute.ZDataMup.OddForm.hChar (K := K) (p := p) ζ hζ β hKL
        (Work.SSGRoute.ZDataMup.LTRecFamHonest.hLocalFactor (K := K) A hA L
          (Work.SSGRoute.ZDataMup.oddArtin (K := K) L hcommL) ν) := by
  classical
  -- The algebra structure `↥L → ↥M` given by the inclusion `L ⊆ M`, and its compatibility with
  -- the ambient field `Ω`.
  letI : Algebra ↥L ↥M := (Subsemiring.inclusion hLM).toAlgebra
  haveI hST1 : IsScalarTower ↥K ↥L ↥M := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI hST2 : IsScalarTower ↥L ↥M Ω := IsScalarTower.of_algebraMap_eq fun x => rfl
  -- Level compatibility of the two Artin maps.
  have hkey : (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := ↥M) ↥L).comp
      (oddArtin (K := K) M hcommM) = oddArtin (K := K) L hcommL :=
    artinMap_restrictNormalHom_of_le (F := ↥K) (Ω := Ω) hcommL hcommM
      (oddArtin (K := K) M hcommM) (oddArtin_ker M hcommM) (oddArtin_frob M hcommM)
      (oddArtin (K := K) L hcommL) (oddArtin_ker L hcommL) (oddArtin_frob L hcommL)
  -- hence the local factors are compatible under restriction
  have htower : (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := ↥M) ↥L)
      (LTRecFamHonest.hLocalFactor (K := K) A hA M (oddArtin (K := K) M hcommM) ν)
      = LTRecFamHonest.hLocalFactor (K := K) A hA L (oddArtin (K := K) L hcommL) ν := by
    have hx := DFunLike.congr_fun hkey
      (NK.HassePrinciple.onePlace
        (NK.GlobalCFT.Place.ofFinite (LTRecFamHonest.hPrimeBelow (K := K) A hA))
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
          (NK.GlobalCFT.Place.ofFinite (LTRecFamHonest.hPrimeBelow (K := K) A hA)) ν))
    simpa only [LTRecFamHonest.hLocalFactor, MonoidHom.comp_apply] using hx
  -- and the characters are compatible under restriction
  rw [← htower]
  exact hChar_restrictNormalHom_apply (K := K) (p := p) (L := L) (M := M) ζ hζ β hLM hKL
    (LTRecFamHonest.hLocalFactor (K := K) A hA M (oddArtin (K := K) M hcommM) ν)

end Work.SSGRoute.ZDataMup
