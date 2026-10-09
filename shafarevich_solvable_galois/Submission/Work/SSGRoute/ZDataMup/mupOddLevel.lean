import Mathlib
import Submission.Work.SSGRoute.ZConstruction.levelK_kummerCharHom_dictionary
import Submission.Work.SSGRoute.ZDataMup.LTRecFamCrux.exists_abelianArtin_localFactors
import Submission.Work.SSGRoute.ZDataMup.ArtinUniqueness.artinMap_restrictNormalHom_eq_abelian
import Submission.Work.SSGRoute.ZDataMup.mupLocalForm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The odd-`p` level pairing: vocabulary

This file sets up the vocabulary of the route described in
`Submission/Work/SSGRoute/ZDataMup/NOTES_mupOdd_session11.md`, whose point is that the whole wiring
of the odd-`p` local Tate system can be done with the **global** abelian Artin map
`exists_abelianArtin_localFactors` at the *Kummer levels* `L(γ) = ↥K(γ^{1/p})` of the two variables,
so that

* the **product formula** (hence the reciprocity) is available (`cprod_localFactor_eq_one`), and
* the **level compatibility** of the Artin maps is available
  (`ArtinUniqueness.artinMap_restrictNormalHom_eq_abelian`),

while the two inputs that the `ZConstruction`/`ZSplit` lanes are missing —

* the membership of the local factor in the decomposition group (`LFM`), and
* the level compatibility of the *local* Artin maps (the `AbelianOnePlace` crux)

are never used.  The two devices that replace them are (SPL) (an extension in which the place splits
completely has trivial local norm group, hence trivial local factor) and (POW) (`p`-th powers are
local norms; `NK.CFTLib.IdeleHasse`/`mem_localNormSubgroup_of_mem_powRange`).

The mathematical notes are in the NOTES file; this file contains the vocabulary only.
-/

open scoped NumberField Pointwise

namespace Work.SSGRoute.ZDataMup

open _root_.SSGRoute

noncomputable section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
  [IsSepClosure ↥K Ω]
  [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]

/-! ## The Kummer level of a global element -/

/-- **The Kummer level of `γ`**: the field `↥K(γ^{1/p}) ⊆ Ω`, a cyclic extension of `↥K` of degree
dividing `p`. -/
abbrev oddLevel (γ : (↥K)ˣ) : IntermediateField ↥K Ω :=
  NK.LocalAnabelian.kummerField (K' := Ω) p γ

theorem oddLevel_finiteDimensional (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (γ : (↥K)ˣ) :
    FiniteDimensional ↥K ↥(oddLevel (K := K) (p := p) γ) :=
  NK.GlobalCFTdeep.SecondInequality.finiteDimensional_kummerField (K' := Ω) (k := ↥K)
    (p := p) Fact.out hζ γ

theorem oddLevel_isGalois (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (γ : (↥K)ˣ) :
    IsGalois ↥K ↥(oddLevel (K := K) (p := p) γ) :=
  NK.GlobalCFTdeep.SecondInequality.isGalois_kummerField (K' := Ω) (k := ↥K)
    (p := p) Fact.out hζ γ

theorem oddLevel_numberField (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (γ : (↥K)ˣ) :
    NumberField ↥(oddLevel (K := K) (p := p) γ) := by
  haveI := oddLevel_finiteDimensional (K := K) (p := p) ζ hζ γ
  exact Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := ↥K) (K' := Ω)
    (oddLevel (K := K) (p := p) γ)

/-- In a group of prime order everything commutes. -/
theorem odd_comm_of_prime_card {G : Type*} [Group G] (h : Nat.card G = p) (a b : G) :
    a * b = b * a := by
  haveI : IsCyclic G := isCyclic_of_prime_card h
  exact IsMulCommutative.is_comm.comm a b

/-- **The Galois group of a Kummer level is commutative** (its order is `1` or `p`). -/
theorem oddLevel_gal_comm (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (γ : (↥K)ˣ) :
    ∀ a b : ↥(oddLevel (K := K) (p := p) γ) ≃ₐ[↥K] ↥(oddLevel (K := K) (p := p) γ),
      a * b = b * a := by
  by_cases hγ : γ ∈ NK.LocalAnabelian.powSubgroup p ↥K
  · have hbot : oddLevel (K := K) (p := p) γ = ⊥ :=
      NK.LocalAnabelian.Kummer.kummerField_eq_bot_of_mem_powSubgroup (K' := Ω) (k := ↥K) p
        Fact.out hζ hγ
    rw [hbot]
    intro a b
    have hsub : Subsingleton (↥(⊥ : IntermediateField ↥K Ω) ≃ₐ[↥K]
        ↥(⊥ : IntermediateField ↥K Ω)) :=
      ⟨fun x y => AlgEquiv.ext fun z => by
        obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp z.2
        have hz : z = algebraMap ↥K ↥(⊥ : IntermediateField ↥K Ω) c := (Subtype.ext hc).symm
        rw [hz, AlgEquiv.commutes, AlgEquiv.commutes]⟩
    rw [Subsingleton.elim a b]
  · have hgal := NK.LocalAnabelian.Kummer.isGalois_kummerField_and_finrank (K' := Ω) (k := ↥K) p
      Fact.out hζ γ hγ
    haveI hfd : FiniteDimensional ↥K ↥(oddLevel (K := K) (p := p) γ) :=
      oddLevel_finiteDimensional (K := K) (p := p) ζ hζ γ
    haveI : IsGalois ↥K ↥(oddLevel (K := K) (p := p) γ) := hgal.1
    have hcard : Nat.card (↥(oddLevel (K := K) (p := p) γ) ≃ₐ[↥K]
        ↥(oddLevel (K := K) (p := p) γ)) = p := by
      rw [IsGalois.card_aut_eq_finrank, hgal.2]
    exact fun a b => odd_comm_of_prime_card (p := p) hcard a b

/-! ## The abelian Artin map at a level, and its one-place factors -/

/-- **The abelian idèlic Artin map at the level `L`**, chosen once and for all, with kernel
`N 𝕀 ⊔ ↥Kˣ`: `Work.SSGRoute.ZConstruction.exists_abelianArtin_localFactors`. -/
noncomputable def oddArtin (L : IntermediateField ↥K Ω) [FiniteDimensional ↥K L]
    [IsGalois ↥K L] [NumberField ↥L]
    (hcomm : ∀ a b : ↥L ≃ₐ[↥K] ↥L, a * b = b * a) :
    NK.GlobalCFT.Idele ↥K →* (↥L ≃ₐ[↥K] ↥L) :=
  Classical.choose (Work.SSGRoute.ZConstruction.exists_abelianArtin_localFactors (K := ↥K)
    (L := ↥L) hcomm)

theorem oddArtin_ker (L : IntermediateField ↥K Ω) [FiniteDimensional ↥K L] [IsGalois ↥K L]
    [NumberField ↥L] (hcomm : ∀ a b : ↥L ≃ₐ[↥K] ↥L, a * b = b * a) :
    MonoidHom.ker (oddArtin (K := K) L hcomm) =
      NK.GlobalCFT.Idele.normImage ↥K ↥L ⊔ NK.GlobalCFT.Idele.principalSubgroup ↥K :=
  (Classical.choose_spec (Work.SSGRoute.ZConstruction.exists_abelianArtin_localFactors
    (K := ↥K) (L := ↥L) hcomm)).1

theorem oddArtin_prin (L : IntermediateField ↥K Ω) [FiniteDimensional ↥K L] [IsGalois ↥K L]
    [NumberField ↥L] (hcomm : ∀ a b : ↥L ≃ₐ[↥K] ↥L, a * b = b * a) (a : (↥K)ˣ) :
    oddArtin (K := K) L hcomm (NK.GlobalCFT.Idele.principalIdele ↥K a) = 1 :=
  (Classical.choose_spec (Work.SSGRoute.ZConstruction.exists_abelianArtin_localFactors
    (K := ↥K) (L := ↥L) hcomm)).2.2.1 a

theorem oddArtin_norm (L : IntermediateField ↥K Ω) [FiniteDimensional ↥K L] [IsGalois ↥K L]
    [NumberField ↥L] (hcomm : ∀ a b : ↥L ≃ₐ[↥K] ↥L, a * b = b * a)
    (y : NK.GlobalCFT.Idele ↥L) :
    oddArtin (K := K) L hcomm (NK.GlobalCFT.Idele.normIdeleHom ↥K ↥L y) = 1 :=
  (Classical.choose_spec (Work.SSGRoute.ZConstruction.exists_abelianArtin_localFactors
    (K := ↥K) (L := ↥L) hcomm)).2.1 y

/-- **One-place faithfulness**: the one-place factor of the level Artin map is trivial exactly on the
local norm group. -/
theorem oddArtin_onePlace (L : IntermediateField ↥K Ω) [FiniteDimensional ↥K L] [IsGalois ↥K L]
    [NumberField ↥L] (hcomm : ∀ a b : ↥L ≃ₐ[↥K] ↥L, a * b = b * a)
    (v : NK.GlobalCFT.Place ↥K) (a : (NK.GlobalCFT.Place.localField ↥K v)ˣ) :
    oddArtin (K := K) L hcomm (NK.HassePrinciple.onePlace v a) = 1 ↔
      a ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥L) v :=
  (Classical.choose_spec (Work.SSGRoute.ZConstruction.exists_abelianArtin_localFactors
    (K := ↥K) (L := ↥L) hcomm)).2.2.2.1 v a

theorem oddArtin_frob (L : IntermediateField ↥K Ω) [FiniteDimensional ↥K L] [IsGalois ↥K L]
    [NumberField ↥L] (hcomm : ∀ a b : ↥L ≃ₐ[↥K] ↥L, a * b = b * a)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (hunr : NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥L) Q) :
    oddArtin (K := K) L hcomm (NK.HeckeL.ideleOfPrime ↥K Q) =
      NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥L) Q :=
  (Classical.choose_spec (Work.SSGRoute.ZConstruction.exists_abelianArtin_localFactors
    (K := ↥K) (L := ↥L) hcomm)).2.2.2.2.1 Q hunr

/-- **The product formula for the level Artin map**: a principal idèle has trivial local factors
outside a finite set and their product is `1`. -/
theorem oddArtin_product (L : IntermediateField ↥K Ω) [FiniteDimensional ↥K L] [IsGalois ↥K L]
    [NumberField ↥L] (hcomm : ∀ a b : ↥L ≃ₐ[↥K] ↥L, a * b = b * a) (x : (↥K)ˣ)
    (s : Finset (NK.GlobalCFT.Place ↥K))
    (hs : ∀ v, v ∉ s →
      oddArtin (K := K) L hcomm
        (NK.HassePrinciple.onePlace v (NK.CFTLib.IdeleHasse.localImageAt v x)) = 1) :
    NK.CFTLib.IdeleHasse.cprod hcomm s
      (fun v => oddArtin (K := K) L hcomm
        (NK.HassePrinciple.onePlace v (NK.CFTLib.IdeleHasse.localImageAt v x))) = 1 :=
  (Classical.choose_spec (Work.SSGRoute.ZConstruction.exists_abelianArtin_localFactors
    (K := ↥K) (L := ↥L) hcomm)).2.2.2.2.2 x s hs

/-! ## Level compatibility (recipe, not yet formalised here)

The two lemmas below are the only places where a *nested* intermediate field occurs: for
`L ≤ M` (both intermediate fields of `Ω` over `↥K`) one needs the restriction
`Gal(M/↥K) → Gal(L/↥K)`.  Mathlib's form of this is `IntermediateField.restrict hLM :
IntermediateField ↥K ↥M` together with `AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := ↥M)
↥(IntermediateField.restrict hLM)`, and then `AlgEquiv.restrictNormalHom_surjective` /
`IntermediateField.restrictAlgEquiv` to transport values back to `↥L ≃ₐ[↥K] ↥L`.  The needed
statement is

* `oddArtin (L) = (restrictNormalHom) ∘ oddArtin (M)` for `L ≤ M`, which is exactly
  `Work.SSGRoute.ZDataMup.ArtinUniqueness.artinMap_restrictNormalHom_eq_abelian` applied to the
  two chosen Artin maps `oddArtin M hcommM` (kernel and Frobenius: `oddArtin_ker`,
  `oddArtin_frob`) and `oddArtin L hcommL`;
* hence `χ_γ(θ^M_A(γ')) = χ_γ(θ^L_A(γ'))` whenever `L(γ) ⊆ L ⊆ M`, since `χ_γ` kills
  `Gal(Ω/L(γ))`.

This is the "level compatibility of the global θ's" used in (A)–(C) of
`NOTES_mupOdd_session11.md`; it is *free* (unlike the level compatibility of the *local* Artin
maps, which is the `AbelianOnePlace` crux). -/

/-! ## The local factor of the level Artin map -/

/-- **The local factor at the finite place `A` of the level Artin map**, applied to a global
element: `θ^L_A(γ) = Φ_L(onePlace_𝔭(localImageAt_𝔭 γ))`. -/
noncomputable def oddTheta (L : IntermediateField ↥K Ω) [FiniteDimensional ↥K L]
    [IsGalois ↥K L] [NumberField ↥L] (hcomm : ∀ a b : ↥L ≃ₐ[↥K] ↥L, a * b = b * a)
    (A : ValuationSubring Ω) (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤) (γ : (↥K)ˣ) :
    ↥L ≃ₐ[↥K] ↥L :=
  oddArtin (K := K) L hcomm
    (NK.HassePrinciple.onePlace
      (NK.GlobalCFT.Place.ofFinite (Submission.NeukirchUchida.primeOf A hAK))
      (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
        (NK.GlobalCFT.Place.ofFinite (Submission.NeukirchUchida.primeOf A hAK)) γ))

/-- **The local factor is trivial on local norms**: its kernel is the local norm group. -/
theorem oddTheta_eq_one_iff_mem_localNormSubgroup (L : IntermediateField ↥K Ω)
    [FiniteDimensional ↥K L] [IsGalois ↥K L] [NumberField ↥L]
    (hcomm : ∀ a b : ↥L ≃ₐ[↥K] ↥L, a * b = b * a) (A : ValuationSubring Ω)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤) (γ : (↥K)ˣ) :
    oddTheta (K := K) L hcomm A hAK γ = 1 ↔
      NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
        (NK.GlobalCFT.Place.ofFinite (Submission.NeukirchUchida.primeOf A hAK)) γ ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥L)
          (NK.GlobalCFT.Place.ofFinite (Submission.NeukirchUchida.primeOf A hAK)) :=
  oddArtin_onePlace (K := K) L hcomm
    (NK.GlobalCFT.Place.ofFinite (Submission.NeukirchUchida.primeOf A hAK))
    (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
      (NK.GlobalCFT.Place.ofFinite (Submission.NeukirchUchida.primeOf A hAK)) γ)

end

end Work.SSGRoute.ZDataMup
