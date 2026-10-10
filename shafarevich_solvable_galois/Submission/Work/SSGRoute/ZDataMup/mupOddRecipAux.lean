import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.ZDataMup.mupOddPairBilin
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliaries for the reciprocity sum of the odd-`p` pairing

* `exists_mem_fixingSubgroup_smul_eq_of_comap_eq`: two places of `Ω` with the same restriction to
  `↥K` are conjugate by an element of `K.fixingSubgroup` (transitivity of the Galois action on the
  places over a fixed prime), in the `τ • A = B` form;
* `exists_conj_of_oddPrime_eq`: the same statement in the `∀ x, x ∈ B ↔ τ⁻¹ • x ∈ A` form used by
  the conjugacy hypothesis of `IsProductFormula` (via the prime `oddPrime` of `↥K` below a place);
* `hChar_cprod`: the character of a finite product of local factors is the sum of the characters —
  the conversion of the multiplicative product formula `oddArtin_product` into the additive
  reciprocity sum.
-/

open scoped Pointwise NumberField

namespace Work.SSGRoute.ZDataMup.OddForm

open _root_.SSGRoute
open Work.SSGRoute.ZDataMup.LTRecFamHonest

noncomputable section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
  [IsSepClosure ↥K Ω]
  [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]

/-- **Transitivity of the `G_K`-action on the places of `Ω` over a prime of `K`.**  Two places of
`Ω` whose restrictions to `↥K` agree are `Gal(Ω/↥K)`-conjugate, and the conjugating element may be
read in the subgroup `K.fixingSubgroup ≤ G_k`. -/
theorem exists_mem_fixingSubgroup_smul_eq_of_comap_eq (A B : ValuationSubring Ω)
    (hA : A.comap (algebraMap ↥K Ω) ≠ ⊤)
    (h : A.comap (algebraMap ↥K Ω) = B.comap (algebraMap ↥K Ω)) :
    ∃ τ ∈ K.fixingSubgroup, τ • A = B := by
  haveI hNum : NumberField ↥K := NumberField.of_module_finite k ↥K
  haveI hAlg : IsAlgClosure ↥K Ω :=
    IsAlgClosure.mk (inferInstance : IsAlgClosure k Ω).isAlgClosed inferInstance
  haveI hSep : IsSepClosure ↥K Ω := IsSepClosure.of_isAlgClosure_of_perfectField ↥K Ω
  obtain ⟨σ, hσ⟩ := Submission.NeukirchUchida.exists_smul_eq_of_comap_eq' (K₁ := ↥K) (K₁' := Ω)
    (A := A) (B := B) hA h
  refine ⟨↑((IntermediateField.fixingSubgroupEquiv K).symm σ), ?_, ?_⟩
  · exact ((IntermediateField.fixingSubgroupEquiv K).symm σ).2
  · have hfun : ⇑(σ : Ω ≃ₐ[↥K] Ω) =
        ⇑(↑((IntermediateField.fixingSubgroupEquiv K).symm σ) : Ω ≃ₐ[k] Ω) := by
      have h1 : (((IntermediateField.fixingSubgroupEquiv K)
          ((IntermediateField.fixingSubgroupEquiv K).symm σ) : Ω ≃ₐ[↥K] Ω) : Ω → Ω) =
          ⇑(↑((IntermediateField.fixingSubgroupEquiv K).symm σ) : Ω ≃ₐ[k] Ω) := rfl
      rwa [MulEquiv.apply_symm_apply] at h1
    have hsmul : (↑((IntermediateField.fixingSubgroupEquiv K).symm σ) : Ω ≃ₐ[k] Ω) • A =
        σ • A := by
      apply ValuationSubring.ext
      intro x
      rw [ValuationSubring.mem_smul_pointwise_iff_exists,
        ValuationSubring.mem_smul_pointwise_iff_exists]
      constructor
      · rintro ⟨s, hs, hx⟩
        exact ⟨s, hs, by rw [← hx, AlgEquiv.smul_def, AlgEquiv.smul_def]; exact congrFun hfun s⟩
      · rintro ⟨s, hs, hx⟩
        exact ⟨s, hs, by
          rw [← hx, AlgEquiv.smul_def, AlgEquiv.smul_def]
          exact (congrFun hfun s).symm⟩
    rw [hsmul, hσ]

/-- **Two finite places with the same prime of `↥K` below them are `K.fixingSubgroup`-conjugate**,
in the form consumed by the conjugacy hypothesis of `IsProductFormula`. -/
theorem exists_conj_of_oddPrime_eq {A B : ValuationSubring Ω} (hA : SSGRoute.IsFinPlace k A)
    (hB : SSGRoute.IsFinPlace k B) (h : oddPrime (K := K) A hA = oddPrime (K := K) B hB) :
    ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A := by
  have hcomap : A.comap (algebraMap ↥K Ω) = B.comap (algebraMap ↥K Ω) := by
    rw [oddPrime_spec (K := K) (A := A) hA, oddPrime_spec (K := K) (A := B) hB, h]
  obtain ⟨τ, hτ, hτA⟩ :=
    exists_mem_fixingSubgroup_smul_eq_of_comap_eq (K := K) A B
      (oddFinPlace (K := K) (A := A) hA) hcomap
  exact ⟨τ, hτ, fun x => by
    rw [← hτA, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]⟩

/-- The prime of `↥K` below a place of `Ω` is injective on places with a prescribed membership:
places over distinct primes of `↥K` are not `K.fixingSubgroup`-conjugate. -/
theorem oddPrime_ne_of_not_conj {A B : ValuationSubring Ω} (hA : SSGRoute.IsFinPlace k A)
    (hB : SSGRoute.IsFinPlace k B)
    (hnot : ¬ ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) :
    oddPrime (K := K) A hA ≠ oddPrime (K := K) B hB :=
  fun h => hnot (exists_conj_of_oddPrime_eq (K := K) hA hB h)

/-- **The local factor of the level-`α` Artin map at a place of `↥K`, applied to `β`**, packaged with
the instances of the Kummer level so that statements about it need no instance gymnastics. -/
noncomputable def oTheta (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (α β : (↥K)ˣ)
    (v : NK.GlobalCFT.Place ↥K) :
    ↥(hLevel (K := K) (Ω := Ω) (p := p) α) ≃ₐ[↥K] ↥(hLevel (K := K) (Ω := Ω) (p := p) α) :=
  letI : FiniteDimensional ↥K ↥(hLevel (K := K) (Ω := Ω) (p := p) α) :=
    hLevel_finiteDimensional (Ω := Ω) (K := K) (p := p) ζ hζ α
  letI : IsGalois ↥K ↥(hLevel (K := K) (Ω := Ω) (p := p) α) :=
    hLevel_isGalois (Ω := Ω) (K := K) (p := p) ζ hζ α
  letI : NumberField ↥(hLevel (K := K) (Ω := Ω) (p := p) α) :=
    hLevel_numberField (Ω := Ω) (K := K) (p := p) ζ hζ α
  oddArtin (K := K) (hLevel (K := K) (Ω := Ω) (p := p) α)
    (hLevel_isMulCommutative (Ω := Ω) (K := K) ζ hζ α)
    (NK.HassePrinciple.onePlace v (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) v β))

/-- The local factor of the odd-`p` pairing at a finite place is `oTheta` at the prime below it. -/
theorem oFactorGlob_eq_oTheta (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) {A : ValuationSubring Ω}
    (hA : SSGRoute.IsFinPlace k A) (α β : (↥K)ˣ) :
    oFactorGlob (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA α β =
      oTheta (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ α β
        (NK.GlobalCFT.Place.ofFinite (oddPrime (K := K) A hA)) :=
  rfl

/-- **The character of a finite product of local factors is the sum of the characters.**  This
converts the multiplicative product formula `oddArtin_product` into the additive reciprocity sum. -/
theorem hChar_cprod {L : IntermediateField ↥K Ω} [FiniteDimensional ↥K L] [IsGalois ↥K L]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (β : (↥K)ˣ)
    (hKL : NK.LocalAnabelian.kummerField (K' := Ω) p β ≤ L)
    (hcomm : ∀ a b : ↥L ≃ₐ[↥K] ↥L, a * b = b * a) {ι : Type*}
    (s : Finset ι) (f : ι → ↥L ≃ₐ[↥K] ↥L) :
    (hChar (K := K) (p := p) ζ hζ β hKL (NK.CFTLib.IdeleHasse.cprod hcomm s f)).toAdd =
      ∑ v ∈ s, (hChar (K := K) (p := p) ζ hζ β hKL (f v)).toAdd := by
  letI : CommMonoid (↥L ≃ₐ[↥K] ↥L) :=
    { (inferInstance : Group (↥L ≃ₐ[↥K] ↥L)) with mul_comm := hcomm }
  have hc : NK.CFTLib.IdeleHasse.cprod hcomm s f = ∏ v ∈ s, f v := rfl
  rw [hc, map_prod, toAdd_prod]

end

end Work.SSGRoute.ZDataMup.OddForm
