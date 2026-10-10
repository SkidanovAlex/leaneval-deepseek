import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.Work.SSGRoute.ZDataMup.OddForm.oPair_toClass_eq_oPairGlob
import Submission.Work.SSGRoute.ZDataMup.mupOddRecipAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataMup.OddForm

open _root_.SSGRoute
open Work.SSGRoute.ZDataMup.LTRecFamHonest

open scoped Pointwise NumberField

set_option maxHeartbeats 4000000

theorem oPairForm_sum_attach_eq_zero_of_outside {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (a b : (Ω ≃ₐ[k] Ω) → ZMod p) (α β : (↥K)ˣ)
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup a)
    (hla : SSGRoute.IsLocConstOn K.fixingSubgroup a)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup b)
    (hlb : SSGRoute.IsLocConstOn K.fixingSubgroup b)
    (hα : ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup),
      a σ = Work.SSGRoute.kummerCharZMod (Ω := Ω) (K := ↥K) p (ζ := ζ) hζ α
        ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩))
    (hβ : ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup),
      b σ = Work.SSGRoute.kummerCharZMod (Ω := Ω) (K := ↥K) p (ζ := ζ) hζ β
        ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩))
    (T' : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T', SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T', ∀ B ∈ T',
      (∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) → A = B)
    (hout : ∀ v : NK.GlobalCFT.Place ↥K,
      (∀ A ∈ T'.attach,
        NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A.1
          (hTfin A.1 A.2)) ≠ v) →
      Work.SSGRoute.ZDataMup.OddForm.oTheta (K := K) (p := p) ζ hζ α β v = 1) :
    ∑ A ∈ T'.attach,
      Work.SSGRoute.ZDataMup.OddForm.oPairForm (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ
        (hTfin A.1 A.2)
        (Work.SSGRoute.toClass p k Ω K (ZMod p) (SSGRoute.decomp k A.1 ⊓ K.fixingSubgroup) a)
        (Work.SSGRoute.toClass p k Ω K (ZMod p) (SSGRoute.decomp k A.1 ⊓ K.fixingSubgroup) b)
      = 0 := by
  classical
  -- instances of the Kummer level of the first variable `α`
  letI hfdα : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) α) :=
    hLevel_finiteDimensional (Ω := Ω) (K := K) (p := p) ζ hζ α
  letI hgalα : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) α) :=
    hLevel_isGalois (Ω := Ω) (K := K) (p := p) ζ hζ α
  letI hnfα : NumberField ↥(hLevel (Ω := Ω) (K := K) (p := p) α) :=
    hLevel_numberField (Ω := Ω) (K := K) (p := p) ζ hζ α
  have hcomm := hLevel_isMulCommutative (Ω := Ω) (K := K) (p := p) ζ hζ α
  letI : CommMonoid (↥(hLevel (Ω := Ω) (K := K) (p := p) α) ≃ₐ[↥K]
      ↥(hLevel (Ω := Ω) (K := K) (p := p) α)) :=
    { (inferInstance : Group (↥(hLevel (Ω := Ω) (K := K) (p := p) α) ≃ₐ[↥K]
        ↥(hLevel (Ω := Ω) (K := K) (p := p) α))) with mul_comm := hcomm }
  -- the place of `↥K` below a place of `T'`
  let φ : {A : ValuationSubring Ω // A ∈ T'} → NK.GlobalCFT.Place ↥K :=
    fun A => NK.GlobalCFT.Place.ofFinite (oddPrime (K := K) A.1 (hTfin A.1 A.2))
  let s : Finset (NK.GlobalCFT.Place ↥K) := T'.attach.image φ
  -- distinct places of `T'` give distinct primes of `↥K`
  have hφinj : Set.InjOn φ ↑(T'.attach) := by
    intro A hA B hB hAB
    have hq : oddPrime (K := K) A.1 (hTfin A.1 A.2) =
        oddPrime (K := K) B.1 (hTfin B.1 B.2) :=
      NK.GlobalCFT.Place.ofFinite_inj.mp hAB
    obtain ⟨τ, hτ, hconj⟩ :=
      exists_conj_of_oddPrime_eq (K := K) (hTfin A.1 A.2) (hTfin B.1 B.2) hq
    exact Subtype.ext (hTdisj A.1 A.2 B.1 B.2 ⟨τ, hτ, hconj⟩)
  -- the local pairing is the Kummer character of `α` at the local factor of `β`
  have hstep : ∀ A : {A : ValuationSubring Ω // A ∈ T'},
      oPairForm (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ (hTfin A.1 A.2)
        (Work.SSGRoute.toClass p k Ω K (ZMod p) (SSGRoute.decomp k A.1 ⊓ K.fixingSubgroup) a)
        (Work.SSGRoute.toClass p k Ω K (ZMod p) (SSGRoute.decomp k A.1 ⊓ K.fixingSubgroup) b)
      = (hChar (K := K) (p := p) ζ hζ α (le_refl _)
          (oTheta (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ α β (φ A))).toAdd := by
    intro A
    rw [oPair_toClass_eq_oPairGlob (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ
      (hTfin A.1 A.2) a b α β ha hla hb hlb hα hβ]
    rfl
  -- the local factor of `β` is trivial outside the primes coming from `T'`
  have hs : ∀ v : NK.GlobalCFT.Place ↥K, v ∉ s →
      Work.SSGRoute.ZDataMup.oddArtin (K := K) (hLevel (Ω := Ω) (K := K) (p := p) α) hcomm
        (NK.HassePrinciple.onePlace v (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) v β)) = 1 := by
    intro v hv
    have hv' : ∀ A ∈ T'.attach,
        NK.GlobalCFT.Place.ofFinite (oddPrime (K := K) A.1 (hTfin A.1 A.2)) ≠ v := by
      intro A hA hEq
      exact hv (Finset.mem_image.mpr ⟨A, hA, hEq⟩)
    have h1 : oTheta (K := K) (p := p) ζ hζ α β v = 1 := hout v hv'
    rw [← h1]
    rfl
  -- the product formula at the Kummer level of `α`
  have hprod : (∏ v ∈ s, oTheta (K := K) (p := p) ζ hζ α β v) = 1 :=
    Work.SSGRoute.ZDataMup.oddArtin_product (K := K)
      (hLevel (Ω := Ω) (K := K) (p := p) α) hcomm β s hs
  -- the character of a product is the sum of the characters
  have hzero : ∑ v ∈ s, (hChar (K := K) (p := p) ζ hζ α (le_refl _)
      (oTheta (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ α β v)).toAdd = 0 := by
    rw [← hChar_cprod (K := K) (p := p) (L := hLevel (Ω := Ω) (K := K) (p := p) α) ζ hζ α
      (le_refl _) hcomm s (fun v => oTheta (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ α β v)]
    rw [show NK.CFTLib.IdeleHasse.cprod hcomm s
        (fun v => oTheta (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ α β v)
        = (∏ v ∈ s, oTheta (K := K) (p := p) ζ hζ α β v) from rfl, hprod]
    rw [map_one]
    rfl
  calc ∑ A ∈ T'.attach,
        oPairForm (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ (hTfin A.1 A.2)
          (Work.SSGRoute.toClass p k Ω K (ZMod p) (SSGRoute.decomp k A.1 ⊓ K.fixingSubgroup) a)
          (Work.SSGRoute.toClass p k Ω K (ZMod p) (SSGRoute.decomp k A.1 ⊓ K.fixingSubgroup) b)
      = ∑ A ∈ T'.attach, (hChar (K := K) (p := p) ζ hζ α (le_refl _)
          (oTheta (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ α β (φ A))).toAdd :=
        Finset.sum_congr rfl (fun A _ => hstep A)
    _ = ∑ v ∈ s, (hChar (K := K) (p := p) ζ hζ α (le_refl _)
          (oTheta (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ α β v)).toAdd :=
        (Finset.sum_image (f := fun v => (hChar (K := K) (p := p) ζ hζ α (le_refl _)
          (oTheta (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ α β v)).toAdd) (g := φ) hφinj).symm
    _ = 0 := hzero

end Work.SSGRoute.ZDataMup.OddForm
