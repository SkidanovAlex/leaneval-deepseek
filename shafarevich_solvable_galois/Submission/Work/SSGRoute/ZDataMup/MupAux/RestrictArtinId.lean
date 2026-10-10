import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Submission.NK.NUV2.ARL.transferSelfContained
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Artin symbol of `Ω/E` restricts to that of `E·L/E` (ideal moduli)

Ideal-modulus version of `NK.NUV2.ARL.SC.restrictNormalHom_artinSym_eq_ofLe`: for an auxiliary field
`E ⊆ Ω = L(ζ_M)`, an ideal modulus `𝔠` of `E` whose support contains every prime ramified in `Ω/E`,
and a fractional ideal `𝔄` of `E` coprime to `𝔠`, the Artin symbol of `𝔄` in `E·L/E` is the
restriction of its Artin symbol in `Ω/E`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.ZDataMup.MupAux

theorem restrictNormalHom_artinSymId_eq_ofLe {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (M : ℕ) [NeZero M] (E : IntermediateField K (CyclotomicField M L))
    [IsGalois ↥E (CyclotomicField M L)]
    [IsMulCommutative (Gal((CyclotomicField M L)/↥E))]
    [IsGalois ↥E ↥(NK.CFTLib.ARLAlt.ofLe E
      (E ⊔ NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M) le_sup_left)]
    [IsMulCommutative (Gal(↥(NK.CFTLib.ARLAlt.ofLe E
      (E ⊔ NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M) le_sup_left)/↥E))]
    (hcommΩ : ∀ a b : Gal((CyclotomicField M L)/↥E), a * b = b * a)
    (hcommC : ∀ a b : Gal(↥(NK.CFTLib.ARLAlt.ofLe E
      (E ⊔ NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M) le_sup_left)/↥E), a * b = b * a)
    (𝔠 : Ideal (NumberField.RingOfIntegers ↥E))
    (hram : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥E,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := ↥E)
        (L := CyclotomicField M L) 𝔮 →
      NK.CFTLib.ArtinReciprocityIdeal.DvdPrime 𝔠 𝔮)
    (𝔄 : NK.CFTLib.ArtinReciprocityIdeal.Frac ↥E)
    (hcop : NK.CFTLib.ArtinReciprocityIdeal.FracCoprimeId (K := ↥E) 𝔠 𝔄) :
    AlgEquiv.restrictNormalHom (F := ↥E) (K₁ := CyclotomicField M L)
        ↥(NK.CFTLib.ARLAlt.ofLe E
          (E ⊔ NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M) le_sup_left)
        (NK.CFTLib.Arl.artinSym (K := ↥E) (L := CyclotomicField M L) hcommΩ
          (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E))
      = NK.CFTLib.Arl.artinSym (K := ↥E)
          (L := ↥(NK.CFTLib.ARLAlt.ofLe E
            (E ⊔ NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M) le_sup_left)) hcommC
          (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E) := by
  classical
  let LE := E ⊔ NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M
  letI hMCΩ : IsMulCommutative (Gal((CyclotomicField M L)/↥E)) := ⟨⟨hcommΩ⟩⟩
  letI hMCC : IsMulCommutative (Gal(↥(NK.CFTLib.ARLAlt.ofLe E LE le_sup_left)/↥E)) := ⟨⟨hcommC⟩⟩
  letI : CommMonoid (CyclotomicField M L ≃ₐ[↥E] CyclotomicField M L) :=
    NK.CFTLib.Arl.galCommMonoid hcommΩ
  letI : CommMonoid (↥(NK.CFTLib.ARLAlt.ofLe E LE le_sup_left) ≃ₐ[↥E]
      ↥(NK.CFTLib.ARLAlt.ofLe E LE le_sup_left)) := NK.CFTLib.Arl.galCommMonoid hcommC
  let F : NK.CFTLib.ArtinReciprocityIdeal.Frac ↥E →*
      Gal(↥(NK.CFTLib.ARLAlt.ofLe E LE le_sup_left)/↥E) :=
    (AlgEquiv.restrictNormalHom (F := ↥E) (K₁ := CyclotomicField M L)
      ↥(NK.CFTLib.ARLAlt.ofLe E LE le_sup_left)).comp
      (NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := ↥E)
        (L := CyclotomicField M L) hcommΩ)
  let G : NK.CFTLib.ArtinReciprocityIdeal.Frac ↥E →*
      Gal(↥(NK.CFTLib.ARLAlt.ofLe E LE le_sup_left)/↥E) :=
    NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := ↥E)
      (L := ↥(NK.CFTLib.ARLAlt.ofLe E LE le_sup_left)) hcommC
  have hFG : F 𝔄 = G 𝔄 := by
    set S : Finset (NK.Chebotarev.PrimeIdeal ↥E) :=
      (Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors (K := ↥E)
        (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E))).toFinset with hS
    have hSmem : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥E,
        𝔮 ∈ S ↔ FractionalIdeal.count ↥E 𝔮 (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E) ≠ 0 :=
      fun 𝔮 => Set.Finite.mem_toFinset _
    have hsupp : Function.mulSupport (fun 𝔮 : NK.Chebotarev.PrimeIdeal ↥E =>
        ((𝔮.asIdeal : Ideal (𝓞 ↥E)) : FractionalIdeal (𝓞 ↥E)⁰ ↥E) ^
          FractionalIdeal.count ↥E 𝔮 (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E)) ⊆ ↑S := by
      intro 𝔮 h𝔮
      exact (hSmem 𝔮).mpr fun h0 => h𝔮 (by simp only [h0, zpow_zero])
    have hfac : (∏ 𝔮 ∈ S, (NK.CFTLib.ARL.primeUnit 𝔮) ^
        FractionalIdeal.count ↥E 𝔮 (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E)) = 𝔄 := by
      apply Units.ext
      rw [Units.coe_prod]
      simp only [NK.CFTLib.ARL.primeUnit_val, Units.val_zpow_eq_zpow_val]
      rw [← finprod_eq_prod_of_mulSupport_subset _ hsupp]
      exact FractionalIdeal.finprod_heightOneSpectrum_factorization' ↥E 𝔄.ne_zero
    have hprime : ∀ 𝔮 ∈ S, F (NK.CFTLib.ARL.primeUnit 𝔮)
        = G (NK.CFTLib.ARL.primeUnit 𝔮) := by
      intro 𝔮 h𝔮
      have hcount : FractionalIdeal.count ↥E 𝔮 (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E) ≠ 0 :=
        (hSmem 𝔮).mp h𝔮
      have hunrΩ : NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := ↥E)
          (L := CyclotomicField M L) 𝔮 := by
        by_contra h
        exact hcount (hcop 𝔮 (hram 𝔮 h))
      have hunrC : NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := ↥E)
          (L := ↥(NK.CFTLib.ARLAlt.ofLe E LE le_sup_left)) 𝔮 :=
        NK.NUV2.ARL.SC.isUnramified_ofLe_of_isUnramified (K := K) (L := L) M E LE le_sup_left
          𝔮 hunrΩ
      have hF : F (NK.CFTLib.ARL.primeUnit 𝔮) =
          AlgEquiv.restrictNormalHom (F := ↥E) (K₁ := CyclotomicField M L)
            ↥(NK.CFTLib.ARLAlt.ofLe E LE le_sup_left)
            (NK.Chebotarev.frobAtPrime (K := ↥E) (L := CyclotomicField M L) 𝔮) := by
        change AlgEquiv.restrictNormalHom (F := ↥E) (K₁ := CyclotomicField M L)
            ↥(NK.CFTLib.ARLAlt.ofLe E LE le_sup_left)
            (NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := ↥E)
              (L := CyclotomicField M L) hcommΩ (NK.CFTLib.ARL.primeUnit 𝔮)) = _
        rw [NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply,
          NK.CFTLib.ARL.primeUnit_val, NK.CFTLib.Arl.artinSym_prime]
      have hG : G (NK.CFTLib.ARL.primeUnit 𝔮) =
          NK.Chebotarev.frobAtPrime (K := ↥E)
            (L := ↥(NK.CFTLib.ARLAlt.ofLe E LE le_sup_left)) 𝔮 := by
        change NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := ↥E)
          (L := ↥(NK.CFTLib.ARLAlt.ofLe E LE le_sup_left)) hcommC
          (NK.CFTLib.ARL.primeUnit 𝔮) = _
        rw [NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply,
          NK.CFTLib.ARL.primeUnit_val, NK.CFTLib.Arl.artinSym_prime]
      rw [hF, hG]
      exact NK.CFTLib.ARLAlt.restrictNormalHom_frobAtPrime_ofLe (K := K) (L := L) M E LE
        le_sup_left le_sup_right rfl 𝔮 hunrC
    calc F 𝔄 = F (∏ 𝔮 ∈ S, (NK.CFTLib.ARL.primeUnit 𝔮) ^
            FractionalIdeal.count ↥E 𝔮 (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E)) := by rw [hfac]
      _ = ∏ 𝔮 ∈ S, F (NK.CFTLib.ARL.primeUnit 𝔮) ^
            FractionalIdeal.count ↥E 𝔮 (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E) := by
          rw [map_prod]
          exact Finset.prod_congr rfl fun 𝔮 _ => map_zpow _ _ _
      _ = ∏ 𝔮 ∈ S, G (NK.CFTLib.ARL.primeUnit 𝔮) ^
            FractionalIdeal.count ↥E 𝔮 (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E) :=
          Finset.prod_congr rfl fun 𝔮 h𝔮 => by rw [hprime 𝔮 h𝔮]
      _ = G (∏ 𝔮 ∈ S, (NK.CFTLib.ARL.primeUnit 𝔮) ^
            FractionalIdeal.count ↥E 𝔮 (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E)) := by
          rw [map_prod]
          exact Finset.prod_congr rfl fun 𝔮 _ => (map_zpow _ _ _).symm
      _ = G 𝔄 := by rw [hfac]
  simpa only [F, G, MonoidHom.comp_apply,
    NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply] using hFG

end Work.SSGRoute.ZDataMup.MupAux
