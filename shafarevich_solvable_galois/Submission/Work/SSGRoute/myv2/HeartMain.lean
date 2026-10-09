import Mathlib
import Submission.Work.SSGRoute.N2v2.artin_lifts_zdata
import Submission.Work.SSGRoute.N2v2.exists_artinMap_with_decompLift
import Submission.Work.SSGRoute.N2v2.heart_chi1_part
import Submission.Work.SSGRoute.N2v2.char_eq_neg_localSum
import Submission.Work.SSGRoute.N2v2.isUnramifiedIn_of_notMem_Tprime
import Submission.Work.SSGRoute.N2v2.exists_kummerChar_level
import Submission.Work.SSGRoute.N2v2.kummerSplit_of_hsplit
import Submission.Work.SSGRoute.N2v2.artin_fixes_of_local_factors
import Submission.Work.SSGRoute.ZDataMup.localFaithful_abelian
import Submission.Work.SSGRoute.ZDataMup.localFactorProductFormulaAux
import Submission.Work.SSGRoute.ZSplit.exists_kummerCocharZMod_of_additive_locConst
import Submission.Work.SSGRoute.ZSplit.FrobeniusValue
import Submission.Work.SSGRoute.myv2.KummerSep
import Submission.Work.SSGRoute.myv2.KummerFieldInst
import Submission.Work.SSGRoute.myv2.Hdiag
import Submission.Work.SSGRoute.myv2.Hdata
import Submission.Work.SSGRoute.myv2.LevelE
import Submission.Work.SSGRoute.myv2.ExpP
import Submission.Work.SSGRoute.myv2.localFactor_archimedean_eq_one
import Submission.Work.SSGRoute.myv2.transfer_of_le
import Submission.Work.SSGRoute.myv2.gsum_vanishes
import Submission.Work.SSGRoute.EscapeCoreLib.baseChange_over_K
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The main assembly of the `hsplit` orthogonality (the heart of the `N2` repair)

This file proves the heart `Work.SSGRoute.N2v2.alpha_fixes_inf_hsplit_main` — the field form of the
escape orthogonality with the `hsplit` repair — by assembling the two per-place halves
(`N2v2.heart_chi1_part`, `N2v2.heart_chi2_part`, both proved) at a common level
`E = M ⊔ ↥K⟮a^{1/p}⟯ ⊔ ↥K⟮c₁^{1/p}⟯ ⊔ ↥K⟮c₂^{1/p}⟯ ⊔ ↥K⟮b_g^{1/p}⟯`, together with

* `N2v2.exists_artinMap_with_lifts` (the Artin map of `E/↥K` with kernel, Frobenius normalisation and
  both lift clauses) for the local factors `θ = Φ ∘ onePlace`,
* `myv2.transfer_of_le` for the compatibility of the local factors of `E` with those of `M`,
* `myv2.localFactor_archimedean_eq_one` and `myv2.gsum_vanishes` for the archimedean and the
  `g`-sum inputs of the halves.
-/

open scoped Pointwise NumberField
open NumberField IsDedekindDomain
open NK.GlobalCFT

namespace Work.SSGRoute.N2v2

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-- `Multiplicative.ofAdd` turns a `Finset`-sum into a product. -/
private lemma ofAdd_sum_eq_prod {p : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ZMod p) :
    Multiplicative.ofAdd (∑ i ∈ s, f i) = ∏ i ∈ s, Multiplicative.ofAdd (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.prod_insert ha, ofAdd_add, ih]

/-- A `Finset`-product in `Multiplicative (ZMod p)` is the exponential of the sum of the
`toAdd`-values. -/
private lemma prod_eq_ofAdd_sum {p : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Multiplicative (ZMod p)) :
    (∏ i ∈ s, f i) = Multiplicative.ofAdd (∑ i ∈ s, (f i).toAdd) := by
  classical
  rw [ofAdd_sum_eq_prod]
  exact Finset.prod_congr rfl (fun i _ => (ofAdd_toAdd (f i)).symm)

/-- **The orthogonality of the escape-form Grünwald statement (field form, with `hsplit` and with
`hT'above`)** — the assembly.  See `Work.SSGRoute.N2v2.alpha_fixes_inf_ssg8_hsplit` for the statement
that the target consumes; this is the same claim under a different name, proved here. -/
theorem alpha_fixes_inf_hsplit_main (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (hKimag : p = 2 → ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → c = 1)
    (L₁ L₂ : IntermediateField k Ω) [FiniteDimensional k L₁] [IsGalois k L₁]
    [FiniteDimensional k L₂] [IsGalois k L₂] (hKL₁ : K ≤ L₁) (hKL₂ : K ≤ L₂)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (T' : Finset (NK.Chebotarev.PrimeIdeal ↥K))
    (hTbelow : ∀ A ∈ T, ∃ 𝔭 ∈ T', A.comap (algebraMap ↥K Ω) =
      HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (hT'above : ∀ 𝔭 ∈ T', ∃ A ∈ T, A.comap (algebraMap ↥K Ω) =
      HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, (∃ τ ∈ K.fixingSubgroup, τ • A = B) → A = B)
    (hTcov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (B.valuation (p : Ω) < 1 ∨
        (∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ L₁.fixingSubgroup) ∨
        (∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ L₂.fixingSubgroup)) →
      ∃ A ∈ T, ∃ τ ∈ K.fixingSubgroup, τ • A = B)
    (g : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hg : ∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, g (x * y) = g x + g y)
    (hgc : SSGRoute.IsLocConstOn K.fixingSubgroup g)
    (hgram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ T, ∀ τ ∈ K.fixingSubgroup, τ • A ≠ B) → ¬ SSGRoute.IsSplitIn k L₁ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → g σ = 0)
    (h : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p)
    (hh : ∀ A ∈ T, ∀ x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      ∀ y ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A (x * y) = h A x + h A y)
    (hhc : ∀ A ∈ T, ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      ∀ x ∈ U, x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup → h A x = 0)
    (horth₁ : ∀ A ∈ T,
      (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A σ = 0) ∨
      (∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
        (∀ σ ∈ L₁.fixingSubgroup, χ σ = 0) →
        ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, χ σ = 0) ∨
      ((∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → h A σ = 0) ∧
        ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
          (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
          (∀ σ ∈ L₁.fixingSubgroup, χ σ = 0) →
          ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → χ σ = 0))
    (horth₂ : ∀ A ∈ T,
      (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, g σ + h A σ = 0) ∨
      (∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
        (∀ σ ∈ L₂.fixingSubgroup, χ σ = 0) →
        ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, χ σ = 0) ∨
      ((∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → g σ + h A σ = 0) ∧
        ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
          (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
          (∀ σ ∈ L₂.fixingSubgroup, χ σ = 0) →
          ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → χ σ = 0))
    (hsplit : ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
      (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
      (∀ σ ∈ (L₁ ⊔ L₂).fixingSubgroup, χ σ = 0) →
      ∃ χ₁ χ₂ : (Ω ≃ₐ[k] Ω) → ZMod p,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ₁ (x * y) = χ₁ x + χ₁ y) ∧
        (∀ σ ∈ L₁.fixingSubgroup, χ₁ σ = 0) ∧
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ₂ (x * y) = χ₂ x + χ₂ y) ∧
        (∀ σ ∈ L₂.fixingSubgroup, χ₂ σ = 0) ∧
        ∀ σ ∈ K.fixingSubgroup, χ σ = χ₁ σ + χ₂ σ)
    (a : (↥K)ˣ)
    (ha : ∀ A ∈ T, ∀ σ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
      g (σ : Ω ≃ₐ[k] Ω) + h A (σ : Ω ≃ₐ[k] Ω) =
        kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ a
          (Work.SSGRoute.gesLocalToGalK K σ))
    (M : IntermediateField ↥K Ω) [FiniteDimensional ↥K M] [IsGalois ↥K M] [NumberField ↥M]
    [IsMulCommutative (↥M ≃ₐ[↥K] ↥M)]
    (hM : Idele.normClassSubgroup ↥K ↥M = Work.SSGRoute.SSG8Escape.gesUPow ↥K p T')
    (art : Idele ↥K →* (↥M ≃ₐ[↥K] ↥M))
    (hker : art.ker = Idele.normImage ↥K ↥M ⊔ Idele.principalSubgroup ↥K)
    (hfrob : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥K,
      NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥M) 𝔮 →
      art (NK.HeckeL.ideleOfPrime ↥K 𝔮) = NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥M) 𝔮)
    (α : ↥M ≃ₐ[↥K] ↥M)
    (hα : art (NK.NUV2.RouteB.RayModulus.fracIdele (tFreePart (K := ↥K) T' a)) = α) :
    ∀ x : ↥M, ((x : Ω) ∈ (L₁ ⊔ L₂)) → α x = x := by
  classical
  haveI hAlgClosedΩ : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  haveI hNumK : NumberField ↥K := NumberField.of_module_finite k ↥K
  haveI hAlgK : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
  haveI hSepK : IsSepClosure ↥K Ω := IsSepClosure.of_isAlgClosure_of_perfectField ↥K Ω
  have hcommM : ∀ a b : ↥M ≃ₐ[↥K] ↥M, a * b = b * a := fun a b => mul_comm' a b
  have hζΩ : IsPrimitiveRoot ((ζ : ↥K) : Ω) p :=
    hζ.map_of_injective (algebraMap ↥K Ω).injective
  -- ## Step 1: `Gal(M/↥K)` has exponent `p`
  have hexpM : ∀ σ : ↥M ≃ₐ[↥K] ↥M, σ ^ p = 1 :=
    gal_pow_eq_one p K T' M hM art hker hfrob
  -- ## Step 2: reduce to Kummer characters
  refine alpha_fixes_of_kummerChars p k Ω K ζ hζ L₁ L₂ hKL₁ hKL₂ M hexpM α ?_
  intro c hc σ hσ
  -- ## the descent of `χ_c` to the level `M`
  obtain ⟨χM, hχM⟩ := exists_kummerChar_level p k Ω K ζ hζ M c (le_trans hc inf_le_left)
  -- ## the Kummer split `c = c₁ c₂`
  obtain ⟨c₁, c₂, hc₁, hc₂, hsplitc⟩ :=
    kummerSplit_of_hsplit p k Ω K ζ hζ L₁ L₂ hKL₁ hKL₂ hsplit (L₁ ⊔ L₂)
      (hKL₁.trans le_sup_left) le_rfl
      (by rw [IntermediateField.fixingSubgroup_sup]; exact le_sup_left)
      c (le_trans hc inf_le_right)
  -- ## the global unit `bg` with `χ_{bg} = g`
  obtain ⟨bg, hbgraw⟩ :=
    ZSplit.exists_kummerCocharZMod_of_additive_locConst p k Ω K ((ζ : ↥K) : Ω) ζ.2 hζΩ g hg hgc
  have hbg : ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup),
      g σ = Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ bg
        ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩) := by
    intro τ hτ
    rw [hbgraw τ hτ,
      ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ((ζ : ↥K) : Ω)) (hζK := ζ.2)
        (hζ := hζΩ) (β := bg) hτ]
  -- ## the level `E`
  set Fa : IntermediateField ↥K Ω := NK.LocalAnabelian.kummerField (K' := Ω) p a with hFadef
  set Fc₁ : IntermediateField ↥K Ω := NK.LocalAnabelian.kummerField (K' := Ω) p c₁ with hFc₁def
  set Fc₂ : IntermediateField ↥K Ω := NK.LocalAnabelian.kummerField (K' := Ω) p c₂ with hFc₂def
  set Fbg : IntermediateField ↥K Ω := NK.LocalAnabelian.kummerField (K' := Ω) p bg with hFbgdef
  set E : IntermediateField ↥K Ω := M ⊔ Fa ⊔ Fc₁ ⊔ Fc₂ ⊔ Fbg with hEdef
  -- instances and the exponent for the Kummer fields
  have hFDk (x : (↥K)ˣ) : FiniteDimensional ↥K
      (NK.LocalAnabelian.kummerField (K' := Ω) p x) :=
    NK.GlobalCFTdeep.SecondInequality.finiteDimensional_kummerField (K' := Ω) (p := p) Fact.out hζ x
  have hGalk (x : (↥K)ˣ) : IsGalois ↥K (NK.LocalAnabelian.kummerField (K' := Ω) p x) := by
    by_cases hx : x ∈ NK.LocalAnabelian.powSubgroup p ↥K
    · rw [kummerField_eq_bot_of_mem_powSubgroup p K ζ hζ x hx]
      infer_instance
    · exact (NK.LocalAnabelian.Kummer.isGalois_kummerField_and_finrank (K' := Ω) p Fact.out hζ
        (k := ↥K) x hx).1
  haveI hFa_fd : FiniteDimensional ↥K ↥Fa := hFadef ▸ hFDk a
  haveI hFa_gal : IsGalois ↥K ↥Fa := hFadef ▸ hGalk a
  haveI hFa_comm : IsMulCommutative (↥Fa ≃ₐ[↥K] ↥Fa) :=
    hFadef ▸ kummerField_isMulCommutative p K ζ hζ a
  have hFa_exp : ∀ σ : ↥Fa ≃ₐ[↥K] ↥Fa, σ ^ p = 1 :=
    hFadef ▸ kummerField_pow_eq_one p K ζ hζ a
  haveI hFc₁_fd : FiniteDimensional ↥K ↥Fc₁ := hFc₁def ▸ hFDk c₁
  haveI hFc₁_gal : IsGalois ↥K ↥Fc₁ := hFc₁def ▸ hGalk c₁
  haveI hFc₁_comm : IsMulCommutative (↥Fc₁ ≃ₐ[↥K] ↥Fc₁) :=
    hFc₁def ▸ kummerField_isMulCommutative p K ζ hζ c₁
  have hFc₁_exp : ∀ σ : ↥Fc₁ ≃ₐ[↥K] ↥Fc₁, σ ^ p = 1 :=
    hFc₁def ▸ kummerField_pow_eq_one p K ζ hζ c₁
  haveI hFc₂_fd : FiniteDimensional ↥K ↥Fc₂ := hFc₂def ▸ hFDk c₂
  haveI hFc₂_gal : IsGalois ↥K ↥Fc₂ := hFc₂def ▸ hGalk c₂
  haveI hFc₂_comm : IsMulCommutative (↥Fc₂ ≃ₐ[↥K] ↥Fc₂) :=
    hFc₂def ▸ kummerField_isMulCommutative p K ζ hζ c₂
  have hFc₂_exp : ∀ σ : ↥Fc₂ ≃ₐ[↥K] ↥Fc₂, σ ^ p = 1 :=
    hFc₂def ▸ kummerField_pow_eq_one p K ζ hζ c₂
  haveI hFbg_fd : FiniteDimensional ↥K ↥Fbg := hFbgdef ▸ hFDk bg
  haveI hFbg_gal : IsGalois ↥K ↥Fbg := hFbgdef ▸ hGalk bg
  haveI hFbg_comm : IsMulCommutative (↥Fbg ≃ₐ[↥K] ↥Fbg) :=
    hFbgdef ▸ kummerField_isMulCommutative p K ζ hζ bg
  have hFbg_exp : ∀ σ : ↥Fbg ≃ₐ[↥K] ↥Fbg, σ ^ p = 1 :=
    hFbgdef ▸ kummerField_pow_eq_one p K ζ hζ bg
  -- the four successive composita
  haveI h1_fd : FiniteDimensional ↥K ↥(M ⊔ Fa) := IntermediateField.finiteDimensional_sup M Fa
  haveI h1_gal : IsGalois ↥K ↥(M ⊔ Fa) := inferInstance
  haveI h1_comm : IsMulCommutative (↥(M ⊔ Fa) ≃ₐ[↥K] ↥(M ⊔ Fa)) :=
    Work.SSGRoute.myv2.sup_isMulCommutative K M Fa
  haveI h1_nf : NumberField ↥(M ⊔ Fa) := NumberField.of_module_finite ↥K ↥(M ⊔ Fa)
  have h1_exp : ∀ σ : ↥(M ⊔ Fa) ≃ₐ[↥K] ↥(M ⊔ Fa), σ ^ p = 1 :=
    Work.SSGRoute.myv2.sup_pow_eq_one K M Fa p hexpM hFa_exp
  haveI h2_fd : FiniteDimensional ↥K ↥((M ⊔ Fa) ⊔ Fc₁) :=
    IntermediateField.finiteDimensional_sup (M ⊔ Fa) Fc₁
  haveI h2_gal : IsGalois ↥K ↥((M ⊔ Fa) ⊔ Fc₁) := inferInstance
  haveI h2_comm : IsMulCommutative (↥((M ⊔ Fa) ⊔ Fc₁) ≃ₐ[↥K] ↥((M ⊔ Fa) ⊔ Fc₁)) :=
    Work.SSGRoute.myv2.sup_isMulCommutative K (M ⊔ Fa) Fc₁
  haveI h2_nf : NumberField ↥((M ⊔ Fa) ⊔ Fc₁) := NumberField.of_module_finite ↥K _
  have h2_exp : ∀ σ : ↥((M ⊔ Fa) ⊔ Fc₁) ≃ₐ[↥K] ↥((M ⊔ Fa) ⊔ Fc₁), σ ^ p = 1 :=
    Work.SSGRoute.myv2.sup_pow_eq_one K (M ⊔ Fa) Fc₁ p h1_exp hFc₁_exp
  haveI h3_fd : FiniteDimensional ↥K ↥(((M ⊔ Fa) ⊔ Fc₁) ⊔ Fc₂) :=
    IntermediateField.finiteDimensional_sup ((M ⊔ Fa) ⊔ Fc₁) Fc₂
  haveI h3_gal : IsGalois ↥K ↥(((M ⊔ Fa) ⊔ Fc₁) ⊔ Fc₂) := inferInstance
  haveI h3_comm : IsMulCommutative
      (↥(((M ⊔ Fa) ⊔ Fc₁) ⊔ Fc₂) ≃ₐ[↥K] ↥(((M ⊔ Fa) ⊔ Fc₁) ⊔ Fc₂)) :=
    Work.SSGRoute.myv2.sup_isMulCommutative K ((M ⊔ Fa) ⊔ Fc₁) Fc₂
  haveI h3_nf : NumberField ↥(((M ⊔ Fa) ⊔ Fc₁) ⊔ Fc₂) := NumberField.of_module_finite ↥K _
  have h3_exp : ∀ σ : ↥(((M ⊔ Fa) ⊔ Fc₁) ⊔ Fc₂) ≃ₐ[↥K] ↥(((M ⊔ Fa) ⊔ Fc₁) ⊔ Fc₂),
      σ ^ p = 1 :=
    Work.SSGRoute.myv2.sup_pow_eq_one K ((M ⊔ Fa) ⊔ Fc₁) Fc₂ p h2_exp hFc₂_exp
  haveI hE_fd : FiniteDimensional ↥K ↥E := by
    rw [hEdef]
    exact IntermediateField.finiteDimensional_sup (((M ⊔ Fa) ⊔ Fc₁) ⊔ Fc₂) Fbg
  haveI hE_gal : IsGalois ↥K ↥E := by
    rw [hEdef]
    infer_instance
  haveI hE_comm : IsMulCommutative (↥E ≃ₐ[↥K] ↥E) := by
    rw [hEdef]
    exact Work.SSGRoute.myv2.sup_isMulCommutative K (((M ⊔ Fa) ⊔ Fc₁) ⊔ Fc₂) Fbg
  haveI hE_nf : NumberField ↥E := by
    rw [hEdef]
    exact NumberField.of_module_finite ↥K _
  have hexpE : ∀ σ : ↥E ≃ₐ[↥K] ↥E, σ ^ p = 1 := by
    rw [hEdef]
    exact Work.SSGRoute.myv2.sup_pow_eq_one K (((M ⊔ Fa) ⊔ Fc₁) ⊔ Fc₂) Fbg p h3_exp hFbg_exp
  -- the inclusion lemmas
  have hME : M ≤ E := by
    rw [hEdef]
    exact le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left))
  have hFaE : Fa ≤ E := by
    rw [hEdef]
    exact le_sup_right.trans (le_sup_left.trans (le_sup_left.trans le_sup_left))
  have hFc₁E : Fc₁ ≤ E := by
    rw [hEdef]
    exact le_sup_right.trans (le_sup_left.trans le_sup_left)
  have hFc₂E : Fc₂ ≤ E := by
    rw [hEdef]
    exact le_sup_right.trans le_sup_left
  have hFbgE : Fbg ≤ E := by
    rw [hEdef]
    exact le_sup_right
  -- ## the Artin map of `E` and its local factors
  obtain ⟨Φ, hΦker, hΦfrob, hΦinertia⟩ :=
    Work.SSGRoute.N2v2.exists_artinMap_with_inertiaLift_zdata (K := K) E
  have hΦdec : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
      (𝔭 : NK.Chebotarev.PrimeIdeal ↥K),
      A.comap (algebraMap ↥K Ω) = HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 →
      ∀ x : (↥K)ˣ, ∃ σ : Ω ≃ₐ[↥K] Ω, σ ∈ SSGRoute.decomp (k := ↥K) A ∧
        AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E σ =
          Φ (NK.HassePrinciple.onePlace (Place.ofFinite 𝔭)
            (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔭) x)) :=
    fun A hA 𝔭 h𝔭 x =>
      Work.SSGRoute.N2v2.decompLift_of_artinMap (K := K) (E := E) Φ hΦker hΦfrob A hA 𝔭 h𝔭 x
  let θ : (v : Place ↥K) → (Place.localField ↥K v)ˣ →* (↥E ≃ₐ[↥K] ↥E) := fun v =>
    { toFun := fun u => Φ (NK.HassePrinciple.onePlace v u)
      map_one' := by
        show Φ (NK.HassePrinciple.onePlace v 1) = 1
        rw [← NK.CFTLib.IdeleHasse.onePlaceHom_apply (K := ↥K) v (1 : _), map_one, map_one]
      map_mul' := fun u w => by
        show Φ (NK.HassePrinciple.onePlace v (u * w)) = Φ (NK.HassePrinciple.onePlace v u) *
          Φ (NK.HassePrinciple.onePlace v w)
        rw [onePlace_mul_local v u w, map_mul] }
  have hlift : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
      (𝔭 : NK.Chebotarev.PrimeIdeal ↥K),
      A.comap (algebraMap ↥K Ω) = HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 →
      ∀ x : (↥K)ˣ, ∃ σ : Ω ≃ₐ[↥K] Ω, σ ∈ SSGRoute.decomp (k := ↥K) A ∧
        AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E σ =
          θ (Place.ofFinite 𝔭) (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
            (Place.ofFinite 𝔭) x) :=
    fun A hA 𝔭 h𝔭 x => hΦdec A hA 𝔭 h𝔭 x
  have hunith : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
      (𝔭 : NK.Chebotarev.PrimeIdeal ↥K),
      A.comap (algebraMap ↥K Ω) = HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 →
      ∀ u : (Place.localField ↥K (Place.ofFinite 𝔭))ˣ,
        u ∈ Place.localUnits ↥K (Place.ofFinite 𝔭) →
        ∃ σ : Ω ≃ₐ[↥K] Ω, SSGRoute.IsInertia k A (σ.restrictScalars k) ∧
          AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E σ =
            θ (Place.ofFinite 𝔭) u :=
    fun A hA 𝔭 h𝔭 u hu => hΦinertia A hA 𝔭 h𝔭 u hu
  have hθker : ∀ v : Place ↥K, (θ v).ker =
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥E) v := by
    intro v
    ext u
    rw [MonoidHom.mem_ker]
    show Φ (NK.HassePrinciple.onePlace v u) = 1 ↔ _
    rw [← MonoidHom.mem_ker, hΦker]
    constructor
    · intro h
      exact (NK.CFTLib.IdeleHasse.onePlace_mem_normImage_iff (K := ↥K) (L := ↥E) v u).mp
        (Work.SSGRoute.ZDataMup.localFaithful_abelian (K := ↥K) (L := ↥E)
          (fun a b => mul_comm' a b) h)
    · intro h
      exact Subgroup.mem_sup_left
        ((NK.CFTLib.IdeleHasse.onePlace_mem_normImage_iff (K := ↥K) (L := ↥E) v u).mpr h)
  have hθprod : ∀ (x : (↥K)ˣ) (s : Finset (Place ↥K)),
      (∀ v, v ∉ s → θ v (NK.CFTLib.IdeleHasse.localImageAt v x) = 1) →
      NK.CFTLib.IdeleHasse.cprod (fun a b => mul_comm' a b) s
        (fun v => θ v (NK.CFTLib.IdeleHasse.localImageAt v x)) = 1 := by
    intro x s hs
    have hprin : ∀ c : (↥K)ˣ, Φ (Idele.principalIdele ↥K c) = 1 := by
      intro c
      rw [← MonoidHom.mem_ker, hΦker]
      exact Subgroup.mem_sup_right (Idele.mem_principalSubgroup.mpr ⟨c, rfl⟩)
    have hnorm : ∀ y : Idele ↥E, Φ (Idele.normIdeleHom ↥K ↥E y) = 1 := by
      intro y
      rw [← MonoidHom.mem_ker, hΦker]
      exact Subgroup.mem_sup_left (Idele.mem_normImage.mpr ⟨y, fun v => rfl⟩)
    exact Work.SSGRoute.ZDataMup.cprod_localFactor_eq_one (K := ↥K) (L := ↥E)
      (fun a b => mul_comm' a b) Φ hprin hnorm x s (fun v hv => hs v hv)
  have harchE : ∀ v : Place ↥K, (∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥K,
      v ≠ Place.ofFinite 𝔮) → ∀ u : (Place.localField ↥K v)ˣ, θ v u = 1 :=
    Work.SSGRoute.myv2.localFactor_archimedean_eq_one p k Ω K ζ hζ hKimag E θ
  -- ## the twisted diagonal
  have hdiagLift : ∀ 𝔭 ∈ T', ∃ σ₀ : Ω ≃ₐ[↥K] Ω,
      ∀ (y : (↥K)ˣ), NK.LocalAnabelian.kummerField (K' := Ω) p y ≤ E →
      ∀ τ : Ω ≃ₐ[↥K] Ω,
        AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E τ =
          θ (Place.ofFinite 𝔭) (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
            (Place.ofFinite 𝔭) y) →
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ y τ =
          Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ y σ₀ :=
    fun 𝔭 _ => hdiag_E p K ζ hζ E Φ 𝔭
      (fun c' hc' => hdata_of_kummerField_le p K ζ hζ E Φ hΦker hΦfrob 𝔭 c' hc')
  -- ## the vanishing of `g` on the fixing subgroup of `E`
  have hgE : ∀ τ : Ω ≃ₐ[↥K] Ω, τ ∈ E.fixingSubgroup → g (τ.restrictScalars k) = 0 := by
    intro τ hτ
    have hτk : τ.restrictScalars k ∈ K.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact τ.commutes ⟨x, hx⟩
    rw [hbg (τ.restrictScalars k) hτk,
      fixingSubgroupEquiv_restrictScalars_apply K τ hτk]
    exact kummerCharZMod_eq_zero_of_kummerField_le p k Ω K ζ hζ bg E hFbgE τ hτ
  -- ## the descents of `χ_{c₁}` and `χ_{c₂}` to the level `E`
  obtain ⟨χE₁, hχE₁⟩ := exists_kummerChar_level p k Ω K ζ hζ E c₁ (le_trans hFc₁E le_rfl)
  obtain ⟨χE₂, hχE₂⟩ := exists_kummerChar_level p k Ω K ζ hζ E c₂ (le_trans hFc₂E le_rfl)
  -- ## the `g`-sum
  have hgsum : ∑ 𝔭 ∈ T', (χE₁ (θ (Place.ofFinite 𝔭)
      (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔭) bg))).toAdd = 0 :=
    Work.SSGRoute.myv2.gsum_vanishes p k Ω K ζ hζ L₁ hKL₁ T hTfin T' hTbelow
      (fun B hB hcB => hTcov B hB (hcB.elim Or.inl (fun h => Or.inr (Or.inl h))))
      g hg hgc hgram E hexpE θ hθker hθprod harchE
      hlift hunith hgE bg hbg c₁ (le_trans hFc₁E le_rfl) (le_trans hc₁ inf_le_right) χE₁ hχE₁
  -- ## the two per-place halves
  have hsum₂ : ∑ 𝔭 ∈ T', (χE₂ (θ (Place.ofFinite 𝔭)
      (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔭) a))).toAdd = 0 :=
    heart_chi2_part p k Ω K ζ hζ L₂ hKL₂ T hTfin T' hT'above g h horth₂ a ha E hexpE θ
      hlift hunith c₂ (le_trans hFc₂E le_rfl) (le_trans hc₂ inf_le_right) χE₂ hχE₂
  have hsum₁ : ∑ 𝔭 ∈ T', (χE₁ (θ (Place.ofFinite 𝔭)
      (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔭) a))).toAdd = 0 :=
    heart_chi1_part p k Ω K ζ hζ L₁ hKL₁ T hTfin T' hTbelow hT'above
      (fun B hB hcB => hTcov B hB (hcB.elim Or.inl (fun h => Or.inr (Or.inl h)))) g hg hgc hgram h hh
      horth₁ a ha E hexpE θ hθker hθprod harchE hlift hunith hdiagLift hgE hFaE bg hbg c₁
      (le_trans hFc₁E le_rfl) (le_trans hc₁ inf_le_right) χE₁ hχE₁ hgsum
  -- ## the product over `T'` at the level `E`
  have hprodE : (∏ 𝔭 ∈ T', (χE₁ * χE₂) (θ (Place.ofFinite 𝔭)
      (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔭) a))) = 1 := by
    rw [prod_eq_ofAdd_sum]
    have h1 : ∀ 𝔭 ∈ T', ((χE₁ * χE₂) (θ (Place.ofFinite 𝔭)
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔭) a))).toAdd =
        (χE₁ (θ (Place.ofFinite 𝔭)
          (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔭) a))).toAdd +
        (χE₂ (θ (Place.ofFinite 𝔭)
          (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔭) a))).toAdd := by
      intro 𝔭 _
      rw [MonoidHom.mul_apply, toAdd_mul]
    have hsum : (∑ 𝔭 ∈ T', ((χE₁ * χE₂) (θ (Place.ofFinite 𝔭)
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔭) a))).toAdd) = 0 := by
      rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, hsum₁, hsum₂, add_zero]
    rw [hsum, ofAdd_zero]
  -- ## the transfer from the level `E` to the level `M`
  have htr : ∀ (x : Idele ↥K) (y : ↥M),
      (((art x) y : ↥M) : Ω) = (((Φ x) ⟨(y : Ω), hME y.2⟩ : ↥E) : Ω) :=
    Work.SSGRoute.myv2.transfer_of_le p K M E hME art hker hfrob Φ hΦker hΦfrob
  -- ## the character identity at each place of `T'`
  have hterm : ∀ 𝔭 ∈ T', χM (art (NK.HassePrinciple.onePlace (Place.ofFinite 𝔭)
      (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔭) a))) =
      (χE₁ * χE₂) (θ (Place.ofFinite 𝔭)
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔭) a)) := by
    intro 𝔭 _
    set x : Idele ↥K := NK.HassePrinciple.onePlace (Place.ofFinite 𝔭)
      (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔭) a) with hx
    obtain ⟨σ₀, hσ₀⟩ := AlgEquiv.restrictNormalHom_surjective (F := ↥K) (E := Ω) (K₁ := E) (Φ x)
    have hart : art x = AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) M σ₀ := by
      refine AlgEquiv.ext fun y => Subtype.ext ?_
      rw [htr x y, ← hσ₀, AlgEquiv.restrictNormalHom_apply, AlgEquiv.restrictNormalHom_apply]
    show χM (art x) = (χE₁ * χE₂) (Φ x)
    rw [← hσ₀, hart, MonoidHom.mul_apply, hχM σ₀, hχE₁ σ₀, hχE₂ σ₀]
    have hsplit₀ : Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c σ₀ =
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c₁ σ₀ +
          Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c₂ σ₀ := by
      have hσ₀k : σ₀.restrictScalars k ∈ K.fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro y hy
        exact σ₀.commutes ⟨y, hy⟩
      have h1 := hsplitc (σ₀.restrictScalars k) hσ₀k
      rwa [fixingSubgroupEquiv_restrictScalars_apply K σ₀ hσ₀k] at h1
    rw [hsplit₀, ofAdd_add]
  -- ## the product over `T'` at the level `M`
  have hprodM : (∏ 𝔭 ∈ T', χM (art (NK.HassePrinciple.onePlace (Place.ofFinite 𝔭)
      (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔭) a)))) = 1 := by
    rw [← hprodE]
    exact Finset.prod_congr rfl (fun 𝔭 h𝔭 => hterm 𝔭 h𝔭)
  -- ## the level-`M` reduction
  have hprin : ∀ c' : (↥K)ˣ, art (Idele.principalIdele ↥K c') = 1 := by
    intro c'
    rw [← MonoidHom.mem_ker, hker]
    exact Subgroup.mem_sup_right (Idele.mem_principalSubgroup.mpr ⟨c', rfl⟩)
  have hnorm : ∀ y : Idele ↥M, art (Idele.normIdeleHom ↥K ↥M y) = 1 := by
    intro y
    rw [← MonoidHom.mem_ker, hker]
    exact Subgroup.mem_sup_left (Idele.mem_normImage.mpr ⟨y, fun v => rfl⟩)
  have hMunr : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥K, 𝔮 ∉ T' →
      NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥M) 𝔮 :=
    fun 𝔮 h𝔮 => isUnramifiedIn_of_notMem_Tprime p k Ω K T' M hM 𝔮 h𝔮
  have hχMα : χM α = 1 := by
    rw [← hα]
    exact artin_fixes_of_local_factors p K ζ hζ hKimag M c (le_trans hc inf_le_left) χM hχM a T'
      hMunr art hprin hnorm hprodM
  -- ## conclude
  have h1 : Multiplicative.ofAdd
      (Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c σ) = 1 := by
    rw [← hχM σ, hσ, hχMα]
  have h2 := congrArg Multiplicative.toAdd h1
  simpa using h2

end Work.SSGRoute.N2v2
