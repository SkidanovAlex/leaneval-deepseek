import Mathlib
import Submission.Work.SSGRoute.H9.two_heart
import Submission.Work.SSGRoute.N2v2.exists_kummerChar_level
import Submission.Work.SSGRoute.ZDataTwo.OrthTwoGSum
import Submission.Work.SSGRoute.ZDataTwo.artinFixes_localFactors_two
import Submission.Work.SSGRoute.ZDataTwo.exists_levelCharacter_of_classCharacter
import Submission.Work.SSGRoute.ZDataTwo.OrthTwoLevelField
import Submission.Work.SSGRoute.N2v2.kummerCharZMod_surjective_openKernel
import Submission.Work.SSGRoute.N2v2.isUnramifiedIn_of_unitIdeles_le_normClassSubgroup
import Submission.Work.SSGRoute.ZDataTwo.OrthTwoArchIn
import Submission.Work.SSGRoute.n4_char_separation
import Submission.Work.SSGRoute.step4_y_escape_v2.GesUFacts
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `p = 2` trichotomy orthogonality: assembly

This file assembles `Work.SSGRoute.H9.orthogonality_L2K_trichotomy_two_proved` from the proved
pieces of the workspace:

* `Work.SSGRoute.N2v2.exists_levelField_of_gesUPow_subfield_N` — the level field `F ≤ N'` whose
  norm class subgroup is `gesU ↥K 2 T' ⊔ C_↥K² ⊔ N_{N'/↥K}`;
* `Work.SSGRoute.ZDataTwo.artinMap_fullClauses_of_levelField` — its idèlic Artin map with all the
  clauses (kernel, local norms, Frobenius, product formula, exponent `2`, and the decomposition and
  inertia lift clauses);
* `Work.SSGRoute.ZDataTwo.exists_levelCharacter_of_classCharacter` — the descent of a character of
  `C_↥K` killing the norm class subgroup of `F` to `Gal(F/↥K)`;
* `Work.SSGRoute.N2v2.exists_kummerChar_of_vanishes_on_fixingSubgroup` — its realisation as a
  Kummer character `χ_c` with the Kummer field `↥K⟮c^{1/2}⟯ ≤ F`;
* `Work.SSGRoute.ZDataMup.KummerSurjectivity.kummerCharZMod_surjective_levelK` — the Kummer element
  `bg` of the datum `g`;
* `Work.SSGRoute.N2v2.sup5_abelian_expP` + `Work.SSGRoute.N2v2.kummerField_data` — the big abelian
  level `E` of exponent `2` containing `F`, `↥K⟮a^{1/2}⟯` and `↥K⟮bg^{1/2}⟯`;
* `Work.SSGRoute.N2v2.exists_artinMap_fullClauses` at `E` — its local Artin family `θ`;
* `Work.SSGRoute.N2v2.hdiag_E` + `Work.SSGRoute.N2v2.hdata_of_kummerField_le` — the corrected
  diagonal of the local Kummer pairing at the level `E` (the `p = 2` prime-`2` correction);
* `Work.SSGRoute.N2v2.heart_two_sum` (in `two_heart.lean`) — the `χ₁`-part heart, i.e. the local
  case analysis of `horth₁`;
* `Work.SSGRoute.ZDataTwo.gsum_trichotomy_two` — the `g`-sum (the local product of the `bg`-terms
  is `1`, by the product formula with the archimedean input from `hginf`);
* `Work.SSGRoute.ZDataTwo.artinFixes_localFactors_two` — the reduction from the membership to the
  local product over `T'`;
* `Work.SSGRoute.charSeparation_exponent_p` — separation of points by characters.

The two `p = 2` ingredients that replace the odd-`p` hypothesis "`↥K` is totally complex" are
`hginf` (already consumed by `gsum_trichotomy_two` through
`Work.SSGRoute.ZDataTwo.arch_localNorm_of_involution_condition`) and `hapos` (consumed through
`Work.SSGRoute.ZDataTwo.hapos_arch_localNorm_aux`); the archimedean clause `harch` of
`heart_chi1_part` is not used at all and is dropped in `heart_two_sum`.
-/

namespace Work.SSGRoute.H9

open scoped Pointwise
open NumberField IsDedekindDomain
open NK.GlobalCFT

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- **The per-character form of the `p = 2` orthogonality.**  Every character of the idèle class
group `C_↥K` with values in `μ₂` that kills `gesU ↥K 2 T' ⊔ C_↥K² ⊔ N_{N'/↥K}` kills the class of
the `T'`-free part of the divisor of the Grünwald element `a`. -/
theorem orth_two_chi
    (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2)
    (N : IntermediateField k Ω) [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, Work.SSGRoute.gesKConj K A B → A = B)
    (hTcov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (B.valuation (2 : Ω) < 1 ∨
        (∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ N.fixingSubgroup)) →
      ∃ A ∈ T, Work.SSGRoute.gesKConj K A B)
    (g : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hg : ∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, g (x * y) = g x + g y)
    (hgc : SSGRoute.IsLocConstOn K.fixingSubgroup g)
    (hgram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) → ¬ SSGRoute.IsSplitIn k N B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → g σ = 0)
    (hginf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → g c = 0)
    (h : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hh : ∀ A ∈ T, ∀ x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      ∀ y ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A (x * y) = h A x + h A y)
    (hhc : ∀ A ∈ T, ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      ∀ x ∈ U, x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup → h A x = 0)
    (horth₁ : ∀ A ∈ T,
      (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A σ = 0) ∨
      (∀ χ : (Ω ≃ₐ[k] Ω) → ZMod 2,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
        (∀ σ ∈ N.fixingSubgroup, χ σ = 0) →
        ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, χ σ = 0) ∨
      ((∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → h A σ = 0) ∧
        ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod 2,
          (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
          (∀ σ ∈ N.fixingSubgroup, χ σ = 0) →
          ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → χ σ = 0))
    (hinertia : ∀ A ∈ T, ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ →
      g σ + h A σ = 0)
    (T' : Finset (NK.Chebotarev.PrimeIdeal ↥K))
    (hTbelow : ∀ A ∈ T, ∃ 𝔭 ∈ T', A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (hT'above : ∀ 𝔭 ∈ T', ∃ A ∈ T, A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (N' : IntermediateField ↥K Ω) [FiniteDimensional ↥K N'] [IsGalois ↥K N'] [NumberField ↥N']
    (hNN' : (N' : Set Ω) = (N : Set Ω))
    (a : (↥K)ˣ)
    (ha : ∀ A ∈ T, ∀ σ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
      g (σ : Ω ≃ₐ[k] Ω) + h A (σ : Ω ≃ₐ[k] Ω) =
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ a
          (Work.SSGRoute.gesLocalToGalK K σ))
    (hapos : ∀ (c : Ω ≃ₐ[k] Ω) (hc : c ∈ K.fixingSubgroup), c ^ 2 = 1 →
      Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ a
        (Work.SSGRoute.gesGalKOfFixing K c hc) = 0)
    (χ : NK.GlobalCFT.IdeleClassGroup ↥K →* Multiplicative (ZMod 2))
    (hχU : Work.SSGRoute.GrunwaldEscapeCore.gesU ↥K 2 T' ⊔
      Work.SSGRoute.EscapeCoreLib.pPowSubgroup 2 (NK.GlobalCFT.IdeleClassGroup ↥K) ≤ χ.ker)
    (hχW : NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥N' ≤ χ.ker) :
    χ (NK.GlobalCFT.IdeleClassGroup.mk ↥K
      (NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart (K := ↥K) T' a))) = 1 := by
  classical
  haveI hNumK : NumberField ↥K := NumberField.of_module_finite k ↥K
  haveI hCFT : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
  -- ## 1. the level field `F ≤ N'` with `N_F = U' ⊔ N_{N'}`
  obtain ⟨F, hFfd, hFgal, hFnf, hFcomm, hFleN', hFnorm⟩ :=
    Work.SSGRoute.N2v2.exists_levelField_of_gesUPow_subfield_N 2 k Ω K N K hKN le_rfl T' N'
      (by rw [show (N ⊔ K : IntermediateField k Ω) = N from sup_eq_left.mpr hKN]; exact hNN')
  haveI hFfdI : FiniteDimensional ↥K F := hFfd
  haveI hFgalI : IsGalois ↥K F := hFgal
  haveI hFnfI : NumberField ↥F := hFnf
  haveI hFcommI : IsMulCommutative (↥F ≃ₐ[↥K] ↥F) := hFcomm
  -- `N_F = U' ⊔ N_{N'}`
  have hFle : Work.SSGRoute.GrunwaldEscapeCore.gesU ↥K 2 T' ⊔
      Work.SSGRoute.EscapeCoreLib.pPowSubgroup 2 (NK.GlobalCFT.IdeleClassGroup ↥K) ⊔
      NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥N' ≤ χ.ker := sup_le hχU hχW
  -- ## 2. the Artin map of `F/↥K`, with all clauses
  have hp2F : Work.SSGRoute.EscapeCoreLib.pPowSubgroup 2
      (NK.GlobalCFT.IdeleClassGroup ↥K) ≤ NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥F := by
    rw [hFnorm]
    exact le_trans le_sup_right le_sup_left
  obtain ⟨Φ, hΦker, hΦloc, hΦfrob, hΦprod, hΦexp, hΦlift, hΦunith⟩ :=
    Work.SSGRoute.ZDataTwo.artinMap_fullClauses_of_levelField k Ω K F hp2F
  -- ## 3. `χ` descends to `Gal(F/↥K)`
  have hχFker : NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥F ≤ χ.ker := by
    rw [hFnorm]
    exact sup_le hχU hχW
  obtain ⟨χF, hχFart⟩ :=
    Work.SSGRoute.ZDataTwo.exists_levelCharacter_of_classCharacter k Ω K F Φ hΦker hΦfrob χ hχFker
  -- ## 4. its Kummer element `c`, with `↥K⟮c^{1/2}⟯ ≤ F`
  haveI hFnormI : Normal ↥K F := hFgal.to_normal
  obtain ⟨c, hcF, hχFkum⟩ :=
    Work.SSGRoute.N2v2.exists_kummerChar_of_vanishes_on_fixingSubgroup 2 k Ω K ζ hζ F F χF
      (by
        intro σ hσ
        have h1 : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) F σ = 1 := by
          rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker (K := ↥K) (L := Ω) F]
          exact hσ
        rw [h1, map_one])
  -- ## 5. `F/↥K` is unramified outside `T'`
  have hFunr : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥K, 𝔮 ∉ T' →
      NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥F) 𝔮 :=
    fun 𝔮 h𝔮 => Work.SSGRoute.N2v2.isUnramifiedIn_of_unitIdeles_le_normClassSubgroup 2 k Ω K T' F
      (by rw [hFnorm]; exact le_trans le_sup_left le_sup_left) 𝔮 h𝔮
  -- ## 6. the Kummer element `bg` of the datum `g`
  obtain ⟨bg, hbg⟩ :=
    Work.SSGRoute.ZDataMup.KummerSurjectivity.kummerCharZMod_surjective_levelK 2 k Ω K ζ hζ g
      hg hgc
  -- ## 7. the big level `E ⊇ F ⊔ ↥K⟮a^{1/2}⟯ ⊔ ↥K⟮bg^{1/2}⟯`, abelian of exponent `2`
  have hFa := Work.SSGRoute.N2v2.kummerField_data 2 K ζ hζ a
  have hFbg := Work.SSGRoute.N2v2.kummerField_data 2 K ζ hζ bg
  haveI hFa_fd : FiniteDimensional ↥K (NK.LocalAnabelian.kummerField (K' := Ω) 2 a) := hFa.1
  haveI hFa_gal : IsGalois ↥K (NK.LocalAnabelian.kummerField (K' := Ω) 2 a) := hFa.2.1
  haveI hFa_nf : NumberField ↥(NK.LocalAnabelian.kummerField (K' := Ω) 2 a) := hFa.2.2.1
  haveI hFa_cm : IsMulCommutative (↥(NK.LocalAnabelian.kummerField (K' := Ω) 2 a) ≃ₐ[↥K]
    ↥(NK.LocalAnabelian.kummerField (K' := Ω) 2 a)) := hFa.2.2.2.1
  haveI hFbg_fd : FiniteDimensional ↥K (NK.LocalAnabelian.kummerField (K' := Ω) 2 bg) := hFbg.1
  haveI hFbg_gal : IsGalois ↥K (NK.LocalAnabelian.kummerField (K' := Ω) 2 bg) := hFbg.2.1
  haveI hFbg_nf : NumberField ↥(NK.LocalAnabelian.kummerField (K' := Ω) 2 bg) := hFbg.2.2.1
  haveI hFbg_cm : IsMulCommutative (↥(NK.LocalAnabelian.kummerField (K' := Ω) 2 bg) ≃ₐ[↥K]
    ↥(NK.LocalAnabelian.kummerField (K' := Ω) 2 bg)) := hFbg.2.2.2.1
  obtain ⟨E, hEfd, hEgal, hEcomm, hEnf, hFE, hFaE, hFbgE, _h2, _h3, hexpE⟩ :=
    Work.SSGRoute.N2v2.sup5_abelian_expP (k := k) (Ω := Ω) 2 K F
      (NK.LocalAnabelian.kummerField (K' := Ω) 2 a)
      (NK.LocalAnabelian.kummerField (K' := Ω) 2 bg) F F
      hΦexp hFa.2.2.2.2 hFbg.2.2.2.2 hΦexp hΦexp
  haveI hEfdI : FiniteDimensional ↥K E := hEfd
  haveI hEgalI : IsGalois ↥K E := hEgal
  haveI hEcommI : IsMulCommutative (↥E ≃ₐ[↥K] ↥E) := hEcomm
  haveI hEnfI : NumberField ↥E := hEnf
  -- ## 8. the Artin map of `E`, its local family `θ`, and the diagonal
  obtain ⟨ΦE, hΦEker, hΦEloc, hΦEfrob, hΦEprod, hΦElift, hΦEunith⟩ :=
    Work.SSGRoute.N2v2.exists_artinMap_fullClauses (K := K) E
  let θ : (v : NK.GlobalCFT.Place ↥K) →
      (NK.GlobalCFT.Place.localField ↥K v)ˣ →* (↥E ≃ₐ[↥K] ↥E) :=
    fun v => ΦE.comp (NK.CFTLib.IdeleHasse.onePlaceHom (K := ↥K) v)
  have hdiagLift : ∀ 𝔭 ∈ T', ∃ σ₀ : Ω ≃ₐ[↥K] Ω,
      ∀ (y : (↥K)ˣ), NK.LocalAnabelian.kummerField (K' := Ω) 2 y ≤ E →
      ∀ τ : Ω ≃ₐ[↥K] Ω,
        AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E τ =
          θ (NK.GlobalCFT.Place.ofFinite 𝔭)
            (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) y) →
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ y τ =
          Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ y σ₀ := by
    intro 𝔭 _
    exact Work.SSGRoute.N2v2.hdiag_E 2 K ζ hζ E ΦE 𝔭
      (fun c' hc' => Work.SSGRoute.N2v2.hdata_of_kummerField_le 2 K ζ hζ E ΦE hΦEker hΦEfrob
        𝔭 c' hc')
  -- ## 9. `χ` as a Kummer character at the level `E`
  obtain ⟨χE₁, hχE₁⟩ :=
    Work.SSGRoute.N2v2.exists_kummerChar_level 2 k Ω K ζ hζ E c (le_trans hcF hFE)
  -- ## 10. `g` kills the fixing subgroup of `E`
  have hgE : ∀ σ : Ω ≃ₐ[↥K] Ω, σ ∈ E.fixingSubgroup → g (σ.restrictScalars k) = 0 := by
    intro σ hσE
    have hσK : σ.restrictScalars k ∈ K.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact σ.commutes ⟨x, hx⟩
    rw [hbg (σ.restrictScalars k) hσK,
      Work.SSGRoute.N2v2.fixingSubgroupEquiv_restrictScalars_apply K σ hσK]
    exact Work.SSGRoute.N2v2.kummerCharZMod_eq_zero_of_kummerField_le 2 k Ω K ζ hζ bg E hFbgE
      σ hσE
  -- ## 11. the bridge `χ (mk y) = χE₁ (ΦE y)`
  have hbridge : ∀ y : NK.GlobalCFT.Idele ↥K, χF (Φ y) = χE₁ (ΦE y) := by
    intro y
    obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (F := ↥K) (K₁ := E) (E := Ω) (ΦE y)
    have hFσ : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) F σ = Φ y :=
      Work.SSGRoute.N2v2.restrictNormalHom_artinMap_eq_of_le 2 K F E hFE Φ hΦker hΦfrob ΦE
        hΦEker hΦEfrob σ y hσ
    calc χF (Φ y) = χF (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) F σ) := by rw [hFσ]
      _ = Multiplicative.ofAdd (Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ c σ)
            := hχFkum σ
      _ = χE₁ (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E σ) := (hχE₁ σ).symm
      _ = χE₁ (ΦE y) := by rw [hσ]
  -- ## 12. the archimedean input for `bg` and the `g`-sum
  have hbginf : ∀ (c' : Ω ≃ₐ[k] Ω) (hc' : c' ∈ K.fixingSubgroup), c' ^ 2 = 1 →
      Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ bg
        (Work.SSGRoute.gesGalKOfFixing K c' hc') = 0 := by
    intro c' hc' hc'2
    have h1 : Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ bg
        (Work.SSGRoute.gesGalKOfFixing K c' hc') = g c' := (hbg c' hc').symm
    rw [h1]
    exact hginf c' hc' hc'2
  have harchbg := Work.SSGRoute.ZDataTwo.arch_localNorm_of_involution_condition k Ω K ζ hζ bg N'
    hbginf
  have hbgprod : (∏ 𝔭 ∈ T', χ (NK.GlobalCFT.IdeleClassGroup.mk ↥K
      (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) bg)))) = 1 :=
    Work.SSGRoute.ZDataTwo.gsum_trichotomy_two k Ω K ζ hζ N hKN T hTfin hTdisj hTcov g hgram
      T' hTbelow N' hNN' χ hχU hχW bg hbg harchbg
  have hgsum : (∑ 𝔭 ∈ T', (χE₁ (θ (NK.GlobalCFT.Place.ofFinite 𝔭)
      (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) bg))).toAdd) = 0 := by
    rw [← Work.SSGRoute.GrunwaldEscapeCore.toAdd_prod_eq_sum 2 T'
      (fun 𝔭 => χE₁ (θ (NK.GlobalCFT.Place.ofFinite 𝔭)
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) bg)))]
    rw [show (∏ 𝔭 ∈ T', χE₁ (θ (NK.GlobalCFT.Place.ofFinite 𝔭)
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) bg)))
        = ∏ 𝔭 ∈ T', χ (NK.GlobalCFT.IdeleClassGroup.mk ↥K
            (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
              (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
                (NK.GlobalCFT.Place.ofFinite 𝔭) bg))) from
      Finset.prod_congr rfl (fun 𝔭 _ => ((hbridge (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) bg))).symm).trans
          (hχFart (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
            (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) bg))))]
    rw [hbgprod]
    rfl
  -- ## 13. the heart: the `χ_{c₁}`-sum over `T'` of the `a`-terms vanishes
  have hcL : NK.LocalAnabelian.kummerField (K' := Ω) 2 c ≤
      Work.SSGRoute.EscapeCoreLib.baseChange K N hKN := by
    rw [Work.SSGRoute.EscapeCoreLib.le_baseChange_iff]
    intro x hx
    have hxN' : x ∈ (N' : Set Ω) := hFleN' (hcF hx)
    rw [hNN'] at hxN'
    exact hxN'
  have hsum := Work.SSGRoute.N2v2.heart_two_sum 2 k Ω K ζ hζ N hKN T hTfin T' hTbelow hT'above
    hTcov g hg hgc
    (fun B hB hnotT hnsplit => hgram B hB (fun A hA hconj => by
      obtain ⟨τ, hτ, hτA⟩ := hconj
      exact hnotT A hA τ hτ hτA) hnsplit)
    h hh horth₁ a ha E hexpE θ hΦElift hΦEunith hdiagLift hgE hFaE bg
    (fun σ hσ => hbg σ hσ) c (le_trans hcF hFE) hcL χE₁ hχE₁ hgsum
  -- ## 14. the product of the `a`-terms is `1`
  have hproda : (∏ 𝔭 ∈ T', χF (Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
      (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) a)))) = 1 := by
    rw [show (∏ 𝔭 ∈ T', χF (Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
          (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) a))))
        = ∏ 𝔭 ∈ T', χE₁ (θ (NK.GlobalCFT.Place.ofFinite 𝔭)
            (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
              (NK.GlobalCFT.Place.ofFinite 𝔭) a)) from
      Finset.prod_congr rfl (fun 𝔭 _ => hbridge _)]
    have hinj : Function.Injective
        (Multiplicative.toAdd : Multiplicative (ZMod 2) → ZMod 2) := fun _ _ h => h
    refine hinj ?_
    rw [Work.SSGRoute.GrunwaldEscapeCore.toAdd_prod_eq_sum 2 T'
      (fun 𝔭 => χE₁ (θ (NK.GlobalCFT.Place.ofFinite 𝔭)
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) a))), hsum]
    rfl
  -- ## 15. the reduction to the local product
  have haposF := Work.SSGRoute.ZDataTwo.hapos_arch_localNorm_aux k Ω K ζ hζ a F hapos
  have hmain : χF (Φ (NK.NUV2.RouteB.RayModulus.fracIdele
      (Work.SSGRoute.tFreePart (K := ↥K) T' a))) = 1 :=
    Work.SSGRoute.ZDataTwo.artinFixes_localFactors_two k Ω K ζ hζ F c hcF χF hχFkum a T' hFunr Φ
      (fun x => by
        rw [← MonoidHom.mem_ker, hΦker]
        exact Subgroup.mem_sup_right (NK.GlobalCFT.Idele.mem_principalSubgroup.mpr ⟨x, rfl⟩))
      (fun y => by
        rw [← MonoidHom.mem_ker, hΦker]
        exact Subgroup.mem_sup_left (NK.GlobalCFT.Idele.mem_normImage.mpr ⟨y, fun v => rfl⟩))
      haposF hproda
  rw [← hχFart (NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart (K := ↥K) T' a))]
  exact hmain

/-- **The `p = 2` orthogonality in the form of
`Work.SSGRoute.ZDataTwo.orthogonality_L2K_trichotomy_two`** (and of the H9 node
`Work.SSGRoute.H9.orthogonality_L2K_trichotomy_two_proved`), obtained from `orth_two_chi` by
separation of the points of the finite exponent-`2` quotient
`C_↥K / (gesU ↥K 2 T' ⊔ C_↥K² ⊔ N_{N'/↥K})`. -/
theorem orth_two_core (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2)
    (N : IntermediateField k Ω) [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, Work.SSGRoute.gesKConj K A B → A = B)
    (hTcov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (B.valuation (2 : Ω) < 1 ∨
        (∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ N.fixingSubgroup)) →
      ∃ A ∈ T, Work.SSGRoute.gesKConj K A B)
    (g : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hg : ∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, g (x * y) = g x + g y)
    (hgc : SSGRoute.IsLocConstOn K.fixingSubgroup g)
    (hgram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) → ¬ SSGRoute.IsSplitIn k N B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → g σ = 0)
    (hginf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → g c = 0)
    (h : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hh : ∀ A ∈ T, ∀ x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      ∀ y ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A (x * y) = h A x + h A y)
    (hhc : ∀ A ∈ T, ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      ∀ x ∈ U, x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup → h A x = 0)
    (horth₁ : ∀ A ∈ T,
      (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A σ = 0) ∨
      (∀ χ : (Ω ≃ₐ[k] Ω) → ZMod 2,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
        (∀ σ ∈ N.fixingSubgroup, χ σ = 0) →
        ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, χ σ = 0) ∨
      ((∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → h A σ = 0) ∧
        ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod 2,
          (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
          (∀ σ ∈ N.fixingSubgroup, χ σ = 0) →
          ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → χ σ = 0))
    (hinertia : ∀ A ∈ T, ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ →
      g σ + h A σ = 0)
    (T' : Finset (NK.Chebotarev.PrimeIdeal ↥K))
    (hTbelow : ∀ A ∈ T, ∃ 𝔭 ∈ T', A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (hT'above : ∀ 𝔭 ∈ T', ∃ A ∈ T, A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (M : IntermediateField ↥K Ω) [FiniteDimensional ↥K M] [IsGalois ↥K M] [NumberField ↥M]
    (hMnorm : NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥M =
      Work.SSGRoute.GrunwaldEscapeCore.gesU ↥K 2 T' ⊔
        Work.SSGRoute.EscapeCoreLib.pPowSubgroup 2 (NK.GlobalCFT.IdeleClassGroup ↥K))
    (N' : IntermediateField ↥K Ω) [FiniteDimensional ↥K N'] [IsGalois ↥K N'] [NumberField ↥N']
    (hNN' : (N' : Set Ω) = (N : Set Ω))
    (a : (↥K)ˣ)
    (ha : ∀ A ∈ T, ∀ σ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
      g (σ : Ω ≃ₐ[k] Ω) + h A (σ : Ω ≃ₐ[k] Ω) =
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ a
          (Work.SSGRoute.gesLocalToGalK K σ))
    (hapos : ∀ (c : Ω ≃ₐ[k] Ω) (hc : c ∈ K.fixingSubgroup), c ^ 2 = 1 →
      Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ a
        (Work.SSGRoute.gesGalKOfFixing K c hc) = 0) :
    NK.GlobalCFT.IdeleClassGroup.mk ↥K (NK.NUV2.RouteB.RayModulus.fracIdele
        (Work.SSGRoute.tFreePart (K := ↥K) T' a)) ∈
      NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥M ⊔
        NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥N' := by
  classical
  haveI hNumK : NumberField ↥K := NumberField.of_module_finite k ↥K
  rw [hMnorm]
  haveI hUfin : (Work.SSGRoute.GrunwaldEscapeCore.gesU ↥K 2 T' ⊔
      Work.SSGRoute.EscapeCoreLib.pPowSubgroup 2 (NK.GlobalCFT.IdeleClassGroup ↥K)).FiniteIndex :=
    Work.SSGRoute.step4_y_escape_v2.finiteIndex_gesU_sup_pPow (p := 2) (K := ↥K) T'
  haveI hfin : (Work.SSGRoute.GrunwaldEscapeCore.gesU ↥K 2 T' ⊔
      Work.SSGRoute.EscapeCoreLib.pPowSubgroup 2 (NK.GlobalCFT.IdeleClassGroup ↥K) ⊔
      NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥N').FiniteIndex :=
    Subgroup.finiteIndex_of_le le_sup_left
  refine (Work.SSGRoute.charSeparation_exponent_p (p := 2)
    (Work.SSGRoute.GrunwaldEscapeCore.gesU ↥K 2 T' ⊔
      Work.SSGRoute.EscapeCoreLib.pPowSubgroup 2 (NK.GlobalCFT.IdeleClassGroup ↥K))
    (NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥N') le_sup_right _).mpr ?_
  intro χ hχ
  exact orth_two_chi k Ω K ζ hζ N hKN T hTfin hTdisj hTcov g hg hgc hgram hginf h hh hhc
    horth₁ hinertia T' hTbelow hT'above N' hNN' a ha hapos χ
    (fun u hu => hχ u (Subgroup.mem_sup_left hu)) (fun u hu => hχ u (Subgroup.mem_sup_right hu))

end Work.SSGRoute.H9
