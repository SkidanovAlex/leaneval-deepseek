import Mathlib
import Submission.NK.NUV2.LC.RouteB.Defs
import Submission.NK.NUV2.LC.RouteB.res_injective_of_coprime_index
import Submission.NK.NUV2.LC.finite_support_loc_odd_of_twist
import Submission.NK.NUV2.LC.RouteB.exists_prime_step_of_dvd_index
import Submission.NK.NUV2.LC.RouteB.isLive_of_isMuOpen
import Submission.NK.NUV2.LC.RouteB.HTX_Phi_res_natural
import Submission.NK.NUV2.LC.RouteB.local_res_eq_zero_adicCompletion
import Submission.NK.Mine.exists_isHomeomorph_mulEquiv_sepClosure_of_decompositionGroup_map

/-! Guidance from the project lead (the requester):

FULL ROUTE: read Submission/Work/NUV2/LC/RouteB/DESIGN_containment_v3.md first (the orchestrator's
redesign of decompContainment_B; your lemma is one node). Never use the circular
le_stabSubgroup_of_localType, SurjTwo/HasseTwo/ABHNSurjectivity shapes. hFC and hKC are PROVED
(NK.CFTLib.fundamentalClassElement, NK.NUV2.kernelCondition_all).

# coprime_relIndex_of_res_ne_zero (L2 = F3; Branch L, formal given L1)

**Target file** `RouteB/coprime_relIndex_of_res_ne_zero.lean`.

**Proof** (by contraposition: assume `p ∣ [O₁:O₂]`, where `O_i := U_i ⊓ D_A`; we show `res = 0`).
1. **Finite quotient.** Take an open normal `N₀ ≤ U₂` of `Gal(K'/K)`
   (`ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one`). Put `C := O₁ ⊓ N₀ ◁ O₁`; then
   `C ≤ O₂` and `C` has finite index in `O₁`, so `Q := O₁/C` is finite. Every `X` with
   `C ≤ X ≤ O₁` equals `(X ⊔ N₀ ⊓ U₁) ⊓ D_A` (Dedekind/modular law, `dedekind_saturation`), so
   every subgroup of `Q` is again of the form `U ⊓ D_A` with `U` open.
2. **Sylow.** `NK.NUV2.LC.RouteB.exists_prime_step_of_dvd_index` (the finite Sylow step) produces
   `C ≤ R₁ ≤ O₂ ≤ X ≤ O₁` with `R₁ ◁ X`, `[O₂:R₁]` prime to `p` and `[X:R₁] = p`.
3. **Compose.** With `R₀ := R₁` and `X' := X`:
   - `res_{O₁→R₁} = res_{X→R₁} ∘ res_{O₁→X} = 0` by (LZ) `res_zero_of_prime_index_local` (proved in this file from
   `local_res_eq_zero_adicCompletion` and the transport `HTX_Phi_res_natural`);
   - `res_{O₂→R₁}` is injective (`H2Profinite_res_injective_of_coprime_index`, since `[O₂:R₁]` is
     prime to `p`);
   - `res_{O₁→R₁} = res_{O₂→R₁} ∘ res_{O₁→O₂}` (`OddTwist.H2Profinite_res_comp`).

   Hence `res_{O₁→O₂} = 0`.

**Sanity check.** Same example as (LZ):
- index 3: `res = 0`, so the hypothesis `res y ≠ 0` fails (fine);
- index 2 (`ℚ_7(√7)`): `res` is an isomorphism and `gcd(2, 3) = 1`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u

namespace NK.NUV2.LC.RouteB

open NK.BrauerHasse


/-- `Subgroup.topEquiv.symm` is a homeomorphism (the two spaces differ only by the trivial
subtype). -/
private lemma isHomeomorph_topEquiv_symm {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G]
    [T2Space G] : IsHomeomorph ⇑(Subgroup.topEquiv.symm : G ≃* ↥(⊤ : Subgroup G)) := by
  rw [isHomeomorph_iff_continuous_bijective]
  refine ⟨?_, (Subgroup.topEquiv.symm).bijective⟩
  have hfun : ⇑(Subgroup.topEquiv.symm : G ≃* ↥(⊤ : Subgroup G)) =
      fun x => (⟨x, Subgroup.mem_top x⟩ : ↥(⊤ : Subgroup G)) := by
    funext x
    exact Subtype.ext (by rw [← Subgroup.topEquiv_apply, MulEquiv.apply_symm_apply])
  rw [hfun]
  exact continuous_id.subtype_mk (fun x => Subgroup.mem_top x)


/-- `HTX.Phi` sends `0` to `0`. -/
private lemma HTX_Phi_zero {K K' κ κ' : Type} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']
    (H : Subgroup Gal(K'/K)) (J : Subgroup Gal(κ'/κ)) (p : ℕ) (e : ↥H ≃ₜ* ↥J) :
    NK.NUV2.LC.HTX.Phi H J p e 0 = 0 := by
  show NK.NUV2.LC.HTX.Phi H J p e
    (NK.BrauerHasse.H2Profinite.ofLevel (p := p) (U := H) ⊥
      (0 : NK.BrauerHasse.LevelH2 p H ⊥)) = 0
  rw [NK.NUV2.LC.HTX.Phi_ofLevel, NK.NUV2.LC.HTX.fwd, map_zero]
  exact NK.BrauerHasse.ofLevel_zero _

/-- **The transport step of `(LZ)`**: the global restriction vanishes as soon as the corresponding
local restriction does. -/
private theorem transport_LZ {K K' κ κ' : Type} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']
    {O₁ O₂ : Subgroup Gal(K'/K)} (h : O₂ ≤ O₁) (p : ℕ)
    (e : ↥O₁ ≃ₜ* ↥(⊤ : Subgroup Gal(κ'/κ)))
    (W : Subgroup Gal(κ'/κ)) (e' : ↥O₂ ≃ₜ* ↥W)
    (he : ∀ x : ↥O₂, (e (Subgroup.inclusion h x) : ↥(⊤ : Subgroup Gal(κ'/κ))) =
      Subgroup.inclusion le_top (e' x))
    (hlocal : ∀ x : NK.BrauerHasse.H2Profinite (K := κ) (K' := κ') p
        (⊤ : Subgroup Gal(κ'/κ)),
      NK.LocalDecomposition.H2Profinite.res p
        (show W ≤ (⊤ : Subgroup Gal(κ'/κ)) from le_top) x = 0)
    (y : NK.BrauerHasse.H2Profinite (K := K) (K' := K') p O₁) :
    NK.LocalDecomposition.H2Profinite.res p h y = 0 := by
  have hinj : Function.Injective
      (NK.NUV2.LC.HTX.Phi O₂ W p e') := by
    intro a b hab
    rw [← NK.NUV2.LC.HTX.Psi_Phi O₂ W p e' a,
      ← NK.NUV2.LC.HTX.Psi_Phi O₂ W p e' b, hab]
  have h1 : NK.LocalDecomposition.H2Profinite.res p
      (show W ≤ (⊤ : Subgroup Gal(κ'/κ)) from le_top)
      (NK.NUV2.LC.HTX.Phi O₁ (⊤ : Subgroup Gal(κ'/κ)) p e y) = 0 := hlocal _
  rw [HTX_Phi_res_natural (H := O₁) (H' := O₂) (J := (⊤ : Subgroup Gal(κ'/κ))) (J' := W)
    h le_top e e' he p y] at h1
  exact hinj (by rw [h1, HTX_Phi_zero O₂ W p e'])

/-- **The local statement in the form needed for the transport**: for a closed *normal* subgroup
`W` of index `p` of the absolute Galois group of `𝔮.adicCompletion L`, the restriction from `⊤` to
`W` kills `H²(·, Z/p)`. -/
theorem local_res_zero_of_index_prime {L : Type} [Field L] [NumberField L]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hζ : ∃ ζ : 𝔮.adicCompletion L, IsPrimitiveRoot ζ p)
    (W : Subgroup Gal(SeparableClosure (𝔮.adicCompletion L) / (𝔮.adicCompletion L)))
    (hWcl : IsClosed (W : Set Gal(SeparableClosure (𝔮.adicCompletion L) /
      (𝔮.adicCompletion L))))
    (hWnormal : W.Normal) (hWidx : W.index = p)
    (x : NK.BrauerHasse.H2Profinite (K := 𝔮.adicCompletion L)
      (K' := SeparableClosure (𝔮.adicCompletion L)) p
      (⊤ : Subgroup Gal(SeparableClosure (𝔮.adicCompletion L) / (𝔮.adicCompletion L)))) :
    NK.LocalDecomposition.H2Profinite.res p
      (show W ≤ (⊤ : Subgroup Gal(SeparableClosure (𝔮.adicCompletion L) /
        (𝔮.adicCompletion L))) from le_top) x = 0 := by
  classical
  haveI : W.Normal := hWnormal
  haveI : IsGalois (𝔮.adicCompletion L) (SeparableClosure (𝔮.adicCompletion L)) :=
    IsSepClosure.isGalois
  let E : IntermediateField (𝔮.adicCompletion L) (SeparableClosure (𝔮.adicCompletion L)) :=
    IntermediateField.fixedField W
  have hEfix : E.fixingSubgroup = W :=
    InfiniteGalois.fixingSubgroup_fixedField (k := 𝔮.adicCompletion L)
      (K := SeparableClosure (𝔮.adicCompletion L)) ⟨W, hWcl⟩
  have hEgal : IsGalois (𝔮.adicCompletion L) E :=
    (InfiniteGalois.normal_iff_isGalois (k := 𝔮.adicCompletion L)
      (K := SeparableClosure (𝔮.adicCompletion L)) E).mp (by rw [hEfix]; exact hWnormal)
  haveI : IsGalois (𝔮.adicCompletion L) E := hEgal
  have hEfd : FiniteDimensional (𝔮.adicCompletion L) E := by
    rw [← InfiniteGalois.isOpen_iff_finite (k := 𝔮.adicCompletion L)
      (K := SeparableClosure (𝔮.adicCompletion L)) E, hEfix]
    haveI : W.FiniteIndex := Subgroup.finiteIndex_iff.mpr (by rw [hWidx]; exact hp.ne_zero)
    exact Subgroup.isOpen_of_isClosed_of_finiteIndex W hWcl
  haveI : FiniteDimensional (𝔮.adicCompletion L) E := hEfd
  have hdeg : Module.finrank (𝔮.adicCompletion L) E = p := by
    have h1 := IntermediateField.finrank_eq_fixingSubgroup_index
      (F := 𝔮.adicCompletion L) (E' := SeparableClosure (𝔮.adicCompletion L)) E
    rw [h1, hEfix, hWidx]
  obtain ⟨ζ, hζ'⟩ := hζ
  have hloc := NK.NUV2.LC.RouteB.local_res_eq_zero_adicCompletion (K := L) p hp 𝔮 ζ hζ'
    (FiniteGaloisIntermediateField.mk E) hdeg
  rw [← hEfix]
  exact hloc x

/-- **(LZ)** — the assembled statement: local restriction along a degree-`p` step kills `H²(·, Z/p)`. -/
theorem res_zero_of_prime_index_local (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) {K K' : Type}
    [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K'] (ζ : K')
    (hζ : IsPrimitiveRoot ζ p) (A : NK.BrauerHasse.OverFinitePrime K K')
    {U₁ U₂ : Subgroup Gal(K'/K)} (hU₁ : NK.NUV2.LC.RouteB.IsMuOpen (K := K) (K' := K') ζ U₁)
    (hU₂ : IsOpen (U₂ : Set Gal(K'/K))) (h21 : U₂ ≤ U₁)
    (hnormal : ((U₂ ⊓ NK.BrauerHasse.stabSubgroup A.1).subgroupOf
      (U₁ ⊓ NK.BrauerHasse.stabSubgroup A.1)).Normal)
    (hidx : (U₂ ⊓ NK.BrauerHasse.stabSubgroup A.1).relIndex
      (U₁ ⊓ NK.BrauerHasse.stabSubgroup A.1) = p)
    (y : NK.BrauerHasse.H2Profinite (K := K) (K' := K') p
      (U₁ ⊓ NK.BrauerHasse.stabSubgroup A.1)) :
    NK.LocalDecomposition.H2Profinite.res p
      (inf_le_inf_right _ h21 : U₂ ⊓ NK.BrauerHasse.stabSubgroup A.1 ≤
        U₁ ⊓ NK.BrauerHasse.stabSubgroup A.1) y = 0 := by
  classical
  obtain ⟨A₀, hA₀⟩ := A
  obtain ⟨hU₁open, hU₁ζ⟩ := hU₁
  -- ===== the fixed field `F` of `U₁`, the prime `𝔮` of `F` below `A`, the local field `κ` =====
  let F : IntermediateField K K' := IntermediateField.fixedField U₁
  have hU₁cl : IsClosed (U₁ : Set Gal(K'/K)) := Subgroup.isClosed_of_isOpen U₁ hU₁open
  have hFixF : F.fixingSubgroup = U₁ :=
    InfiniteGalois.fixingSubgroup_fixedField (k := K) (K := K') ⟨U₁, hU₁cl⟩
  have hFfd : FiniteDimensional K F := by
    rw [← InfiniteGalois.isOpen_iff_finite (k := K) (K := K') F, hFixF]
    exact hU₁open
  haveI : FiniteDimensional K F := hFfd
  haveI : NumberField ↥F := NumberField.of_module_finite K ↥F
  haveI : IsSepClosure ↥F K' := ⟨IsSepClosure.sep_closed K, inferInstance⟩
  have hζF : ζ ∈ F := by
    rw [IntermediateField.mem_fixedField_iff]
    intro f hf
    exact (IntermediateField.mem_fixingSubgroup_iff _ f).mp (hU₁ζ hf) ζ
      (IntermediateField.mem_adjoin_simple_self K ζ)
  have hAF : A₀.comap (algebraMap ↥F K') ≠ ⊤ := by
    intro htop
    refine hA₀ ?_
    have h1 : (A₀.comap (algebraMap ↥F K')).comap (algebraMap K ↥F)
        = A₀.comap (algebraMap K K') := by
      rw [ValuationSubring.comap_comap, IsScalarTower.algebraMap_eq K ↥F K']
    rw [← h1, htop]
    ext x; simp [ValuationSubring.mem_comap]
  obtain ⟨𝔮, h𝔮⟩ :=
    NK.BrauerHasse.exists_heightOneSpectrum_eq_comap (K := ↥F) (K' := K') A₀ hAF
  have hζ₀ : IsPrimitiveRoot (⟨ζ, hζF⟩ : ↥F) p :=
    IsPrimitiveRoot.of_map_of_injective (f := F.val) (by simpa using hζ)
      (fun a b h => Subtype.ext h)
  have hζκ : ∃ ζ' : 𝔮.adicCompletion ↥F, IsPrimitiveRoot ζ' p :=
    ⟨algebraMap ↥F (𝔮.adicCompletion ↥F) (⟨ζ, hζF⟩ : ↥F),
      IsPrimitiveRoot.map_of_injective (f := algebraMap ↥F (𝔮.adicCompletion ↥F)) hζ₀
        (Commons.NumberTheory.NumberField.Completion.injective_algebraMap_adicCompletion 𝔮)⟩
  -- ===== the topological isomorphism `O₁ ≃ₜ* Gal(κ'/κ)` =====
  letI : Algebra (𝔮.adicCompletion ↥F) (NK.NeukirchUchida.placeCompletion A₀) :=
    (NK.NeukirchUchida.adicCompletionToPlaceCompletion 𝔮 A₀ h𝔮).toAlgebra
  have hWpt : (NK.NeukirchUchida.placeCompletionIntegers A₀).comap
      (NK.NeukirchUchida.adicCompletionToPlaceCompletion 𝔮 A₀ h𝔮) =
      IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ↥F 𝔮 :=
    NK.NeukirchUchida.comap_adicCompletionToPlaceCompletion_eq_adicCompletionIntegers 𝔮 A₀ h𝔮
  haveI : IsSepClosure (𝔮.adicCompletion ↥F)
      ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := ↥F) (K' := K') 𝔮 A₀) :=
    NK.Mine.isSepClosure_adjoinPlaceCompletion 𝔮 A₀ h𝔮 (fun z => rfl)
  haveI : IsGalois (𝔮.adicCompletion ↥F)
      ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := ↥F) (K' := K') 𝔮 A₀) :=
    IsSepClosure.isGalois
  let eMul : ↥(NK.Mine.decompositionGroupOf ↥F K' A₀) ≃*
      Gal(SeparableClosure (𝔮.adicCompletion ↥F) / (𝔮.adicCompletion ↥F)) :=
    NK.Mine.localGaloisEquiv 𝔮 A₀ h𝔮 (fun z => rfl) hWpt
  have heMulHom : IsHomeomorph (eMul : _ → _) :=
    NK.Mine.isHomeomorph_trans (NK.Mine.adjoinLocalEquiv 𝔮 A₀ h𝔮 (fun z => rfl) hWpt)
      (AlgEquiv.autCongr (NK.Mine.adjoinSepEquiv 𝔮 A₀ h𝔮 (fun z => rfl)))
      (NK.Mine.isHomeomorph_adjoinLocalEquiv 𝔮 A₀ h𝔮 (fun z => rfl) hWpt)
      (NK.Mine.isHomeomorph_autCongr (NK.Mine.adjoinSepEquiv 𝔮 A₀ h𝔮 (fun z => rfl)))
  obtain ⟨eFix⟩ := nonempty_continuousMulEquiv_fixingSubgroup_inf_stabSubgroup F A₀
  let eL : ↥(U₁ ⊓ NK.BrauerHasse.stabSubgroup A₀) ≃ₜ*
      Gal(SeparableClosure (𝔮.adicCompletion ↥F) / (𝔮.adicCompletion ↥F)) :=
    (hFixF ▸ eFix).trans (continuousMulEquivOfIsHomeomorph eMul heMulHom)
  -- ===== the local subgroup `W` and the two transported restrictions =====
  let O₁ : Subgroup Gal(K'/K) := U₁ ⊓ NK.BrauerHasse.stabSubgroup A₀
  let O₂ : Subgroup Gal(K'/K) := U₂ ⊓ NK.BrauerHasse.stabSubgroup A₀
  have hO₂O₁ : O₂ ≤ O₁ := fun x hx => ⟨h21 hx.1, hx.2⟩
  haveI : CompactSpace (Gal(SeparableClosure (𝔮.adicCompletion ↥F) /
      (𝔮.adicCompletion ↥F))) := inferInstance
  haveI : T2Space (↥(⊤ : Subgroup Gal(SeparableClosure (𝔮.adicCompletion ↥F) /
      (𝔮.adicCompletion ↥F)))) := inferInstance
  let eTop : ↥O₁ ≃ₜ* ↥(⊤ : Subgroup Gal(SeparableClosure (𝔮.adicCompletion ↥F) /
      (𝔮.adicCompletion ↥F))) :=
    continuousMulEquivOfIsHomeomorph
      ((eL : ↥O₁ ≃* Gal(SeparableClosure (𝔮.adicCompletion ↥F) / (𝔮.adicCompletion ↥F))).trans
        Subgroup.topEquiv.symm)
      (NK.Mine.isHomeomorph_trans _ Subgroup.topEquiv.symm eL.toHomeomorph.isHomeomorph
        (isHomeomorph_topEquiv_symm))
  let W : Subgroup Gal(SeparableClosure (𝔮.adicCompletion ↥F) / (𝔮.adicCompletion ↥F)) :=
    (O₂.subgroupOf O₁).map (eL : ↥O₁ →* Gal(SeparableClosure (𝔮.adicCompletion ↥F) /
      (𝔮.adicCompletion ↥F)))
  have hWidx : W.index = p := by
    show ((O₂.subgroupOf O₁).map (eL : ↥O₁ →* Gal(SeparableClosure (𝔮.adicCompletion ↥F) /
      (𝔮.adicCompletion ↥F)))).index = p
    rw [Subgroup.index_map_eq (O₂.subgroupOf O₁) (f := (eL : ↥O₁ →*
      Gal(SeparableClosure (𝔮.adicCompletion ↥F) / (𝔮.adicCompletion ↥F)))) eL.surjective (by
        intro x hx
        rw [MonoidHom.mem_ker] at hx
        have hx1 : x = 1 := eL.injective (by simpa using hx)
        rw [hx1]
        exact (O₂.subgroupOf O₁).one_mem)]
    exact hidx
  have hWcl : IsClosed (W : Set Gal(SeparableClosure (𝔮.adicCompletion ↥F) /
      (𝔮.adicCompletion ↥F))) := by
    have hO₂cl : IsClosed (O₂ : Set Gal(K'/K)) :=
      (Subgroup.isClosed_of_isOpen U₂ hU₂).inter
        (NK.LocalDecomposition.isClosed_stabSubgroup A₀)
    have h1 : IsClosed ((O₂.subgroupOf O₁ : Subgroup ↥O₁) : Set ↥O₁) := by
      rw [Subgroup.subgroupOf]
      rw [Subgroup.coe_comap]
      exact hO₂cl.preimage continuous_subtype_val
    rw [Subgroup.coe_map]
    have h2 : IsClosedMap ⇑eL.toHomeomorph := Homeomorph.isClosedMap eL.toHomeomorph
    exact h2 _ h1
  have hWnormal : W.Normal :=
    (show (O₂.subgroupOf O₁).Normal from hnormal).map
      (eL : ↥O₁ →* Gal(SeparableClosure (𝔮.adicCompletion ↥F) / (𝔮.adicCompletion ↥F)))
      eL.surjective
  have hlocal : ∀ x : NK.BrauerHasse.H2Profinite (K := 𝔮.adicCompletion ↥F)
      (K' := SeparableClosure (𝔮.adicCompletion ↥F)) p
      (⊤ : Subgroup Gal(SeparableClosure (𝔮.adicCompletion ↥F) / (𝔮.adicCompletion ↥F))),
      NK.LocalDecomposition.H2Profinite.res p
        (show W ≤ (⊤ : Subgroup Gal(SeparableClosure (𝔮.adicCompletion ↥F) /
          (𝔮.adicCompletion ↥F))) from le_top) x = 0 :=
    local_res_zero_of_index_prime (L := ↥F) 𝔮 p hp hp2 hζκ W hWcl hWnormal hWidx
  let e' : ↥O₂ ≃ₜ* ↥W :=
    (subgroupOfEquiv O₁ O₂ hO₂O₁).trans (tsubEquiv eL (O₂.subgroupOf O₁))
  have he : ∀ x : ↥O₂, (eTop (Subgroup.inclusion hO₂O₁ x) :
      ↥(⊤ : Subgroup Gal(SeparableClosure (𝔮.adicCompletion ↥F) /
        (𝔮.adicCompletion ↥F)))) =
      Subgroup.inclusion (le_top : W ≤ (⊤ : Subgroup Gal(SeparableClosure
        (𝔮.adicCompletion ↥F) / (𝔮.adicCompletion ↥F)))) (e' x) := by
    intro x
    apply Subtype.ext
    rfl
  have hres := transport_LZ (K := K) (K' := K')
    (κ := 𝔮.adicCompletion ↥F) (κ' := SeparableClosure (𝔮.adicCompletion ↥F))
    hO₂O₁ p eTop W e' he hlocal y
  rw [show (inf_le_inf_right (NK.BrauerHasse.stabSubgroup A₀) h21 : O₂ ≤ O₁) = hO₂O₁
    from Subsingleton.elim _ _]
  exact hres



/-! ### the Dedekind saturation lemma -/

private lemma dedekind_saturation {G : Type*} [Group G] {N U₁ D X : Subgroup G}
    (hN : N.Normal) (hXU₁ : X ≤ U₁) (hXD : X ≤ D) (hCN : (U₁ ⊓ D) ⊓ N ≤ X) :
    (X ⊔ N) ⊓ U₁ ⊓ D = X := by
  haveI := hN
  refine le_antisymm ?_ ?_
  · intro g hg
    rw [Subgroup.mem_inf] at hg
    obtain ⟨hg1, hgD⟩ := hg
    rw [Subgroup.mem_inf] at hg1
    obtain ⟨hgsup, hgU₁⟩ := hg1
    obtain ⟨x, hxX, n, hnN, hxn⟩ := (Subgroup.mem_sup_of_normal_right (s := X) (t := N)).mp hgsup
    have hn_eq : n = x⁻¹ * g := by rw [← hxn]; group
    have hnU₁ : n ∈ U₁ := by rw [hn_eq]; exact mul_mem (inv_mem (hXU₁ hxX)) hgU₁
    have hnD : n ∈ D := by rw [hn_eq]; exact mul_mem (inv_mem (hXD hxX)) hgD
    rw [← hxn]
    exact mul_mem hxX (hCN ⟨⟨hnU₁, hnD⟩, hnN⟩)
  · intro g hg
    exact ⟨⟨Subgroup.mem_sup_left hg, hXU₁ hg⟩, hXD hg⟩

/-! ### the main argument -/

theorem coprime_relIndex_of_res_ne_zero (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) {K K' : Type}
    [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K'] (ζ : K')
    (hζ : IsPrimitiveRoot ζ p) (A : NK.BrauerHasse.OverFinitePrime K K')
    {U₁ U₂ : Subgroup Gal(K'/K)} (hU₁ : NK.NUV2.LC.RouteB.IsMuOpen (K := K) (K' := K') ζ U₁)
    (hU₂ : IsOpen (U₂ : Set Gal(K'/K))) (h21 : U₂ ≤ U₁)
    (y : NK.BrauerHasse.H2Profinite (K := K) (K' := K') p
      (U₁ ⊓ NK.BrauerHasse.stabSubgroup A.1))
    (hy : NK.LocalDecomposition.H2Profinite.res p
      (inf_le_inf_right _ h21 : U₂ ⊓ NK.BrauerHasse.stabSubgroup A.1 ≤
        U₁ ⊓ NK.BrauerHasse.stabSubgroup A.1) y ≠ 0) :
    Nat.Coprime ((U₂ ⊓ NK.BrauerHasse.stabSubgroup A.1).relIndex
      (U₁ ⊓ NK.BrauerHasse.stabSubgroup A.1)) p := by
  let D : Subgroup Gal(K'/K) := NK.BrauerHasse.stabSubgroup A.1
  let O₁ : Subgroup Gal(K'/K) := U₁ ⊓ D
  let O₂ : Subgroup Gal(K'/K) := U₂ ⊓ D
  have hO₂O₁ : O₂ ≤ O₁ := fun x hx => ⟨h21 hx.1, hx.2⟩
  by_contra hnc
  -- `p` divides the index
  have hdiv : p ∣ (O₂.subgroupOf O₁).index := by
    have hnot : ¬ p.Coprime (O₂.relIndex O₁) := fun h => hnc (Nat.coprime_comm.mp h)
    by_contra hd
    exact hnot ((hp.coprime_iff_not_dvd).mpr hd)
  -- an open normal subgroup of `Gal(K'/K)` contained in `U₂`
  obtain ⟨N₀, hN₀le⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (G := Gal(K'/K)) hU₂ (Subgroup.one_mem U₂)
  set N : Subgroup Gal(K'/K) := (N₀ : Subgroup Gal(K'/K)) with hNdef
  have hNle : N ≤ U₂ := hN₀le
  have hNopen : IsOpen (N : Set Gal(K'/K)) := N₀.isOpen
  have hNnormal : N.Normal := by rw [hNdef]; infer_instance
  haveI : N.Normal := hNnormal
  have hNfin : N.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hNU₁ : N ≤ U₁ := le_trans hNle h21
  -- the core `C`
  set C : Subgroup Gal(K'/K) := O₁ ⊓ N with hCdef
  have hCO₂ : C ≤ O₂ := fun x hx => ⟨hNle hx.2, hx.1.2⟩
  have hCO₁ : C ≤ O₁ := inf_le_left
  have hCnormal : (C.subgroupOf O₁).Normal := by
    have heq : C.subgroupOf O₁ = N.subgroupOf O₁ := by
      ext x
      simp only [hCdef, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
    rw [heq]
    exact hNnormal.subgroupOf O₁
  have hCfin : (C.subgroupOf O₁).FiniteIndex := by
    rw [Subgroup.finiteIndex_iff]
    have hdvd : (C.subgroupOf O₁).index ∣ N.index := by
      show (C.relIndex O₁) ∣ N.index
      rw [hCdef, inf_comm, Subgroup.inf_relIndex_right]
      exact Subgroup.relIndex_dvd_index_of_normal N O₁
    intro h0
    rw [h0] at hdvd
    exact hNfin.index_ne_zero (Nat.eq_zero_of_zero_dvd hdvd)
  -- the Sylow step
  obtain ⟨R₁, X, hCR₁, hR₁O₂, hR₁X, hXO₁, hR₁norm, hcop, hidxR⟩ :=
    NK.NUV2.LC.RouteB.exists_prime_step_of_dvd_index (K := K) (K' := K')
      (O₁ := O₁) (O₂ := O₂) (C := C) p hp hCO₂ hO₂O₁ hCnormal hCfin hdiv
  -- the Dedekind saturation: the intermediate groups have the form `U ⊓ D`
  have hXU₁ : X ≤ U₁ := le_trans hXO₁ inf_le_left
  have hXD : X ≤ D := le_trans hXO₁ inf_le_right
  have hR₁U₁ : R₁ ≤ U₁ := le_trans hR₁O₂ (le_trans hO₂O₁ inf_le_left)
  have hR₁D : R₁ ≤ D := le_trans hR₁O₂ (le_trans hO₂O₁ inf_le_right)
  have hsatX : (X ⊔ N) ⊓ U₁ ⊓ D = X :=
    dedekind_saturation hNnormal hXU₁ hXD (le_trans hCR₁ hR₁X)
  have hsatR : (R₁ ⊔ N) ⊓ U₁ ⊓ D = R₁ :=
    dedekind_saturation hNnormal hR₁U₁ hR₁D hCR₁
  set U₁' : Subgroup Gal(K'/K) := (X ⊔ N) ⊓ U₁ with hU₁'def
  set U₂' : Subgroup Gal(K'/K) := (R₁ ⊔ N) ⊓ U₁ with hU₂'def
  have hU₁'D : U₁' ⊓ D = X := hsatX
  have hU₂'D : U₂' ⊓ D = R₁ := hsatR
  have h21' : U₂' ≤ U₁' := fun x hx =>
    ⟨sup_le_sup_right hR₁X N hx.1, hx.2⟩
  have hN_le_U₁' : N ≤ U₁' := fun x hx => ⟨Subgroup.mem_sup_right hx, hNU₁ hx⟩
  have hN_le_U₂' : N ≤ U₂' := fun x hx => ⟨Subgroup.mem_sup_right hx, hNU₁ hx⟩
  have hU₁'open : IsOpen (U₁' : Set Gal(K'/K)) := Subgroup.isOpen_mono hN_le_U₁' hNopen
  have hU₂'open : IsOpen (U₂' : Set Gal(K'/K)) := Subgroup.isOpen_mono hN_le_U₂' hNopen
  have hU₁'mu : IsMuOpen (K := K) (K' := K') ζ U₁' := ⟨hU₁'open, le_trans inf_le_right hU₁.2⟩
  have hnormal' : ((U₂' ⊓ D).subgroupOf (U₁' ⊓ D)).Normal := by
    rw [hU₁'D, hU₂'D]
    exact hR₁norm
  have hidx' : (U₂' ⊓ D).relIndex (U₁' ⊓ D) = p := by
    rw [hU₁'D, hU₂'D]
    exact hidxR
  -- the two inclusions of the chain `U₂' ⊓ D ≤ U₁' ⊓ D ≤ O₁` and `U₂' ⊓ D ≤ O₂`
  have hC₀X' : U₂' ⊓ D ≤ U₁' ⊓ D := inf_le_inf_right D h21'
  have hX'A : U₁' ⊓ D ≤ O₁ := by rw [hU₁'D]; exact hXO₁
  have hC₀A : U₂' ⊓ D ≤ O₁ := hC₀X'.trans hX'A
  have hC₀B : U₂' ⊓ D ≤ O₂ := by rw [hU₂'D]; exact hR₁O₂
  -- (LZ)
  have hLZ : ∀ z : NK.BrauerHasse.H2Profinite (K := K) (K' := K') p (U₁' ⊓ D),
      NK.LocalDecomposition.H2Profinite.res p hC₀X' z = 0 := by
    intro z
    exact res_zero_of_prime_index_local (K := K) (K' := K') p hp hp2 ζ hζ
      A (U₁ := U₁') (U₂ := U₂') hU₁'mu hU₂'open h21' hnormal' hidx' z
  -- the composition `res_{O₁ → R₁} = res_{X → R₁} ∘ res_{O₁ → X} = 0`
  have hzeroA : ∀ z : NK.BrauerHasse.H2Profinite (K := K) (K' := K') p O₁,
      NK.LocalDecomposition.H2Profinite.res p hC₀A z = 0 := by
    intro z
    rw [← NK.NUV2.LC.OddTwist.H2Profinite_res_comp p hC₀X' hX'A z]
    exact hLZ (NK.LocalDecomposition.H2Profinite.res p hX'A z)
  -- injectivity of `res_{O₂ → R₁}`
  have hcop' : Nat.Coprime (Subgroup.index ((U₂' ⊓ D).subgroupOf O₂)) p := by
    have h1 : Subgroup.index ((U₂' ⊓ D).subgroupOf O₂) = (U₂' ⊓ D).relIndex O₂ := rfl
    rw [h1, hU₂'D]
    exact hcop
  have hinj := H2Profinite_res_injective_of_coprime_index (K := K) (K' := K') p hp
    hC₀B hcop'
  have hO₂zero : ∀ z : NK.BrauerHasse.H2Profinite (K := K) (K' := K') p O₁,
      NK.LocalDecomposition.H2Profinite.res p hO₂O₁ z = 0 := by
    intro z
    apply hinj
    rw [NK.NUV2.LC.OddTwist.H2Profinite_res_comp p hC₀B hO₂O₁ z]
    rw [show (hC₀B.trans hO₂O₁ : U₂' ⊓ D ≤ O₁) = hC₀A from Subsingleton.elim _ _]
    rw [hzeroA z]
    exact (NK.NUV2.LC.OddTwist.H2Profinite_res_zero p hC₀B).symm
  -- contradiction
  refine hy ?_
  rw [show (inf_le_inf_right (NK.BrauerHasse.stabSubgroup A.1) h21 : U₂ ⊓ D ≤ U₁ ⊓ D) =
    hO₂O₁ from Subsingleton.elim _ _]
  exact hO₂zero y


end NK.NUV2.LC.RouteB
