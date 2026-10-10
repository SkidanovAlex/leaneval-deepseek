import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Algebra.ProperAction.Basic
import Submission.NK.TameStructureDeep.Tame.CorrectedInterface
import Submission.NK.TameStructureDeep.Tame.coprime_finrank_of_le_tameClosure
import Submission.NK.TameStructureDeep.Tame.isProPrimeToP_of_openNormal_index
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical
open scoped Topology
open Filter
open IntermediateField

namespace NK.TameStructureDeep.Tame


/-! ## The general profinite bookkeeping

`Gal(κ^{tr}/κ^{ur})` is the quotient `I_κ/V_κ` (`I_κ = Gal(K'/κ^{ur})`, `V_κ = Gal(K'/κ^{tr})`),
and it is a profinite group.  By `isProPrimeToP_of_openNormal_index` it suffices to test the
*open* normal subgroups, which correspond to finite subextensions `κ^{ur} ⊆ L ⊆ κ^{tr}`; their
index is `[L : κ^{ur}]`, and `[L : κ^{ur}]` is prime to `p` by `coprime_finrank_of_le_tameClosure`.
This section puts that bookkeeping in general form, with no reference to arithmetic. -/

/-- **`I/V` as the image of `I` in `G ⧸ V`.**  For `V ◁ G` and any `I ≤ G`, the map
`↥I →* ↥(quotientImage V I)` induced by `QuotientGroup.mk' V` has kernel `V.subgroupOf I` and is
surjective, so the first isomorphism theorem gives `↥I ⧸ V.subgroupOf I ≃* ↥(quotientImage V I)`. -/
noncomputable def quotientImageMulEquivQuotient {G : Type*} [Group G] {V I : Subgroup G}
    [V.Normal] : ↥(NK.LocalTame.quotientImage V I) ≃* (↥I ⧸ V.subgroupOf I) := by
  let hmk : ↥I →* ↥(NK.LocalTame.quotientImage V I) :=
    ((QuotientGroup.mk' V).comp I.subtype).codRestrict (NK.LocalTame.quotientImage V I)
      (fun x => Subgroup.mem_map_of_mem (QuotientGroup.mk' V) x.2)
  have hcoe : ∀ x : ↥I, ((hmk x : ↥(NK.LocalTame.quotientImage V I)) : G ⧸ V)
      = (QuotientGroup.mk' V) (x : G) := fun x => rfl
  have hker : hmk.ker = V.subgroupOf I := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h2 : (QuotientGroup.mk' V) (x : G) = 1 := by
        have := congrArg (fun z : ↥(NK.LocalTame.quotientImage V I) => (z : G ⧸ V)) h
        simpa [hcoe x] using this
      exact (QuotientGroup.eq_one_iff (x : G)).mp h2
    · intro h
      refine Subtype.ext ?_
      show ((hmk x : ↥(NK.LocalTame.quotientImage V I)) : G ⧸ V) = 1
      rw [hcoe x]
      exact (QuotientGroup.eq_one_iff (x : G)).mpr h
  have hsurj : Function.Surjective hmk := by
    rintro ⟨y, hy⟩
    rw [NK.LocalTame.quotientImage, Subgroup.mem_map] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  exact ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective hmk hsurj)).symm

/-- **Change of base for fixing subgroups.**  For intermediate fields `U ≤ F` of a Galois
extension `K'/κ`, the fixing subgroup of `F` inside `Gal(K'/U)` is the image of the fixing
subgroup of `F` inside `Gal(K'/κ)` under `IntermediateField.fixingSubgroupEquiv U`. -/
theorem map_fixingSubgroupEquiv_subgroupOf {κ K' : Type*} [Field κ] [Field K']
    [Algebra κ K'] [IsGalois κ K'] {U F : IntermediateField κ K'} (h : U ≤ F) :
    Subgroup.map (↑(IntermediateField.fixingSubgroupEquiv U))
        (F.fixingSubgroup.subgroupOf U.fixingSubgroup) =
      (IntermediateField.extendScalars h).fixingSubgroup := by
  ext f
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact hg ⟨x, hx⟩
  · intro hf
    refine ⟨(IntermediateField.fixingSubgroupEquiv U).symm f, ?_, rfl⟩
    intro x
    show ((IntermediateField.fixingSubgroupEquiv U).symm f : Gal(K'/κ)) x = x
    exact (IntermediateField.mem_fixingSubgroup_iff _ f).mp hf x x.2

/-- **The relative index formula for fixing subgroups.**  For intermediate fields `U ≤ F` of a
Galois extension `K'/κ`, the index of `Gal(K'/F)` in `Gal(K'/U)` is `[F : U]`. -/
theorem index_subgroupOf_fixingSubgroup {κ K' : Type*} [Field κ] [Field K']
    [Algebra κ K'] [IsGalois κ K'] {U F : IntermediateField κ K'} (h : U ≤ F) :
    (F.fixingSubgroup.subgroupOf U.fixingSubgroup).index =
      Module.finrank ↥U (IntermediateField.extendScalars h) := by
  rw [← Subgroup.index_map_equiv (F.fixingSubgroup.subgroupOf U.fixingSubgroup)
      (IntermediateField.fixingSubgroupEquiv U), map_fixingSubgroupEquiv_subgroupOf h]
  exact (IntermediateField.finrank_eq_fixingSubgroup_index K'
    (IntermediateField.extendScalars h)).symm

/-- **The profinite bookkeeping, in general form.**  Let `K'/κ` be a Galois extension of fields and
`U ≤ T` intermediate fields such that (i) `Gal(K'/T)` is normal in `Gal(K'/κ)` (i.e. `T/κ` is
normal) and (ii) every finite extension `L/κ^{ur}` inside `κ^{tr}` has degree prime to `p`.  Then
the image of `Gal(K'/U)` in `Gal(K'/κ) ⧸ Gal(K'/T)` — that is, `Gal(T/U)` — is pro-prime-to-`p`.

The proof tests the *open* normal subgroups (`isProPrimeToP_of_openNormal_index`): an open normal
subgroup of `Gal(K'/U) ⧸ Gal(K'/T)` pulls back to an open normal subgroup `W ≤ Gal(K'/U)`
containing `Gal(K'/T)`; then `W` is the fixing subgroup of its fixed field `M`, which is finite
over `U` and contained in `T`, so `[Gal(K'/U) : W] = [M : U]` is prime to `p` by (ii). -/
theorem isProPrimeToP_of_coprime_index {κ K' : Type*} [Field κ] [Field K']
    [Algebra κ K'] [IsGalois κ K'] [Algebra.IsIntegral κ K'] {U T : IntermediateField κ K'}
    (hUT : U ≤ T) [(T.fixingSubgroup).Normal] {p : ℕ} (hp : p.Prime)
    (harith : ∀ L : IntermediateField ↥U K', (L : Set K') ⊆ (T : Set K') →
      FiniteDimensional ↥U L → Nat.Coprime p (Module.finrank ↥U L)) :
    NK.LocalTame.IsProPrimeToP p
      ↥(NK.LocalTame.quotientImage T.fixingSubgroup U.fixingSubgroup) := by
  classical
  haveI hIfin : (T.fixingSubgroup.subgroupOf U.fixingSubgroup).Normal :=
    Subgroup.Normal.subgroupOf ‹(T.fixingSubgroup).Normal› (U.fixingSubgroup)
  -- `T` viewed over the base `↥U`
  let T' : IntermediateField ↥U K' := IntermediateField.extendScalars hUT
  have hmapW : Subgroup.map ↑(IntermediateField.fixingSubgroupEquiv U)
      (T.fixingSubgroup.subgroupOf U.fixingSubgroup) = T'.fixingSubgroup :=
    map_fixingSubgroupEquiv_subgroupOf hUT
  haveI hWnorm : T'.fixingSubgroup.Normal := by
    rw [← hmapW]
    exact Subgroup.Normal.map (Subgroup.Normal.subgroupOf ‹(T.fixingSubgroup).Normal› _)
      (IntermediateField.fixingSubgroupEquiv U).toMonoidHom
      (IntermediateField.fixingSubgroupEquiv U).surjective
  have hWclosed : IsClosed (T'.fixingSubgroup : Set (Gal(K'/↥U))) :=
    NK.TameStructure.ProfiniteAux.fixingSubgroup_isClosed_of_isIntegral T'
  haveI hTD : TotallyDisconnectedSpace (Gal(K'/↥U) ⧸ T'.fixingSubgroup) :=
    NK.ProfiniteP.ProPCore.totallyDisconnectedSpace_quotient hWclosed
  -- the arithmetic test on open normal subgroups
  have hH : NK.LocalTame.IsProPrimeToP p (Gal(K'/↥U) ⧸ T'.fixingSubgroup) := by
    refine isProPrimeToP_of_openNormal_index hp (fun U' => ?_)
    -- pull back to an open normal subgroup of `Gal(K'/↥U)` containing `Gal(K'/T')`
    let W₁ : Subgroup (Gal(K'/↥U)) := U'.toSubgroup.comap (QuotientGroup.mk' T'.fixingSubgroup)
    have hcont : Continuous (QuotientGroup.mk' T'.fixingSubgroup) :=
      QuotientGroup.continuous_mk.congr fun x => QuotientGroup.mk'_apply _ x
    have hW₁open : IsOpen (W₁ : Set (Gal(K'/↥U))) :=
      U'.toOpenSubgroup.isOpen'.preimage hcont
    haveI : W₁.Normal := Subgroup.Normal.comap U'.isNormal' _
    have hW₁nhds : (W₁ : Set (Gal(K'/↥U))) ∈ 𝓝 1 := hW₁open.mem_nhds W₁.one_mem
    obtain ⟨L₀, hL₀fd, hL₀le⟩ :=
      (krullTopology_mem_nhds_one_iff ↥U K' (W₁ : Set (Gal(K'/↥U)))).mp hW₁nhds
    -- the fixed field of `W₁`, its finiteness and its containment in `T`
    let M : IntermediateField ↥U K' := IntermediateField.fixedField W₁
    have hWW₁ : T'.fixingSubgroup ≤ W₁ := by
      intro x hx
      have h1 : (QuotientGroup.mk' T'.fixingSubgroup) x = 1 := by
        rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
        exact hx
      show (QuotientGroup.mk' T'.fixingSubgroup) x ∈ U'.toSubgroup
      rw [h1]
      exact Subgroup.one_mem _
    have hantitone : ∀ {A B : Subgroup (Gal(K'/↥U))}, A ≤ B →
        IntermediateField.fixedField B ≤ IntermediateField.fixedField A := by
      intro A B hAB x hx
      rw [IntermediateField.mem_fixedField_iff] at hx ⊢
      exact fun f hf => hx f (hAB hf)
    have hMT : M ≤ T' := by
      have h2 : IntermediateField.fixedField W₁ ≤ IntermediateField.fixedField T'.fixingSubgroup :=
        hantitone hWW₁
      rwa [InfiniteGalois.fixedField_fixingSubgroup T'] at h2
    have hML₀ : M ≤ L₀ := by
      have h2 : IntermediateField.fixedField W₁ ≤ IntermediateField.fixedField L₀.fixingSubgroup :=
        hantitone hL₀le
      rwa [InfiniteGalois.fixedField_fixingSubgroup L₀] at h2
    have hMfd : FiniteDimensional ↥U M := by
      haveI : FiniteDimensional ↥U ↥(IntermediateField.restrict hML₀) :=
        IntermediateField.finiteDimensional_left (IntermediateField.restrict hML₀)
      exact (IntermediateField.restrictAlgEquiv hML₀).symm.toLinearEquiv.finiteDimensional
    have hsubT : (M : Set K') ⊆ (T : Set K') := fun x hx => hMT hx
    -- the index of `W₁` is `[M : U]`, and `[M : U]` is prime to `p`
    have hfix : M.fixingSubgroup = W₁ :=
      InfiniteGalois.fixingSubgroup_fixedField (⟨W₁, Subgroup.isClosed_of_isOpen W₁ hW₁open⟩ :
        ClosedSubgroup (Gal(K'/↥U)))
    have hidx : W₁.index = Module.finrank ↥U M := by
      rw [IntermediateField.finrank_eq_fixingSubgroup_index K' M, hfix]
    have hidxU : U'.toSubgroup.index = W₁.index :=
      (Subgroup.index_comap_of_surjective U'.toSubgroup
        (QuotientGroup.mk'_surjective T'.fixingSubgroup)).symm
    rw [hidxU, hidx]
    exact harith M hsubT hMfd
  -- transport along `↥(quotientImage T.fs U.fs) ≃* Gal(K'/↥U) ⧸ T'.fixingSubgroup`
  have e1 : ↥(NK.LocalTame.quotientImage T.fixingSubgroup U.fixingSubgroup) ≃*
      (↥(U.fixingSubgroup) ⧸ (T.fixingSubgroup).subgroupOf U.fixingSubgroup) :=
    quotientImageMulEquivQuotient
  have e2 : (↥(U.fixingSubgroup) ⧸ (T.fixingSubgroup).subgroupOf U.fixingSubgroup) ≃*
      (Gal(K'/↥U) ⧸ T'.fixingSubgroup) :=
    QuotientGroup.congr _ _ (IntermediateField.fixingSubgroupEquiv U) hmapW
  exact (NK.LocalTame.isProPrimeToP_congr (e1.trans e2) p).mpr hH

/-! ## The target: the tame inertia of the corrected wild inertia is pro-prime-to-`p` -/

/-- **`I_κ/V_κ` is pro-prime-to-`p` for the corrected wild inertia `V_κ = Gal(K'/κ^{tr})`**
(NSW (7.5.11)), at every `𝔭`-adic completion. -/
theorem isProPrimeToP_correctedWildInertia {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']
    {π : 𝔭.adicCompletionIntegers K} (hπ : NK.TameStructureDeep.Tame.IsUniformizerAt 𝔭 π)
    [hV : (NK.TameStructureDeep.Tame.correctedWildInertia (κ := 𝔭.adicCompletion K) (K' := K')
      (NK.TameStructureDeep.Tame.resCharAt 𝔭) π).Normal] :
    NK.LocalTame.IsProPrimeToP (NK.TameStructureDeep.Tame.resCharAt 𝔭)
      ↥(NK.LocalTame.quotientImage
        (NK.TameStructureDeep.Tame.correctedWildInertia (κ := 𝔭.adicCompletion K) (K' := K')
          (NK.TameStructureDeep.Tame.resCharAt 𝔭) π)
        (NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K')
          (NK.TameStructureDeep.Tame.resCharAt 𝔭))) := by
  classical
  have hp : (NK.TameStructureDeep.Tame.resCharAt 𝔭).Prime :=
    NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭
  have hUT : NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
        (NK.TameStructureDeep.Tame.resCharAt 𝔭) ≤
      NK.TameStructureDeep.Tame.tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
        (NK.TameStructureDeep.Tame.resCharAt 𝔭) π :=
    NK.TameStructureDeep.Tame.unramifiedClosure_le_tameClosure _ _
  have hI : NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K')
        (NK.TameStructureDeep.Tame.resCharAt 𝔭) =
      (NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
        (NK.TameStructureDeep.Tame.resCharAt 𝔭)).fixingSubgroup :=
    NK.LocalAnabelian.ResidueField.inertiaSubgroup_eq_fixingSubgroup_unramifiedClosure _
  haveI : (NK.TameStructureDeep.Tame.tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
      (NK.TameStructureDeep.Tame.resCharAt 𝔭) π).fixingSubgroup.Normal := hV
  have hmain : NK.LocalTame.IsProPrimeToP (NK.TameStructureDeep.Tame.resCharAt 𝔭)
      ↥(NK.LocalTame.quotientImage
        (NK.TameStructureDeep.Tame.correctedWildInertia (κ := 𝔭.adicCompletion K) (K' := K')
          (NK.TameStructureDeep.Tame.resCharAt 𝔭) π)
        ((NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
          (NK.TameStructureDeep.Tame.resCharAt 𝔭)).fixingSubgroup)) :=
    isProPrimeToP_of_coprime_index hUT hp
      (fun L hL hfd => by
        haveI := hfd
        exact coprime_finrank_of_le_tameClosure 𝔭 L hL)
  have hIm : NK.LocalTame.quotientImage
        (NK.TameStructureDeep.Tame.correctedWildInertia (κ := 𝔭.adicCompletion K) (K' := K')
          (NK.TameStructureDeep.Tame.resCharAt 𝔭) π)
        (NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K')
          (NK.TameStructureDeep.Tame.resCharAt 𝔭)) =
      NK.LocalTame.quotientImage
        (NK.TameStructureDeep.Tame.correctedWildInertia (κ := 𝔭.adicCompletion K) (K' := K')
          (NK.TameStructureDeep.Tame.resCharAt 𝔭) π)
        ((NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
          (NK.TameStructureDeep.Tame.resCharAt 𝔭)).fixingSubgroup) := by
    rw [hI]
  exact (NK.LocalTame.isProPrimeToP_congr (MulEquiv.subgroupCongr hIm)
    (NK.TameStructureDeep.Tame.resCharAt 𝔭)).mpr hmain

end NK.TameStructureDeep.Tame
