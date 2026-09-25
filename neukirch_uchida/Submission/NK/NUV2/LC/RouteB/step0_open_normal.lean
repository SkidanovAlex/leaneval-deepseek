import Mathlib
import Submission.NK.NUV2.LC.RouteB.Defs
import Submission.NK.LocalDecomposition.Basic
import Submission.NK.LocalAnabelian.ResidueField.Defs

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

universe u

open scoped Pointwise

namespace NK.NUV2.LC.RouteB

/-! ## Auxiliary: restriction of topological group isomorphisms to subgroups -/

/-- The restriction of a topological group isomorphism to a subgroup is a topological isomorphism
onto its image. -/
noncomputable def subgroupMapCME {G H : Type*} [Group G] [TopologicalSpace G] [Group H]
    [TopologicalSpace H] (e : G ≃ₜ* H) (V : Subgroup G) :
    ↥V ≃ₜ* ↥(V.map (e : G →* H)) :=
  ContinuousMulEquiv.mk'
    { toEquiv :=
      { toFun := fun x => ⟨(e : G → H) (x : G), ⟨(x : G), x.2, rfl⟩⟩
        invFun := fun y => ⟨((e : G ≃* H).symm (y : H)), by
          obtain ⟨z, hz, hzy⟩ := y.2
          have hy : (y : H) = (e : G ≃* H) z := hzy.symm
          rw [hy]
          simpa using hz⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun y => Subtype.ext (by simp) }
      continuous_toFun := Continuous.subtype_mk (e.continuous_toFun.comp continuous_subtype_val) _
      continuous_invFun := Continuous.subtype_mk (e.symm.continuous_toFun.comp continuous_subtype_val) _ }
    (fun x y => Subtype.ext (map_mul e (x : G) (y : G)))

/-- A subgroup and its restriction to a bigger subgroup are topologically isomorphic. -/
noncomputable def subgroupOfCME {G : Type*} [Group G] [TopologicalSpace G]
    (D V : Subgroup G) (h : V ≤ D) : ↥V ≃ₜ* ↥(V.subgroupOf D) :=
  ContinuousMulEquiv.mk'
    { toEquiv :=
      { toFun := fun x => ⟨⟨(x : G), h x.2⟩, x.2⟩
        invFun := fun y => ⟨((y : ↥D) : G), y.2⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun y => Subtype.ext rfl }
      continuous_toFun := Continuous.subtype_mk
        (Continuous.subtype_mk continuous_subtype_val _) _
      continuous_invFun := Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _ }
    (fun x y => Subtype.ext rfl)

/-- Equal subgroups of a topological group are topologically isomorphic. -/
noncomputable def subgroupCongrCME {G : Type*} [Group G] [TopologicalSpace G]
    {S T : Subgroup G} (h : S = T) : ↥S ≃ₜ* ↥T := by
  let φ : S ≃* T := MulEquiv.subgroupCongr h
  refine ContinuousMulEquiv.mk φ ?_ ?_
  · exact Continuous.subtype_mk continuous_subtype_val (fun x => (φ x).2)
  · exact Continuous.subtype_mk continuous_subtype_val (fun x => (φ.symm x).2)

section Aux

variable {K K' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
variable {κ κ' : Type u} [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']

/-- **The abstract group-theoretic content of Step 0.**

Let `ζ ∈ K'` be a primitive `p`-th root of unity, let `e : H ≃ₜ* Gal(κ'/κ)` be a topological
isomorphism of the closed subgroup `H ≤ Gal(K'/K)` with the absolute Galois group of (an abstract
model of) a local field, and let `ξ ∈ κ'` be a primitive `p`-th root of unity.  Then `H` has an open
normal subgroup `H₁` fixing `ζ` which is `Gal(κ'/M)` for a finite Galois `M/κ` containing `ξ`.

`H₁` is the `H`-core of `rootFix ζ ⊓ e⁻¹(Gal(κ'/κ(ξ)))`. -/
theorem step0_open_normal_aux (p : ℕ) (hp : p.Prime) (ζ : K') (hζ : IsPrimitiveRoot ζ p)
    (ξ : κ') (hξ : IsPrimitiveRoot ξ p)
    (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (e : ↥H ≃ₜ* Gal(κ'/κ)) :
    ∃ (H₁ : Subgroup Gal(K'/K)) (M : FiniteGaloisIntermediateField κ κ')
      (e₁ : ↥H₁ ≃ₜ* ↥(M.fixingSubgroup)),
      H₁ ≤ H ∧ H ≤ Subgroup.normalizer H₁ ∧ 0 < H₁.relIndex H ∧
        H₁ ≤ NK.NUV2.LC.RouteB.rootFix (K := K) (K' := K') ζ ∧
        (∃ ζ' : ↥M, IsPrimitiveRoot ζ' p) := by
  classical
  -- ## `ζ` is integral over `K`, so `rootFix ζ` is open of finite index
  have hζint : IsIntegral K ζ :=
    ⟨Polynomial.X ^ p - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hp.pos.ne',
      by simp [hζ.pow_eq_one]⟩
  haveI hrootFix_fd : FiniteDimensional K ↥(IntermediateField.adjoin K ({ζ} : Set K')) :=
    IntermediateField.finiteDimensional_adjoin (S := ({ζ} : Set K')) fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hζint
  have hrootFix_open : IsOpen (rootFix (K := K) (K' := K') ζ : Set Gal(K'/K)) := by
    show IsOpen ((IntermediateField.adjoin K ({ζ} : Set K')).fixingSubgroup : Set Gal(K'/K))
    exact IntermediateField.fixingSubgroup_isOpen _
  have hrootFix_fin : (rootFix (K := K) (K' := K') ζ).FiniteIndex := by
    rw [Subgroup.finiteIndex_iff]
    show (IntermediateField.adjoin K ({ζ} : Set K')).fixingSubgroup.index ≠ 0
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index (E' := K')
      (IntermediateField.adjoin K ({ζ} : Set K'))]
    exact (Module.finrank_pos).ne'
  -- ## the level `κ(ξ)` of the local field
  have hξint : IsIntegral κ ξ :=
    ⟨Polynomial.X ^ p - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hp.pos.ne',
      by simp [hξ.pow_eq_one]⟩
  haveI hξ_fd : FiniteDimensional κ ↥(IntermediateField.adjoin κ ({ξ} : Set κ')) :=
    IntermediateField.finiteDimensional_adjoin (S := ({ξ} : Set κ')) fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hξint
  let J : Subgroup Gal(κ'/κ) := (IntermediateField.adjoin κ ({ξ} : Set κ')).fixingSubgroup
  have hJ_open : IsOpen (J : Set Gal(κ'/κ)) := by
    show IsOpen ((IntermediateField.adjoin κ ({ξ} : Set κ')).fixingSubgroup : Set Gal(κ'/κ))
    exact IntermediateField.fixingSubgroup_isOpen _
  have hJ_fin : J.FiniteIndex := by
    rw [Subgroup.finiteIndex_iff]
    show (IntermediateField.adjoin κ ({ξ} : Set κ')).fixingSubgroup.index ≠ 0
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index (E' := κ')
      (IntermediateField.adjoin κ ({ξ} : Set κ'))]
    exact (Module.finrank_pos).ne'
  -- ## the subgroup `V = rootFix ζ ⊓ e⁻¹(Gal(κ'/κ(ξ)))` and its `H`-core
  let H₀ : Subgroup Gal(K'/K) := (J.comap (e : ↥H →* Gal(κ'/κ))).map H.subtype
  let V : Subgroup Gal(K'/K) := rootFix (K := K) (K' := K') ζ ⊓ H₀
  let Vh : Subgroup ↥H := (rootFix (K := K) (K' := K') ζ).subgroupOf H ⊓ J.comap (e : ↥H →* Gal(κ'/κ))
  let C : Subgroup ↥H := Vh.normalCore
  let H₁ : Subgroup Gal(K'/K) := C.map H.subtype
  let E : Subgroup Gal(κ'/κ) := C.map (e : ↥H →* Gal(κ'/κ))
  have hVsub : V.subgroupOf H = Vh := by
    change Subgroup.comap H.subtype (rootFix (K := K) (K' := K') ζ ⊓ H₀)
        = (rootFix (K := K) (K' := K') ζ).subgroupOf H ⊓ J.comap (e : ↥H →* Gal(κ'/κ))
    rw [Subgroup.comap_inf,
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective
        (J.comap (e : ↥H →* Gal(κ'/κ)))]
    rfl
  have hH₁eq : H₁ = NK.LocalDecomposition.coreIn H V := by
    rw [NK.LocalDecomposition.coreIn_eq_normalCore_map H V, hVsub]
  -- ## openness and finiteness of `Vh` and `C`
  have hrootFixH_open : IsOpen (((rootFix (K := K) (K' := K') ζ).subgroupOf H : Subgroup ↥H) : Set ↥H) := by
    rw [← Subgroup.comap_subtype (K := H) (H := rootFix (K := K) (K' := K') ζ), Subgroup.coe_comap]
    exact hrootFix_open.preimage continuous_subtype_val
  have hJH_open : IsOpen ((J.comap (e : ↥H →* Gal(κ'/κ)) : Subgroup ↥H) : Set ↥H) := by
    rw [Subgroup.coe_comap]
    exact hJ_open.preimage e.continuous_toFun
  have hVh_open : IsOpen (Vh : Set ↥H) := by
    show IsOpen ((((rootFix (K := K) (K' := K') ζ).subgroupOf H : Subgroup ↥H) : Set ↥H)
      ∩ ((J.comap (e : ↥H →* Gal(κ'/κ)) : Subgroup ↥H) : Set ↥H))
    exact hrootFixH_open.inter hJH_open
  haveI : (rootFix (K := K) (K' := K') ζ).FiniteIndex := hrootFix_fin
  haveI hrootFixH_fin : ((rootFix (K := K) (K' := K') ζ).subgroupOf H).FiniteIndex := inferInstance
  haveI hJH_fin : (J.comap (e : ↥H →* Gal(κ'/κ))).FiniteIndex := by
    rw [Subgroup.finiteIndex_iff, Subgroup.index_comap_of_surjective J e.surjective]
    exact hJ_fin.index_ne_zero
  haveI hVh_fin : Vh.FiniteIndex := inferInstance
  haveI hC_fin : C.FiniteIndex := Subgroup.finiteIndex_normalCore Vh
  have hVh_closed : IsClosed (Vh : Set ↥H) := Subgroup.isClosed_of_isOpen Vh hVh_open
  have hC_closed : IsClosed (C : Set ↥H) := Subgroup.normalCore_isClosed Vh hVh_closed
  have hC_open : IsOpen (C : Set ↥H) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex Vh.normalCore hC_closed
  have hC_normal : C.Normal := Subgroup.normalCore_normal Vh
  have hC_le_J : C ≤ J.comap (e : ↥H →* Gal(κ'/κ)) :=
    le_trans (Subgroup.normalCore_le Vh) inf_le_right
  -- ## the open normal subgroup `E = e(C)` of `Gal(κ'/κ)`
  have hE_open : IsOpen (E : Set Gal(κ'/κ)) := by
    rw [Subgroup.coe_map]
    exact Homeomorph.isOpenMap e.toHomeomorph _ hC_open
  have hE_normal : E.Normal :=
    Subgroup.Normal.map hC_normal (e : ↥H →* Gal(κ'/κ)) e.surjective
  have hE_closed : IsClosed (E : Set Gal(κ'/κ)) := Subgroup.isClosed_of_isOpen E hE_open
  -- ## the finite Galois extension `M/κ` fixed by `E`
  let M : FiniteGaloisIntermediateField κ κ' :=
    { toIntermediateField := IntermediateField.fixedField E
      finiteDimensional := by
        rw [← InfiniteGalois.isOpen_iff_finite (IntermediateField.fixedField E),
          InfiniteGalois.fixingSubgroup_fixedField ⟨E, hE_closed⟩]
        exact hE_open
      isGalois := by
        rw [← InfiniteGalois.normal_iff_isGalois (IntermediateField.fixedField E),
          InfiniteGalois.fixingSubgroup_fixedField ⟨E, hE_closed⟩]
        exact hE_normal }
  have hMfix : M.fixingSubgroup = E := InfiniteGalois.fixingSubgroup_fixedField ⟨E, hE_closed⟩
  have hHh : H₁.subgroupOf H = C := by
    show Subgroup.comap H.subtype (C.map H.subtype) = C
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective C
  let e₁ : ↥H₁ ≃ₜ* ↥(M.fixingSubgroup) :=
    (subgroupOfCME H H₁ (Subgroup.map_subtype_le C)).trans
      ((subgroupCongrCME hHh).trans
        ((subgroupMapCME e C).trans (subgroupCongrCME hMfix.symm)))
  refine ⟨H₁, M, e₁, ?_, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.map_subtype_le C
  · rw [hH₁eq]
    exact NK.LocalDecomposition.le_normalizer_coreIn H V
  · rw [hH₁eq]
    refine NK.LocalDecomposition.coreIn_relIndex_pos H V ?_
    show 0 < (V.subgroupOf H).index
    rw [hVsub]
    exact Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := Vh))
  · rw [hH₁eq]
    exact le_trans (NK.LocalDecomposition.coreIn_le_right H V) inf_le_left
  · have hE_le_J : E ≤ J := by
      refine le_trans (Subgroup.map_mono hC_le_J) ?_
      rw [Subgroup.map_comap_eq]
      exact inf_le_right
    have hξmem : ξ ∈ (M : IntermediateField κ κ') := by
      have h1 : ξ ∈ IntermediateField.adjoin κ ({ξ} : Set κ') :=
        IntermediateField.subset_adjoin κ _ (Set.mem_singleton ξ)
      have h2 : (IntermediateField.adjoin κ ({ξ} : Set κ')) ≤ (M : IntermediateField κ κ') := by
        rw [← InfiniteGalois.fixedField_fixingSubgroup
          (L := IntermediateField.adjoin κ ({ξ} : Set κ'))]
        exact IntermediateField.fixedField_le hE_le_J
      exact h2 h1
    exact ⟨⟨ξ, hξmem⟩, IsPrimitiveRoot.coe_submonoidClass_iff.mp hξ⟩

end Aux

/-- **Route B, Step 0: replacement of `H` by an open normal subgroup of local type fixing
`ζ_p`.**

Let `H ≤ Gal(K'/K)` be closed and continuously isomorphic to the absolute Galois group
`Gal(κ'/κ)` of a completion `κ = 𝔮.adicCompletion L` of a number field, and let `ζ ∈ K'` be a
primitive `p`-th root of unity.  Then there is an open normal subgroup `H₁ ≤ H` (so
`H ≤ Subgroup.normalizer H₁` and `0 < H₁.relIndex H`) which fixes `ζ` and which is continuously
isomorphic to `Gal(κ'/M)` for a **finite Galois** extension `M/κ` containing a primitive `p`-th root
of unity.  (Such an `M` is exactly what the local computation `NK.NUV2.LC.RouteB.card_open_local`
consumes.)

Construction: `H₁` = the `H`-core of `H ⊓ rootFix ζ ⊓ e⁻¹(Gal(κ'/κ(ζ'_p)))` for a primitive `p`-th
root `ζ'_p` of the separable closure of `κ`; it is open (the three factors are open in `H`) and
normal in `H`, and `e(H₁)` is an open normal subgroup of `Gal(κ'/κ)` whose fixed field `M` is finite
Galois over `κ` and contains `ζ'_p`. -/
theorem step0_open_normal (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) {K K' : Type} [Field K]
    [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K'] (ζ : K')
    (hζ : IsPrimitiveRoot ζ p) {L : Type} [Field L] [NumberField L]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (e : ↥H ≃ₜ* Gal(SeparableClosure (𝔮.adicCompletion L) / 𝔮.adicCompletion L)) :
    ∃ (H₁ : Subgroup Gal(K'/K))
      (M : FiniteGaloisIntermediateField (𝔮.adicCompletion L)
        (SeparableClosure (𝔮.adicCompletion L)))
      (e₁ : ↥H₁ ≃ₜ* ↥(M.fixingSubgroup)),
      H₁ ≤ H ∧ H ≤ Subgroup.normalizer H₁ ∧ 0 < H₁.relIndex H ∧
        H₁ ≤ NK.NUV2.LC.RouteB.rootFix (K := K) (K' := K') ζ ∧
        (∃ ζ' : ↥M, IsPrimitiveRoot ζ' p) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ξ, hξ⟩ : ∃ ξ : SeparableClosure (𝔮.adicCompletion L), IsPrimitiveRoot ξ p :=
    HasEnoughRootsOfUnity.exists_primitiveRoot (SeparableClosure (𝔮.adicCompletion L)) p
  exact step0_open_normal_aux (K := K) (K' := K') (κ := 𝔮.adicCompletion L)
    (κ' := SeparableClosure (𝔮.adicCompletion L)) p hp ζ hζ ξ hξ H hH e

end NK.NUV2.LC.RouteB
