import Mathlib
import Submission.NK.NUV2.LC.RouteB.Defs
import Submission.NK.NUV2.LC.RouteB.card_open_local
import Submission.NK.NUV2.LC.decompContinuousIso

/-!
# Route B: every place over a finite prime is live for a `μ_p`-open subgroup

The target `NK.NUV2.LC.RouteB.isLive_of_isMuOpen` says: for `p` an odd prime, `K` a number field
with separable closure `K'`, `ζ ∈ K'` a primitive `p`-th root of unity and `V ≤ Gal(K'/K)` a
`μ_p`-**open** subgroup (i.e. `V` is open and fixes `ζ`), the local cohomology `H²(V ⊓ D_A, Z/p)` is
non-trivial at **every** place `A` of `K'` over a finite prime of `K`; equivalently
`|H²(V ⊓ D_A, Z/p)| = p`.

## The mathematics

Let `F = K'^V` be the fixed field of `V`.  Since `V` is open, `F/K` is a finite extension — hence
`F` is a number field — and `ζ ∈ F` because `V` fixes `ζ`.

At a place `A` of `K'` over the finite prime `𝔭` of `K`, let `𝔮` be the prime of `F` below `A`.  The
completion `κ = 𝔮.adicCompletion F` is a `p`-adic field containing a primitive `p`-th root of unity
(namely the image of `ζ`), and the decomposition group of `A` in `Gal(K'/F)`

  `V ⊓ D_A = F.fixingSubgroup ⊓ D_A = {σ ∈ Gal(K'/F) : σ(A) = A}`

is the absolute Galois group of the local field `κ`: this is the *continuous* decomposition-group
identification `NK.NUV2.LC.decompContinuousIso` at the base field `F` (equivalently
`NK.Mine.localGaloisEquiv` plus a homeomorphism statement).  Local class field theory then gives

  `|H²(V ⊓ D_A, Z/p)| = |H²(G_κ, Z/p)| = |Br(κ)[p]| = p`,

the local Brauer group of a `p`-adic field being `ℚ/ℤ`; on disk this is
`NK.NUV2.LC.card_h2P_of_homeomorph` with `L = F`, `𝔮 = 𝔮` and `U = V ⊓ D_A`.

## What is proved here

The passage from the ambient subgroup `V ⊓ D_A ≤ Gal(K'/K)` to the local group
`M.fixingSubgroup ≤ Gal(κ̄/κ)` is the only structural input:

* `tsubEquiv`, `subgroupOfEquiv` — the elementary facts that a subgroup and its restriction to a
  larger subgroup are topologically isomorphic, and that restricting a topological group
  isomorphism to a subgroup preserves the topology;
* `smul_eq_of_coe_eq` — an `F`-linear and a `K`-linear automorphism of `K'` with the same underlying
  function act in the same way on the places of `K'`;
* `map_subgroupOf_inf_eq_stabilizer` — the transport of the stabiliser of a place along the Galois
  correspondence `↥F.fixingSubgroup ≃* Gal(K'/↥F)`;
* `nonempty_continuousMulEquiv_fixingSubgroup_inf_stabSubgroup` — **the topological isomorphism**
  `(F.fixingSubgroup ⊓ D_A) ≃ₜ* D_{A/↥F}` (the stabiliser of `A` in `Gal(K'/↥F)`), which combines
  the Galois correspondence (a homeomorphism by
  `NK.Reconstruct.isHomeomorph_fixingSubgroupEquiv`) with the two subgroup lemmas above.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Pointwise

namespace NK.NUV2.LC.RouteB

universe u

section Helpers

variable {K K' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- Restriction of a topological group isomorphism to a subgroup. -/
noncomputable def tsubEquiv {G H : Type*} [Group G] [TopologicalSpace G] [Group H]
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

/-- A subgroup and its restriction to a bigger one are topologically isomorphic. -/
noncomputable def subgroupOfEquiv {G : Type*} [Group G] [TopologicalSpace G]
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

/-- **The action on places of two automorphisms with the same underlying function.**  An `F`-linear
and a `K`-linear automorphism of `K'` (`K ≤ F ≤ K'`) which agree as functions act in the same way
on the valuation subrings of `K'`: membership in a `Pointwise`-translated valuation subring depends
on the automorphism only through its underlying function (indeed only through the function
`σ ↦ σ⁻¹ x`). -/
theorem smul_eq_of_coe_eq (F : IntermediateField K K') (A : ValuationSubring K')
    (σ : K' ≃ₐ[↥F] K') (τ : K' ≃ₐ[K] K') (h : ⇑σ = ⇑τ) : σ • A = τ • A := by
  apply ValuationSubring.ext
  intro x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, AlgEquiv.smul_def]
  have hx : (σ⁻¹) x = (τ⁻¹) x := by
    apply σ.injective
    rw [show σ ((τ⁻¹) x) = τ ((τ⁻¹) x) from congrFun h ((τ⁻¹) x)]
    simp
  rw [hx]

/-- **The fixing subgroup of a finite intermediate field intersected with the stabiliser of a place
is the stabiliser of that place in `Gal(K'/F)`.**  Along the Galois correspondence
`↥F.fixingSubgroup ≃* Gal(K'/↥F)` (the identity on underlying functions) the subgroup
`F.fixingSubgroup ⊓ D_A` corresponds to the decomposition group `D_{A/↥F}` of `A` for the extension
`K'/F`. -/
theorem map_subgroupOf_inf_eq_stabilizer (F : IntermediateField K K') [FiniteDimensional K F]
    (A : ValuationSubring K') :
    ((F.fixingSubgroup ⊓ NK.BrauerHasse.stabSubgroup A).subgroupOf F.fixingSubgroup).map
        ((IntermediateField.fixingSubgroupEquiv F : ↥F.fixingSubgroup ≃* (K' ≃ₐ[↥F] K')) :
          ↥F.fixingSubgroup →* (K' ≃ₐ[↥F] K'))
      = MulAction.stabilizer (K' ≃ₐ[↥F] K') A := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hy
    obtain ⟨-, hyA⟩ := hy
    rw [MulAction.mem_stabilizer_iff]
    rw [← hyx]
    exact (smul_eq_of_coe_eq F A _ _ rfl).trans hyA
  · intro hx
    rw [MulAction.mem_stabilizer_iff] at hx
    rw [Subgroup.mem_map]
    refine ⟨(IntermediateField.fixingSubgroupEquiv F).symm x, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      refine ⟨((IntermediateField.fixingSubgroupEquiv F).symm x).2, ?_⟩
      rw [MulAction.mem_stabilizer_iff]
      refine (smul_eq_of_coe_eq F A x
        ((((IntermediateField.fixingSubgroupEquiv F).symm x : ↥F.fixingSubgroup)) : K' ≃ₐ[K] K')
        (AlgEquiv.coe_restrictScalars K x).symm).symm.trans hx
    · simp

/-- **`(F.fixingSubgroup ⊓ D_A) ≃ₜ* D_{A/↥F}`.**  The decomposition group at `A` of the extension
`K'/F` is topologically isomorphic to the stabiliser of `A` inside `Gal(K'/↥F)`.

This is the Galois correspondence `↥F.fixingSubgroup ≃ₜ* Gal(K'/↥F)`
(`NK.Reconstruct.isHomeomorph_fixingSubgroupEquiv`, a homeomorphism for the Krull topologies)
restricted to the two subgroups encoding the stabilisation of `A`. -/
theorem nonempty_continuousMulEquiv_fixingSubgroup_inf_stabSubgroup
    (F : IntermediateField K K') [FiniteDimensional K F] (A : ValuationSubring K') :
    Nonempty (↥(F.fixingSubgroup ⊓ NK.BrauerHasse.stabSubgroup A) ≃ₜ*
      ↥(MulAction.stabilizer (K' ≃ₐ[↥F] K') A)) := by
  haveI : IsGalois K K' := IsSepClosure.isGalois
  let e : ↥F.fixingSubgroup ≃ₜ* (K' ≃ₐ[↥F] K') :=
    continuousMulEquivOfIsHomeomorph (IntermediateField.fixingSubgroupEquiv F)
      (NK.Reconstruct.isHomeomorph_fixingSubgroupEquiv (K := K) (Ω := K') F)
  have hcoe : (⇑e : ↥F.fixingSubgroup → (K' ≃ₐ[↥F] K'))
      = ⇑(IntermediateField.fixingSubgroupEquiv F) := rfl
  have hmap : (((F.fixingSubgroup ⊓ NK.BrauerHasse.stabSubgroup A).subgroupOf
        F.fixingSubgroup).map (e : ↥F.fixingSubgroup →* (K' ≃ₐ[↥F] K')))
      = MulAction.stabilizer (K' ≃ₐ[↥F] K') A := by
    rw [show (e : ↥F.fixingSubgroup →* (K' ≃ₐ[↥F] K'))
        = (IntermediateField.fixingSubgroupEquiv F) from MonoidHom.ext fun x => congrFun hcoe x]
    exact map_subgroupOf_inf_eq_stabilizer F A
  exact ⟨(subgroupOfEquiv F.fixingSubgroup (F.fixingSubgroup ⊓ NK.BrauerHasse.stabSubgroup A)
      inf_le_left).trans (hmap ▸ tsubEquiv e
        ((F.fixingSubgroup ⊓ NK.BrauerHasse.stabSubgroup A).subgroupOf F.fixingSubgroup))⟩

end Helpers

theorem isLive_of_isMuOpen (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) {K K' : Type} [Field K]
    [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K'] (ζ : K')
    (hζ : IsPrimitiveRoot ζ p) (V : Subgroup Gal(K'/K))
    (hV : IsMuOpen (K := K) (K' := K') ζ V) (A : NK.BrauerHasse.OverFinitePrime K K') :
    IsLive (K := K) (K' := K') p V A.1 := by
  classical
  obtain ⟨A₀, hA₀⟩ := A
  obtain ⟨hVopen, hVζ⟩ := hV
  -- the fixed field `F` of `V`, a number field since `V` is open
  let F : IntermediateField K K' := IntermediateField.fixedField V
  have hVcl : IsClosed (V : Set Gal(K'/K)) := Subgroup.isClosed_of_isOpen V hVopen
  have hFixF : F.fixingSubgroup = V :=
    InfiniteGalois.fixingSubgroup_fixedField (k := K) (K := K') ⟨V, hVcl⟩
  have hFfd : FiniteDimensional K F := by
    rw [← InfiniteGalois.isOpen_iff_finite (k := K) (K := K') F, hFixF]
    exact hVopen
  haveI : FiniteDimensional K F := hFfd
  haveI : NumberField ↥F := NumberField.of_module_finite K ↥F
  haveI : IsSepClosure ↥F K' := ⟨IsSepClosure.sep_closed K, inferInstance⟩
  -- `ζ` lies in `F`
  have hζF : ζ ∈ F := by
    rw [IntermediateField.mem_fixedField_iff]
    intro f hf
    exact (IntermediateField.mem_fixingSubgroup_iff _ f).mp (hVζ hf) ζ
      (IntermediateField.mem_adjoin_simple_self K ζ)
  -- the finite prime of `F` below `A`
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
  -- the continuous decomposition-group identification at the base field `F`
  obtain ⟨eD⟩ := NK.NUV2.LC.decompContinuousIso ↥F K' 𝔮 A₀ h𝔮
  -- the ambient decomposition group is the local one
  have hE : Nonempty (↥(V ⊓ NK.BrauerHasse.stabSubgroup A₀) ≃ₜ*
      ↥(MulAction.stabilizer (K' ≃ₐ[↥F] K') A₀)) :=
    hFixF ▸ nonempty_continuousMulEquiv_fixingSubgroup_inf_stabSubgroup F A₀
  -- a primitive `p`-th root of unity in the completion `κ = 𝔮.adicCompletion F`
  have hζ₀ : IsPrimitiveRoot (⟨ζ, hζF⟩ : ↥F) p :=
    IsPrimitiveRoot.of_map_of_injective (f := F.val) (by simpa using hζ)
      (fun a b h => Subtype.ext h)
  have hζroot : ∃ ζ' : 𝔮.adicCompletion ↥F, IsPrimitiveRoot ζ' p :=
    ⟨algebraMap ↥F (𝔮.adicCompletion ↥F) (⟨ζ, hζF⟩ : ↥F),
      IsPrimitiveRoot.map_of_injective (f := algebraMap ↥F (𝔮.adicCompletion ↥F)) hζ₀
        (Commons.NumberTheory.NumberField.Completion.injective_algebraMap_adicCompletion 𝔮)⟩
  -- the local Brauer cardinality `|H²(V ⊓ D_A, Z/p)| = p`
  have hcard : Nat.card (NK.BrauerHasse.H2Profinite (K := K) (K' := K') p
      (V ⊓ NK.BrauerHasse.stabSubgroup A₀)) = p := by
    rw [natCard_h2Profinite_of_homeomorph (k := K) (k' := K') (κ := ↥F) (κ' := K')
      (H := V ⊓ NK.BrauerHasse.stabSubgroup A₀)
      (J := MulAction.stabilizer (K' ≃ₐ[↥F] K') A₀) p hE.some]
    exact NK.NUV2.LC.card_h2P_of_homeomorph (K := ↥F) (K' := K') (L := ↥F) 𝔮 hp hζroot _
      (Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring A₀) eD
  -- extract a non-zero class
  haveI : Finite (NK.BrauerHasse.H2Profinite (K := K) (K' := K') p
      (V ⊓ NK.BrauerHasse.stabSubgroup A₀)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  haveI : Fintype (NK.BrauerHasse.H2Profinite (K := K) (K' := K') p
      (V ⊓ NK.BrauerHasse.stabSubgroup A₀)) := Fintype.ofFinite _
  have h1 : 1 < Fintype.card (NK.BrauerHasse.H2Profinite (K := K) (K' := K') p
      (V ⊓ NK.BrauerHasse.stabSubgroup A₀)) := by
    rw [← Nat.card_eq_fintype_card, hcard]; exact hp.one_lt
  obtain ⟨a⟩ := Fintype.card_pos_iff.mp (lt_trans Nat.zero_lt_one h1)
  obtain ⟨y, hy⟩ := Fintype.exists_ne_of_one_lt_card h1 a
  by_cases ha : a = 0
  · exact ⟨y, fun hy0 => hy (hy0.trans ha.symm)⟩
  · exact ⟨a, ha⟩

end NK.NUV2.LC.RouteB
