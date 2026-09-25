import Mathlib
import Submission.NK.NUV2.LC.RouteB.Defs
import Submission.NK.NUV2.LC.RouteB.step0_open_normal

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Topology Pointwise

namespace NK.NUV2.LC.RouteB

/-- **Route B, Step 0 refined: the open normal subgroup of local type is `H ⊓ N₀` for an open
`N₀`, hence closed in `Gal(K'/K)`.**

Same hypotheses and conclusion as `NK.NUV2.LC.RouteB.step0_open_normal`, with the *finite index*
clause replaced by the stronger description `H₁ = H ⊓ N₀` with `N₀` open.  Consequently `H₁` is
closed in `Gal(K'/K)` (intersection of the closed `H` with the closed `N₀`), which is what the
closed-subgroup lemmas of the final argument (`Claim U`, `live_places_one_orbit`) need; the plain
finite-index form does not give it (finite index in a closed subgroup does not imply closed —
Nikolov–Segal).

Proof: `H₁` is the `H`-core of the open-in-`H` subgroup
`H ⊓ rootFix ζ ⊓ e⁻¹(Gal(κ'/κ(ζ'_p)))`; take an open normal `V ≤ Gal(K'/K)` with `V ⊓ H ≤ H₁`
(fixing subgroups of finite Galois levels form a basis of the open normal subgroups) and put
`N₀ := V · H₁`; then `V` normal makes `N₀` a subgroup, it is open, and `H ⊓ N₀ = H₁`. -/
theorem step0_inf_open (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) {K K' : Type} [Field K]
    [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K'] (ζ : K')
    (hζ : IsPrimitiveRoot ζ p) {L : Type} [Field L] [NumberField L]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (e : ↥H ≃ₜ* Gal(SeparableClosure (𝔮.adicCompletion L) / 𝔮.adicCompletion L)) :
    ∃ (H₁ N₀ : Subgroup Gal(K'/K))
      (M : FiniteGaloisIntermediateField (𝔮.adicCompletion L)
        (SeparableClosure (𝔮.adicCompletion L)))
      (e₁ : ↥H₁ ≃ₜ* ↥(M.fixingSubgroup)),
      H₁ ≤ H ∧ H ≤ Subgroup.normalizer H₁ ∧ IsOpen (N₀ : Set Gal(K'/K)) ∧ H₁ = H ⊓ N₀ ∧
        H₁ ≤ NK.NUV2.LC.RouteB.rootFix (K := K) (K' := K') ζ ∧
        (∃ ζ' : ↥M, IsPrimitiveRoot ζ' p) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ξ, hξ⟩ : ∃ ξ : SeparableClosure (𝔮.adicCompletion L), IsPrimitiveRoot ξ p :=
    HasEnoughRootsOfUnity.exists_primitiveRoot (SeparableClosure (𝔮.adicCompletion L)) p
  -- ## `ζ` is integral over `K`, so `rootFix ζ` is open
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
  -- ## the local field side: `ξ` is integral over `κ`, so `Gal(κ'/κ(ξ))` is open
  have hξint : IsIntegral (𝔮.adicCompletion L) ξ :=
    ⟨Polynomial.X ^ p - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hp.pos.ne',
      by simp [hξ.pow_eq_one]⟩
  haveI hJfd : FiniteDimensional (𝔮.adicCompletion L)
      ↥(IntermediateField.adjoin (𝔮.adicCompletion L) ({ξ} : Set
        (SeparableClosure (𝔮.adicCompletion L)))) :=
    IntermediateField.finiteDimensional_adjoin (S := ({ξ} : Set
        (SeparableClosure (𝔮.adicCompletion L)))) fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hξint
  let J : Subgroup Gal(SeparableClosure (𝔮.adicCompletion L) / 𝔮.adicCompletion L) :=
    (IntermediateField.adjoin (𝔮.adicCompletion L) ({ξ} : Set
      (SeparableClosure (𝔮.adicCompletion L)))).fixingSubgroup
  have hJ_open : IsOpen (J : Set Gal(SeparableClosure (𝔮.adicCompletion L) /
      𝔮.adicCompletion L)) := by
    show IsOpen ((IntermediateField.adjoin (𝔮.adicCompletion L) ({ξ} : Set
      (SeparableClosure (𝔮.adicCompletion L)))).fixingSubgroup : Set
        Gal(SeparableClosure (𝔮.adicCompletion L) / 𝔮.adicCompletion L))
    exact IntermediateField.fixingSubgroup_isOpen _
  -- ## the open-in-`H` subgroup `Vh` whose `H`-core is `H₁`
  let Vh : Subgroup ↥H := (rootFix (K := K) (K' := K') ζ).subgroupOf H ⊓
    J.comap (e : ↥H →* Gal(SeparableClosure (𝔮.adicCompletion L) / 𝔮.adicCompletion L))
  have hrootFixH_open : IsOpen
      (((rootFix (K := K) (K' := K') ζ).subgroupOf H : Subgroup ↥H) : Set ↥H) := by
    rw [← Subgroup.comap_subtype (K := H) (H := rootFix (K := K) (K' := K') ζ),
      Subgroup.coe_comap]
    exact hrootFix_open.preimage continuous_subtype_val
  have hJH_open : IsOpen ((J.comap (e : ↥H →*
      Gal(SeparableClosure (𝔮.adicCompletion L) / 𝔮.adicCompletion L)) : Subgroup ↥H) :
      Set ↥H) := by
    rw [Subgroup.coe_comap]
    exact hJ_open.preimage e.continuous_toFun
  have hVh_open : IsOpen (Vh : Set ↥H) := by
    show IsOpen ((((rootFix (K := K) (K' := K') ζ).subgroupOf H : Subgroup ↥H) : Set ↥H)
      ∩ ((J.comap (e : ↥H →* Gal(SeparableClosure (𝔮.adicCompletion L) /
          𝔮.adicCompletion L)) : Subgroup ↥H) : Set ↥H))
    exact hrootFixH_open.inter hJH_open
  -- ## an open normal subgroup `U ≤ Gal(K'/K)` with `U ⊓ H ≤ Vh`
  -- (open normal subgroups of the profinite group `Gal(K'/K)` form a neighbourhood basis of `1`)
  obtain ⟨W, hWopen, hWpre⟩ := isOpen_induced_iff.mp hVh_open
  have h1W : (1 : Gal(K'/K)) ∈ W := by
    have hmem : (1 : ↥H) ∈ (Subtype.val ⁻¹' W : Set ↥H) := by
      rw [hWpre]; exact Vh.one_mem
    simpa using hmem
  obtain ⟨L', hL'sub⟩ := (InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois
    (k := K) (K := K') W).mp (IsOpen.mem_nhds hWopen h1W)
  let U : Subgroup Gal(K'/K) := (L' : IntermediateField K K').fixingSubgroup
  have hU_open : IsOpen (U : Set Gal(K'/K)) :=
    IntermediateField.fixingSubgroup_isOpen (L' : IntermediateField K K')
  have hU_normal : U.Normal := inferInstance
  have hU_le_W : U ≤ W := hL'sub
  have hU_sub : U.subgroupOf H ≤ Vh := by
    intro x hx
    have hxW : (x : Gal(K'/K)) ∈ W := hU_le_W (Subgroup.mem_subgroupOf.mp hx)
    have hmem : x ∈ (Subtype.val ⁻¹' W : Set ↥H) := hxW
    rwa [hWpre] at hmem
  -- ## the answer
  let H₁ : Subgroup Gal(K'/K) := H ⊓ U
  let C : Subgroup ↥H := H₁.subgroupOf H
  let E : Subgroup Gal(SeparableClosure (𝔮.adicCompletion L) / 𝔮.adicCompletion L) :=
    C.map (e : ↥H →* Gal(SeparableClosure (𝔮.adicCompletion L) / 𝔮.adicCompletion L))
  have hC_eq : C = U.subgroupOf H := Subgroup.inf_subgroupOf_left U H
  have hC_le_Vh : C ≤ Vh := by rw [hC_eq]; exact hU_sub
  have hC_le_J : C ≤ J.comap (e : ↥H →* Gal(SeparableClosure (𝔮.adicCompletion L) /
      𝔮.adicCompletion L)) := le_trans hC_le_Vh inf_le_right
  have hE_le_J : E ≤ J := Subgroup.map_le_iff_le_comap.mpr hC_le_J
  have hC_open : IsOpen (C : Set ↥H) := by
    rw [hC_eq, ← Subgroup.comap_subtype (K := H) (H := U), Subgroup.coe_comap]
    exact hU_open.preimage continuous_subtype_val
  have hC_normal : C.Normal := by
    rw [hC_eq]
    exact hU_normal.subgroupOf H
  have hE_open : IsOpen (E : Set Gal(SeparableClosure (𝔮.adicCompletion L) /
      𝔮.adicCompletion L)) := by
    rw [Subgroup.coe_map]
    exact Homeomorph.isOpenMap e.toHomeomorph _ hC_open
  have hE_normal : E.Normal :=
    Subgroup.Normal.map hC_normal (e : ↥H →*
      Gal(SeparableClosure (𝔮.adicCompletion L) / 𝔮.adicCompletion L)) e.surjective
  have hE_closed : IsClosed (E : Set Gal(SeparableClosure (𝔮.adicCompletion L) /
      𝔮.adicCompletion L)) := Subgroup.isClosed_of_isOpen E hE_open
  let M : FiniteGaloisIntermediateField (𝔮.adicCompletion L)
      (SeparableClosure (𝔮.adicCompletion L)) :=
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
  let e₁ : ↥H₁ ≃ₜ* ↥(M.fixingSubgroup) :=
    (subgroupOfCME H H₁ inf_le_left).trans
      ((subgroupMapCME e C).trans (subgroupCongrCME hMfix.symm))
  refine ⟨H₁, U, M, e₁, inf_le_left, ?_, hU_open, rfl, ?_, ?_⟩
  · -- `H ≤ normalizer H₁`
    rw [← Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    exact hC_normal
  · -- `H₁ ≤ rootFix ζ`
    intro x hx
    have hmem : (⟨x, hx.1⟩ : ↥H) ∈ Vh :=
      hU_sub (by rw [Subgroup.mem_subgroupOf]; exact hx.2)
    have hmem2 : (⟨x, hx.1⟩ : ↥H) ∈ (rootFix (K := K) (K' := K') ζ).subgroupOf H :=
      (Subgroup.mem_inf.mp hmem).1
    rwa [Subgroup.mem_subgroupOf] at hmem2
  · -- a primitive `p`-th root of unity in `M`
    have hξmem : ξ ∈ (M : IntermediateField (𝔮.adicCompletion L)
        (SeparableClosure (𝔮.adicCompletion L))) := by
      have h1 : ξ ∈ IntermediateField.adjoin (𝔮.adicCompletion L) ({ξ} : Set
          (SeparableClosure (𝔮.adicCompletion L))) :=
        IntermediateField.subset_adjoin _ _ (Set.mem_singleton ξ)
      have h2 : (IntermediateField.adjoin (𝔮.adicCompletion L) ({ξ} : Set
          (SeparableClosure (𝔮.adicCompletion L)))) ≤ (M : IntermediateField
            (𝔮.adicCompletion L) (SeparableClosure (𝔮.adicCompletion L))) := by
        rw [← InfiniteGalois.fixedField_fixingSubgroup
          (L := IntermediateField.adjoin (𝔮.adicCompletion L) ({ξ} : Set
            (SeparableClosure (𝔮.adicCompletion L))))]
        exact IntermediateField.fixedField_le hE_le_J
      exact h2 h1
    exact ⟨⟨ξ, hξmem⟩, IsPrimitiveRoot.coe_submonoidClass_iff.mp hξ⟩

end NK.NUV2.LC.RouteB
