import Mathlib
import Submission.NK.HassePrinciple.IdeleLevel

namespace NK.HassePrinciple

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false

open CategoryTheory Representation
open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **Stabilising a finite set of places.**  For a finite set `T` of places of `L`, the set
`{v | σ • v ∈ T for some σ ∈ Gal(L/K)}` is a finite `Gal(L/K)`-stable set of places containing
`T`. -/
theorem exists_gstable_finite_superset (T : Set (Place L)) (hT : T.Finite) :
    ∃ S : GStableSet K L, S.carrier.Finite ∧ T ⊆ S.carrier := by
  classical
  refine ⟨⟨{v | ∃ σ : L ≃ₐ[K] L, σ • v ∈ T}, ?_⟩, ?_, ?_⟩
  · intro σ v h
    obtain ⟨τ, hτ⟩ := h
    refine ⟨τ * σ⁻¹, ?_⟩
    rw [mul_smul, inv_smul_smul]
    exact hτ
  · have h : {v : Place L | ∃ σ : L ≃ₐ[K] L, σ • v ∈ T} ⊆
        ⋃ σ : L ≃ₐ[K] L, (fun u => σ⁻¹ • u) '' T := by
      intro v hv
      obtain ⟨σ, hσ⟩ := hv
      refine Set.mem_iUnion.mpr ⟨σ, σ • v, hσ, ?_⟩
      exact inv_smul_smul σ v
    exact Set.Finite.subset (Set.finite_iUnion fun σ => hT.image _) h
  · intro v hv
    exact ⟨1, by simpa using hv⟩

/-- **Every `2`-cocycle of `𝕀_L` lands in some finite level `𝕀_L^S`.**  For a `2`-cocycle `z` with
values in the idèles, the union of the (finite) sets of places at which the finitely many values
`z p` are not local units is finite, and the finitely many `Gal(L/K)`-translates of a finite set of
places are finite because `Gal(L/K)` is finite; stabilising this finite set gives a finite
`Gal(L/K)`-stable set `S` with `z` factoring through the inclusion `𝕀_L^S ⟶ 𝕀_L`. -/
theorem exists_level_cocycle (z : groupCohomology.cocycles₂ (ideleRep K L)) :
    ∃ (S : GStableSet K L), S.carrier.Finite ∧
      ∃ z_S : groupCohomology.cocycles₂ (levelRep K L S),
        groupCohomology.mapCocycles₂ (MonoidHom.id (L ≃ₐ[K] L)) (levelIncl K L S) z_S = z := by
  classical
  let x : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Idele L := fun p => Additive.toMul (z p)
  have hbad : (⋃ p : (L ≃ₐ[K] L) × (L ≃ₐ[K] L),
      {v : Place L | x p v ∉ Place.localUnits L v}).Finite := by
    refine Set.finite_iUnion fun p => ?_
    exact Filter.eventually_cofinite.mp (x p).2
  obtain ⟨S, hSfin, hSsub⟩ := exists_gstable_finite_superset (K := K) (L := L) _ hbad
  have hmem : ∀ p, x p ∈ levelSubgroup S.carrier := by
    intro p
    rw [mem_levelSubgroup]
    intro v hv
    by_contra h
    exact hv (hSsub (Set.mem_iUnion.mpr ⟨p, h⟩))
  let F : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Additive ↥(levelSubgroup S.carrier) :=
    fun p => Additive.ofMul ⟨x p, hmem p⟩
  have hF : ∀ p, (levelIncl K L S).hom (F p) = z p := fun p => rfl
  have hc : F ∈ groupCohomology.cocycles₂ (levelRep K L S) := by
    have hinj : Function.Injective (levelIncl K L S).hom := by
      intro a b hab
      have h : Additive.ofMul ((Additive.toMul a : ↥(levelSubgroup S.carrier)) : Idele L)
          = Additive.ofMul ((Additive.toMul b : ↥(levelSubgroup S.carrier)) : Idele L) := hab
      exact Additive.toMul.injective (Subtype.ext (Additive.ofMul.injective h))
    refine (groupCohomology.mem_cocycles₂_def (A := levelRep K L S) F).mpr fun g h j => ?_
    apply hinj
    rw [map_sub, map_add, map_sub, map_zero, Rep.hom_comm_apply, hF, hF, hF, hF]
    exact (groupCohomology.mem_cocycles₂_def (A := ideleRep K L) ⇑z).mp z.2 g h j
  refine ⟨S, hSfin, ⟨F, hc⟩, ?_⟩
  apply groupCohomology.cocycles₂_ext
  intro g h
  rw [groupCohomology.coe_mapCocycles₂]
  show (levelIncl K L S).hom (F (g, h)) = z (g, h)
  exact hF (g, h)

/-- **The finite-level reduction of `H²(Gal(L/K), 𝕀_L)`.**

Let `Γ = Gal(L/K)`.  The idèle group `𝕀_L` is the filtered union of its `Γ`-stable subgroups
`𝕀_L^S = {x : x_v ∈ 𝒪_vˣ for all v ∉ S}` over the finite `Γ`-stable sets `S` of places
(`NK.HassePrinciple.levelRep K L S`, with inclusion `NK.HassePrinciple.levelIncl K L S`).

The claim: every class of `H²(Γ, 𝕀_L)` (`ideleRep K L`) is in the image of `H²(Γ, 𝕀_L^S)` for some
finite `Γ`-stable `S`.

Proof sketch: represent the class by an inhomogeneous `2`-cocycle `c : Γ × Γ → 𝕀_L`, and let `S` be
the union, over the finitely many pairs `(g, h)`, of the finite sets of places at which `c g h` is
not a local unit, saturated under `Γ` (using `Filter.eventually_cofinite`).  Then all the values of
`c` lie in `𝕀_L^S`, so `c` is a cocycle with values in `𝕀_L^S`, and its class maps to the class of
`a`.  The relevant low-degree API is `groupCohomology.H2π` surjectivity together with
`groupCohomology.mapCocycles₂` / `coe_mapCocycles₂`. -/
theorem exists_level_of_h2 {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (a : groupCohomology (NK.HassePrinciple.ideleRep K L) 2) :
    ∃ (S : NK.HassePrinciple.GStableSet K L), S.carrier.Finite ∧
      ∃ a_S : groupCohomology (NK.HassePrinciple.levelRep K L S) 2,
        ((groupCohomology.functor NK.HassePrinciple.CoeffInt (L ≃ₐ[K] L) 2).map
          (NK.HassePrinciple.levelIncl K L S)).hom a_S = a := by
  obtain ⟨z, hz⟩ :=
    (ModuleCat.epi_iff_surjective (groupCohomology.H2π (ideleRep K L))).1 inferInstance a
  obtain ⟨S, hSfin, z_S, hzS⟩ := exists_level_cocycle z
  refine ⟨S, hSfin, groupCohomology.H2π (levelRep K L S) z_S, ?_⟩
  rw [← hz]
  show (groupCohomology.map (MonoidHom.id (L ≃ₐ[K] L)) (levelIncl K L S) 2)
      ((groupCohomology.H2π (levelRep K L S)) z_S) = (groupCohomology.H2π (ideleRep K L)) z
  rw [groupCohomology.H2π_comp_map_apply (MonoidHom.id (L ≃ₐ[K] L)) (levelIncl K L S) z_S, hzS]

end NK.HassePrinciple
