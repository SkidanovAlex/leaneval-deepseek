/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFTdeep.Herbrand.FiberUnitsLocal
import Submission.NK.GlobalCFTdeep.Herbrand.UnitIdelesDefs
import Submission.NK.GlobalCFTdeep.Herbrand.fiberIdelesRep_iso_coind

/-!
# Shapiro's lemma for the local units of a fibre

For a finite place `q` of `L` with decomposition group `D_q` and a place `v` of `K` under it, the
*unit part of the fibre of `v`* — the idèles supported on the places above `v` all of whose
components are local units, i.e. `∏_{w' | v} 𝒪_{w'}ˣ` — is the coinduced module
`Coind_{D_q}^{G} 𝒪_qˣ` of the local units at `q` (`NK.GlobalCFTdeep.fiberUnitsRep`,
`NK.GlobalCFTdeep.localUnitSubRep`).

The isomorphism is the Shapiro isomorphism of `NK.GlobalCFTdeep.fiberIdelesRep_iso_coind`
restricted to the unit parts: the forward map is the adjunction transpose of the coordinate at `q`
(`fiberUnitsToCoind`), which is injective because the coordinate map on the full fibre
`fiberToCoind` is, and surjective because the preimage of a coind element with unit values
produced by `fiberToCoind_surjective` has local-unit components (its components are the values of
the coind element, transported by local isomorphisms preserving `𝒪ˣ`).

Together with `NK.GlobalCFTdeep.Herbrand.herbrandEq_coind_iff` this reduces the Herbrand
quotient of `∏_{w' | v} 𝒪_{w'}ˣ` to the local computation at `q`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain
open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ## Invariance of the local units under the transported local isomorphism -/

theorem units_map_map_symm {A B : Type*} [Monoid A] [Monoid B] (f : A ≃* B) (u : Bˣ) :
    Units.map f.toMonoidHom (Units.map f.symm.toMonoidHom u) = u := by
  ext
  simp

/-- **Membership in the local units is transported by the local isomorphism**: an element of
`L_{σ·w}ˣ` is a local unit at `σ · w` if and only if its image under `(localRingEquiv σ w)⁻¹` is a
local unit at `w`. -/
theorem mem_localUnits_map_symm_iff (σ : L ≃ₐ[K] L) (w : Place L)
    (u : (Place.localField L (σ • w))ˣ) :
    Units.map (Place.localRingEquiv σ w).symm.toMonoidHom u ∈ Place.localUnits L w ↔
      u ∈ Place.localUnits L (σ • w) := by
  rw [Place.localRingEquiv_mem_localUnits (σ := σ) (v := w)
    (u := Units.map (Place.localRingEquiv σ w).symm.toMonoidHom u)]
  rw [show Units.map (Place.localRingEquiv σ w).toMonoidHom
      (Units.map (Place.localRingEquiv σ w).symm.toMonoidHom u) = u from
    units_map_map_symm (Place.localRingEquiv σ w).toMulEquiv u]

/-! ## The coordinate at `w` of an idèle of the unit part of a fibre -/

/-- The `w`-component of an idèle of the unit part of the fibre of `v`, as a monoid
homomorphism. -/
def fiberUnitsEvalHom (v : Place K) (w : Place L) :
    ↥(fiberUnits (K := K) (L := L) v) →* ↥(Place.localUnits L w) where
  toFun x := ⟨(x : Idele L) w, (mem_fiberUnits.mp x.2).2 w⟩
  map_one' := Subtype.ext (Idele.one_apply w)
  map_mul' x y := Subtype.ext (Idele.mul_apply (x : Idele L) (y : Idele L) w)

@[simp] theorem fiberUnitsEvalHom_apply (v : Place K) (w : Place L)
    (x : ↥(fiberUnits (K := K) (L := L) v)) :
    (fiberUnitsEvalHom (K := K) (L := L) v w x : (Place.localField L w)ˣ) =
      (x : Idele L) w := rfl

/-- **The coordinate at `w` of an idèle of the unit part of the fibre**, as a morphism of
`ℤ[D_w]`-modules. -/
noncomputable def fiberUnitsCoord (v : Place K) (w : Place L) :
    Rep.res (decompositionSubgroup (K := K) (L := L) w).subtype
        (fiberUnitsRep (K := K) (L := L) v) ⟶ localUnitSubRep (K := K) (L := L) w :=
  Rep.ofHom
    { toFun := ⇑(fiberUnitsEvalHom (K := K) (L := L) v w).toAdditive
      map_add' := map_add _
      map_smul' := fun n x => map_zsmul _ n x
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro x
        apply congrArg Additive.ofMul
        apply Subtype.ext
        show (σ.1 • ((Additive.toMul x : ↥(fiberUnits (K := K) (L := L) v)) : Idele L)) w
          = Units.map (NK.GlobalCFT.Inclusion.Place.localAction σ.1 w σ.2).toMonoidHom
              (((Additive.toMul x : ↥(fiberUnits (K := K) (L := L) v)) : Idele L) w)
        exact smul_apply_decomposition w σ
          ((Additive.toMul x : ↥(fiberUnits (K := K) (L := L) v)) : Idele L) }

/-- **The Shapiro map `∏_{w' | v} 𝒪_{w'}ˣ ⟶ Coind_{D_w}^{G} 𝒪_wˣ`** for the unit part of the
fibre, the adjunction transpose of the coordinate at `w`. -/
noncomputable def fiberUnitsToCoind (v : Place K) (w : Place L) :
    fiberUnitsRep (K := K) (L := L) v ⟶
      Rep.coind (decompositionSubgroup (K := K) (L := L) w).subtype
        (localUnitSubRep (K := K) (L := L) w) :=
  Rep.resCoindToHom _ _ _ (fiberUnitsCoord (K := K) (L := L) v w)

/-- The value of the Shapiro map at `γ`, as an element of the local units at `w`. -/
theorem fiberUnitsToCoind_apply (v : Place K) (w : Place L)
    (x : (fiberUnitsRep (K := K) (L := L) v).V) (γ : L ≃ₐ[K] L) :
    ((fiberUnitsToCoind (K := K) (L := L) v w).hom x).1 γ =
      Additive.ofMul (fiberUnitsEvalHom (K := K) (L := L) v w
        ⟨γ • ((Additive.toMul x : ↥(fiberUnits (K := K) (L := L) v)) : Idele L),
          smul_mem_fiberUnits (Additive.toMul x).2⟩) := by
  rw [fiberUnitsToCoind, Rep.resCoindToHom_hom_apply_coe]
  rfl

/-- The value of the Shapiro map at `γ`, as an element of `L_wˣ`. -/
theorem coe_fiberUnitsToCoind_apply (v : Place K) (w : Place L)
    (x : (fiberUnitsRep (K := K) (L := L) v).V) (γ : L ≃ₐ[K] L) :
    (((fiberUnitsToCoind (K := K) (L := L) v w).hom x).1 γ).toMul.1 =
      (γ • ((Additive.toMul x : ↥(fiberUnits (K := K) (L := L) v)) : Idele L)) w := by
  rw [fiberUnitsToCoind_apply]
  rfl

/-! ## Injectivity and surjectivity of the Shapiro map -/

/-- **The Shapiro map for the unit part of the fibre is injective.** -/
theorem fiberUnitsToCoind_injective (v : Place K) (w : Place L) (hw : Place.LiesOver w v) :
    Function.Injective (fiberUnitsToCoind (K := K) (L := L) v w).hom := by
  intro x y h
  have hsm : ∀ γ : L ≃ₐ[K] L,
      (γ • ((Additive.toMul x : ↥(fiberUnits (K := K) (L := L) v)) : Idele L)) w =
        (γ • ((Additive.toMul y : ↥(fiberUnits (K := K) (L := L) v)) : Idele L)) w := by
    intro γ
    have h2 : ((fiberUnitsToCoind (K := K) (L := L) v w).hom x).1 γ =
        ((fiberUnitsToCoind (K := K) (L := L) v w).hom y).1 γ :=
      congrFun (congrArg Subtype.val h) γ
    have h3 := congrArg (fun z => (Additive.toMul z).1) h2
    rwa [coe_fiberUnitsToCoind_apply, coe_fiberUnitsToCoind_apply] at h3
  have hxy : ((Additive.toMul x : ↥(fiberUnits (K := K) (L := L) v)) : Idele L) =
      ((Additive.toMul y : ↥(fiberUnits (K := K) (L := L) v)) : Idele L) := by
    refine Idele.ext fun u => ?_
    by_cases hu : Place.LiesOver u v
    · obtain ⟨σ, hσ⟩ :=
        NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver hw hu
      exact NK.HassePrinciple.eq_of_smul_apply_eq (w := w) hsm (v := u) (γ := σ⁻¹)
        (by rw [inv_inv, hσ])
    · rw [show ((Additive.toMul x : ↥(fiberUnits (K := K) (L := L) v)) : Idele L) u = 1 from
            (mem_fiberUnits.mp (Additive.toMul x).2).1 u hu,
          show ((Additive.toMul y : ↥(fiberUnits (K := K) (L := L) v)) : Idele L) u = 1 from
            (mem_fiberUnits.mp (Additive.toMul y).2).1 u hu]
  exact Additive.toMul.injective (Subtype.ext hxy)

/-- **The Shapiro map for the unit part of the fibre at a finite place is surjective.** -/
theorem fiberUnitsToCoind_surjective (v : Place K) (q : HeightOneSpectrum (𝓞 L))
    (hw : Place.LiesOver (Place.ofFinite q) v) :
    Function.Surjective (fiberUnitsToCoind (K := K) (L := L) v (Place.ofFinite q)).hom := by
  intro f
  let g : localUnitSubRep (K := K) (L := L) (Place.ofFinite q) ⟶
      localUnitsRep (K := K) (L := L) (Place.ofFinite q) := localUnitIncl (K := K) q
  let f' : (Rep.coind (decompositionSubgroup (K := K) (L := L) (Place.ofFinite q)).subtype
      (localUnitsRep (K := K) (L := L) (Place.ofFinite q))).V :=
    (Rep.coindMap (decompositionSubgroup (K := K) (L := L) (Place.ofFinite q)).subtype g).hom f
  obtain ⟨x, hx⟩ := fiberToCoind_surjective (K := K) (L := L) v (Place.ofFinite q) hw f'
  have hval : ∀ γ : L ≃ₐ[K] L,
      (γ • fiberToIdele (K := K) (L := L) v x) (Place.ofFinite q) =
        ((f.1 γ).toMul).1 := by
    intro γ
    have h2 : ((fiberToCoind (K := K) (L := L) v (Place.ofFinite q)).hom x).1 γ = f'.1 γ :=
      congrFun (congrArg Subtype.val hx) γ
    rw [fiberToCoind_apply] at h2
    have h3 : f'.1 γ = Additive.ofMul (((f.1 γ).toMul).1) := rfl
    rw [h3] at h2
    exact Additive.ofMul.injective h2
  have hunits : ∀ u : Place L,
      fiberToIdele (K := K) (L := L) v x u ∈ Place.localUnits L u := by
    intro u
    by_cases hu : Place.LiesOver u v
    · obtain ⟨τ, hτ⟩ :=
        NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver hw hu
      have h1 : (τ⁻¹ • fiberToIdele (K := K) (L := L) v x) (Place.ofFinite q) ∈
          Place.localUnits L (Place.ofFinite q) := by
        rw [hval τ⁻¹]
        exact (f.1 τ⁻¹).toMul.2
      rw [Idele.smul_apply] at h1
      rw [← hτ]
      exact (mem_localUnits_map_symm_iff τ (Place.ofFinite q)
        (fiberToIdele (K := K) (L := L) v x (τ • Place.ofFinite q))).1 h1
    · rw [(mem_fiberIdeles.mp (fiberToIdele_mem (K := K) (L := L) v x)) u hu]
      exact Subgroup.one_mem _
  have hmem : fiberToIdele (K := K) (L := L) v x ∈ fiberUnits (K := K) (L := L) v :=
    mem_fiberUnits.mpr
      ⟨fun u hu => (mem_fiberIdeles.mp (fiberToIdele_mem (K := K) (L := L) v x)) u hu, hunits⟩
  refine ⟨Additive.ofMul (α := ↥(fiberUnits (K := K) (L := L) v))
    ⟨fiberToIdele (K := K) (L := L) v x, hmem⟩, ?_⟩
  apply Subtype.ext
  funext γ
  apply Additive.ofMul.injective
  apply Subtype.ext
  exact (coe_fiberUnitsToCoind_apply (K := K) (L := L) v (Place.ofFinite q)
    (Additive.ofMul (α := ↥(fiberUnits (K := K) (L := L) v))
      ⟨fiberToIdele (K := K) (L := L) v x, hmem⟩) γ).trans (hval γ)

/-! ## The isomorphism -/

/-- **Shapiro's lemma for the local units of a fibre**: for a finite place `q` of `L` and a place
`v` of `K` under it, the unit part of the fibre `∏_{w' | v} 𝒪_{w'}ˣ` is the coinduced module
`Coind_{D_q}^{G} 𝒪_qˣ`. -/
theorem fiberUnitsRep_iso_coind (v : Place K) (q : HeightOneSpectrum (𝓞 L))
    (hw : Place.LiesOver (Place.ofFinite q) v) :
    Nonempty (fiberUnitsRep (K := K) (L := L) v ≅
      Rep.coind (decompositionSubgroup (K := K) (L := L) (Place.ofFinite q)).subtype
        (localUnitSubRep (K := K) (L := L) (Place.ofFinite q))) := by
  have hbij : Function.Bijective
      (fiberUnitsToCoind (K := K) (L := L) v (Place.ofFinite q)).hom :=
    ⟨fiberUnitsToCoind_injective v (Place.ofFinite q) hw,
      fiberUnitsToCoind_surjective v q hw⟩
  let e : (fiberUnitsRep (K := K) (L := L) v).V ≃ₗ[ℤ]
      (Rep.coind (decompositionSubgroup (K := K) (L := L) (Place.ofFinite q)).subtype
        (localUnitSubRep (K := K) (L := L) (Place.ofFinite q))).V :=
    LinearEquiv.ofBijective (fiberUnitsToCoind (K := K) (L := L) v (Place.ofFinite q)).hom hbij
  exact ⟨Rep.mkIso (Representation.Equiv.mk e
    (fun γ => (fiberUnitsToCoind (K := K) (L := L) v (Place.ofFinite q)).hom.isIntertwining' γ))⟩

end NK.GlobalCFTdeep
