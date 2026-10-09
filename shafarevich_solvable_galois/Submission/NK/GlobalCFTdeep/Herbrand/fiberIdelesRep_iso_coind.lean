/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFTdeep.Herbrand.LocalUnits
import Submission.NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver
import Submission.NK.HassePrinciple.OrbitCoindSection
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Shapiro's lemma for the fibre of the idèles

For a finite Galois extension `L/K` of number fields, a place `v` of `K` and a place `w` of `L`
over `v`, the idèles supported on the places above `v` — the fibre `∏_{w' | v} L_{w'}ˣ` — form
the coinduced module `Coind_{D_w}^{G} L_wˣ` of the decomposition group `D_w`.

The isomorphism is the Shapiro isomorphism.  Its forward map `fiberToCoind` is the adjunction
transpose (`Rep.resCoindToHom`) of the evaluation at `w`, i.e. `x ↦ (γ ↦ (γ · x)_w)`.  Its
inverse is Milne's section, which is taken from
`NK.HassePrinciple.OrbitCoindSection`: for each place `w'` above `v` one chooses a Galois
element `γ` with `γ • w = w'`.  The two `ℤ`-representations
`NK.HassePrinciple.localUnitsRep` and `NK.GlobalCFTdeep.localUnitsRep` differ only in the
bookkeeping of the `ULift ℤ`-coefficients and their underlying actions agree.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ## The local action and the two local-unit representations -/

/-- The local action of a stabiliser element of a place is `NK.HassePrinciple.localAut`. -/
theorem localAction_eq_localAut (w : Place L) (σ : L ≃ₐ[K] L) (h : σ • w = w) :
    NK.GlobalCFT.Inclusion.Place.localAction σ w h =
      NK.HassePrinciple.localAut (K := K) w ⟨σ, h⟩ := by
  ext y
  rw [NK.GlobalCFT.Inclusion.Place.localAction_apply, NK.HassePrinciple.localAut_apply,
    NK.HassePrinciple.ringEquiv_cast_apply_eq]

/-- The Hasse–Brauer–Noether action of the decomposition group on the local units agrees with
the local action of `NK.GlobalCFTdeep`. -/
theorem localUnitsEquiv_apply_eq (w : Place L)
    (σ : MulAction.stabilizer (L ≃ₐ[K] L) w) (u : (Place.localField L w)ˣ) :
    NK.HassePrinciple.localUnitsEquiv (K := K) w σ u =
      Units.map (NK.GlobalCFT.Inclusion.Place.localAction σ.1 w
        (MulAction.mem_stabilizer_iff.mp σ.2)).toMonoidHom u := by
  have hι : (⟨σ.1, MulAction.mem_stabilizer_iff.mp σ.2⟩ : MulAction.stabilizer (L ≃ₐ[K] L) w)
      = σ := Subtype.ext rfl
  apply Units.ext
  show ((NK.HassePrinciple.localUnitsEquiv (K := K) w σ u : (Place.localField L w)ˣ) :
      Place.localField L w)
    = (NK.GlobalCFT.Inclusion.Place.localAction σ.1 w
        (MulAction.mem_stabilizer_iff.mp σ.2)) ↑u
  rw [NK.HassePrinciple.coe_localUnitsEquiv]
  show (NK.HassePrinciple.localAutHom (K := K) w σ) (↑u : Place.localField L w)
    = (NK.GlobalCFT.Inclusion.Place.localAction σ.1 w
        (MulAction.mem_stabilizer_iff.mp σ.2)) ↑u
  rw [show (NK.HassePrinciple.localAutHom (K := K) w σ) (↑u : Place.localField L w)
      = NK.HassePrinciple.localAut (K := K) w σ ↑u from rfl]
  rw [← hι, ← localAction_eq_localAut]

/-- The Hasse–Brauer–Noether local units representation, with the coefficient ring pinned to
`CoeffInt = ULift ℤ`, so that the universe level cannot float. -/
noncomputable abbrev hasseUnitsRep (w : Place L) :
    Rep NK.HassePrinciple.CoeffInt.{0} (MulAction.stabilizer (L ≃ₐ[K] L) w) :=
  NK.HassePrinciple.localUnitsRep K L w

/-- The underlying actions of the Hasse–Brauer–Noether local units representation and of the
local units representation of `NK.GlobalCFTdeep` agree. -/
theorem hasseUnitsRep_rho_eq (w : Place L)
    (σ : MulAction.stabilizer (L ≃ₐ[K] L) w) (a : Additive ((Place.localField L w)ˣ)) :
    (hasseUnitsRep (K := K) (L := L) w).ρ σ a =
      (localUnitsRep (K := K) (L := L) w).ρ σ a := by
  have hhs : (hasseUnitsRep (K := K) (L := L) w).ρ σ a = σ • a := rfl
  have hgs : (localUnitsRep (K := K) (L := L) w).ρ σ a
      = Additive.ofMul (Units.map (NK.GlobalCFT.Inclusion.Place.localAction σ.1 w
          (MulAction.mem_stabilizer_iff.mp σ.2)).toMonoidHom a.toMul) := rfl
  rw [hhs, hgs]
  change Additive.ofMul (NK.HassePrinciple.localUnitsEquiv (K := K) w σ a.toMul)
    = Additive.ofMul ((Units.map (NK.GlobalCFT.Inclusion.Place.localAction σ.1 w
        (MulAction.mem_stabilizer_iff.mp σ.2)).toMonoidHom) a.toMul)
  congr 1
  exact localUnitsEquiv_apply_eq w σ a.toMul

/-- **The component at the stabilised place is the local action on the component**, for an
arbitrary idèle. -/
theorem smul_apply_decomposition' (w : Place L) (σ : L ≃ₐ[K] L) (h : σ • w = w) (y : Idele L) :
    (σ • y) w = Units.map (NK.GlobalCFT.Inclusion.Place.localAction σ w h).toMonoidHom (y w) := by
  have hh := NK.HassePrinciple.smul_apply_stabilizer w
    (⟨σ, h⟩ : MulAction.stabilizer (L ≃ₐ[K] L) w) y
  rw [localAction_eq_localAut w σ h]
  simpa using hh

/-- **The component at the stabilised place is the local action on the component** for an element
of the decomposition group of `w`. -/
theorem smul_apply_decomposition (w : Place L) (σ : decompositionSubgroup (K := K) (L := L) w)
    (y : Idele L) :
    (σ.1 • y) w = Units.map (NK.GlobalCFT.Inclusion.Place.localAction σ.1 w
        (show σ.1 • w = w from σ.2)).toMonoidHom (y w) :=
  smul_apply_decomposition' w σ.1 (show σ.1 • w = w from σ.2) y

/-! ## The fibre and its coordinates -/

/-- The action of `Gal(L/K)` on the idèles supported on the places above `v`. -/
instance instMulDistribMulActionFiberIdeles (v : Place K) :
    MulDistribMulAction (L ≃ₐ[K] L) ↥(fiberIdeles (K := K) (L := L) v) :=
  stableMulDistribMulAction (L ≃ₐ[K] L) (fiberIdeles (K := K) (L := L) v)
    (fun σ x hx => smul_mem_fiberIdeles v hx)

theorem fiberIdelesRep_ρ_apply (v : Place K) (γ : L ≃ₐ[K] L)
    (x : (fiberIdelesRep (K := K) (L := L) v).V) :
    (fiberIdelesRep (K := K) (L := L) v).ρ γ x =
      Additive.ofMul (γ • (Additive.toMul x : ↥(fiberIdeles (K := K) (L := L) v))) := rfl

theorem coe_smul_fiberIdeles (v : Place K) (γ : L ≃ₐ[K] L)
    (x : ↥(fiberIdeles (K := K) (L := L) v)) :
    ((γ • x : ↥(fiberIdeles (K := K) (L := L) v)) : Idele L) = γ • (x : Idele L) := rfl

/-- The idèle underlying an element of the fibre. -/
noncomputable def fiberToIdele (v : Place K) (x : (fiberIdelesRep (K := K) (L := L) v).V) :
    Idele L :=
  ((Additive.toMul x : ↥(fiberIdeles (K := K) (L := L) v)) : Idele L)

theorem fiberToIdele_mem (v : Place K) (x : (fiberIdelesRep (K := K) (L := L) v).V) :
    fiberToIdele (K := K) (L := L) v x ∈ fiberIdeles (K := K) (L := L) v :=
  (Additive.toMul x : ↥(fiberIdeles (K := K) (L := L) v)).2

theorem fiberToIdele_smul (v : Place K) (γ : L ≃ₐ[K] L)
    (x : (fiberIdelesRep (K := K) (L := L) v).V) :
    fiberToIdele (K := K) (L := L) v ((fiberIdelesRep (K := K) (L := L) v).ρ γ x)
      = γ • fiberToIdele (K := K) (L := L) v x := by
  change ((Additive.toMul ((fiberIdelesRep (K := K) (L := L) v).ρ γ x) :
      ↥(fiberIdeles (K := K) (L := L) v)) : Idele L) = γ • _
  rw [fiberIdelesRep_ρ_apply]
  change (((γ • (Additive.toMul x : ↥(fiberIdeles (K := K) (L := L) v))) :
      ↥(fiberIdeles (K := K) (L := L) v)) : Idele L)
    = γ • ((Additive.toMul x : ↥(fiberIdeles (K := K) (L := L) v)) : Idele L)
  rw [coe_smul_fiberIdeles]

theorem fiberToIdele_injective (v : Place K) :
    Function.Injective (fiberToIdele (K := K) (L := L) v) := by
  intro x y h
  have h1 : (Additive.toMul x : ↥(fiberIdeles (K := K) (L := L) v))
      = (Additive.toMul y : ↥(fiberIdeles (K := K) (L := L) v)) := Subtype.ext h
  simpa using congrArg Additive.ofMul h1

/-- Evaluation of an idèle supported on the fibre at the place `w`, as a monoid homomorphism. -/
def fiberEvalHom (v : Place K) (w : Place L) :
    ↥(fiberIdeles (K := K) (L := L) v) →* (Place.localField L w)ˣ :=
  (Idele.eval w).comp (Subgroup.subtype (fiberIdeles (K := K) (L := L) v))

@[simp] theorem fiberEvalHom_apply (v : Place K) (w : Place L)
    (x : ↥(fiberIdeles (K := K) (L := L) v)) :
    fiberEvalHom (K := K) (L := L) v w x = (x : Idele L) w := rfl

/-- **The coordinate at `w` of an idèle of the fibre**, as a morphism of `D_w`-representations. -/
noncomputable def fiberCoord (v : Place K) (w : Place L) :
    Rep.res (decompositionSubgroup (K := K) (L := L) w).subtype
        (fiberIdelesRep (K := K) (L := L) v) ⟶ localUnitsRep (K := K) (L := L) w :=
  Rep.ofHom
    { toFun := ⇑(fiberEvalHom (K := K) (L := L) v w).toAdditive
      map_add' := map_add _
      map_smul' := fun n x => map_zsmul _ n x
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro x
        show Additive.ofMul (fiberEvalHom (K := K) (L := L) v w
              (Additive.toMul ((Rep.res (decompositionSubgroup (K := K) (L := L) w).subtype
                (fiberIdelesRep (K := K) (L := L) v)).ρ σ x)))
          = Additive.ofMul (Units.map (NK.GlobalCFT.Inclusion.Place.localAction σ.1 w
              (show σ.1 • w = w from σ.2)).toMonoidHom
                (fiberEvalHom (K := K) (L := L) v w (Additive.toMul x)))
        change Additive.ofMul (fiberEvalHom (K := K) (L := L) v w
              (Additive.toMul ((fiberIdelesRep (K := K) (L := L) v).ρ σ.1 x)))
          = Additive.ofMul (Units.map (NK.GlobalCFT.Inclusion.Place.localAction σ.1 w
              (show σ.1 • w = w from σ.2)).toMonoidHom
                (fiberEvalHom (K := K) (L := L) v w (Additive.toMul x)))
        rw [fiberIdelesRep_ρ_apply]
        show Additive.ofMul (((σ.1 • (Additive.toMul x : ↥(fiberIdeles (K := K) (L := L) v)) :
            ↥(fiberIdeles (K := K) (L := L) v)) : Idele L) w)
          = Additive.ofMul (Units.map (NK.GlobalCFT.Inclusion.Place.localAction σ.1 w
              (show σ.1 • w = w from σ.2)).toMonoidHom
                (((Additive.toMul x : ↥(fiberIdeles (K := K) (L := L) v)) : Idele L) w))
        rw [coe_smul_fiberIdeles, smul_apply_decomposition] }

/-- **The Shapiro map `∏_{w' | v} L_{w'}ˣ ⟶ Coind_{D_w}^{G} L_wˣ`**: the adjunction transpose of
the evaluation at `w`; on elements it is `(t x) γ = (γ · x)_w`. -/
noncomputable def fiberToCoind (v : Place K) (w : Place L) :
    fiberIdelesRep (K := K) (L := L) v ⟶
      Rep.coind (decompositionSubgroup (K := K) (L := L) w).subtype
        (localUnitsRep (K := K) (L := L) w) :=
  Rep.resCoindToHom _ _ _ (fiberCoord (K := K) (L := L) v w)

theorem fiberCoord_apply (v : Place K) (w : Place L)
    (y : (fiberIdelesRep (K := K) (L := L) v).V) :
    (fiberCoord (K := K) (L := L) v w).hom y
      = Additive.ofMul ((fiberToIdele (K := K) (L := L) v y) w) := rfl

theorem fiberToCoind_apply (v : Place K) (w : Place L)
    (x : (fiberIdelesRep (K := K) (L := L) v).V) (γ : L ≃ₐ[K] L) :
    ((fiberToCoind (K := K) (L := L) v w).hom x).1 γ
      = Additive.ofMul ((γ • fiberToIdele (K := K) (L := L) v x) w) := by
  rw [fiberToCoind, Rep.resCoindToHom_hom_apply_coe, fiberCoord_apply, fiberToIdele_smul]

/-! ## The fibre of `v` is the orbit of `w` -/

/-- A place in the orbit of `w` lies over the same place that `w` does. -/
theorem liesOver_of_mem_placeOrbit {v : Place K} {w u : Place L} (hw : Place.LiesOver w v)
    (hu : u ∈ NK.HassePrinciple.placeOrbit K L w) : Place.LiesOver u v := by
  obtain ⟨σ, rfl⟩ := NK.HassePrinciple.mem_placeOrbit.mp hu
  exact Place.liesOver_smul_iff.mpr hw

/-- Every place over `v` lies in the orbit of `w`. -/
theorem mem_placeOrbit_of_liesOver {v : Place K} {w u : Place L} (hw : Place.LiesOver w v)
    (hu : Place.LiesOver u v) : u ∈ NK.HassePrinciple.placeOrbit K L w :=
  NK.HassePrinciple.mem_placeOrbit.mpr
    (NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver hw hu)

/-- The idèles supported on the places above `v` are the idèles supported on the orbit of `w`. -/
theorem fiberIdeles_eq_supportedSubgroup (v : Place K) (w : Place L) (hw : Place.LiesOver w v) :
    fiberIdeles (K := K) (L := L) v
      = NK.HassePrinciple.supportedSubgroup (NK.HassePrinciple.placeOrbit K L w) := by
  refine Subgroup.ext fun x => ?_
  rw [mem_fiberIdeles, NK.HassePrinciple.mem_supportedSubgroup]
  constructor
  · intro hx u hu
    exact hx u (fun hLies => hu (mem_placeOrbit_of_liesOver hw hLies))
  · intro hx u hu
    exact hx u (fun humem => hu (liesOver_of_mem_placeOrbit hw humem))

/-! ## Injectivity and surjectivity of the Shapiro map -/

theorem fiberToCoind_injective (v : Place K) (w : Place L) (hw : Place.LiesOver w v) :
    Function.Injective (fiberToCoind (K := K) (L := L) v w).hom := by
  intro x y h
  have hsm : ∀ γ : L ≃ₐ[K] L,
      (γ • fiberToIdele (K := K) (L := L) v x) w
        = (γ • fiberToIdele (K := K) (L := L) v y) w := by
    intro γ
    have hγ := congrArg (fun z => z.1 γ) h
    rw [fiberToCoind_apply, fiberToCoind_apply] at hγ
    exact Additive.ofMul.injective hγ
  have hxy : fiberToIdele (K := K) (L := L) v x
      = fiberToIdele (K := K) (L := L) v y := by
    refine Idele.ext fun u => ?_
    by_cases hu : Place.LiesOver u v
    · obtain ⟨σ, hσ⟩ :=
        NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver hw hu
      exact NK.HassePrinciple.eq_of_smul_apply_eq (w := w) hsm (v := u) (γ := σ⁻¹)
        (by rw [inv_inv, hσ])
    · rw [show fiberToIdele (K := K) (L := L) v x u = 1 from
          mem_fiberIdeles.mp (fiberToIdele_mem (K := K) (L := L) v x) u hu,
        show fiberToIdele (K := K) (L := L) v y u = 1 from
          mem_fiberIdeles.mp (fiberToIdele_mem (K := K) (L := L) v y) u hu]
  exact fiberToIdele_injective (K := K) (L := L) v hxy

/-- The Hasse–Brauer–Noether coinduced module as a `ℤ`-representation, transported from the
`ULift ℤ`-version: the underlying equivariant functions are the same. -/
noncomputable def coindH (w : Place L)
    (f : (Rep.coind (decompositionSubgroup (K := K) (L := L) w).subtype
          (localUnitsRep (K := K) (L := L) w)).V) :
    (Rep.coind.{0, 0, 0, 0} (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype
      (hasseUnitsRep (K := K) (L := L) w)).V :=
  ⟨f.1, fun g h => by
    have h1 := f.2 g h
    rw [← hasseUnitsRep_rho_eq (K := K) (L := L) w g (f.1 h)] at h1
    exact h1⟩

@[simp] theorem coindH_apply (w : Place L)
    (f : (Rep.coind (decompositionSubgroup (K := K) (L := L) w).subtype
          (localUnitsRep (K := K) (L := L) w)).V) (γ : L ≃ₐ[K] L) :
    (coindH (K := K) (L := L) w f).1 γ = f.1 γ := rfl

theorem fiberToCoind_surjective (v : Place K) (w : Place L) (hw : Place.LiesOver w v) :
    Function.Surjective (fiberToCoind (K := K) (L := L) v w).hom := by
  intro f
  let cs := NK.HassePrinciple.coindSection w (coindH (K := K) (L := L) w f)
  have hmem : (cs : Idele L) ∈ fiberIdeles (K := K) (L := L) v := by
    rw [mem_fiberIdeles]
    intro u hu
    exact NK.HassePrinciple.mem_supportedSubgroup.mp cs.2 u
      (fun hmem' => hu (liesOver_of_mem_placeOrbit hw hmem'))
  refine ⟨Additive.ofMul ⟨(cs : Idele L), hmem⟩, ?_⟩
  apply Subtype.ext
  funext γ
  rw [fiberToCoind_apply]
  show Additive.ofMul ((γ • (cs : Idele L)) w) = f.1 γ
  rw [NK.HassePrinciple.smul_coindSection_apply, NK.HassePrinciple.coindToFun_apply,
    coindH_apply]
  rfl

end NK.GlobalCFTdeep

/-! ## The isomorphism -/

namespace NK.GlobalCFTdeep.Herbrand

theorem fiberIdelesRep_iso_coind {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (v : NK.GlobalCFT.Place K) (w : NK.GlobalCFT.Place L)
    (hw : NK.GlobalCFT.Place.LiesOver w v) :
    Nonempty (NK.GlobalCFTdeep.fiberIdelesRep (K := K) (L := L) v ≅
      Rep.coind (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L) w).subtype
        (NK.GlobalCFTdeep.localUnitsRep (K := K) (L := L) w)) := by
  have hbij : Function.Bijective (fiberToCoind (K := K) (L := L) v w).hom :=
    ⟨fiberToCoind_injective v w hw, fiberToCoind_surjective v w hw⟩
  let e : (fiberIdelesRep (K := K) (L := L) v).V ≃ₗ[ℤ]
      (Rep.coind (decompositionSubgroup (K := K) (L := L) w).subtype
        (localUnitsRep (K := K) (L := L) w)).V :=
    LinearEquiv.ofBijective (fiberToCoind (K := K) (L := L) v w).hom hbij
  exact ⟨Rep.mkIso (Representation.Equiv.mk e
    (fun γ => (fiberToCoind (K := K) (L := L) v w).hom.isIntertwining' γ))⟩

end NK.GlobalCFTdeep.Herbrand
