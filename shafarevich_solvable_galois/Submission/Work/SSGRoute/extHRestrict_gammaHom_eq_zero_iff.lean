import Mathlib.Tactic.Have
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.ExtH1Iso
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Restriction of the degree-one `Ext` class attached to a `1`-cocycle

`ExtH1Iso.lean` produces, for a group `G`, a `G`-module `M` and a proof `hS` of the short
exactness of the augmentation sequence `0 → I_G → k[G] → k → 0`, the isomorphism

  `gammaHom hS : H¹(G, M) →+ Ext¹_G(ℤ, M)`

computed on the class of `ψ ∈ Z¹(G, M)` by `Φ(cocycleHom ψ) = hS.extClass.comp (mk₀ (cocycleHom ψ))`.

This file computes the restriction of that class to a subgroup `D ≤ G`: it is the class of the
restriction of `ψ` to `D`, so it vanishes exactly when `ψ|_D` is a coboundary

  `extHRestrict D (gammaHom hS (H1π ψ)) = 0 ↔ ∃ m : M, ∀ d ∈ D, ψ.1 d = d • m - m`.

The proof restricts the whole construction along the exact functor `Rep.resFunctor D.subtype`:
`Ext.mapExactFunctor` carries the class of the augmentation sequence to the class of the restricted
sequence `0 → res I_G → res k[G] → ℤ → 0`, and a general exactness lemma for connecting maps
(`extClass_comp_mk0_eq_zero_iff`) identifies the vanishing with the existence of a `D`-equivariant
splitting `res k[G] → M` of the restricted derivation `res I_G → M`.  Finally, such a splitting
exists exactly when `ψ|_D` is a coboundary: given `m` with `ψ d = d • m - m` for `d ∈ D`, the
`Coeff`-linear extension of `ebas γ ↦ m + ψ γ` is `D`-equivariant and extends the derivation,
and conversely its value at `ebas 1` is the required `m`.

-/

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open SSGRoute.PTExt

namespace Work.SSGRoute

universe u v w

/-! ## A general exactness lemma for connecting maps -/

/-- **The kernel of the connecting map.**  For a short exact short complex `S` in an abelian
category, the connecting map `f ↦ S.extClass.comp (Ext.mk₀ f)` has as kernel exactly the maps
`S.X₁ ⟶ Y` which factor through the inclusion `S.f`. -/
theorem extClass_comp_mk0_eq_zero_iff {C : Type u} [Category.{v} C] [Abelian C]
    [HasExt.{w} C] {S : ShortComplex C} (hS : S.ShortExact) {Y : C} (f : S.X₁ ⟶ Y) :
    hS.extClass.comp (Abelian.Ext.mk₀ f) (by norm_num : 1 + 0 = 1) = 0 ↔
      ∃ k : S.X₂ ⟶ Y, S.f ≫ k = f := by
  constructor
  · intro hf
    obtain ⟨x₂, hx₂⟩ := Abelian.Ext.contravariant_sequence_exact₁ hS Y (Abelian.Ext.mk₀ f)
      (n₁ := 1) (by norm_num) hf
    refine ⟨Abelian.Ext.addEquiv₀ x₂, ?_⟩
    have h1 : Abelian.Ext.mk₀ f = Abelian.Ext.mk₀ (S.f ≫ Abelian.Ext.addEquiv₀ x₂) := by
      rw [← Abelian.Ext.mk₀_comp_mk₀, Abelian.Ext.mk₀_addEquiv₀_apply]
      exact hx₂.symm
    exact ((Abelian.Ext.mk₀_bijective (X := S.X₁) (Y := Y)).1 h1).symm
  · rintro ⟨k, rfl⟩
    rw [← Abelian.Ext.mk₀_comp_mk₀]
    exact hS.extClass_comp_assoc (Abelian.Ext.mk₀ k) (n := 0)

namespace ExtH1

variable (G : Type) [Group G]

/-! ## Extending a `Coeff`-linear map from the basis `ebas` -/

/-- A `Coeff`-linear map on `k[G]` is determined by its values on the basis elements `ebas γ`. -/
theorem linearMap_ext_ebas {N : Type} [AddCommGroup N] [Module Coeff N]
    {f g : MonoidAlgebra Coeff G →ₗ[Coeff] N}
    (h : ∀ γ : G, f (ebas G γ) = g (ebas G γ)) : f = g := by
  apply LinearMap.ext
  intro x
  have hx : (MonoidAlgebra.coeff x).sum (fun γ c => c • ebas G γ) = x :=
    sum_coeff_smul_ebas G x
  rw [← hx, Finsupp.sum, map_sum, map_sum]
  exact Finset.sum_congr rfl (fun γ _ => by
    rw [LinearMap.map_smul, LinearMap.map_smul, h γ])

/-- A `Coeff`-linear map on the augmentation ideal `I` is determined by its values on the
elements `γ - 1`. -/
theorem linearMap_ext_augDiff {N : Type} [AddCommGroup N] [Module Coeff N]
    {f g : ↥(augI G) →ₗ[Coeff] N}
    (h : ∀ γ : G, f (augDiff G γ) = g (augDiff G γ)) : f = g := by
  apply LinearMap.ext
  intro x
  have hx : (MonoidAlgebra.coeff (x : regRep G)).sum (fun γ c => c • augDiff G γ) = x :=
    sum_coeff_smul_augDiff G x
  rw [← hx, Finsupp.sum, map_sum, map_sum]
  exact Finset.sum_congr rfl (fun γ _ => by
    rw [LinearMap.map_smul, LinearMap.map_smul, h γ])

section Res

variable (M : Type) [AddCommGroup M] [DistribMulAction G M] [SMulCommClass G Coeff M]

/-- `↥(Rep.res D.subtype (modRep G M))` regarded as the type `M` it is definitionally. -/
abbrev resToM (D : Subgroup G) : ↥(Rep.res D.subtype (modRep G M)) → M := fun x => x

/-- The action of `D` on the restricted module `Rep.res D.subtype (modRep G M)`, read in `M`. -/
theorem resToM_rho (D : Subgroup G) (d : D) (x : ↥(Rep.res D.subtype (modRep G M))) :
    resToM G M D ((Rep.res D.subtype (modRep G M)).ρ d x) =
      (D.subtype d) • resToM G M D x := by
  rw [show ((Rep.res D.subtype (modRep G M)).ρ d x)
      = ((modRep G M).ρ (D.subtype d)) x from rfl]
  rw [show resToM G M D (((modRep G M).ρ (D.subtype d)) x)
      = modRepToM G M (((modRep G M).ρ (D.subtype d)) x) from rfl]
  rw [show (((D.subtype d) • resToM G M D x : M)) = (D.subtype d) • modRepToM G M x from rfl]
  exact modRepToM_rho G M (D.subtype d) x

/-- Restriction of `Ext`-cohomology to a subgroup needs no change of the coefficient module: it
is plain application of the exact functor `Rep.resFunctor D.subtype`. -/
theorem extHRestrict_eq_extRes (D : Subgroup G) {A : Rep.{0} Coeff G} {n : ℕ}
    (y : extH A n) : extHRestrict D y = extRes D.subtype y := by
  rw [extHRestrict, extHMap]
  have h : (extRes D.subtype y).comp
      (Abelian.Ext.mk₀ (𝟙 (Rep.res D.subtype A))) (add_zero n) = extRes D.subtype y :=
    Abelian.Ext.comp_mk₀_id _
  rw [h]
  exact Abelian.Ext.mk₀_id_comp _

/-- **Restriction of `Φ(cocycleHom ψ)`**: applying `Ext.mapExactFunctor` to the class of the
augmentation sequence gives the class of the restricted sequence, with the restricted derivation. -/
theorem extRes_gammaHom_eq (hS : (augSES G).ShortExact) (D : Subgroup G)
    (ψ : ↥(Work.GroupCohomology.Z1 G M)) :
    extRes D.subtype (gammaHom (G := G) (M := M) hS (Work.GroupCohomology.H1π G M ψ)) =
      ((hS.map_of_exact (Rep.resFunctor D.subtype)).extClass).comp
        (Abelian.Ext.mk₀ ((Rep.resFunctor D.subtype).map
          (cocycleHom (G := G) (M := M) ψ.1
            ((crossedHom_iff (G := G) (M := M) ψ.1).mp ψ.2))))
        (by norm_num : 1 + 0 = 1) := by
  have key : gammaHom (G := G) (M := M) hS (Work.GroupCohomology.H1π G M ψ)
      = phiMap G M hS (cocycleHom (G := G) (M := M) ψ.1
          ((crossedHom_iff (G := G) (M := M) ψ.1).mp ψ.2)) := by
    rw [gammaHom_H1π, gammaZ1_apply]
  rw [extRes, key]
  rw [show phiMap G M hS (cocycleHom (G := G) (M := M) ψ.1
        ((crossedHom_iff (G := G) (M := M) ψ.1).mp ψ.2))
      = hS.extClass.comp (Abelian.Ext.mk₀ (cocycleHom (G := G) (M := M) ψ.1
        ((crossedHom_iff (G := G) (M := M) ψ.1).mp ψ.2))) (by norm_num : 1 + 0 = 1) from rfl]
  rw [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_extClass,
    Abelian.Ext.mapExactFunctor_mk₀]

/-! ## The restricted derivation bridge -/

/-- **The restricted derivation extends across a coboundary.**  If the restriction of `ψ` to `D`
is a coboundary, then the `D`-equivariant derivation `res I_G → M` attached to `ψ` extends to a
`D`-equivariant map `res k[G] → M`. -/
theorem resMap_comp_eq_of_coboundary (D : Subgroup G)
    (ψ : ↥(Work.GroupCohomology.Z1 G M))
    (hm : ∃ m : M, ∀ d ∈ D, ψ.1 d = d • m - m) :
    ∃ k : Rep.res D.subtype (regRep G) ⟶ Rep.res D.subtype (modRep G M),
      Rep.resMap D.subtype (augIncl G) ≫ k =
        Rep.resMap D.subtype (cocycleHom (G := G) (M := M) ψ.1
          ((crossedHom_iff (G := G) (M := M) ψ.1).mp ψ.2)) := by
  have hψ : IsCrossedHom (G := G) (M := M) ψ.1 :=
    (crossedHom_iff (G := G) (M := M) ψ.1).mp ψ.2
  obtain ⟨m, hm⟩ := hm
  let L : MonoidAlgebra Coeff G →ₗ[Coeff] M := cocycleLin G M (fun g => m + ψ.1 g)
  have hL : ∀ g : G, L (ebas G g) = m + ψ.1 g := fun g =>
    cocycleLin_ebas G (fun g => m + ψ.1 g) g
  have hpoint : ∀ d : D, ∀ g : G,
      m + ψ.1 (D.subtype d * g) = (D.subtype d) • (m + ψ.1 g) := by
    intro d g
    rw [hψ (D.subtype d) g, hm (D.subtype d) d.2, smul_add]
    abel
  have hint : ∀ d : D, L.comp ((Rep.res D.subtype (regRep G)).ρ d) =
      ((Rep.res D.subtype (modRep G M)).ρ d).comp L := by
    intro d
    apply linearMap_ext_ebas G
    intro g
    show L (((Rep.res D.subtype (regRep G)).ρ d) (ebas G g)) =
      ((Rep.res D.subtype (modRep G M)).ρ d) (L (ebas G g))
    rw [show ((Rep.res D.subtype (regRep G)).ρ d) (ebas G g) = ebas G (D.subtype d * g) from
      regRep_ρ_ebas G (D.subtype d) g]
    rw [hL, hL]
    show resToM G M D (m + ψ.1 (D.subtype d * g)) =
      resToM G M D (((Rep.res D.subtype (modRep G M)).ρ d) (m + ψ.1 g))
    rw [resToM_rho G M D d (m + ψ.1 g), hpoint d g]
  let k : Rep.res D.subtype (regRep G) ⟶ Rep.res D.subtype (modRep G M) :=
    Rep.ofHom { toLinearMap := L, isIntertwining' := fun d => hint d }
  refine ⟨k, ?_⟩
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply linearMap_ext_augDiff G
  intro γ
  show L (ebas G γ - ebas G 1) =
    (Rep.Hom.hom (cocycleHom (G := G) (M := M) ψ.1 hψ)) (augDiff G γ)
  rw [map_sub, hL, hL, cocycleHom_augDiff (G := G) (M := M) ψ.1 hψ γ,
    crossedHom_one (G := G) (M := M) ψ.1 hψ]
  simp

/-- **The restricted derivation bridge.**  The restricted derivation `res I_G → M` attached to
`ψ` extends to a `D`-equivariant map `res k[G] → M` exactly when `ψ|_D` is a coboundary. -/
theorem exists_resMap_comp_eq_iff_coboundary (D : Subgroup G)
    (ψ : ↥(Work.GroupCohomology.Z1 G M)) :
    (∃ k : Rep.res D.subtype (regRep G) ⟶ Rep.res D.subtype (modRep G M),
        Rep.resMap D.subtype (augIncl G) ≫ k =
          Rep.resMap D.subtype (cocycleHom (G := G) (M := M) ψ.1
            ((crossedHom_iff (G := G) (M := M) ψ.1).mp ψ.2))) ↔
      ∃ m : M, ∀ d ∈ D, ψ.1 d = d • m - m := by
  refine ⟨?_, resMap_comp_eq_of_coboundary G M D ψ⟩
  rintro ⟨k, hk⟩
  refine ⟨resToM G M D (k.hom (ebas G 1)), fun d hd => ?_⟩
  set dd : D := ⟨d, hd⟩ with hdd
  have hkapp := congrArg (fun (φ : Rep.res D.subtype (augI G) ⟶
      Rep.res D.subtype (modRep G M)) => φ.hom (augDiff G d)) hk
  simp only [Rep.hom_comp] at hkapp
  have hcomm := Rep.hom_comm_apply k dd (ebas G 1)
  calc ψ.1 d
      = (cocycleHom (G := G) (M := M) ψ.1
          ((crossedHom_iff (G := G) (M := M) ψ.1).mp ψ.2)).hom (augDiff G d) := by
        rw [cocycleHom_augDiff]
    _ = (Rep.resMap D.subtype (cocycleHom (G := G) (M := M) ψ.1
          ((crossedHom_iff (G := G) (M := M) ψ.1).mp ψ.2))).hom (augDiff G d) := by
        rw [Rep.resMap_hom_apply]
    _ = k.hom ((Rep.resMap D.subtype (augIncl G)).hom (augDiff G d)) := hkapp.symm
    _ = k.hom (ebas G d - ebas G 1) := by
        rw [Rep.resMap_hom_apply, augIncl_augDiff]
    _ = k.hom (ebas G d) - k.hom (ebas G 1) := by rw [map_sub]
    _ = d • resToM G M D (k.hom (ebas G 1)) - resToM G M D (k.hom (ebas G 1)) := by
        rw [show ebas G d = (regRep G).ρ d (ebas G 1) from by rw [regRep_ρ_ebas, mul_one],
          show k.hom ((regRep G).ρ d (ebas G 1))
            = k.hom ((Rep.res D.subtype (regRep G)).ρ dd (ebas G 1)) from rfl]
        rw [hcomm]
        show resToM G M D (((Rep.res D.subtype (modRep G M)).ρ dd) (k.hom (ebas G 1)))
            - resToM G M D (k.hom (ebas G 1))
          = d • resToM G M D (k.hom (ebas G 1)) - resToM G M D (k.hom (ebas G 1))
        rw [resToM_rho G M D dd (k.hom (ebas G 1))]
        rfl

end Res

end ExtH1

/-! ## The main theorem -/

theorem extHRestrict_gammaHom_eq_zero_iff (G : Type) [Group G] (M : Type) [AddCommGroup M]
    [DistribMulAction G M] [SMulCommClass G SSGRoute.PTExt.Coeff M]
    (hS : CategoryTheory.ShortComplex.ShortExact (Work.SSGRoute.ExtH1.augSES G))
    (D : Subgroup G) (ψ : ↥(Work.GroupCohomology.Z1 G M)) :
    SSGRoute.PTExt.extHRestrict D
        (Work.SSGRoute.ExtH1.gammaHom (G := G) (M := M) hS (Work.GroupCohomology.H1π G M ψ)) = 0 ↔
      ∃ m : M, ∀ d ∈ D, ψ.1 d = d • m - m := by
  rw [ExtH1.extHRestrict_eq_extRes]
  rw [ExtH1.extRes_gammaHom_eq (G := G) (M := M) hS D ψ]
  rw [extClass_comp_mk0_eq_zero_iff]
  refine Iff.trans ?_ (ExtH1.exists_resMap_comp_eq_iff_coboundary (G := G) (M := M) D ψ)
  exact ⟨fun ⟨k, hk⟩ => ⟨k, hk⟩, fun ⟨k, hk⟩ => ⟨k, hk⟩⟩

end Work.SSGRoute
