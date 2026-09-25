import Mathlib
import Submission.NK.NUV2.LC.RouteB.level_kills_aux
import Submission.NK.NUV2.LC.RouteB.muLift
import Submission.NK.NUV2.LC.RouteB.locUnits_tower_fibre
import Submission.NK.NUV2.LC.RouteB.unitsLift_kummerLevel
import Submission.NK.HassePrinciple.UnitsColimit
import Submission.NK.HassePrinciple.LocalUnits
import Submission.NK.NUV2.LC.RouteB.v2.exists_galoisElement_liesOver_fixing
import Submission.NK.NUV2.LC.RouteB.v2.levelGroupEquiv_mk_apply_eq_levelRestrict
import Submission.NK.NUV2.LC.RouteB.v2.locUnits_conj_self
import Submission.NK.NUV2.LC.RouteB.v2.place_smul_eq_of_apply_eq

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open CategoryTheory

namespace NK.NUV2.LC.RouteB.v2

/-- **Combining two successive applications of the `H²`-map of `groupCohomology.map` into one.** -/
theorem map_map_apply {k G H K : Type} [CommRing k] [Group G] [Group H] [Group K]
    {A : Rep k K} {B : Rep k H} {C : Rep k G} (f : H →* K) (g : G →* H)
    (φ : Rep.res f A ⟶ B) (ψ : Rep.res g B ⟶ C) (n : ℕ) (y : groupCohomology A n) :
    (groupCohomology.map g ψ n).hom ((groupCohomology.map f φ n).hom y)
      = (groupCohomology.map (f.comp g) ((Rep.resFunctor g).map φ ≫ ψ) n).hom y := by
  rw [← ConcreteCategory.comp_apply, ← groupCohomology.map_comp]

/-- **The conjugation coefficient on the units acts by applying the automorphism.** -/
theorem conjUnitsCoeff_ofMul {F M : Type} [Field F] [Field M] [Algebra F M]
    (σ : M ≃ₐ[F] M) (v : Mˣ) :
    (NK.NUV2.LC.RouteB.conjUnitsCoeff (F := F) (M := M) σ).hom.toLinearMap (Additive.ofMul v)
      = Additive.ofMul (Units.map σ.toMulEquiv.toMonoidHom v) := rfl

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **The conjugation action fixes the inflation of a class from a smaller level.**
Let `L ≤ M` be finite Galois levels of `K'/K`, `V ≤ Gal(K'/K)` with `Gal(K'/L) ≤ V`, let
`σ ∈ Gal(K'/L)` (so that `σ ∈ V`), and let `τ := levelGroupEquiv V M (mk σ)` be the corresponding
element of `Gal(↥M/↥(levelBase V M))`.  Then the conjugation action `conjH2 τ` fixes the transport
`unitsLift V M (unitsLevelMap V hLM b)` of the inflation of a level-`L` class `b`. -/
theorem conjH2_unitsLift_unitsLevelMap (V : Subgroup Gal(K'/K))
    (L M : FiniteGaloisIntermediateField K K') (hLM : L ≤ M) (hF : L.fixingSubgroup ≤ V)
    (σ : Gal(K'/K)) (hσL : σ ∈ L.fixingSubgroup)
    (b : NK.HassePrinciple.UnitsLevelH2 (K := K) (K' := K') V L) :
    NK.NUV2.LC.RouteB.conjH2 (F := ↥(NK.NUV2.LC.RouteB.levelBase V M))
        (M := ↥(M : IntermediateField K K'))
        ((NK.NUV2.LC.RouteB.levelGroupEquiv V M) (QuotientGroup.mk (⟨σ, hF hσL⟩ : ↥V)))
        (NK.NUV2.LC.RouteB.unitsLift (K := K) (K' := K') V M
          ((NK.HassePrinciple.unitsLevelMap (K := K) (K' := K') V hLM).hom b))
      = NK.NUV2.LC.RouteB.unitsLift (K := K) (K' := K') V M
          ((NK.HassePrinciple.unitsLevelMap (K := K) (K' := K') V hLM).hom b) := by
  have hfix : ∀ u : ↥(L : IntermediateField K K'),
      ((NK.NUV2.LC.RouteB.levelGroupEquiv V M) (QuotientGroup.mk (⟨σ, hF hσL⟩ : ↥V)))
        ((IntermediateField.inclusion hLM) u) = (IntermediateField.inclusion hLM) u := by
    intro u
    rw [levelGroupEquiv_mk_apply_eq_levelRestrict V M σ (hF hσL) ((IntermediateField.inclusion hLM) u)]
    have h1 : (((NK.HassePrinciple.levelRestrict M σ) ((IntermediateField.inclusion hLM) u) :
        ↥(M : IntermediateField K K')) : K')
        = σ (((IntermediateField.inclusion hLM) u : ↥(M : IntermediateField K K')) : K') :=
      AlgEquiv.restrictNormal_commutes σ (↥(M : IntermediateField K K'))
        ((IntermediateField.inclusion hLM) u)
    apply Subtype.ext
    rw [h1]
    have hmem : (u : K') ∈ (L : IntermediateField K K') := u.2
    have hσu : σ (u : K') = (u : K') :=
      (IntermediateField.mem_fixingSubgroup_iff (L : IntermediateField K K') σ).mp hσL (u : K') hmem
    simpa using hσu
  rw [NK.NUV2.LC.RouteB.unitsLift_apply, groupCohomology.mapIso_hom]
  rw [NK.NUV2.LC.RouteB.conjH2, NK.HassePrinciple.unitsLevelMap]
  rw [map_map_apply, map_map_apply]
  rw [map_map_apply]
  refine congrArg (fun z => ModuleCat.Hom.hom z b) ?_
  refine groupCohomology.map_congr ?_ ?_ 2
  · apply MonoidHom.ext
    intro a
    have hconj : (NK.NUV2.LC.RouteB.levelGroupEquiv V M).symm
        (NK.NUV2.LC.RouteB.conjHom
          ((NK.NUV2.LC.RouteB.levelGroupEquiv V M) (QuotientGroup.mk (⟨σ, hF hσL⟩ : ↥V))) a)
        = (QuotientGroup.mk (⟨σ, hF hσL⟩ : ↥V))⁻¹
          * ((NK.NUV2.LC.RouteB.levelGroupEquiv V M).symm a)
          * (QuotientGroup.mk (⟨σ, hF hσL⟩ : ↥V)) := by
      rw [NK.NUV2.LC.RouteB.conjHom_apply, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
    have h2 : NK.BrauerHasse.levelQuotHom (U := V) hLM
        (QuotientGroup.mk (⟨σ, hF hσL⟩ : ↥V)) = 1 := by
      rw [NK.BrauerHasse.levelQuotHom, QuotientGroup.map_mk]
      exact (QuotientGroup.eq_one_iff (⟨σ, hF hσL⟩ : ↥V)).mpr (Subgroup.mem_subgroupOf.mpr hσL)
    show (NK.BrauerHasse.levelQuotHom (U := V) hLM)
          ((NK.NUV2.LC.RouteB.levelGroupEquiv V M).symm
            (NK.NUV2.LC.RouteB.conjHom ((NK.NUV2.LC.RouteB.levelGroupEquiv V M)
              (QuotientGroup.mk (⟨σ, hF hσL⟩ : ↥V))) a))
        = (NK.BrauerHasse.levelQuotHom (U := V) hLM)
            ((NK.NUV2.LC.RouteB.levelGroupEquiv V M).symm a)
    simp only [hconj, map_mul, map_inv, h2, inv_one, one_mul, mul_one]
  · apply LinearMap.ext
    intro z
    show (NK.NUV2.LC.RouteB.conjUnitsCoeff (F := ↥(NK.NUV2.LC.RouteB.levelBase V M))
            (M := ↥(M : IntermediateField K K'))
            ((NK.NUV2.LC.RouteB.levelGroupEquiv V M) (QuotientGroup.mk (⟨σ, hF hσL⟩ : ↥V)))).hom.toLinearMap
          (Additive.ofMul (Units.map (IntermediateField.inclusion hLM).toMonoidHom
            (Additive.toMul (α := (↥(L : IntermediateField K K'))ˣ) z)))
        = Additive.ofMul (Units.map (IntermediateField.inclusion hLM).toMonoidHom
            (Additive.toMul (α := (↥(L : IntermediateField K K'))ˣ) z))
    rw [conjUnitsCoeff_ofMul]
    congr 1
    apply Units.ext
    simpa using hfix (↑(Additive.toMul (α := (↥(L : IntermediateField K K'))ˣ) z))

/-- **Level-fibre independence of the `locL`-localisation.**
For finite Galois levels `L ≤ M` of `K'/K`, a subgroup `V` with `Gal(K'/L) ≤ V` (so that
`K'^V ⊆ L`), a class `b : UnitsLevelH2 V L` and two places `w₁, w₂` of `↥M` above the *same* place
`w` of `↥L`: the `locL`-localisation of the inflation `unitsLevelMap V hLM b` vanishes at `w₁` if
and only if it vanishes at `w₂`.

Mathematically: `unitsLevelMap V hLM b` is the inflation of `b` from the quotient
`LevelGroup V L` of `LevelGroup V M`, hence is fixed by the conjugation action of the kernel; the
places of `↥M` above the place `w` of `↥L` are permuted transitively by `Gal(↥M/↥L)`, and the
localisation `locL V M ·` is equivariant under this conjugation (transport of
`NK.NUV2.LC.RouteB.locUnits_conj` / `conjLoc_eq_zero_iff` of `locUnits_tower_fibre.lean`, or
equivalently of the field-theoretic `locUnits_tower_fibre`).

Imports: `locUnits_tower_fibre.lean` contains the (proved) conjugation machinery
(`conjStab`, `conjLoc`, `conjLocIso`, `locUnits_conj`, `locUnits_tower_fibre`) plus its own copy of
the level square; this module must NOT be imported together with `locUnits_tower_eq_zero.lean`
(both define `NK.NUV2.LC.RouteB.unitsLevelMapTower_comp_locUnits`). -/
theorem locL_unitsLevelMap_fibre {K K' : Type} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K']
    (V : Subgroup Gal(K'/K)) (L M : FiniteGaloisIntermediateField K K')
    (hLM : L ≤ M) (hF : L.fixingSubgroup ≤ V)
    (b : NK.HassePrinciple.UnitsLevelH2 (K := K) (K' := K') V L)
    {w : NK.GlobalCFT.Place ↥(L : IntermediateField K K')}
    {w₁ w₂ : NK.GlobalCFT.Place ↥(M : IntermediateField K K')}
    (h₁ : @NK.GlobalCFT.Place.LiesOver ↥(L : IntermediateField K K') _ _ ↥(M : IntermediateField K K') _ _
      ((IntermediateField.inclusion hLM).toAlgebra) w₁ w)
    (h₂ : @NK.GlobalCFT.Place.LiesOver ↥(L : IntermediateField K K') _ _ ↥(M : IntermediateField K K') _ _
      ((IntermediateField.inclusion hLM).toAlgebra) w₂ w) :
    NK.NUV2.LC.RouteB.locL (K := K) (K' := K') V M w₁
        ((NK.HassePrinciple.unitsLevelMap (K := K) (K' := K') V hLM).hom b) = 0 ↔
      NK.NUV2.LC.RouteB.locL (K := K) (K' := K') V M w₂
        ((NK.HassePrinciple.unitsLevelMap (K := K) (K' := K') V hLM).hom b) = 0 := by
  classical
  obtain ⟨σ, hσL, hσw⟩ := exists_galoisElement_liesOver_fixing L M hLM h₁ h₂
  set τ : ↥(M : IntermediateField K K') ≃ₐ[↥(NK.NUV2.LC.RouteB.levelBase V M)]
      ↥(M : IntermediateField K K') :=
    (NK.NUV2.LC.RouteB.levelGroupEquiv V M) (QuotientGroup.mk (⟨σ, hF hσL⟩ : ↥V)) with hτ
  have hfun : ∀ x, τ x = (NK.HassePrinciple.levelRestrict M σ) x :=
    levelGroupEquiv_mk_apply_eq_levelRestrict V M σ (hF hσL)
  have hτw : τ • w₁ = w₂ := by
    rw [← hσw]
    exact place_smul_eq_of_apply_eq τ (NK.HassePrinciple.levelRestrict M σ) hfun w₁
  subst hτw
  have hfixc : (NK.NUV2.LC.RouteB.conjH2 (F := ↥(NK.NUV2.LC.RouteB.levelBase V M))
        (M := ↥(M : IntermediateField K K')) τ)
        (NK.NUV2.LC.RouteB.unitsLift (K := K) (K' := K') V M
          ((NK.HassePrinciple.unitsLevelMap (K := K) (K' := K') V hLM).hom b))
      = NK.NUV2.LC.RouteB.unitsLift (K := K) (K' := K') V M
          ((NK.HassePrinciple.unitsLevelMap (K := K) (K' := K') V hLM).hom b) :=
    conjH2_unitsLift_unitsLevelMap V L M hLM hF σ hσL b
  have hconj := congrArg (fun (f : groupCohomology (NK.HassePrinciple.unitsRep
          (↥(NK.NUV2.LC.RouteB.levelBase V M)) (↥(M : IntermediateField K K'))) 2 ⟶
        groupCohomology (NK.HassePrinciple.localUnitsRep
          (↥(NK.NUV2.LC.RouteB.levelBase V M)) (↥(M : IntermediateField K K')) (τ • w₁)) 2) =>
      f.hom (NK.NUV2.LC.RouteB.unitsLift (K := K) (K' := K') V M
        ((NK.HassePrinciple.unitsLevelMap (K := K) (K' := K') V hLM).hom b)))
    (locUnits_conj_self (F := ↥(NK.NUV2.LC.RouteB.levelBase V M))
      (M := ↥(M : IntermediateField K K')) τ w₁)
  have key : NK.NUV2.LC.RouteB.locL (K := K) (K' := K') V M (τ • w₁)
        ((NK.HassePrinciple.unitsLevelMap (K := K) (K' := K') V hLM).hom b)
      = (NK.NUV2.LC.RouteB.conjLoc (F := ↥(NK.NUV2.LC.RouteB.levelBase V M))
          (M := ↥(M : IntermediateField K K')) τ w₁)
          (NK.NUV2.LC.RouteB.locL (K := K) (K' := K') V M w₁
            ((NK.HassePrinciple.unitsLevelMap (K := K) (K' := K') V hLM).hom b)) := by
    simp only [NK.NUV2.LC.RouteB.locL]
    conv_lhs => rw [← hfixc]
    exact hconj
  rw [key]
  exact (NK.NUV2.LC.RouteB.conjLoc_eq_zero_iff τ w₁ (NK.NUV2.LC.RouteB.locL (K := K)
    (K' := K') V M w₁ ((NK.HassePrinciple.unitsLevelMap (K := K) (K' := K') V hLM).hom b))).symm

end NK.NUV2.LC.RouteB.v2
