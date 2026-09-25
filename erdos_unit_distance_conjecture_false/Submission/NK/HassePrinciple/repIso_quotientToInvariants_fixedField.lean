import Mathlib
import Submission.NK.GlobalCFT.GlobalCFT
import Submission.NK.HassePrinciple.liesOver_smul_of_restrict
import Submission.NK.HassePrinciple.localRingEquiv_localAlgebraMapUnits_of_restrict

/-!
# The Galois invariants of the idèle class group are the idèle class group of the fixed field

For a finite Galois extension `L / K` of number fields and a **normal** subgroup `N ≤ Gal(L/K)`,
the invariants of the idèle class group `C_L` under the action of `N` are canonically isomorphic,
as `Gal(L/K) ⧸ N`-modules, to the idèle class group of the fixed field `L^N`.

In the language of the representation theory of `Gal(L/K)`: the quotient of the representation
`C_L` on which `N` acts trivially is the restriction of the representation `C_{L^N}` along the
canonical isomorphism `Gal(L/K) ⧸ N ≅ Gal(L^N/K)`,

`(rep K L).quotientToInvariants N ≅ Rep.res (IsGalois.normalAutEquivQuotient N).toMonoidHom
  (rep K (fixedField N))`.

This is the `H⁰`-computation `C_{L^N} ≅ (C_L)^N` of class field theory together with its Galois
equivariance; it is the input for the twist computations of Chapter XII of *Cohomology of Number
Fields* (Neukirch–Schmidt–Wingberg).

## Main results

* `NK.HassePrinciple.repIso_quotientToInvariants_fixedField`: the isomorphism of
  `Gal(L/K) ⧸ N`-representations.

## Outline of the proof

* `ψ : C_{L^N} →* C_L` is the inclusion of idèle class groups induced by the local embeddings;
  it is injective and its range is exactly the subgroup of `N`-invariant classes
  (`globalCFT_ideleClassGroup_inclusion_injective`, `globalCFT_invariants_ideleClassGroup`).
* This gives a bijection `Φ : (C_L)^N ≅ C_{L^N}` of the underlying modules.
* `Φ` is `Gal(L/K) ⧸ N`-equivariant: this is the naturality of the idèle inclusion under base
  change, `NK.HassePrinciple.ideleInclusion_smul_restrict`.
* The linear isomorphism condition of `Rep.nonempty_iso_of_intertwining` then produces the
  isomorphism of representations.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.style.setOption false
set_option maxHeartbeats 1000000

open scoped NumberField
open NumberField IsDedekindDomain
open CategoryTheory
open NK.GlobalCFT NK.GlobalCFT.Inclusion

noncomputable section

namespace NK.HassePrinciple

/-! ### The invariants under a normal subgroup -/

/-- **The `N`-invariants of `C_L` are the `Gal(L/L^N)`-invariants.**  For a normal subgroup
`N ≤ Gal(L/K)` the elements of `C_L` fixed by the elements of `N` are exactly those fixed by the
Galois group `Gal(L/L^N)` of the extension `L/L^N`, the two groups being identified through
`IntermediateField.subgroupEquivAlgEquiv`. -/
lemma forall_smul_eq_self_subgroup_iff {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (N : Subgroup (L ≃ₐ[K] L)) [N.Normal] (q : IdeleClassGroup L) :
    (∀ σ : ↥N, σ.1 • q = q) ↔
      (∀ τ : L ≃ₐ[↥(IntermediateField.fixedField N)] L, τ • q = q) := by
  constructor
  · intro h τ
    have h1 := h ((IntermediateField.subgroupEquivAlgEquiv N).symm τ)
    have h2 : ((((IntermediateField.subgroupEquivAlgEquiv N).symm τ : ↥N).1 : L ≃ₐ[K] L)) =
        AlgEquiv.restrictScalars K τ := by
      rw [← MulEquiv.apply_symm_apply (IntermediateField.subgroupEquivAlgEquiv N) τ]
      ext y
      rfl
    rw [h2] at h1
    exact h1
  · intro h σ
    have h1 := h ((IntermediateField.subgroupEquivAlgEquiv N) σ)
    have h2 : AlgEquiv.restrictScalars K ((IntermediateField.subgroupEquivAlgEquiv N) σ) = σ.1 := by
      ext y
      rfl
    have h3 : AlgEquiv.restrictScalars K
        ((IntermediateField.subgroupEquivAlgEquiv N) σ) • q = q := h1
    rw [h2] at h3
    exact h3

/-! ### The local algebra maps over an intermediate field -/

/-- Transport of the local algebra map along an equality of the base place: the maps
`F_vˣ →* L_wˣ` attached to equal places `a`, `b` of the base field correspond under the transport
`h ▸ ·`. -/
lemma localAlgebraMapUnits_cast {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (w : Place L) {a b : Place K} (h : a = b)
    (ha : Place.LiesOver w a) (hb : Place.LiesOver w b) (y : (Place.localField K a)ˣ) :
    Place.localAlgebraMapUnits w a ha y = Place.localAlgebraMapUnits w b hb (h ▸ y) := by
  cases h
  exact congrArg (fun f => f y) (globalCFT_localAlgebraMapUnits_congr w a ha hb)

/-! ### The naturality of the inclusion of idèle groups under base change -/

/-- **The inclusion of idèle groups is compatible with the action of `Gal(L/K)`** in the following
sense: for a tower of number fields `K ⊆ F ⊆ L`, an automorphism `τ : L ≃ₐ[K] L` and the inclusion
`φ : 𝕀 F →* 𝕀 L` whose components are the canonical local algebra maps, one has
`τ • φ x = φ ((τ|_F) • x)`, where `τ|_F` is the induced automorphism of the intermediate field `F`.

This is the naturality of the idèle inclusion under the base change `K → F`. -/
lemma ideleInclusion_smul_restrict {K F L : Type*} [Field K] [NumberField K] [Field F]
    [NumberField F] [Field L] [NumberField L] [Algebra K F] [Algebra F L] [Algebra K L]
    [IsScalarTower K F L] [Normal K F] [FiniteDimensional F L]
    (u : Place L → Place F) (hu : ∀ w : Place L, Place.LiesOver w (u w))
    (φ : 𝕀[F] →* 𝕀[L])
    (hφ : ∀ (x : 𝕀[F]) (w : Place L),
      φ x w = Place.localAlgebraMapUnits w (u w) (hu w) (x (u w)))
    (τ : L ≃ₐ[K] L) (x : 𝕀[F]) :
    τ • φ x = φ ((AlgEquiv.restrictNormalHom F τ) • x) := by
  refine Idele.ext fun w => ?_
  set A : F ≃ₐ[K] F := AlgEquiv.restrictNormalHom F τ with hAdef
  have hA : ∀ y : F, algebraMap F L (A y) = τ (algebraMap F L y) := by
    intro y
    have h := AlgEquiv.restrictNormal_commutes (χ := τ) (E := F) y
    simpa [A, AlgEquiv.restrictNormalHom] using h
  have hAinv : ∀ y : F, algebraMap F L (A⁻¹ y) = τ⁻¹ (algebraMap F L y) := by
    intro y
    have h := hA (A⁻¹ y)
    have h1 : A (A⁻¹ y) = y := AlgEquiv.apply_symm_apply A y
    rw [h1] at h
    rw [h]
    exact (AlgEquiv.symm_apply_apply τ ((algebraMap F L) (A⁻¹ y))).symm
  have hlies : Place.LiesOver (τ⁻¹ • w) (A⁻¹ • u w) :=
    liesOver_smul_of_restrict (τ := τ⁻¹) (A := A⁻¹) hAinv (hu w)
  have hreindex : A⁻¹ • u w = u (τ⁻¹ • w) :=
    globalCFT_liesOver_unique hlies (hu (τ⁻¹ • w))
  have hcomp : Place.localAlgebraMapUnits (τ⁻¹ • w) (u (τ⁻¹ • w)) (hu (τ⁻¹ • w))
        (x (u (τ⁻¹ • w))) =
      Place.localAlgebraMapUnits (τ⁻¹ • w) (A⁻¹ • u w) hlies (x (A⁻¹ • u w)) := by
    rw [globalCFT_idele_component_transport x hreindex]
    exact (localAlgebraMapUnits_cast (τ⁻¹ • w) hreindex hlies (hu (τ⁻¹ • w))
      (x (A⁻¹ • u w))).symm
  set a : (Place.localField F (u w))ˣ :=
    Units.map (Place.localRingEquiv A⁻¹ (u w)).symm.toMonoidHom (x (A⁻¹ • u w)) with hadef
  have hunit : Units.map (Place.localRingEquiv A⁻¹ (u w)).toMonoidHom a = x (A⁻¹ • u w) := by
    rw [hadef]
    apply Units.ext
    simp only [Units.coe_map]
    show (Place.localRingEquiv A⁻¹ (u w)) ((Place.localRingEquiv A⁻¹ (u w)).symm _) = _
    exact (Place.localRingEquiv A⁻¹ (u w)).apply_symm_apply _
  have hLC := localRingEquiv_localAlgebraMapUnits_of_restrict (τ := τ⁻¹) (A := A⁻¹) hAinv
    (h := hu w) (h' := hlies) a
  rw [hunit] at hLC
  rw [Idele.smul_apply, hφ x (τ⁻¹ • w), hφ (A • x) w, Idele.smul_apply A x (u w)]
  rw [hcomp, ← hLC]
  apply Units.ext
  simp only [Units.coe_map]
  show (Place.localRingEquiv τ⁻¹ w).symm ((Place.localRingEquiv τ⁻¹ w) _) = _
  exact (Place.localRingEquiv τ⁻¹ w).symm_apply_apply _

/-! ### An isomorphism criterion for representations -/

/-- **A general criterion for an isomorphism of representations.**  A `k`-linear isomorphism of the
underlying modules of two representations which intertwines the actions is an isomorphism of
representations. -/
lemma Rep.nonempty_iso_of_intertwining {k : Type} [CommRing k] {G : Type} [Group G]
    (A B : Rep k G) (e : A.V ≃ₗ[k] B.V)
    (h : ∀ g, e.toLinearMap ∘ₗ A.ρ g = B.ρ g ∘ₗ e.toLinearMap) :
    Nonempty (A ≅ B) := by
  have h' : ∀ g, e.symm.toLinearMap ∘ₗ B.ρ g = A.ρ g ∘ₗ e.symm.toLinearMap := by
    intro g
    apply LinearMap.ext
    intro x
    have h1 := LinearMap.congr_fun (h g) (e.symm x)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h1
    rw [LinearEquiv.apply_symm_apply] at h1
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← h1, LinearEquiv.symm_apply_apply]
  refine ⟨Iso.mk (Rep.ofHom ⟨e.toLinearMap, h⟩) (Rep.ofHom ⟨e.symm.toLinearMap, h'⟩) ?_ ?_⟩
  · apply Rep.hom_ext
    rw [Rep.hom_comp, Rep.hom_id]
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    show e.symm.toLinearMap (e.toLinearMap x) = x
    exact e.symm_apply_apply x
  · apply Rep.hom_ext
    rw [Rep.hom_comp, Rep.hom_id]
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    show e.toLinearMap (e.symm.toLinearMap x) = x
    exact e.apply_symm_apply x

/-! ### The isomorphism of the invariants with the idèle class group of the fixed field -/

/-- **The main result.**  For a finite Galois extension `L / K` of number fields and a normal
subgroup `N ≤ Gal(L/K)`, the invariants of `C_L` under `N` are the idèle class group of the fixed
field `L^N`, compatibly with the action of `Gal(L/K) ⧸ N ≅ Gal(L^N/K)`. -/
theorem repIso_quotientToInvariants_fixedField {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (N : Subgroup (L ≃ₐ[K] L)) [N.Normal] :
    Nonempty ((NK.GlobalCFT.IdeleClassGroup.rep K L).quotientToInvariants N ≅
      Rep.res (IsGalois.normalAutEquivQuotient N).toMonoidHom
        (NK.GlobalCFT.IdeleClassGroup.rep K (IntermediateField.fixedField N))) := by
  classical
  let F' := ↥(IntermediateField.fixedField N)
  haveI : NumberField F' := inferInstance
  haveI : IsGalois K F' := inferInstance
  haveI : FiniteDimensional F' L := inferInstance
  haveI : IsGalois F' L := inferInstance
  haveI : Normal K F' := inferInstance
  -- the inclusion of idèle class groups `C_{L^N} →* C_L`
  let u : Place L → Place F' :=
    fun w => Classical.choose (globalCFT_exists_placeUnder (K := F') (L := L) w)
  have hu : ∀ w : Place L, Place.LiesOver w (u w) :=
    fun w => Classical.choose_spec (globalCFT_exists_placeUnder (K := F') (L := L) w)
  obtain ⟨φ, hφ⟩ := globalCFT_ideleInclusion_exists (K := F') (L := L) u hu
  obtain ⟨ψ, hψ⟩ := globalCFT_ideleClassGroup_inclusion_exists (K := F') (L := L) u hu φ hφ
  have hψinj : Function.Injective ψ :=
    globalCFT_ideleClassGroup_inclusion_injective (K := F') (L := L) u hu φ hφ ψ hψ
  have hψrange : ∀ q : IdeleClassGroup L,
      (∀ τ : L ≃ₐ[F'] L, τ • q = q) ↔ q ∈ ψ.range :=
    fun q => globalCFT_invariants_ideleClassGroup (K := F') (L := L) u hu φ hφ ψ hψ q
  have hInv : ∀ q : IdeleClassGroup L, (∀ σ : ↥N, σ.1 • q = q) ↔ q ∈ ψ.range := by
    intro q
    rw [forall_smul_eq_self_subgroup_iff N q]
    exact hψrange q
  -- the naturality of the inclusion under base change
  have hL0 : ∀ (τ : L ≃ₐ[K] L) (x : Idele F'),
      τ • φ x = φ ((AlgEquiv.restrictNormalHom F' τ) • x) :=
    fun τ x => ideleInclusion_smul_restrict u hu φ hφ τ x
  have hL1 : ∀ (σ : L ≃ₐ[K] L) (y : IdeleClassGroup F'),
      σ • ψ y = ψ ((IsGalois.normalAutEquivQuotient N) (σ : (L ≃ₐ[K] L) ⧸ N) • y) := by
    intro σ y
    obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective F' y
    rw [hψ x]
    rw [show σ • IdeleClassGroup.mk L (φ x) = IdeleClassGroup.mk L (σ • φ x)
      from IdeleClassGroup.smul_mk σ (φ x)]
    rw [show (IsGalois.normalAutEquivQuotient N) (σ : (L ≃ₐ[K] L) ⧸ N) • IdeleClassGroup.mk F' x
        = IdeleClassGroup.mk F' ((IsGalois.normalAutEquivQuotient N) (σ : (L ≃ₐ[K] L) ⧸ N) • x)
      from IdeleClassGroup.smul_mk _ x]
    rw [hψ]
    congr 1
    rw [IsGalois.normalAutEquivQuotient_apply]
    exact hL0 σ x
  let A := (IdeleClassGroup.rep K L).quotientToInvariants N
  let B := Rep.res (IsGalois.normalAutEquivQuotient N).toMonoidHom (IdeleClassGroup.rep K F')
  -- the underlying additive map `(C_L)^N → C_{L^N}`
  have zero_lem : Additive.ofMul (ψ (Additive.toMul (0 : Additive (IdeleClassGroup F'))))
      = (0 : Additive (IdeleClassGroup L)) := by
    rw [toMul_zero, map_one, ofMul_one]
  have add_lem : ∀ (a b : Additive (IdeleClassGroup F')),
      Additive.ofMul (ψ (Additive.toMul (a + b)))
        = Additive.ofMul (ψ (Additive.toMul a)) + Additive.ofMul (ψ (Additive.toMul b)) :=
    fun a b => by rw [toMul_add, map_mul, ofMul_mul]
  let fwd : B.V →+ A.V :=
    { toFun := fun y => ⟨Additive.ofMul (ψ (Additive.toMul (y : Additive (IdeleClassGroup F')))), by
        intro σ
        show (IdeleClassGroup.rep K L).ρ σ.1
            (Additive.ofMul (ψ (Additive.toMul (y : Additive (IdeleClassGroup F')))))
          = Additive.ofMul (ψ (Additive.toMul (y : Additive (IdeleClassGroup F'))))
        rw [show (IdeleClassGroup.rep K L).ρ σ.1
              (Additive.ofMul (ψ (Additive.toMul (y : Additive (IdeleClassGroup F')))))
            = Additive.ofMul (σ.1 • ψ (Additive.toMul (y : Additive (IdeleClassGroup F'))))
            from rfl]
        congr 1
        exact (hInv (ψ (Additive.toMul (y : Additive (IdeleClassGroup F'))))).mpr
          ⟨Additive.toMul (y : Additive (IdeleClassGroup F')), rfl⟩ σ⟩
      map_zero' := by
        apply Subtype.ext
        exact zero_lem
      map_add' := by
        intro y₁ y₂
        apply Subtype.ext
        exact add_lem (y₁ : Additive (IdeleClassGroup F')) (y₂ : Additive (IdeleClassGroup F')) }
  have hfwd_inj : Function.Injective fwd := by
    intro y₁ y₂ h
    have h' : Additive.ofMul (ψ (Additive.toMul (y₁ : Additive (IdeleClassGroup F'))))
        = Additive.ofMul (ψ (Additive.toMul (y₂ : Additive (IdeleClassGroup F')))) :=
      congrArg Subtype.val h
    have h'' : ψ (Additive.toMul (y₁ : Additive (IdeleClassGroup F')))
        = ψ (Additive.toMul (y₂ : Additive (IdeleClassGroup F'))) := Additive.ofMul.injective h'
    have h''' : Additive.toMul (y₁ : Additive (IdeleClassGroup F'))
        = Additive.toMul (y₂ : Additive (IdeleClassGroup F')) := hψinj h''
    exact Additive.toMul.injective h'''
  have hfwd_surj : Function.Surjective fwd := by
    intro x
    let xt : IdeleClassGroup L := Additive.toMul (x.val : Additive (IdeleClassGroup L))
    have hx : ∀ σ : ↥N, σ.1 • xt = xt := by
      intro σ
      have h2 : (IdeleClassGroup.rep K L).ρ σ.1 x.val = x.val := x.2 σ
      have h4 : (IdeleClassGroup.rep K L).ρ σ.1 x.val = Additive.ofMul (σ.1 • xt) := rfl
      rw [h4] at h2
      have h5 : (x.val : Additive (IdeleClassGroup L)) = Additive.ofMul xt :=
        (ofMul_toMul (x.val : Additive (IdeleClassGroup L))).symm
      rw [h5] at h2
      exact Additive.ofMul.injective h2
    obtain ⟨y, hy⟩ := (hInv xt).mp hx
    refine ⟨Additive.ofMul y, ?_⟩
    apply Subtype.ext
    show Additive.ofMul (ψ (Additive.toMul (Additive.ofMul y : Additive (IdeleClassGroup F'))))
      = (x.val : Additive (IdeleClassGroup L))
    rw [toMul_ofMul, hy]
    exact ofMul_toMul (x.val : Additive (IdeleClassGroup L))
  have hbij : Function.Bijective fwd := ⟨hfwd_inj, hfwd_surj⟩
  let Φ : B.V ≃+ A.V := AddEquiv.ofBijective fwd hbij
  have hΦy : ∀ y : B.V, (Φ y).val
      = Additive.ofMul (ψ (Additive.toMul (y : Additive (IdeleClassGroup F')))) := by
    intro y
    rw [show (Φ y).val = (fwd y).val from rfl]
    rfl
  -- the equivariance of `Φ`
  have hint : ∀ (g : (L ≃ₐ[K] L) ⧸ N) (y : B.V), Φ (B.ρ g y) = A.ρ g (Φ y) := by
    intro g y
    obtain ⟨σ, rfl⟩ := QuotientGroup.mk'_surjective N g
    let ys : IdeleClassGroup F' := Additive.toMul (y : Additive (IdeleClassGroup F'))
    have hT : Additive.toMul (B.ρ (QuotientGroup.mk' N σ) y : Additive (IdeleClassGroup F'))
        = (AlgEquiv.restrictNormalHom F' σ) • ys := by
      rw [show Additive.toMul (B.ρ (QuotientGroup.mk' N σ) y : Additive (IdeleClassGroup F'))
          = Additive.toMul (Additive.ofMul ((AlgEquiv.restrictNormalHom F' σ) • ys)) from rfl]
      rw [toMul_ofMul]
    have hL : (Φ (B.ρ (QuotientGroup.mk' N σ) y)).val
        = Additive.ofMul (ψ ((AlgEquiv.restrictNormalHom F' σ) • ys)) :=
      (hΦy _).trans (congrArg (fun z => Additive.ofMul (ψ z)) hT)
    have hR : (A.ρ (QuotientGroup.mk' N σ) (Φ y)).val = Additive.ofMul (σ • ψ ys) := by
      rw [show (A.ρ (QuotientGroup.mk' N σ) (Φ y)).val
          = (IdeleClassGroup.rep K L).ρ σ (Φ y).val from rfl]
      rw [hΦy]
      rfl
    apply Subtype.ext
    rw [hL, hR, hL1 σ ys]
    rw [show (IsGalois.normalAutEquivQuotient N) (σ : (L ≃ₐ[K] L) ⧸ N)
        = AlgEquiv.restrictNormalHom F' σ from IsGalois.normalAutEquivQuotient_apply N σ]
  refine (Rep.nonempty_iso_of_intertwining B A Φ.toIntLinearEquiv ?_).map Iso.symm
  intro g
  apply LinearMap.ext
  intro y
  exact hint g y

end NK.HassePrinciple
