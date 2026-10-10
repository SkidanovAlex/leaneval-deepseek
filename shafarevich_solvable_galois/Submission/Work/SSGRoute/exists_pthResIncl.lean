import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Submission.Work.SSGRoute.kummer_level_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Restriction of the Kummer level representations along a level inclusion `L ⊆ L'`

For number fields `k ⊆ L ⊆ L'` with `L/k` and `L'/k` finite Galois, this file constructs the
natural morphisms of `Gal(L'/k)`-modules

  `τ₂ : Lˣ → L'ˣ`,   `τ₃ : (Lˣ)^p → (L'ˣ)^p`

given by the inclusions `L ⊆ L'`, and shows that `τ₃` is the restriction of `τ₂` along the
`p`-th power maps.  Concretely, `exists_pthResIncl` produces `τ₂` and `τ₃` together with

* `τ₂.hom (Additive.ofMul u) = Additive.ofMul (Units.map (algebraMap L L') u)`;
* `τ₃.hom (⟨p • ofMul u, _⟩) = ⟨p • ofMul (Units.map (algebraMap L L') u), _⟩`;
* `τ₃.hom ((pthMapX k L p).hom (ofMul u))
     = (pthMapX k L' p).hom (τ₂.hom (ofMul u))`.

The main content is the Galois-equivariance of `τ₂`, which is exactly
`AlgEquiv.restrictNormal_commutes`.
-/

open CategoryTheory SSGRoute.PTExt

namespace Work.SSGRoute

set_option linter.unusedSectionVars false

noncomputable section

/-- The `Coeff`-linear map underlying the inclusion `Lˣ → L'ˣ`, i.e. `u ↦ algebraMap L L' u`. -/
noncomputable def exists_pthResIncl_unitsLin
    (k : Type) [Field k] [NumberField k] (L : Type) [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (L' : Type) [Field L'] [NumberField L'] [Algebra k L'] [FiniteDimensional k L'] [IsGalois k L']
    [Algebra L L'] [IsScalarTower k L L'] :
    Additive Lˣ →ₗ[Coeff] Additive L'ˣ where
  toFun := fun x => Additive.ofMul (Units.map (algebraMap L L').toMonoidHom (Additive.toMul x))
  map_add' := fun a b => by rw [toMul_add, map_mul, ofMul_mul]
  map_smul' := fun c x => by
    obtain ⟨z⟩ := c
    rw [ULift.smul_def, toMul_zsmul, map_zpow, ofMul_zpow]
    rfl

@[simp]
theorem exists_pthResIncl_unitsLin_ofMul
    (k : Type) [Field k] [NumberField k] (L : Type) [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (L' : Type) [Field L'] [NumberField L'] [Algebra k L'] [FiniteDimensional k L'] [IsGalois k L']
    [Algebra L L'] [IsScalarTower k L L'] (u : Lˣ) :
    exists_pthResIncl_unitsLin k L L' (Additive.ofMul u)
      = Additive.ofMul (Units.map (algebraMap L L').toMonoidHom u) := rfl

/-- The key Galois-equivariance of the inclusion `Lˣ → L'ˣ`: restriction of `γ` to `L` followed by
the inclusion equals the inclusion followed by `γ`. -/
theorem exists_pthResIncl_unitsLin_smul
    (k : Type) [Field k] [NumberField k] (L : Type) [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (L' : Type) [Field L'] [NumberField L'] [Algebra k L'] [FiniteDimensional k L'] [IsGalois k L']
    [Algebra L L'] [IsScalarTower k L L'] (γ : L' ≃ₐ[k] L') (x : Additive Lˣ) :
    exists_pthResIncl_unitsLin k L L' ((galRes k L L' γ) • x)
      = γ • exists_pthResIncl_unitsLin k L L' x := by
  have hkey : ∀ u : Lˣ,
      Units.map (algebraMap L L').toMonoidHom (Units.map (galRes k L L' γ) u)
        = Units.map γ (Units.map (algebraMap L L').toMonoidHom u) := by
    intro u
    apply Units.ext
    rw [Units.coe_map, Units.coe_map, Units.coe_map]
    exact AlgEquiv.restrictNormal_commutes γ L (u : L)
  rw [show x = Additive.ofMul (Additive.toMul x) from
        (Equiv.apply_symm_apply Additive.ofMul x).symm]
  rw [show (galRes k L L' γ) • Additive.ofMul (Additive.toMul x)
        = Additive.ofMul (Units.map (galRes k L L' γ) (Additive.toMul x)) from rfl]
  rw [show γ • exists_pthResIncl_unitsLin k L L' (Additive.ofMul (Additive.toMul x))
        = Additive.ofMul
            (Units.map γ (Units.map (algebraMap L L').toMonoidHom (Additive.toMul x)))
        from rfl]
  rw [exists_pthResIncl_unitsLin_ofMul, hkey]

/-- **`τ₂`**: the inclusion `Lˣ → L'ˣ` as a morphism of `Gal(L'/k)`-modules, where `Lˣ` carries
the `Gal(L'/k)`-action restricted along `galRes k L L'`. -/
noncomputable def exists_pthResIncl_units
    (k : Type) [Field k] [NumberField k] (L : Type) [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (L' : Type) [Field L'] [NumberField L'] [Algebra k L'] [FiniteDimensional k L'] [IsGalois k L']
    [Algebra L L'] [IsScalarTower k L L'] :
    Rep.res (galRes k L L') (levelUnits k L) ⟶ levelUnits k L' :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (exists_pthResIncl_unitsLin k L L')
    (fun γ x => exists_pthResIncl_unitsLin_smul k L L' γ x))

@[simp]
theorem exists_pthResIncl_units_hom_ofMul
    (k : Type) [Field k] [NumberField k] (L : Type) [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (L' : Type) [Field L'] [NumberField L'] [Algebra k L'] [FiniteDimensional k L'] [IsGalois k L']
    [Algebra L L'] [IsScalarTower k L L'] (u : Lˣ) :
    (exists_pthResIncl_units k L L').hom (Additive.ofMul u)
      = Additive.ofMul (Units.map (algebraMap L L').toMonoidHom u) := rfl

/-- The `Coeff`-linear map underlying `τ₃`, obtained by restricting `τ₂` to `p`-th powers. -/
noncomputable def exists_pthResIncl_pthLin
    (k : Type) [Field k] [NumberField k] (L : Type) [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (L' : Type) [Field L'] [NumberField L'] [Algebra k L'] [FiniteDimensional k L'] [IsGalois k L']
    [Algebra L L'] [IsScalarTower k L L'] (p : ℕ) :
    ↥(pthSubX L p) →ₗ[Coeff] ↥(pthSubX L' p) :=
  LinearMap.codRestrict (pthSubX L' p)
    ((exists_pthResIncl_unitsLin k L L').comp (Submodule.subtype (pthSubX L p)))
    (fun x => by
      obtain ⟨u, hu⟩ := (mem_pthSubX_iff L p (x : Additive Lˣ)).mp x.2
      refine (mem_pthSubX_iff L' p
        (exists_pthResIncl_unitsLin k L L' (x : Additive Lˣ))).mpr
        ⟨Units.map (algebraMap L L').toMonoidHom u, ?_⟩
      rw [← hu, map_nsmul, exists_pthResIncl_unitsLin_ofMul])

/-- The key Galois-equivariance of `τ₃`, deduced from that of `τ₂`. -/
theorem exists_pthResIncl_pthLin_smul
    (k : Type) [Field k] [NumberField k] (L : Type) [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (L' : Type) [Field L'] [NumberField L'] [Algebra k L'] [FiniteDimensional k L'] [IsGalois k L']
    [Algebra L L'] [IsScalarTower k L L'] (p : ℕ) (γ : L' ≃ₐ[k] L') (x : ↥(pthSubX L p)) :
    exists_pthResIncl_pthLin k L L' p ((galRes k L L' γ) • x)
      = γ • exists_pthResIncl_pthLin k L L' p x := by
  apply Subtype.ext
  change exists_pthResIncl_unitsLin k L L' ((galRes k L L' γ) • (x : Additive Lˣ))
      = γ • exists_pthResIncl_unitsLin k L L' (x : Additive Lˣ)
  exact exists_pthResIncl_unitsLin_smul k L L' γ (x : Additive Lˣ)

/-- **`τ₃`**: the map `(Lˣ)^p → (L'ˣ)^p` as a morphism of `Gal(L'/k)`-modules. -/
noncomputable def exists_pthResIncl_pth
    (k : Type) [Field k] [NumberField k] (L : Type) [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (L' : Type) [Field L'] [NumberField L'] [Algebra k L'] [FiniteDimensional k L'] [IsGalois k L']
    [Algebra L L'] [IsScalarTower k L L'] (p : ℕ) :
    Rep.res (galRes k L L') (pthRepX k L p) ⟶ pthRepX k L' p :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (exists_pthResIncl_pthLin k L L' p)
    (fun γ x => exists_pthResIncl_pthLin_smul k L L' p γ x))

theorem exists_pthResIncl (k : Type) [Field k] [NumberField k] (L : Type) [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (L' : Type) [Field L'] [NumberField L'] [Algebra k L'] [FiniteDimensional k L'] [IsGalois k L']
    [Algebra L L'] [IsScalarTower k L L'] (p : ℕ) [Fact p.Prime] :
    ∃ (τ₂ : Rep.res (SSGRoute.PTExt.galRes k L L') (Work.SSGRoute.levelUnits k L) ⟶ Work.SSGRoute.levelUnits k L')
      (τ₃ : Rep.res (SSGRoute.PTExt.galRes k L L') (Work.SSGRoute.pthRepX k L p) ⟶ Work.SSGRoute.pthRepX k L' p),
      (∀ u : Lˣ, τ₂.hom (Additive.ofMul u)
        = Additive.ofMul (Units.map (algebraMap L L').toMonoidHom u)) ∧
      (∀ u : Lˣ, τ₃.hom ⟨(p:ℕ) • Additive.ofMul u, LinearMap.mem_range_self _ _⟩
        = ⟨(p:ℕ) • Additive.ofMul (Units.map (algebraMap L L').toMonoidHom u),
           LinearMap.mem_range_self _ _⟩) ∧
      (∀ (u : Lˣ), τ₃.hom ((Work.SSGRoute.pthMapX k L p).hom (Additive.ofMul u))
        = (Work.SSGRoute.pthMapX k L' p).hom (τ₂.hom (Additive.ofMul u))) := by
  refine ⟨exists_pthResIncl_units k L L', exists_pthResIncl_pth k L L' p, ?_, ?_, ?_⟩
  · intro u
    rfl
  · intro u
    apply Subtype.ext
    change exists_pthResIncl_unitsLin k L L' ((p:ℕ) • Additive.ofMul u)
        = (p:ℕ) • Additive.ofMul (Units.map (algebraMap L L').toMonoidHom u)
    rw [map_nsmul, exists_pthResIncl_unitsLin_ofMul]
  · intro u
    apply Subtype.ext
    change exists_pthResIncl_unitsLin k L L' ((p:ℕ) • Additive.ofMul u)
        = (p:ℕ) • Additive.ofMul (Units.map (algebraMap L L').toMonoidHom u)
    rw [map_nsmul, exists_pthResIncl_unitsLin_ofMul]

end

end Work.SSGRoute
