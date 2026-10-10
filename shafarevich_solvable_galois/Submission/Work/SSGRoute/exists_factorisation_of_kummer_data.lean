import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Submission.Work.SSGRoute.kummer_level_defs

namespace Work.SSGRoute

open CategoryTheory SSGRoute.PTExt

set_option linter.unusedVariables false

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

/-!
# Factoring Kummer data through a level (`Work.SSGRoute.exists_factorisation_of_kummer_data`)

The main result is `exists_factorisation_of_kummer_data` below.

## Mathematics

We are given a tower `k ⊆ L ⊆ L'` of number fields, `L'/k` and `L/k` finite Galois, a prime `p`,
an element `x ∈ Lˣ` which becomes a `p`-th power upstairs: `algebraMap x = y ^ p` for some
`y ∈ L'ˣ`, and a morphism `f : I ⟶ (Lˣ)^p` of `Gal(L/k)`-representations whose attached crossed
homomorphism (the `derivCochain` of the augmentation resolution) is the Kummer cocycle of `x`,
`σ ↦ σ • x - x`.  Given also `τ₃ : res (Lˣ)^p ⟶ (L'ˣ)^p` compatible with `algebraMap` on `p`-th
powers, we must exhibit a `Gal(L'/k)`-morphism `k'` from the (restricted) regular representation
`ℤ[Gal(L/k)]` to `(L'ˣ)^p` extending `τ₃ ∘ f` along `I ↪ ℤ[Gal(L/k)]`.

The extension is the `ℤ`-linear map sending the basis element `γ` to
`m + τ₃(f(γ - 1))`, where `m = p • y ∈ (L'ˣ)^p`.  The point is that the crossed homomorphism
`σ ↦ σ • m - m` on `Gal(L'/k)` equals `τ₃(f(φσ - 1))` with `φ = galRes`, which is the very
condition that makes the above assignment `Gal(L'/k)`-equivariant (the extension lemma
`exists_lift_regRep`), and it rests on `algebraMap(x^σ/x) = (σ • y)^p / y^p`.

## Contents

* `mk_single_one`, `ext_ebas`: a `ℤ`-linear map out of `ℤ[G]` is determined by its values on the
  basis elements `ebas γ = γ`;
* `cocycleLin_ebas'`: the value of `cocycleLin` on `ebas γ` (with the module instance of the
  ambient context, unlike `ExtH1.cocycleLin_ebas`);
* `exists_lift_regRep`: the equivariant extension of a function `G → M` satisfying the
  "cocycle" compatibility;
* `map_galRes_smul`: `algebraMap` intertwines the `Gal(L/k)`-action on `Lˣ` (restricted along
  `galRes`) with the `Gal(L'/k)`-action on `L'ˣ`;
* `lin_ext_augDiff`: `ℤ`-linear maps on the augmentation ideal agreeing on `γ - 1` are equal;
* `exists_factorisation_of_kummer_data`: the requested lemma.
-/

/-- `ℤ[G] →ₗ N`-linear maps are determined by their values on the basis elements `γ`, phrased at
the level of the coefficient linear equivalence `ℤ[G] ≃ (G →₀ ℤ)`. -/
lemma mk_single_one {G : Type} [Group G] (a : G) :
    (MonoidAlgebra.coeffLinearEquiv (R := Coeff) (S := Coeff)).symm (Finsupp.single a 1)
      = ExtH1.ebas G a := by
  apply (MonoidAlgebra.coeffLinearEquiv (R := Coeff) (S := Coeff)).symm_apply_eq.mpr
  rw [show ExtH1.ebas G a = MonoidAlgebra.single a 1 from rfl, MonoidAlgebra.coeffLinearEquiv_apply,
    MonoidAlgebra.coeff_single]

/-- Two `ℤ`-linear maps `ℤ[G] →ₗ N` agreeing on the basis elements `ebas γ = γ` are equal. -/
lemma ext_ebas {G : Type} [Group G] {N : Type} [AddCommGroup N] [Module Coeff N]
    {f g : MonoidAlgebra Coeff G →ₗ[Coeff] N}
    (h : ∀ γ, f (ExtH1.ebas G γ) = g (ExtH1.ebas G γ)) : f = g := by
  have hcomp : f.comp (MonoidAlgebra.coeffLinearEquiv (R := Coeff) (S := Coeff)).symm.toLinearMap
      = g.comp (MonoidAlgebra.coeffLinearEquiv (R := Coeff) (S := Coeff)).symm.toLinearMap := by
    refine Finsupp.basisSingleOne.ext ?_
    intro a
    change f ((MonoidAlgebra.coeffLinearEquiv (R := Coeff) (S := Coeff)).symm (Finsupp.single a 1))
       = g ((MonoidAlgebra.coeffLinearEquiv (R := Coeff) (S := Coeff)).symm (Finsupp.single a 1))
    rw [mk_single_one a, h a]
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun hcomp ((MonoidAlgebra.coeffLinearEquiv (R := Coeff) (S := Coeff)) x)
  simpa using hx

/-- `cocycleLin` on a basis element, with the `Module Coeff N` instance of the ambient context
(so that it applies when `N` is a `Rep` carrier carrying its own structure). -/
lemma cocycleLin_ebas' {G : Type} [Group G] {N : Type} [AddCommGroup N] [Module Coeff N]
    (v : G → N) (γ : G) :
    (ExtH1.cocycleLin G N v) (ExtH1.ebas G γ) = v γ := by
  rw [ExtH1.cocycleLin, LinearMap.comp_apply, LinearEquiv.coe_coe,
    MonoidAlgebra.coeffLinearEquiv_apply]
  rw [show (ExtH1.ebas G γ).coeff = Finsupp.single γ 1 from rfl]
  rw [Finsupp.linearCombination_single]
  exact @one_smul Coeff N _ ((inferInstance : Module Coeff N)).toMulAction (v γ)

/-- **Extension of a compatible function to an equivariant map out of the regular
representation.**  Given `φ : H →* G`, a `H`-representation `M` and `v : G → M` with
`M.ρ h (v g) = v (φ h * g)`, there is a morphism `res φ ℤ[G] ⟶ M` sending `γ ↦ v γ`. -/
lemma exists_lift_regRep {G H : Type} [Group G] [Group H] (φ : H →* G) (M : Rep.{0} Coeff H)
    (v : G → M) (hv : ∀ (h : H) (g : G), M.ρ h (v g) = v (φ h * g)) :
    ∃ k : Rep.res φ (ExtH1.regRep G) ⟶ M, ∀ g, k.hom (ExtH1.ebas G g) = v g := by
  refine ⟨Rep.ofHom { toLinearMap := ExtH1.cocycleLin G M v, isIntertwining' := ?_ }, ?_⟩
  · intro h
    apply ext_ebas
    intro γ
    simp only [LinearMap.comp_apply]
    rw [cocycleLin_ebas' v γ]
    rw [show ((Rep.res φ (ExtH1.regRep G)).ρ h (ExtH1.ebas G γ)) = ExtH1.ebas G (φ h * γ) from by
      rw [show (Rep.res φ (ExtH1.regRep G)).ρ h = (ExtH1.regRep G).ρ (φ h) from rfl,
        ExtH1.regRep_ρ_ebas]]
    rw [cocycleLin_ebas' v (φ h * γ)]
    exact (hv h γ).symm
  · intro g
    rw [Rep.ofHom_apply]
    exact cocycleLin_ebas' v g

/-- `algebraMap` intertwines the `Gal(L/k)`-action on `Lˣ` (viewed through `galRes`) with the
`Gal(L'/k)`-action on `L'ˣ`. -/
lemma map_galRes_smul (k : Type) [Field k] [NumberField k] (L : Type) [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (L' : Type) [Field L'] [NumberField L'] [Algebra k L'] [FiniteDimensional k L'] [IsGalois k L']
    [Algebra L L'] [IsScalarTower k L L'] (σ : L' ≃ₐ[k] L') (z : Lˣ) :
    Units.map (algebraMap L L').toMonoidHom ((galRes k L L' σ) • z)
      = σ • (Units.map (algebraMap L L').toMonoidHom z) := by
  have hhom : (algebraMap L L').toMonoidHom.comp (galRes k L L' σ).toMonoidHom
      = σ.toMonoidHom.comp (algebraMap L L').toMonoidHom := by
    ext w
    exact AlgEquiv.restrictNormal_commutes σ L w
  apply Units.ext
  rw [show ((galRes k L L' σ) • z : Lˣ) = Units.map (galRes k L L' σ).toMonoidHom z from rfl]
  rw [show (σ • (Units.map (algebraMap L L').toMonoidHom z) : L'ˣ)
        = Units.map σ.toMonoidHom (Units.map (algebraMap L L').toMonoidHom z) from rfl]
  rw [Units.coe_map, Units.coe_map, Units.coe_map, Units.coe_map]
  exact congrFun (congrArg (fun f : L →* L' => (f : L → L')) hhom) ↑z

/-- `ℤ`-linear maps on the augmentation ideal `I` of `ℤ[G]` agreeing on the elements `γ - 1`
are equal. -/
lemma lin_ext_augDiff {G : Type} [Group G] {M : Type} [AddCommGroup M] [Module Coeff M]
    (f g : ↥(ExtH1.augI G) →ₗ[Coeff] M)
    (h : ∀ γ, f (ExtH1.augDiff G γ) = g (ExtH1.augDiff G γ)) : f = g := by
  apply LinearMap.ext
  intro x
  rw [← ExtH1.sum_coeff_smul_augDiff G x, Finsupp.sum]
  rw [map_sum, map_sum]
  exact Finset.sum_congr rfl (fun γ _ => by rw [LinearMap.map_smul, LinearMap.map_smul, h γ])

theorem exists_factorisation_of_kummer_data
    (k : Type) [Field k] [NumberField k] (L : Type) [Field L] [NumberField L] [Algebra k L]
    [FiniteDimensional k L] [IsGalois k L]
    (L' : Type) [Field L'] [NumberField L'] [Algebra k L'] [FiniteDimensional k L'] [IsGalois k L']
    [Algebra L L'] [IsScalarTower k L L'] (p : ℕ) [Fact p.Prime]
    (τ₂ : Rep.res (SSGRoute.PTExt.galRes k L L') (Work.SSGRoute.levelUnits k L) ⟶ Work.SSGRoute.levelUnits k L')
    (τ₃ : Rep.res (SSGRoute.PTExt.galRes k L L') (Work.SSGRoute.pthRepX k L p) ⟶ Work.SSGRoute.pthRepX k L' p)
    (hτ₃ : ∀ u : Lˣ, τ₃.hom ⟨(p:ℕ) • Additive.ofMul u, LinearMap.mem_range_self _ _⟩
        = ⟨(p:ℕ) • Additive.ofMul (Units.map (algebraMap L L').toMonoidHom u),
           LinearMap.mem_range_self _ _⟩)
    (hτ₂ : ∀ u : Lˣ, τ₂.hom (Additive.ofMul u)
        = Additive.ofMul (Units.map (algebraMap L L').toMonoidHom u))
    (f : Work.SSGRoute.ExtH1.augI (L ≃ₐ[k] L) ⟶ Work.SSGRoute.pthRepX k L p)
    (x : Lˣ)
    (hy : ∃ y : L'ˣ, Units.map (algebraMap L L').toMonoidHom x = y ^ p)
    (hφ : ∀ σ : L ≃ₐ[k] L,
      ((Work.SSGRoute.ExtH1.derivCochain (L ≃ₐ[k] L) f σ : ↥(Work.SSGRoute.pthSubX L p)) : Additive Lˣ)
        = σ • (Additive.ofMul x) - Additive.ofMul x) :
    ∃ k' : Rep.res (SSGRoute.PTExt.galRes k L L') (Work.SSGRoute.ExtH1.regRep (L ≃ₐ[k] L)) ⟶ Work.SSGRoute.pthRepX k L' p,
      ∀ z : ↥(Work.SSGRoute.ExtH1.augI (L ≃ₐ[k] L)),
        k'.hom ((Work.SSGRoute.ExtH1.augIncl (L ≃ₐ[k] L)).hom z)
          = τ₃.hom (f.hom z) := by
  obtain ⟨y, hy⟩ := hy
  let m : ↥(pthSubX L' p) := ⟨(p:ℕ) • Additive.ofMul y, LinearMap.mem_range_self _ _⟩
  have hmv : (m : Additive L'ˣ) = (p:ℕ) • Additive.ofMul y := rfl
  let τ3v : (L ≃ₐ[k] L) → ↥(pthSubX L' p) :=
    fun γ => τ₃.hom (f.hom (ExtH1.augDiff (L ≃ₐ[k] L) γ))
  have hτvdef : ∀ γ, τ3v γ = τ₃.hom (f.hom (ExtH1.augDiff (L ≃ₐ[k] L) γ)) := fun γ => rfl
  have ha_val : ∀ σ : L' ≃ₐ[k] L',
      ((σ • m : ↥(pthSubX L' p)) : Additive L'ˣ)
        = (m : Additive L'ˣ) + (τ3v (galRes k L L' σ) : Additive L'ˣ) := by
    intro σ
    set z : ↥(pthSubX L p) := f.hom (ExtH1.augDiff (L ≃ₐ[k] L) (galRes k L L' σ)) with hz
    obtain ⟨u, hu⟩ := (mem_pthSubX_iff L p (z : Additive Lˣ)).mp z.2
    have hzval : (z : Additive Lˣ)
        = ((ExtH1.derivCochain (L ≃ₐ[k] L) f (galRes k L L' σ) : ↥(pthSubX L p)) : Additive Lˣ) := rfl
    have hu1 : (p:ℕ) • Additive.ofMul u
        = (galRes k L L' σ) • Additive.ofMul x - Additive.ofMul x :=
      hu.trans (hzval.trans (hφ (galRes k L L' σ)))
    have hu2 : u ^ p = ((galRes k L L' σ) • x) * x⁻¹ := by
      have h := hu1
      rw [nsmul_ofMul] at h
      rw [show (((galRes k L L' σ) • Additive.ofMul x : Additive Lˣ) - Additive.ofMul x)
          = Additive.ofMul (((galRes k L L' σ) • x) * x⁻¹) from rfl] at h
      exact Additive.ofMul.injective h
    have hσpow : σ • (y ^ p) = (σ • y) ^ p := by
      rw [show (σ • (y^p) : L'ˣ) = Units.map σ.toMonoidHom (y^p) from rfl,
        show (σ • y : L'ˣ) = Units.map σ.toMonoidHom y from rfl, MonoidHom.map_pow]
    have hu3 : (Units.map (algebraMap L L').toMonoidHom u) ^ p = (σ • y) ^ p * (y ^ p)⁻¹ := by
      rw [← MonoidHom.map_pow, hu2, map_mul, map_inv]
      rw [show Units.map (algebraMap L L').toMonoidHom ((galRes k L L' σ) • x)
          = σ • (Units.map (algebraMap L L').toMonoidHom x) from map_galRes_smul k L L' σ x]
      rw [hy, hσpow]
    have hsub : z = (⟨(p:ℕ) • Additive.ofMul u, LinearMap.mem_range_self _ _⟩ : ↥(pthSubX L p)) :=
      Subtype.ext hu.symm
    have hτsub : τ3v (galRes k L L' σ)
        = (⟨(p:ℕ) • Additive.ofMul (Units.map (algebraMap L L').toMonoidHom u),
            LinearMap.mem_range_self _ _⟩ : ↥(pthSubX L' p)) := by
      rw [hτvdef, ← hz, hsub]
      exact hτ₃ u
    rw [show (τ3v (galRes k L L' σ) : Additive L'ˣ)
        = (((⟨(p:ℕ) • Additive.ofMul (Units.map (algebraMap L L').toMonoidHom u),
              LinearMap.mem_range_self _ _⟩ : ↥(pthSubX L' p)) : Additive L'ˣ)) from
      congrArg (fun w : ↥(pthSubX L' p) => (w : Additive L'ˣ)) hτsub]
    rw [show (((⟨(p:ℕ) • Additive.ofMul (Units.map (algebraMap L L').toMonoidHom u),
              LinearMap.mem_range_self _ _⟩ : ↥(pthSubX L' p)) : Additive L'ˣ))
        = (p:ℕ) • Additive.ofMul (Units.map (algebraMap L L').toMonoidHom u) from rfl]
    rw [show ((σ • m : ↥(pthSubX L' p)) : Additive L'ˣ) = σ • (m : Additive L'ˣ) from rfl, hmv]
    rw [show (σ • ((p:ℕ) • (Additive.ofMul y)) : Additive L'ˣ) = (p:ℕ) • (σ • (Additive.ofMul y)) from
        map_nsmul (DistribSMul.toAddMonoidHom (Additive L'ˣ) σ) p (Additive.ofMul y)]
    rw [show (σ • (Additive.ofMul y) : Additive L'ˣ) = Additive.ofMul (σ • y) from rfl]
    rw [nsmul_ofMul, nsmul_ofMul, nsmul_ofMul]
    rw [show (Additive.ofMul (y^p) : Additive L'ˣ)
          + Additive.ofMul ((Units.map (algebraMap L L').toMonoidHom u)^p)
        = Additive.ofMul (y^p * (Units.map (algebraMap L L').toMonoidHom u)^p) from rfl]
    have hunits : (σ • y) ^ p = y ^ p * (Units.map (algebraMap L L').toMonoidHom u) ^ p := by
      rw [hu3, mul_comm (y^p) ((σ • y)^p * (y^p)⁻¹), mul_assoc, inv_mul_cancel, mul_one]
    rw [hunits]
  have ha : ∀ σ : L' ≃ₐ[k] L', σ • m = m + τ3v (galRes k L L' σ) := by
    intro σ
    apply Subtype.ext
    rw [Submodule.coe_add]
    exact ha_val σ
  have hcocyc : ∀ (g h : L ≃ₐ[k] L),
      (pthRepX k L p).ρ g (f.hom (ExtH1.augDiff (L ≃ₐ[k] L) h))
        = f.hom (ExtH1.augDiff (L ≃ₐ[k] L) (g * h)) - f.hom (ExtH1.augDiff (L ≃ₐ[k] L) g) := by
    intro g h
    have h2 : f.hom (ExtH1.augDiff (L ≃ₐ[k] L) (g * h))
        = f.hom (ExtH1.augDiff (L ≃ₐ[k] L) g)
          + (pthRepX k L p).ρ g (f.hom (ExtH1.augDiff (L ≃ₐ[k] L) h)) :=
      ExtH1.derivCochain_isCrossedHom (G := L ≃ₐ[k] L) (M := ↥(pthSubX L p)) f g h
    rw [h2]; abel
  have hb : ∀ (σ : L' ≃ₐ[k] L') (γ : L ≃ₐ[k] L),
      σ • (τ3v γ) = τ3v (galRes k L L' σ * γ) - τ3v (galRes k L L' σ) := by
    intro σ γ
    rw [show σ • (τ3v γ) = (pthRepX k L' p).ρ σ (τ3v γ) from
      (Rep.ofDistribMulAction_ρ_apply_apply Coeff (L' ≃ₐ[k] L') ↥(pthSubX L' p) σ (τ3v γ)).symm]
    rw [hτvdef γ]
    rw [← Rep.hom_comm_apply τ₃ σ (f.hom (ExtH1.augDiff (L ≃ₐ[k] L) γ))]
    rw [show (Rep.res (galRes k L L') (pthRepX k L p)).ρ σ (f.hom (ExtH1.augDiff (L ≃ₐ[k] L) γ))
        = (pthRepX k L p).ρ (galRes k L L' σ) (f.hom (ExtH1.augDiff (L ≃ₐ[k] L) γ)) from rfl]
    rw [hcocyc (galRes k L L' σ) γ]
    rw [map_sub]
    rw [← hτvdef (galRes k L L' σ * γ), ← hτvdef (galRes k L L' σ)]
    rfl
  have hv : ∀ (σ : L' ≃ₐ[k] L') (γ : L ≃ₐ[k] L),
      (pthRepX k L' p).ρ σ (m + τ3v γ) = m + τ3v (galRes k L L' σ * γ) := by
    intro σ γ
    rw [show (pthRepX k L' p).ρ σ (m + τ3v γ) = σ • (m + τ3v γ) from
      Rep.ofDistribMulAction_ρ_apply_apply Coeff (L' ≃ₐ[k] L') ↥(pthSubX L' p) σ (m + τ3v γ)]
    rw [smul_add, ha σ, hb σ γ]
    abel
  obtain ⟨k', hk'⟩ := exists_lift_regRep (galRes k L L') (pthRepX k L' p) (fun γ => m + τ3v γ) hv
  refine ⟨k', ?_⟩
  intro z
  have hgen : ∀ γ : L ≃ₐ[k] L,
      (k'.hom.toLinearMap.comp (ExtH1.augIncl (L ≃ₐ[k] L)).hom.toLinearMap)
          (ExtH1.augDiff (L ≃ₐ[k] L) γ)
        = (τ₃.hom.toLinearMap.comp f.hom.toLinearMap) (ExtH1.augDiff (L ≃ₐ[k] L) γ) := by
    intro γ
    simp only [LinearMap.comp_apply]
    change k'.hom ((ExtH1.augIncl (L ≃ₐ[k] L)) (ExtH1.augDiff (L ≃ₐ[k] L) γ))
        = τ₃.hom (f.hom (ExtH1.augDiff (L ≃ₐ[k] L) γ))
    rw [ExtH1.augIncl_augDiff, map_sub, hk' γ, hk' 1]
    have hτ1 : τ3v 1 = 0 := by
      rw [hτvdef, show ExtH1.augDiff (L ≃ₐ[k] L) 1 = 0 from Subtype.ext (sub_self _)]
      simp only [map_zero]
      rfl
    rw [hτ1, hτvdef γ, add_zero]
    exact add_sub_cancel_left m (τ₃.hom (f.hom (ExtH1.augDiff (L ≃ₐ[k] L) γ)))
  have hmapfin := lin_ext_augDiff _ _ hgen
  exact LinearMap.congr_fun hmapfin z

end Work.SSGRoute
