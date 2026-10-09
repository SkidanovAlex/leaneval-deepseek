import Mathlib
import Submission.Work.SSGRoute.kummer_level_defs
import Submission.Work.SSGRoute.augSES_shortExact
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Naturality of the Kummer extension class

For a level `k ⊆ L` (`L/k` finite Galois, `k` a number field) and a prime `p`, the Kummer short
exact sequence

  `0 → 𝔽_p --z--> Lˣ --pthMapX--> (Lˣ)^p → 0`

of `Gal(L/k)`-representations has an extension class in `Ext¹((Lˣ)^p, 𝔽_p)`.  Passing to a larger
level `L' ⊇ L` (with `k ⊆ L ⊆ L'` both finite Galois over `k`), the class of the *restricted*
sequence at the level `L`, pushed forward along the canonical identification of the restricted
coefficients with `𝔽_p` at the level `L'`, agrees with the class of the sequence at the level `L'`,
pulled back along the map `τ₃` of `p`-th power modules.

This is a formal consequence of the naturality of the extension class of a short exact sequence
(`ShortComplex.ShortExact.extClass_naturality`): the data `z`, `τ₂`, `τ₃` (with the compatibility
of `τ₂`, `τ₃` with the `p`-th power maps) exhibit a morphism of short complexes from the restricted
Kummer sequence at the level `L` to the Kummer sequence at the level `L'`.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace Work.SSGRoute

open CategoryTheory SSGRoute.PTExt

variable {k : Type} [Field k] [NumberField k] {L : Type} [Field L] [NumberField L] [Algebra k L]
  {L' : Type} [Field L'] [NumberField L'] [Algebra k L'] [Algebra L L']
  [IsScalarTower k L L']

/-- The unit `ζ ∈ Lˣ` viewed at the larger level `L'`: `Units.map (algebraMap L L')` sends it to the
corresponding unit at the level `L'`. -/
theorem zetaUnitL_units_map (p : ℕ) [Fact p.Prime] (ζ : k) (hζ : IsPrimitiveRoot ζ p) :
    Units.map (algebraMap L L').toMonoidHom (zetaUnitL k L p ζ hζ) = zetaUnitL k L' p ζ hζ := by
  apply Units.ext
  simp only [Units.coe_map, zetaUnitL, Units.val_mk0, IsScalarTower.algebraMap_apply k L L']
  rfl

/-- Two Kummer coefficient classes at the levels `L` and `L'` (both sending `1` to `ζ`) agree under
the transition `L → L'`, on the level of units. -/
theorem z_apply_units_map (p : ℕ) [Fact p.Prime] (ζ : k) (hζ : IsPrimitiveRoot ζ p)
    (z : Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p) ⟶ levelUnits k L)
    (hz : ((Additive.toMul (z.hom (1 : ZMod p)) : Lˣ) : L) = algebraMap k L ζ)
    (z' : Rep.trivial Coeff (L' ≃ₐ[k] L') (ZMod p) ⟶ levelUnits k L')
    (hz' : ((Additive.toMul (z'.hom (1 : ZMod p)) : L'ˣ) : L') = algebraMap k L' ζ) :
    ∀ x : ZMod p, (z'.hom x : L'ˣ) = Units.map (algebraMap L L').toMonoidHom (z.hom x : Lˣ) := by
  intro x
  obtain ⟨m, hm⟩ := ZMod.intCast_surjective x
  subst hm
  calc (z'.hom (m : ZMod p) : L'ˣ)
      = zetaUnitL k L' p ζ hζ ^ m := z_toMul_apply p hζ hz' m
    _ = (Units.map (algebraMap L L').toMonoidHom (zetaUnitL k L p ζ hζ)) ^ m :=
          (congrArg (fun u => u ^ m) (zetaUnitL_units_map (L := L) (L' := L') p ζ hζ)).symm
    _ = Units.map (algebraMap L L').toMonoidHom (zetaUnitL k L p ζ hζ ^ m) :=
          (map_zpow _ _ _).symm
    _ = Units.map (algebraMap L L').toMonoidHom (z.hom (m : ZMod p) : Lˣ) :=
          congrArg (Units.map (algebraMap L L').toMonoidHom) (z_toMul_apply p hζ hz m).symm

/-- **First naturality square**: the restriction of `z` to `L'` followed by `τ₂` agrees with `z'`. -/
theorem kummerSES_comm12 (p : ℕ) [Fact p.Prime]
    [FiniteDimensional k L] [IsGalois k L] [FiniteDimensional k L'] [IsGalois k L']
    (ζ : k) (hζ : IsPrimitiveRoot ζ p)
    (z : Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p) ⟶ levelUnits k L)
    (hz : ((Additive.toMul (z.hom (1 : ZMod p)) : Lˣ) : L) = algebraMap k L ζ)
    (z' : Rep.trivial Coeff (L' ≃ₐ[k] L') (ZMod p) ⟶ levelUnits k L')
    (hz' : ((Additive.toMul (z'.hom (1 : ZMod p)) : L'ˣ) : L') = algebraMap k L' ζ)
    (τ₂ : Rep.res (galRes k L L') (levelUnits k L) ⟶ levelUnits k L')
    (hτ₂ : ∀ u : Lˣ, τ₂.hom (Additive.ofMul u)
        = Additive.ofMul (Units.map (algebraMap L L').toMonoidHom u)) :
    trivResInv (galRes k L L') (ZMod p) ≫ z'
      = Rep.resMap (galRes k L L') z ≫ τ₂ := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext ?_))
  intro x
  show z'.hom x = τ₂.hom (z.hom x)
  have h1 : τ₂.hom (z.hom x)
      = Additive.ofMul (Units.map (algebraMap L L').toMonoidHom (z.hom x : Lˣ)) :=
    hτ₂ (z.hom x : Lˣ)
  calc z'.hom x
      = Additive.ofMul (z'.hom x : L'ˣ) := rfl
    _ = Additive.ofMul (Units.map (algebraMap L L').toMonoidHom (z.hom x : Lˣ)) :=
          congrArg Additive.ofMul (z_apply_units_map p ζ hζ z hz z' hz' x)
    _ = τ₂.hom (z.hom x) := h1.symm

/-- **Second naturality square**: `τ₂` and `τ₃` intertwine the `p`-th power maps. -/
theorem kummerSES_comm23 (p : ℕ) [Fact p.Prime]
    [FiniteDimensional k L] [IsGalois k L] [FiniteDimensional k L'] [IsGalois k L']
    (τ₂ : Rep.res (galRes k L L') (levelUnits k L) ⟶ levelUnits k L')
    (τ₃ : Rep.res (galRes k L L') (pthRepX k L p) ⟶ pthRepX k L' p)
    (hτ₂ : ∀ u : Lˣ, τ₂.hom (Additive.ofMul u)
        = Additive.ofMul (Units.map (algebraMap L L').toMonoidHom u))
    (hτ₃sq : ∀ u : Lˣ, τ₃.hom ((pthMapX k L p).hom (Additive.ofMul u))
        = (pthMapX k L' p).hom (τ₂.hom (Additive.ofMul u))) :
    τ₂ ≫ pthMapX k L' p = Rep.resMap (galRes k L L') (pthMapX k L p) ≫ τ₃ := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext ?_))
  intro v
  show (pthMapX k L' p).hom (τ₂.hom v) = τ₃.hom ((pthMapX k L p).hom v)
  rw [show v = Additive.ofMul (v : Lˣ) from rfl]
  exact (hτ₃sq (v : Lˣ)).symm

theorem kummerSES_extClass_naturality
    (k : Type) [Field k] [NumberField k] (L : Type) [Field L] [NumberField L] [Algebra k L]
    [FiniteDimensional k L] [IsGalois k L]
    (L' : Type) [Field L'] [NumberField L'] [Algebra k L'] [FiniteDimensional k L']
    [IsGalois k L'] [Algebra L L'] [IsScalarTower k L L'] (p : ℕ) [Fact p.Prime] (ζ : k)
    (hζ : IsPrimitiveRoot ζ p)
    (z : Rep.trivial SSGRoute.PTExt.Coeff (L ≃ₐ[k] L) (ZMod p) ⟶ Work.SSGRoute.levelUnits k L)
    (hz : ((Additive.toMul (z.hom (1 : ZMod p)) : Lˣ) : L) = algebraMap k L ζ)
    (z' : Rep.trivial SSGRoute.PTExt.Coeff (L' ≃ₐ[k] L') (ZMod p) ⟶ Work.SSGRoute.levelUnits k L')
    (hz' : ((Additive.toMul (z'.hom (1 : ZMod p)) : L'ˣ) : L') = algebraMap k L' ζ)
    (τ₂ : Rep.res (SSGRoute.PTExt.galRes k L L') (Work.SSGRoute.levelUnits k L) ⟶ Work.SSGRoute.levelUnits k L')
    (τ₃ : Rep.res (SSGRoute.PTExt.galRes k L L') (Work.SSGRoute.pthRepX k L p) ⟶ Work.SSGRoute.pthRepX k L' p)
    (hτ₂ : ∀ u : Lˣ, τ₂.hom (Additive.ofMul u)
        = Additive.ofMul (Units.map (algebraMap L L').toMonoidHom u))
    (hτ₃ : ∀ u : Lˣ, τ₃.hom ⟨(p:ℕ) • Additive.ofMul u, LinearMap.mem_range_self _ _⟩
        = ⟨(p:ℕ) • Additive.ofMul (Units.map (algebraMap L L').toMonoidHom u),
           LinearMap.mem_range_self _ _⟩)
    (hτ₃sq : ∀ u : Lˣ, τ₃.hom ((Work.SSGRoute.pthMapX k L p).hom (Additive.ofMul u))
        = (Work.SSGRoute.pthMapX k L' p).hom (τ₂.hom (Additive.ofMul u))) :
    ((Work.SSGRoute.kummerSESX_shortExact k L p hζ z hz).map_of_exact
        (Rep.resFunctor (SSGRoute.PTExt.galRes k L L'))).extClass.comp
        (CategoryTheory.Abelian.Ext.mk₀ (SSGRoute.PTExt.trivResInv (SSGRoute.PTExt.galRes k L L') (ZMod p)))
        (add_zero 1)
      = (CategoryTheory.Abelian.Ext.mk₀ τ₃).comp
        (Work.SSGRoute.kummerSESX_shortExact k L' p hζ z' hz').extClass (zero_add 1) := by
  have hcomm12 := kummerSES_comm12 (L := L) (L' := L') p ζ hζ z hz z' hz' τ₂ hτ₂
  have hcomm23 := kummerSES_comm23 (L := L) (L' := L') p τ₂ τ₃ hτ₂ hτ₃sq
  refine ShortComplex.ShortExact.extClass_naturality
    ((kummerSESX_shortExact k L p hζ z hz).map_of_exact (Rep.resFunctor (galRes k L L')))
    (kummerSESX_shortExact k L' p hζ z' hz')
    ({ τ₁ := trivResInv (galRes k L L') (ZMod p)
       τ₂ := τ₂
       τ₃ := τ₃
       comm₁₂ := hcomm12
       comm₂₃ := hcomm23 } : (kummerSESX k L p hζ z hz).map
          (Rep.resFunctor (galRes k L L')) ⟶ kummerSESX k L' p hζ z' hz')

end Work.SSGRoute
