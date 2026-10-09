import Mathlib
import Submission.Work.SSGRoute.PTCore.H2_level_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Nesting of the level inflations of `H²(G_F, k̄ˣ)`

For a tower of finite Galois levels `L ≤ L'` of an algebraic closure `k̄` of `F`, every class of
`H²(G_F, k̄ˣ)` living on `L` also lives on `L'`:

`Set.range (psiTilde L) ⊆ Set.range (psiTilde L')`.

The proof pulls a level-`L` `2`-cocycle back along the restriction `Gal(L'/F) →* Gal(L/F)` and the
coefficient inclusion `Lˣ →+ L'ˣ` of the tower.  The `H²`-classes then agree because the inflation
of the pulled-back cocycle is *literally* the inflation of the original one, by
`resL = resLL ∘ resL'` and `inclL = inclL' ∘ inclLL`.
-/

set_option linter.style.haveILetI false

noncomputable section

open scoped Classical
open Work.AbsoluteKummer

namespace Work.SSGRoute.PTCore

variable {F : Type} [Field F] [IsGalois F (AlgebraicClosure F)]

/-! ## The tower machinery -/

section Tower

variable {L L' : FiniteGaloisIntermediateField F (AlgebraicClosure F)}
variable [Algebra (↥(L : IntermediateField F (AlgebraicClosure F)))
  (↥(L' : IntermediateField F (AlgebraicClosure F)))]
variable [IsScalarTower F (↥(L : IntermediateField F (AlgebraicClosure F)))
  (↥(L' : IntermediateField F (AlgebraicClosure F)))]
variable [IsScalarTower (↥(L : IntermediateField F (AlgebraicClosure F)))
  (↥(L' : IntermediateField F (AlgebraicClosure F))) (AlgebraicClosure F)]

/-- The inclusion `Lˣ →+ L'ˣ` of the units of a tower of levels. -/
noncomputable def inclLL : UnitsL L →+ UnitsL L' where
  toFun x := Units.map (algebraMap ↥L ↥L').toMonoidHom x
  map_zero' := by
    show Additive.ofMul (Units.map (algebraMap ↥L ↥L').toMonoidHom (1 : (↥L : Type)ˣ))
      = Additive.ofMul (1 : (↥L' : Type)ˣ)
    rw [map_one]
  map_add' x y := by
    show Additive.ofMul (Units.map (algebraMap ↥L ↥L').toMonoidHom
        ((Additive.toMul x : (↥L : Type)ˣ) * (Additive.toMul y : (↥L : Type)ˣ)))
      = Additive.ofMul (Units.map (algebraMap ↥L ↥L').toMonoidHom (Additive.toMul x))
        + Additive.ofMul (Units.map (algebraMap ↥L ↥L').toMonoidHom (Additive.toMul y))
    rw [map_mul]
    rfl

@[simp] theorem inclLL_ofMul (u : (↥L : Type)ˣ) :
    inclLL (L := L) (L' := L') (Additive.ofMul u)
      = Additive.ofMul (Units.map (algebraMap ↥L ↥L').toMonoidHom u) := rfl

/-- The coefficient inclusion factorises through the tower. -/
theorem inclL_eq_inclLL (x : UnitsL L) : inclL L x = inclL L' (inclLL (L := L) (L' := L') x) := by
  suffices hh : ∀ u : (↥L : Type)ˣ,
      inclL L (Additive.ofMul u) = inclL L' (inclLL (L := L) (L' := L') (Additive.ofMul u)) by
    rw [show x = Additive.ofMul (Additive.toMul x) from (ofMul_toMul x).symm]
    exact hh x.toMul
  intro u
  apply Additive.ofMul.injective
  apply Units.ext
  show algebraMap ↥L (AlgebraicClosure F) (u : ↥L)
    = algebraMap ↥L' (AlgebraicClosure F)
        ((Units.map (algebraMap ↥L ↥L').toMonoidHom u : (↥L')ˣ) : ↥L')
  rw [IsScalarTower.algebraMap_eq ↥L ↥L' (AlgebraicClosure F)]
  rfl

/-- The restriction `Gal(L'/F) →* Gal(L/F)`. -/
noncomputable def resLL : LevelGal L' →* LevelGal L :=
  AlgEquiv.restrictNormalHom ↥(L : IntermediateField F (AlgebraicClosure F))

/-- The tower of restrictions. -/
theorem resL_eq_resLL_comp (σ : AbsGal F) :
    resL L σ = resLL (L := L) (L' := L') (resL L' σ) := by
  change AlgEquiv.restrictNormalHom ↥(L : IntermediateField F (AlgebraicClosure F)) σ
    = AlgEquiv.restrictNormalHom ↥(L : IntermediateField F (AlgebraicClosure F))
        (AlgEquiv.restrictNormalHom ↥(L' : IntermediateField F (AlgebraicClosure F)) σ)
  rw [IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply (↥L) (↥L') σ]

/-- Equivariance of the tower coefficient inclusion. -/
theorem inclLL_rho (γ : LevelGal L') (x : UnitsL L) :
    inclLL (L := L) (L' := L') ((LevelRep L).ρ (resLL (L := L) (L' := L') γ) x)
      = (LevelRep L').ρ γ (inclLL (L := L) (L' := L') x) := by
  suffices hh : ∀ u : (↥L : Type)ˣ,
      inclLL (L := L) (L' := L') ((LevelRep L).ρ (resLL (L := L) (L' := L') γ)
          (Additive.ofMul u))
        = (LevelRep L').ρ γ (inclLL (L := L) (L' := L') (Additive.ofMul u)) by
    rw [show x = Additive.ofMul (Additive.toMul x) from (ofMul_toMul x).symm]
    exact hh x.toMul
  intro u
  apply Additive.ofMul.injective
  show Units.map (algebraMap ↥L ↥L').toMonoidHom (Units.map (resLL (L := L) (L' := L') γ) u)
    = Units.map γ (Units.map (algebraMap ↥L ↥L').toMonoidHom u)
  apply Units.ext
  show (algebraMap ↥L ↥L') ((resLL (L := L) (L' := L') γ) ((u : (↥L)ˣ) : ↥L))
    = γ ((algebraMap ↥L ↥L') ((u : (↥L)ˣ) : ↥L))
  exact AlgEquiv.restrictNormal_commutes γ (↥L) ((u : (↥L)ˣ) : ↥L)

end Tower

/-! ## Nesting of the level inflations -/

/-- **Nesting of the level inflations.**  For a tower of finite Galois levels `L ≤ L'`, every class
of `H²(G_F, k̄ˣ)` living on `L` also lives on `L'`. -/
theorem H2_level_mono {F : Type} [Field F] [IsGalois F (AlgebraicClosure F)]
    (L L' : FiniteGaloisIntermediateField F (AlgebraicClosure F))
    (h : (L : IntermediateField F (AlgebraicClosure F)) ≤ L') :
    Set.range (Work.SSGRoute.PTCore.psiTilde L) ⊆
      Set.range (Work.SSGRoute.PTCore.psiTilde L') := by
  classical
  letI : Algebra (↥(L : IntermediateField F (AlgebraicClosure F)))
      (↥(L' : IntermediateField F (AlgebraicClosure F))) :=
    (IntermediateField.inclusion h).toAlgebra
  haveI : IsScalarTower F (↥(L : IntermediateField F (AlgebraicClosure F)))
      (↥(L' : IntermediateField F (AlgebraicClosure F))) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower (↥(L : IntermediateField F (AlgebraicClosure F)))
      (↥(L' : IntermediateField F (AlgebraicClosure F))) (AlgebraicClosure F) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- pull-back of a level-`L` cocycle along the tower is a level-`L'` cocycle
  have hpull : ∀ c : ↥(LevelCocycles L),
      (fun p : LevelGal L' × LevelGal L' =>
          inclLL (L := L) (L' := L') (c (resLL (L := L) (L' := L') p.1,
            resLL (L := L) (L' := L') p.2))) ∈ LevelCocycles L' := by
    intro c
    rw [mem_cocycles₂_iff_add]
    intro γ δ ε
    have h1 := (mem_cocycles₂_iff_add L (c : LevelGal L × LevelGal L → UnitsL L)).mp c.2
      (resLL (L := L) (L' := L') γ) (resLL (L := L) (L' := L') δ)
      (resLL (L := L) (L' := L') ε)
    change inclLL (L := L) (L' := L') (c (resLL (L := L) (L' := L') (γ * δ),
          resLL (L := L) (L' := L') ε))
        + inclLL (L := L) (L' := L') (c (resLL (L := L) (L' := L') γ,
            resLL (L := L) (L' := L') δ))
      = (LevelRep L').ρ γ (inclLL (L := L) (L' := L') (c (resLL (L := L) (L' := L') δ,
          resLL (L := L) (L' := L') ε)))
        + inclLL (L := L) (L' := L') (c (resLL (L := L) (L' := L') γ,
            resLL (L := L) (L' := L') (δ * ε)))
    rw [map_mul, map_mul, ← map_add, h1, map_add, inclLL_rho]
  -- the two inflations are literally the same function
  have hcompat : ∀ c : ↥(LevelCocycles L),
      inflCo L c = inflCo L' ⟨fun p : LevelGal L' × LevelGal L' =>
          inclLL (L := L) (L' := L') (c (resLL (L := L) (L' := L') p.1,
            resLL (L := L) (L' := L') p.2)), hpull c⟩ := by
    intro c
    apply Subtype.ext
    funext p
    obtain ⟨g, k⟩ := p
    show inclL L (c (resL L g, resL L k))
      = inclL L' (inclLL (L := L) (L' := L') (c (resLL (L := L) (L' := L') (resL L' g),
          resLL (L := L) (L' := L') (resL L' k))))
    have hA : resL L g = resLL (L := L) (L' := L') (resL L' g) :=
      resL_eq_resLL_comp (L := L) (L' := L') g
    have hB : resL L k = resLL (L := L) (L' := L') (resL L' k) :=
      resL_eq_resLL_comp (L := L) (L' := L') k
    rw [hA, hB]
    exact inclL_eq_inclLL (L := L) (L' := L') _
  intro y hy
  obtain ⟨x, rfl⟩ := hy
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective
    ((LevelCob L).comap (LevelCocycles L).subtype).toAddSubgroup x
  refine ⟨QuotientAddGroup.mk'
      ((LevelCob L').comap (LevelCocycles L').subtype).toAddSubgroup
      (⟨fun p : LevelGal L' × LevelGal L' =>
        inclLL (L := L) (L' := L') (c (resLL (L := L) (L' := L') p.1,
          resLL (L := L) (L' := L') p.2)), hpull c⟩ : ↥(LevelCocycles L')), ?_⟩
  rw [← hc, psiTilde_mk, psiTilde_mk]
  congr 1
  exact (hcompat c).symm

end Work.SSGRoute.PTCore
