import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.inflTrivIn_refl
import Submission.Work.SSGRoute.inflTrivIn_trans
import Submission.Work.SSGRoute.phi1_level_index
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester): read `DESIGN_FIX.md` §1, `phi1_level_index.lean`
and `PHI1_PGROUP_STATUS.md` (the "colimit step" section).

# The directed system `L ↦ H²(Gal(L/k), 𝔽_p)` over the levels

The colimit step of `Work.SSGRoute.phi1_mono_step_in` needs the levels as the index of a direct
limit with the **inflation maps** as transition maps.

* `LevelCoh p L = H²(Gal(L/k), 𝔽_p)` and the bundled transition map
  `levelMap p L L' h : LevelCoh p L →+ LevelCoh p L'` (**additivity proved** below).
* **Functoriality** (`levelMap_self`, `levelMap_map`) — the two `DirectedSystem` axioms — and
  hence the `DirectedSystem` instance itself are *stated but not yet proved* here.

**What the functoriality needs (findings).**  `inflTrivIn h (ZMod p)` is `extHMap` of
`galRes` and `trivResInv`, so functoriality reduces to the `Ext`-functoriality of
`mapExactFunctor` (`𝟭`, composition) and to `extRes_comp`.  **All the needed `mapExactFunctor`
API already exists in the workspace** (proved by colleagues):

* `Work.SSGRoute.ext_mapExactFunctor_comp_functor_aux`
  (`(x.mapExactFunctor F).mapExactFunctor G = x.mapExactFunctor (F ⋙ G)`, `ext_corestriction.lean`),
* `Work.SSGRoute.mapExactFunctor_id` (`x.mapExactFunctor (𝟭 _) = x`, `mapExactFunctor_id.lean`),
* `Work.SSGRoute.extRes_comp_aux` (`extRes (ψ.comp φ) x = extRes φ (extRes ψ x)`,
  `sylow_descend.lean`).

Neither identity nor composition is *definitional* (`rfl` fails: `mapExactFunctor` goes through
`mapHomologicalComplexUpToQuasiIsoLocalizerMorphism`), so the remaining work is the bookkeeping of
`extHMap` (`unitRes`, `trivResInv` are identities on the coefficient type) together with the
`Rep.res`-composition transports (`Rep.res f₂ (Rep.res f₁ M)` vs `Rep.res (f₂.comp f₁) M` are
propositionally, not definitionally, equal).  In particular the *refl* case reduces, after
`galRes = MonoidHom.id` and `Rep.resFunctor (MonoidHom.id) = 𝟭`, to
`(mk₀ (unitRes id)).comp (y.comp (mk₀ (trivResInv id)) _) _ = y`. -/

noncomputable section

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

variable {k K Ω : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [Field Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]

/-- The level system `L ↦ H²(Gal(L/k), 𝔽_p)`. -/
abbrev LevelCoh (p : ℕ) (L : Lvl k K Ω) : Type _ :=
  extH (Rep.trivial Coeff (↥L.1 ≃ₐ[k] ↥L.1) (ZMod p)) 2

/-- The **transition map** of the level system: inflation of `H²(Gal(L/k),𝔽_p)` to a higher level. -/
noncomputable def levelMap (p : ℕ) (L L' : Lvl k K Ω) (h : L ≤ L') :
    LevelCoh p L →+ LevelCoh p L' where
  toFun y := inflTrivIn (k := k) h (ZMod p) y
  map_zero' := by
    show inflTrivIn (k := k) h (ZMod p) (0 : LevelCoh p L) = 0
    simp only [inflTrivIn, inflTriv, extHMap, extRes, Abelian.Ext.mapExactFunctor_zero,
      Abelian.Ext.zero_comp, Abelian.Ext.comp_zero]
  map_add' x y := by
    show inflTrivIn (k := k) h (ZMod p) (x + y)
      = inflTrivIn (k := k) h (ZMod p) x + inflTrivIn (k := k) h (ZMod p) y
    simp only [inflTrivIn, inflTriv, extHMap, extRes, Abelian.Ext.mapExactFunctor_add,
      Abelian.Ext.add_comp, Abelian.Ext.comp_add]

@[simp] theorem levelMap_apply (p : ℕ) (L L' : Lvl k K Ω) (h : L ≤ L')
    (y : LevelCoh p L) :
    levelMap (k := k) p L L' h y = inflTrivIn (k := k) h (ZMod p) y := rfl

/-- **`map` of the level system at `le_rfl` is the identity** (the `map_self` axiom of the
`DirectedSystem`).  Reduces as explained in the file header. -/
theorem levelMap_self (p : ℕ) (L : Lvl k K Ω) (y : LevelCoh p L) :
    levelMap (k := k) p L L le_rfl y = y := by
  rw [levelMap_apply]
  exact inflTrivIn_refl (k := k) (L := L.1) (ZMod p) y

/-- **`map_map` for the level system** (the second `DirectedSystem` axiom): inflating twice is
inflating along the composite inclusion. -/
theorem levelMap_map (p : ℕ) (L L' L'' : Lvl k K Ω) (h₁ : L ≤ L') (h₂ : L' ≤ L'')
    (y : LevelCoh p L) :
    levelMap (k := k) p L' L'' h₂ (levelMap (k := k) p L L' h₁ y)
      = levelMap (k := k) p L L'' (h₁.trans h₂) y := by
  simp only [levelMap_apply]
  exact inflTrivIn_trans (k := k) h₁ h₂ (ZMod p) y

/-- **The level system is a directed system** with the inflation maps as transition maps. -/
instance levelDirectedSystem (p : ℕ) :
    DirectedSystem (LevelCoh (k := k) (K := K) (Ω := Ω) p)
      (fun i j h => levelMap (k := k) p i j h) where
  map_self := fun i y => levelMap_self (k := k) p i y
  map_map := fun {kt jt it} (hij : it ≤ jt) (hjk : jt ≤ kt) (y : LevelCoh p it) =>
    levelMap_map (k := k) p it jt kt hij hjk y

end Work.SSGRoute
