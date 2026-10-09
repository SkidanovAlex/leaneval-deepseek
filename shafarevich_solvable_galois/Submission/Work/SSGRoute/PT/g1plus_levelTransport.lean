import Mathlib
import Submission.Work.SSGRoute.E9c.Core
import Submission.Work.SSGRoute.E7cOmega.zfun_pairing_extLoc
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Level transport of `extToClasses` along the idèle level map

`Work.SSGRoute.PT.finAtLevel` evaluates `χ L hKL (ι_w z)` with `ι_w = extToClasses ∘ iotaLift`
and `z ∈ H²(D_w, L_wˣ)`.  Level independence (given `χ`'s inflation coherence) needs the level
change of that expression; this file supplies the `extToClasses` half:

`extToClasses (idleRepMap q) = inflC (extToClasses q)` (`extToClasses_idleRepMap`), from the proved
coefficient square `Work.SSGRoute.resMap_classGroupMap_comp_classIncl`.

The proof is split deliberately: `extToClasses_extHMap_comp` is the pure `mk₀`/`comp_assoc`
bookkeeping, and the main lemma only rewrites with the coefficient square.  Do NOT
`simp only [extToClasses, extHMap, extRes, ...]` on the composed goal — that route does not
terminate (measured: `CokerPT/PING_h_levelClass_and_finAtLevelFix.md` §4).
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option autoImplicit false

open CategoryTheory SSGRoute.PTExt

namespace Work.SSGRoute.PT

/-- `extHMap` commutes with post-composition by a degree-zero coefficient morphism (the
`Rep.resMap`/`mk₀` reassociation).  Local copy of `dass_extHMap_comp_mk₀`
(`detectAbove_sub_step_aux.lean`), which cannot be imported here: its module clashes with
`detectAbove_sub_step` (`dassW`) inside this import cone. -/
theorem pt_extHMap_comp_mk₀ {G₁ G : Type} [Group G₁] [Group G]
    (g : G →* G₁) {A A' : Rep Coeff G₁} {B : Rep Coeff G} (ψ : Rep.res g A ⟶ B)
    (φ : A' ⟶ A) (s : ℕ) (x : extH A' s) :
    extHMap g ψ (x.comp (Abelian.Ext.mk₀ φ) (add_zero s)) =
      extHMap g (Rep.resMap g φ ≫ ψ) x := by
  simp only [extHMap, extRes, Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
    Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.comp_assoc, Abelian.Ext.mk₀_comp_mk₀]

/-- **Post-composition of an inflated `Ext`-class**: composing `extHMap g κ y` with `mk₀ λ` is
`extHMap` along the coefficient map `κ ≫ λ`. -/
theorem extToClasses_extHMap_comp {G H : Type} [Group G] [Group H] (g : H →* G)
    {A : Rep Coeff G} {B : Rep Coeff H} (κ : Rep.res g A ⟶ B) {C : Rep Coeff H} (lam : B ⟶ C)
    {n : ℕ} (y : extH A n) :
    (extHMap g κ y).comp (Abelian.Ext.mk₀ lam) (add_zero n) = extHMap g (κ ≫ lam) y := by
  simp only [extHMap, extRes, Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
    Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.comp_assoc_of_third_deg_zero,
    Abelian.Ext.comp_assoc, Abelian.Ext.mk₀_comp_mk₀, Abelian.Ext.mk₀_id_comp,
    Abelian.Ext.comp_mk₀_id]

/-- **The class-group map is compatible with the idèle level map.**  For `q ∈ H²(Gal(K/k), 𝕀_K)`,
`extToClasses (idleRepMap q) = inflC (extToClasses q)`: the level-`L` class of the pushed idèle
class is the inflation of the level-`K` class. -/
theorem extToClasses_idleRepMap (k K L : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L] [IsGalois k L]
    {n : ℕ} (q : extH (idelesK k K) n) :
    extToClasses (k := k) (K := L)
        (extHMap (galRes k K L) (Work.SSGRoute.idleRepMap k K L) q)
      = extHMap (galRes k K L) (classIncl k K L) (extToClasses (k := k) (K := K) q) := by
  rw [show extToClasses (k := k) (K := L)
        (extHMap (galRes k K L) (Work.SSGRoute.idleRepMap k K L) q)
      = extHMap (galRes k K L)
          (Work.SSGRoute.idleRepMap k K L ≫ NK.HassePrinciple.classGroupMap k L) q from
    extToClasses_extHMap_comp (galRes k K L) (Work.SSGRoute.idleRepMap k K L)
      (NK.HassePrinciple.classGroupMap k L) q,
    show extHMap (galRes k K L) (classIncl k K L) (extToClasses (k := k) (K := K) q)
      = extHMap (galRes k K L)
          (Rep.resMap (galRes k K L) (NK.HassePrinciple.classGroupMap k K) ≫ classIncl k K L) q
      from pt_extHMap_comp_mk₀ (galRes k K L) (classIncl k K L)
        (NK.HassePrinciple.classGroupMap k K) n q,
    Work.SSGRoute.resMap_classGroupMap_comp_classIncl k K L]

end Work.SSGRoute.PT
