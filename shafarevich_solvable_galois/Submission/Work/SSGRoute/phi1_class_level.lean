import Mathlib
import Submission.Work.SSGRoute.phi1_level_index
import Submission.Work.SSGRoute.inflCIn_trans
import Submission.Work.SSGRoute.inflCIn_refl
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester): read `DESIGN_FIX.md` §1 and the "colimit step"
section of `PHI1_PGROUP_STATUS.md`.

# The direct limit `A = colim_{L} H²(Gal(L/k), C_L)` over the levels

Companion of `Submission.Work.SSGRoute.phi1_level_limit` (which provides
`V = colim_L H²(Gal(L/k), 𝔽_p)`).  The realisation step of E5s
(`Work.SSGRoute.exists_realization_of_delta_lam`) pushes the level functionals into the
`C`-coefficient colimit `A`, so that the gluing does not need any injectivity of inflation:

* `ClassLevel L = H²(Gal(L/k), C_L)`;
* `classLevelMap p L L' h` — inflation of class-group cohomology, bundled as an additive map
  (additivity is proved here from the `Ext`-calculus, as in `phi1_level_system`);
* `classLevelMap_self`, `classLevelMap_map` and the `DirectedSystem` instance (from the delegated
  `Work.SSGRoute.inflCIn_refl` and `Work.SSGRoute.inflCIn_trans`);
* `ClassLevelLimit`, its canonical maps and its universal property.
-/

noncomputable section

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

variable {k K Ω : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [Field Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω] [IsGalois k K]

/-- The level system `L ↦ H²(Gal(L/k), C_L)`. -/
abbrev ClassLevel (L : Lvl k K Ω) : Type _ :=
  extH (classesK k L.1) 2

/-- The **transition map** of the class-group level system: inflation `H²(Gal(L/k),C_L) →
H²(Gal(L'/k),C_{L'})` along `L ≤ L'`. -/
noncomputable def classLevelMap (L L' : Lvl k K Ω) (h : L ≤ L') :
    ClassLevel L →+ ClassLevel L' where
  toFun y := inflCIn (k := k) h y
  map_zero' := by
    show inflCIn (k := k) h (0 : ClassLevel L) = 0
    simp only [inflCIn, inflC, extHMap, extRes, Abelian.Ext.mapExactFunctor_zero,
      Abelian.Ext.zero_comp, Abelian.Ext.comp_zero]
  map_add' x y := by
    show inflCIn (k := k) h (x + y) = inflCIn (k := k) h x + inflCIn (k := k) h y
    simp only [inflCIn, inflC, extHMap, extRes, Abelian.Ext.mapExactFunctor_add,
      Abelian.Ext.add_comp, Abelian.Ext.comp_add]

@[simp] theorem classLevelMap_apply (L L' : Lvl k K Ω) (h : L ≤ L') (y : ClassLevel L) :
    classLevelMap (k := k) L L' h y = inflCIn (k := k) h y := rfl

/-- The `map_self` axiom of the class-group level system. -/
theorem classLevelMap_self (L : Lvl k K Ω) (y : ClassLevel L) :
    classLevelMap (k := k) L L le_rfl y = y := by
  rw [classLevelMap_apply]
  exact inflCIn_refl (k := k) (L := L.1) y

/-- The `map_map` axiom of the class-group level system. -/
theorem classLevelMap_map (L L' L'' : Lvl k K Ω) (h₁ : L ≤ L') (h₂ : L' ≤ L'')
    (y : ClassLevel L) :
    classLevelMap (k := k) L' L'' h₂ (classLevelMap (k := k) L L' h₁ y)
      = classLevelMap (k := k) L L'' (h₁.trans h₂) y := by
  rw [classLevelMap_apply, classLevelMap_apply, classLevelMap_apply]
  exact inflCIn_trans (k := k) h₁ h₂ y

/-- **The class-group level system is a directed system.** -/
instance classDirectedSystem :
    DirectedSystem (ClassLevel (k := k) (K := K) (Ω := Ω))
      (fun i j h => classLevelMap (k := k) i j h) where
  map_self := fun i y => classLevelMap_self (k := k) i y
  map_map := fun {kt jt it} (hij : it ≤ jt) (hjk : jt ≤ kt) (y : ClassLevel it) =>
    classLevelMap_map (k := k) it jt kt hij hjk y

/-- **`A = colim_{L} H²(Gal(L/k), C_L)`**, the class-group direct limit. -/
abbrev ClassLevelLimit : Type _ :=
  DirectLimit (ClassLevel (k := k) (K := K) (Ω := Ω))
    (fun i j h => classLevelMap (k := k) i j h)

/-- The canonical map `H²(Gal(L/k),C_L) → A` of the `L`-th component. -/
def ClassLevelLimit.of (L : Lvl k K Ω) :
    ClassLevel L →+ ClassLevelLimit (k := k) (K := K) (Ω := Ω) where
  toFun y := ⟦⟨L, y⟩⟧
  map_zero' := (DirectLimit.zero_def L).symm
  map_add' x y := (DirectLimit.add_def L x y).symm

@[simp] theorem ClassLevelLimit.of_zero (L : Lvl k K Ω) :
    ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L (0 : ClassLevel L) = 0 := map_zero _

/-- The colimit relation for the class-group system. -/
theorem ClassLevelLimit.of_levelMap {L L' : Lvl k K Ω} (h : L ≤ L') (y : ClassLevel L) :
    ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L' (classLevelMap (k := k) L L' h y)
      = ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L y :=
  DirectLimit.mk_apply (f := fun i j h => classLevelMap (k := k) i j h) L L' y h

/-- An element of the class-group colimit vanishes iff it vanishes at a higher level. -/
theorem ClassLevelLimit.of_eq_zero_iff (L : Lvl k K Ω) (y : ClassLevel L) :
    ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L y = 0
      ↔ ∃ (L' : Lvl k K Ω) (h : L ≤ L'), classLevelMap (k := k) L L' h y = 0 := by
  constructor
  · intro hy
    set L₀ : Lvl k K Ω := Classical.arbitrary (Lvl k K Ω) with hL₀
    have h0 : (0 : ClassLevelLimit (k := k) (K := K) (Ω := Ω))
        = (⟦⟨L₀, (0 : ClassLevel L₀)⟩⟧ : ClassLevelLimit (k := k) (K := K) (Ω := Ω)) :=
      DirectLimit.zero_def L₀
    have heq : (⟦⟨L, y⟩⟧ : ClassLevelLimit (k := k) (K := K) (Ω := Ω))
        = (⟦⟨L₀, (0 : ClassLevel L₀)⟩⟧ : ClassLevelLimit (k := k) (K := K) (Ω := Ω)) := by
      rw [← h0]
      exact hy
    obtain ⟨j, hy', hz', heq'⟩ := Quotient.exact heq
    refine ⟨j, hy', ?_⟩
    have : classLevelMap (k := k) L₀ j hz' (0 : ClassLevel L₀) = 0 := map_zero _
    rw [this] at heq'
    exact heq'
  · rintro ⟨L', h, hz⟩
    rw [← ClassLevelLimit.of_levelMap (k := k) (K := K) (Ω := Ω) h y, hz]
    exact ClassLevelLimit.of_zero (k := k) (K := K) (Ω := Ω) L'

/-- Induction on the class-group colimit. -/
protected theorem ClassLevelLimit.induction
    {C : ClassLevelLimit (k := k) (K := K) (Ω := Ω) → Prop}
    (ih : ∀ (L : Lvl k K Ω) (y : ClassLevel L),
      C (ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L y))
    (x : ClassLevelLimit (k := k) (K := K) (Ω := Ω)) : C x :=
  DirectLimit.induction (f := fun i j h => classLevelMap (k := k) i j h)
    (fun L y => ih L y) x

/-- The universal property of the class-group colimit. -/
noncomputable def ClassLevelLimit.lift {A : Type} [AddCommMonoid A]
    (g : ∀ L : Lvl k K Ω, ClassLevel L →+ A)
    (hg : ∀ (L L' : Lvl k K Ω) (h : L ≤ L') (y : ClassLevel L),
      g L' (classLevelMap (k := k) L L' h y) = g L y) :
    ClassLevelLimit (k := k) (K := K) (Ω := Ω) →+ A where
  toFun := DirectLimit.lift (fun i j h => classLevelMap (k := k) i j h) (fun L => g L)
    (fun L L' h y => (hg L L' h y).symm)
  map_zero' := by
    simpa only using
      DirectLimit.lift_zero (f := fun i j h => classLevelMap (k := k) i j h) (g := fun L => g L)
        (fun L L' h x => (hg L L' h x).symm)
  map_add' x y := by
    simpa only using
      DirectLimit.lift_add (f := fun i j h => classLevelMap (k := k) i j h) (g := fun L => g L)
        (fun L L' h x => (hg L L' h x).symm) x y

@[simp] theorem ClassLevelLimit.lift_of {A : Type} [AddCommMonoid A]
    (g : ∀ L : Lvl k K Ω, ClassLevel L →+ A)
    (hg : ∀ (L L' : Lvl k K Ω) (h : L ≤ L') (y : ClassLevel L),
      g L' (classLevelMap (k := k) L L' h y) = g L y)
    (L : Lvl k K Ω) (y : ClassLevel L) :
    ClassLevelLimit.lift (k := k) (K := K) (Ω := Ω) g hg
        (ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L y) = g L y := rfl

@[ext] theorem ClassLevelLimit.hom_ext {A : Type} [AddCommMonoid A]
    {g₁ g₂ : ClassLevelLimit (k := k) (K := K) (Ω := Ω) →+ A}
    (h : ∀ L : Lvl k K Ω,
      g₁.comp (ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L)
        = g₂.comp (ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L)) : g₁ = g₂ := by
  apply AddMonoidHom.ext
  intro x
  exact ClassLevelLimit.induction (k := k) (K := K) (Ω := Ω)
    (C := fun y => g₁ y = g₂ y)
    (fun L z => by
      have hz := congrArg (fun f : ClassLevel L →+ A => f z) (h L)
      simpa only [AddMonoidHom.coe_comp, Function.comp_apply] using hz) x

end Work.SSGRoute
