import Mathlib
import Submission.Work.HomologyExtra.SimplexCircleCover

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

namespace Work.HomologyExtra

noncomputable section

/-- The topological space `circleU ∩ circleV`, as an object of `TopCat`. -/
abbrev circleInterSpace : TopCat := TopCat.of ↥(circleU ∩ circleV)

/-- The singular simplicial set of `circleU ∩ circleV`. -/
abbrev circleInterSSet : SSet := TopCat.toSSet.obj circleInterSpace

/-- The cycle condition for a `0`-simplex is vacuous: the differential `d 0 j` of the singular
chain complex of a simplicial set vanishes for every `j`, in particular for `j = next 0`. -/
theorem iChainComplex_d_next_zero (X : SSet) (R : ModuleCat ℤ) (x : X _⦋0⦌) :
    X.ιChainComplex x ≫ (X.chainComplex R).d 0 ((ComplexShape.down ℕ).next 0) = 0 := by
  have hnext : (ComplexShape.down ℕ).next 0 = 0 :=
    ComplexShape.next_eq_self' _ 0 (fun k hk => by simp [ComplexShape.down_Rel] at hk)
  rw [hnext]
  simp

/-- **The class of the chain of a `0`-simplex**, followed by the identification of `H₀` with the
free module on `π₀`, is the corresponding basis element. -/
theorem cycleClass_ιChainComplex_homology₀Iso (X : SSet) (R : ModuleCat ℤ) (x : X _⦋0⦌)
    (hx : X.ιChainComplex x ≫ (X.chainComplex R).d 0 ((ComplexShape.down ℕ).next 0) = 0) :
    cycleClass (X.ιChainComplex x) hx ≫ (X.homology₀Iso R).hom =
      Sigma.ι (fun _ => R) (SSet.π₀.mk x) := by
  rw [cycleClass_def]
  simpa using SSet.liftCycles_ιChainComplex_homologyπ_homology₀Iso_hom X R x

/-- **Additivity of `liftCycles` in the chain**: the lift of a difference of cycles is the
difference of the lifts. -/
theorem liftCycles_sub {K : ChainComplex (ModuleCat ℤ) ℕ} {A : ModuleCat ℤ} {i : ℕ}
    (k₁ k₂ : A ⟶ K.X i) (h₁ : k₁ ≫ K.d i ((ComplexShape.down ℕ).next i) = 0)
    (h₂ : k₂ ≫ K.d i ((ComplexShape.down ℕ).next i) = 0)
    (h : (k₁ - k₂) ≫ K.d i ((ComplexShape.down ℕ).next i) = 0) :
    K.liftCycles (k₁ - k₂) ((ComplexShape.down ℕ).next i) rfl h
      = K.liftCycles k₁ ((ComplexShape.down ℕ).next i) rfl h₁
        - K.liftCycles k₂ ((ComplexShape.down ℕ).next i) rfl h₂ := by
  rw [← cancel_mono (K.iCycles i), Preadditive.sub_comp, HomologicalComplex.liftCycles_i,
    HomologicalComplex.liftCycles_i, HomologicalComplex.liftCycles_i]

/-- **Additivity of `cycleClass` in the chain**: the class of a difference of cycles is the
difference of the classes. -/
theorem cycleClass_sub {K : ChainComplex (ModuleCat ℤ) ℕ} {A : ModuleCat ℤ} {i : ℕ}
    (k₁ k₂ : A ⟶ K.X i) (h₁ : k₁ ≫ K.d i ((ComplexShape.down ℕ).next i) = 0)
    (h₂ : k₂ ≫ K.d i ((ComplexShape.down ℕ).next i) = 0)
    (h : (k₁ - k₂) ≫ K.d i ((ComplexShape.down ℕ).next i) = 0) :
    cycleClass (k₁ - k₂) h = cycleClass k₁ h₁ - cycleClass k₂ h₂ := by
  rw [cycleClass_def, cycleClass_def, cycleClass_def, liftCycles_sub, Preadditive.sub_comp]

theorem circlePsi_apply :
    CategoryTheory.CategoryStruct.comp
        (Work.HomologyExtra.cycleClass Work.HomologyExtra.circleIntersectionChain
          Work.HomologyExtra.circleIntersectionChain_cycle)
        Work.HomologyExtra.circlePsi
      = CategoryTheory.CategoryStruct.id Work.Homology.ZMod := by
  classical
  have hV1 : circleInterSSet.ιChainComplex (simplexPoint (X := circleInterSpace) circleInterV1)
      ≫ (circleInterSSet.chainComplex Work.Homology.ZMod).d 0
          ((ComplexShape.down ℕ).next 0) = 0 :=
    iChainComplex_d_next_zero _ _ _
  have hV2 : circleInterSSet.ιChainComplex (simplexPoint (X := circleInterSpace) circleInterV2)
      ≫ (circleInterSSet.chainComplex Work.Homology.ZMod).d 0
          ((ComplexShape.down ℕ).next 0) = 0 :=
    iChainComplex_d_next_zero _ _ _
  have hA : cycleClass (K := circleInterSSet.chainComplex Work.Homology.ZMod)
        (circleInterSSet.ιChainComplex (simplexPoint (X := circleInterSpace) circleInterV2)) hV2
      ≫ ((circleInterSSet.homology₀Iso Work.Homology.ZMod).hom
          ≫ Sigma.desc (fun c => if c = SSet.π₀.mk
              (simplexPoint (X := circleInterSpace) circleInterV2) then 𝟙 Work.Homology.ZMod else 0))
      = 𝟙 Work.Homology.ZMod := by
    rw [← Category.assoc,
      cycleClass_ιChainComplex_homology₀Iso circleInterSSet Work.Homology.ZMod
        (simplexPoint (X := circleInterSpace) circleInterV2) hV2]
    simp
  have hB : cycleClass (K := circleInterSSet.chainComplex Work.Homology.ZMod)
        (circleInterSSet.ιChainComplex (simplexPoint (X := circleInterSpace) circleInterV1)) hV1
      ≫ ((circleInterSSet.homology₀Iso Work.Homology.ZMod).hom
          ≫ Sigma.desc (fun c => if c = SSet.π₀.mk
              (simplexPoint (X := circleInterSpace) circleInterV2) then 𝟙 Work.Homology.ZMod else 0))
      = 0 := by
    rw [← Category.assoc,
      cycleClass_ιChainComplex_homology₀Iso circleInterSSet Work.Homology.ZMod
        (simplexPoint (X := circleInterSpace) circleInterV1) hV1]
    simp [piZero_mk_simplexPoint_ne]
  rw [circlePsi]
  simp only [circleIntersectionChain]
  rw [cycleClass_sub _ _ hV2 hV1 circleIntersectionChain_cycle]
  rw [Preadditive.sub_comp, hA, hB]
  simp

end

end Work.HomologyExtra
