import Mathlib
import Submission.Work.DSCOH.Norm.Maps
import Submission.Work.DSCOH.Norm.cechComplexFunctor_d_comp

namespace Work.DSCOH.Norm

universe u v w m

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory Limits Opposite TopologicalSpace
open scoped Simplicial BigOperators

/-! ## A component formula for the unnormalized Čech differential

`Work.DSCOH.Norm.cechComplexFunctor_d_comp` states the component formula for the differential of
Mathlib's unnormalized Čech complex using `ModuleCat.{0}` (the module category at the lowest
universe).  `semiProj` and `semiD` are however universe-polymorphic in the universe of the module
category, so the comparison of `semiProj` with the Čech differential needs the formula at the
matching universe.  Below we reprove it at the universe where the object universe of the module
category is `max w m` (`w` the universe of the index type), which is exactly the shape that both
`cechCosimp_δ` and `cechComplexFunctor_d_eq` are available at. -/

/-- The component formula for the differential of Mathlib's unnormalized Čech complex, at the
universe level at which `semiProj`/`semiD` live. -/
theorem cechComplexFunctor_d_comp_gen {X : Type u} [TopologicalSpace X] {A : Type v} [CommRing A]
    {ι : Type w} [Fintype ι] [LinearOrder ι]
    [CategoryTheory.Limits.HasProducts.{w, max w m, max v ((max w m)+1)} (ModuleCat.{max w m, v} A)]
    (P : CategoryTheory.Functor (Opposite (TopologicalSpace.Opens X)) (ModuleCat.{max w m, v} A))
    (U : ι → TopologicalSpace.Opens X) (n : ℕ) :
    ((CategoryTheory.cechComplexFunctor U).obj P).d n (n + 1) =
      CategoryTheory.Limits.Pi.lift (fun x : Fin (n + 2) → ι =>
        ∑ b : Fin (n + 2), (-1 : ℤ) ^ (b : ℕ) •
          (CategoryTheory.Limits.Pi.π
              (fun y : Fin (n + 1) → ι => Work.DSCOH.Norm.tupleMod P U y)
              (Work.DSCOH.Norm.del x b) ≫ Work.DSCOH.Norm.resDel P U x b)) := by
  rw [cechComplexFunctor_d_eq P U n]
  apply CategoryTheory.Limits.Pi.hom_ext
    (f := fun y : Fin (n + 2) → ι => Work.DSCOH.Norm.tupleMod P U y)
  intro x
  have key : ∀ b : Fin (n+2), (cechCosimp P U).δ b ≫
      CategoryTheory.Limits.Pi.π (fun y : Fin (n+2) → ι => Work.DSCOH.Norm.tupleMod P U y) x =
      CategoryTheory.Limits.Pi.π (fun y : Fin (n+1) → ι => Work.DSCOH.Norm.tupleMod P U y)
        (Work.DSCOH.Norm.del x b) ≫ Work.DSCOH.Norm.resDel P U x b := by
    intro b
    rw [cechCosimp_δ P U b]
    exact CategoryTheory.Limits.Pi.lift_comp_π _ _
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, CategoryTheory.Limits.Pi.lift_comp_π, key]

/-! ## The component formulas for `semiProj` and `semiD` -/

/-- The `y`-component of `semiProj P U n` is the projection onto the same (nondecreasing) tuple. -/
private lemma semiProj_π {X : Type u} [TopologicalSpace X] {A : Type v} [CommRing A]
    {ι : Type w} [Fintype ι] [LinearOrder ι] [CategoryTheory.Limits.HasProducts (ModuleCat A)]
    (P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → TopologicalSpace.Opens X)
    (n : ℕ) (y : SemiIdx ι n) :
    semiProj P U n ≫ Pi.π (fun x : SemiIdx ι n => tupleMod P U x.val) y =
      Pi.π (fun y' : Fin (n + 1) → ι => tupleMod P U y') y.val := by
  rw [semiProj]; exact Pi.lift_comp_π _ _

/-- The `y`-component of `semiD P U n` is the alternating sum over the entries `b` of `y` of the
"delete the `b`-th entry and restrict" map. -/
private lemma semiD_π {X : Type u} [TopologicalSpace X] {A : Type v} [CommRing A]
    {ι : Type w} [Fintype ι] [LinearOrder ι] [CategoryTheory.Limits.HasProducts (ModuleCat A)]
    (P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → TopologicalSpace.Opens X)
    (n : ℕ) (y : SemiIdx ι (n+1)) :
    semiD P U n ≫ Pi.π (fun x : SemiIdx ι (n+1) => tupleMod P U x.val) y =
      ∑ b : Fin (n + 2), (-1 : ℤ) ^ (b : ℕ) •
        (Pi.π (fun y' : SemiIdx ι n => tupleMod P U y'.val)
          ⟨del y.val b, monotone_del y.val b y.property⟩ ≫ resDel P U y.val b) := by
  rw [semiD]; exact Pi.lift_comp_π _ _

theorem semiProj_chain {X : Type u} [TopologicalSpace X] {A : Type v} [CommRing A]
    {ι : Type w} [Fintype ι] [LinearOrder ι]
    [CategoryTheory.Limits.HasProducts (ModuleCat A)]
    (P : CategoryTheory.Functor (Opposite (TopologicalSpace.Opens X)) (ModuleCat A))
    (U : ι → TopologicalSpace.Opens X) (n : ℕ) :
    CategoryTheory.CategoryStruct.comp (Work.DSCOH.Norm.semiProj P U n)
        (Work.DSCOH.Norm.semiD P U n)
      = CategoryTheory.CategoryStruct.comp
          (((CategoryTheory.cechComplexFunctor U).obj P).d n (n + 1))
          (Work.DSCOH.Norm.semiProj P U (n + 1)) := by
  apply Pi.hom_ext (f := fun x : SemiIdx ι (n + 1) => tupleMod P U x.val)
  intro x
  have hL : (semiProj P U n ≫ semiD P U n) ≫
        Pi.π (fun x : SemiIdx ι (n+1) => tupleMod P U x.val) x
      = ∑ b : Fin (n+2), (-1:ℤ)^(b:ℕ) •
          (Pi.π (fun y : Fin (n+1) → ι => tupleMod P U y) (del x.val b) ≫
            resDel P U x.val b) := by
    rw [Category.assoc]
    rw [semiD_π]
    simp only [Preadditive.comp_sum, Preadditive.comp_zsmul]
    apply Finset.sum_congr rfl
    intro b _
    exact congrArg (fun t => ((-1:ℤ)^(b:ℕ)) • t)
      ((Category.assoc (semiProj P U n)
          (Pi.π (fun y' : SemiIdx ι n => tupleMod P U y'.val)
            ⟨del x.val b, monotone_del x.val b x.property⟩)
          (resDel P U x.val b)).symm.trans
        (congrArg (fun t => t ≫ resDel P U x.val b)
          (semiProj_π P U n ⟨del x.val b, monotone_del x.val b x.property⟩)))
  have hR : ((CategoryTheory.cechComplexFunctor U).obj P).d n (n+1) ≫
        Pi.π (fun y : Fin (n+1+1) → ι => tupleMod P U y) x.val
      = ∑ b : Fin (n+2), (-1:ℤ)^(b:ℕ) •
          (Pi.π (fun y : Fin (n+1) → ι => tupleMod P U y) (del x.val b) ≫
            resDel P U x.val b) := by
    refine Eq.trans (congrArg (fun t => t ≫ Pi.π (fun y : Fin (n+1+1) → ι => tupleMod P U y) x.val)
      (cechComplexFunctor_d_comp_gen P U n)) ?_
    exact Pi.lift_comp_π _ _
  have hDS : (((CategoryTheory.cechComplexFunctor U).obj P).d n (n+1) ≫ semiProj P U (n+1)) ≫
        Pi.π (fun x : SemiIdx ι (n+1) => tupleMod P U x.val) x
      = ((CategoryTheory.cechComplexFunctor U).obj P).d n (n+1) ≫
        Pi.π (fun y : Fin (n+1+1) → ι => tupleMod P U y) x.val :=
    (Category.assoc _ _ _).trans (congrArg
      (fun t => ((CategoryTheory.cechComplexFunctor U).obj P).d n (n+1) ≫ t)
      (semiProj_π P U (n+1) x))
  exact hL.trans (hR.symm.trans hDS.symm)

end Work.DSCOH.Norm
