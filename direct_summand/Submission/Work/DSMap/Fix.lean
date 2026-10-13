import Submission.Work.DSMap.Map

/-! # DSMap.Fix — lead contract repairs (curric-46, 10-13)

* **G1U** replaces `DSMap.area_G1_pullback.{a,b,c,d}`. With `d` arbitrary the frozen statement is
  unprovable: `DSplit.{a,b,d} A X' _` quantifies over `HasDerivedCategory.{d}` instances, and when
  there are none at level `d` the hypothesis is vacuous (DSG1 report, 10-13). `main_dsplit` uses only
  `d = a + 1`, where `HasDerivedCategory.standard` provides the instance. `EnoughInjectives` for
  `SheafOfModules X'.ringCatSheaf` holds because it is Grothendieck abelian, but it is not an
  instance in Mathlib, so the prover builds it. -/

open CategoryTheory AlgebraicGeometry

namespace DSMap.Fix

theorem area_G1_pullbackU.{a, b, c} (A : Type a) [CommRing A] {X X' : Scheme.{a}}
    (f : X ⟶ Spec (.of A)) (g : X' ⟶ X) [IsProper f] [IsProper (g ≫ f)] :
    DSplit.{a, b, a + 1} A X' (g ≫ f) → DSplit.{a, b, c} A X f := sorry

end DSMap.Fix
