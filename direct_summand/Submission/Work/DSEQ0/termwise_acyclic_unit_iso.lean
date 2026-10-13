import Mathlib
import Submission.Work.DSEQ0.WTA_main

/-!
# The unit of the right derived functor at a complex of acyclic objects

Let `F : C ⥤ D` be an additive, left exact functor between abelian categories, `C` having
enough injectives, and let `K` be a bounded below cochain complex of `C` all of whose terms
are `F`-acyclic.  Then the unit `F.rightDerivedFunctorPlusUnit.app K` of the right derived
functor of `F` is an isomorphism.

The auxiliary modules `Submission.Work.DSEQ0.WTA_trunc` (the degreewise split naive truncation
short exact sequence of a bounded below complex, and the associated distinguished triangle) and
`Submission.Work.DSEQ0.WTA_main` (the truncation induction, in namespace `Work.DSEQ0.TA`)
contain the proof.
-/

namespace Work.DSEQ0

universe u v w x

open CategoryTheory CategoryTheory.Limits

theorem termwise_acyclic_unit_iso {C : Type u} [CategoryTheory.Category.{v} C]
    [CategoryTheory.Abelian C] {D : Type w} [CategoryTheory.Category.{x} D]
    [CategoryTheory.Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    [CategoryTheory.EnoughInjectives C]
    (F : C ⥤ D) [F.Additive] [CategoryTheory.Limits.PreservesFiniteLimits F]
    (K : CochainComplex.Plus C)
    (hK : ∀ (n : ℤ) (q : ℕ), 0 < q →
      CategoryTheory.Limits.IsZero ((F.rightDerived q).obj (K.obj.X n))) :
    CategoryTheory.IsIso (F.rightDerivedFunctorPlusUnit.app K) := by
  refine TA.unitIsoAcyclic F K (fun n => ?_)
  exact TA.isIsoUnitSingle_of_acyclic F (K.obj.X n) (fun q hq => hK n q hq) n

end Work.DSEQ0
