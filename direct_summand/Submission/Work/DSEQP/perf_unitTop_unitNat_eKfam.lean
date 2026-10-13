import Mathlib
import Submission.Work.DSEQP.PerfCech
import Submission.Work.DSEQP.PerfUnit
import Submission.Work.DSMap.Map
import Submission.Work.DSMap.Mix2

namespace Work.DSEQP

open CategoryTheory AlgebraicGeometry

universe u

set_option maxHeartbeats 1000000

/-- The degree-`0` component of the compatibility of the level-`0` map
`𝒪_X → 𝒪_X^{1/p^∞}` with the coaugmentations: on the component `a` of the Čech degree-`0`
term, `unitTop ≫ (cechPresheaf).map ≫ unitNat` agrees with `unitA ψ ≫ (restrictScalars ψ).map
(eKfam a)`.  Both sides send `1` to `1` (they are the `A`-linear maps `A → S.W` given by the
structure map and the diagonal), which is what the proof checks. -/
theorem perf_unitTop_unitNat_eKfam {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
    {X : AlgebraicGeometry.Scheme.{u}}
    {f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)}
    (S : Work.DSEQP.PerfSetup A p X f) {ι : Type u} (U : ι → X.Opens)
    (a : (Work.DSEQP.PerfSetup.CechIdx U 0).I) :
    CategoryTheory.CategoryStruct.comp (DSMap.unitTop A X f)
        (CategoryTheory.CategoryStruct.comp
          ((DSMap.cechPresheaf A X f).map (CategoryTheory.homOfLE le_top).op)
          (Work.DSEQP.PerfSetup.unitNat S |>.app (Opposite.op (Work.DSEQP.PerfSetup.CechOp U 0 a)))) =
      CategoryTheory.CategoryStruct.comp (DSMap.Mix2.unitA (S.ψW.comp (DSMap.phi A X f)))
        ((ModuleCat.restrictScalars (S.ψW.comp (DSMap.phi A X f))).map (S.eKfam U a)) := by
  have hU : (DSMap.unitTop A X f).hom (1 : A) = (1 : Γ(X, ⊤)) := by
    change S.resTop ⊤ (DSMap.phi A X f 1) = 1
    rw [map_one (DSMap.phi A X f), map_one (S.resTop ⊤)]
  have hC : (ModuleCat.Hom.hom ((DSMap.cechPresheaf A X f).map
        (CategoryTheory.homOfLE (le_top : Work.DSEQP.PerfSetup.CechOp U 0 a ≤ ⊤)).op))
        (1 : Γ(X, ⊤)) = (1 : Γ(X, Work.DSEQP.PerfSetup.CechOp U 0 a)) := by
    change S.resTop (Work.DSEQP.PerfSetup.CechOp U 0 a) 1 = 1
    exact map_one _
  have hN : (S.unitNat.app (Opposite.op (Work.DSEQP.PerfSetup.CechOp U 0 a))).hom
      (1 : Γ(X, Work.DSEQP.PerfSetup.CechOp U 0 a)) =
      (1 : S.Psec (Work.DSEQP.PerfSetup.CechOp U 0 a)) := by
    change Perf.of (Γ(X, Work.DSEQP.PerfSetup.CechOp U 0 a)) p
      (S.hpU (Work.DSEQP.PerfSetup.CechOp U 0 a)) 0 1 = 1
    exact map_one _
  have hA : (DSMap.Mix2.unitA (S.ψW.comp (DSMap.phi A X f))).hom (1 : A) = (1 : S.W) := by
    change (S.ψW.comp (DSMap.phi A X f)) 1 = 1
    exact map_one _
  have hE : CategoryTheory.ConcreteCategory.hom (S.eKfam U a) (1 : S.W) =
      (1 : S.Psec (Work.DSEQP.PerfSetup.CechOp U 0 a)) := by
    change S.Wmap (Work.DSEQP.PerfSetup.CechOp U 0 a) 1 = 1
    exact map_one _
  apply ModuleCat.hom_ext
  refine LinearMap.ext_ring ?_
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [ModuleCat.restrictScalars.map_apply]
  rw [hU, hC, hN, hA, hE]

end Work.DSEQP
