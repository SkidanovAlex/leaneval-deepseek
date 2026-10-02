import Mathlib
import Submission.Work.Whitney.cruxDefs
import Submission.Work.Whitney.Basic
import Submission.Work.Gen.eSymClass
import Submission.Work.LerayHirsch.LineSum
import Submission.Work.Thom.chernClass_comap
import Submission.Work.Thom.complexPullback

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# Naturality of the delta form of the crux under a change of base

The `ψ`-analysis of the crux of the Whitney sum formula (`PLAN_universality_v3.md`) produces, for
every family `M : Fin N → (complex line bundles over B)`, a degree-`0` class `δ` of `B` with

  `c_{N-1}(lineSumCore N M) = deltaCup N M δ`

(`Work.Whitney.cruxDeltaForm`).  The **product argument** of `PLAN_universality_v3.md` restricts
this relation to the slices of `B₀ × B`, so it needs the relation to be *natural*: pulling it back
along `f : C(B', B)` gives the relation for the pulled-back family with coefficient
`(CohMap f) δ`.  This file proves that (`Work.Whitney.cruxRel_comap`), together with the two
ingredients: the pullback commutes with the iterated sum (`lineSumCore_bundleComap`, an equality,
by `Work.Whitney.whitneySum_bundleComap`) and `eSym` is natural (`eSym_comap`).
-/

namespace Work.Whitney

open Work.TangentClasses Work.Thom

noncomputable section

/-- **The iterated sum of line bundles commutes with the pullback.**  (An equality of
`VectorBundleCore`s, by induction on `N` and the definitional `Work.Whitney.whitneySum_bundleComap`.)
-/
theorem lineSumCore_bundleComap {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    {ι : Type} (N : ℕ)
    (M : Fin N → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) (f : C(B', B)) :
    Work.LerayHirsch.lineSumCore N (fun i => Work.Thom.bundleComap (M i) f)
      = Work.Thom.bundleComap (Work.LerayHirsch.lineSumCore N M) f := by
  induction N with
  | zero =>
      rw [Work.LerayHirsch.lineSumCore_zero, Work.LerayHirsch.lineSumCore_zero]
      rfl
  | succ n ih =>
      rw [Work.LerayHirsch.lineSumCore_succ, Work.LerayHirsch.lineSumCore_succ,
        Work.Whitney.whitneySum_bundleComap]
      have hfamily : ((fun i => Work.Thom.bundleComap (M i) f) ∘ Fin.castSucc)
          = (fun i => Work.Thom.bundleComap ((M ∘ Fin.castSucc) i) f) := rfl
      rw [hfamily]
      rw [ih (M ∘ Fin.castSucc)]

/-- **`Work.Gen.eSym` is natural under a change of base.** -/
theorem eSym_comap {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    {ι : Type} [Fintype ι] {N : ℕ}
    (M : Fin N → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)
    (f : C(B', B)) (k : ℕ) :
    (Work.Thom.CohMap f ℤ (2 * k)).hom (Work.Gen.eSym N M k)
      = Work.Gen.eSym N (fun i => Work.Thom.bundleComap (M i) f) k := by
  rw [Work.Gen.eSym_eq_eSymC, Work.Gen.eSym_eq_eSymC, ← Work.Gen.eSymC_CohMap]
  refine Work.Gen.eSymC_congr (fun i => ?_) k
  exact (Work.Thom.chernClass_comap (m := 1) (j := 1) (M i) f).symm

/-- **Naturality of `Work.Whitney.deltaCup` under a change of base.** -/
theorem deltaCup_comap {N : ℕ}
    {B B' : Type} [TopologicalSpace B] [TopologicalSpace B'] {ι : Type} [Fintype ι]
    (M : Fin N → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)
    (f : C(B', B)) (δ : Work.Thom.Coh ℤ 0 B) :
    (Work.Thom.CohMap f ℤ (2 * (N - 1))).hom (Work.Whitney.deltaCup N M δ)
      = Work.Whitney.deltaCup N (fun i => Work.Thom.bundleComap (M i) f)
          ((Work.Thom.CohMap f ℤ 0).hom δ) := by
  unfold Work.Whitney.deltaCup
  rw [Work.Thom.cohTransport_CohMap,
      Work.Cohomology.cupNaturalH ℤ (TopCat.ofHom f) 0 (2 * (N - 1)) δ
        (Work.Gen.eSym N M (N - 1)),
      eSym_comap]

/-- **Naturality of the delta form of the crux under a change of base.** -/
theorem cruxRel_comap {N : ℕ}
    {B B' : Type} [TopologicalSpace B] [TopologicalSpace B'] {ι : Type} [Fintype ι]
    (M : Fin N → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)
    (f : C(B', B)) (δ : Work.Thom.Coh ℤ 0 B)
    (hδ : Work.Thom.chernClass N (N - 1) (Work.LerayHirsch.lineSumCore N M)
        = Work.Whitney.deltaCup N M δ) :
    Work.Thom.chernClass N (N - 1)
        (Work.LerayHirsch.lineSumCore N (fun i => Work.Thom.bundleComap (M i) f))
      = Work.Whitney.deltaCup N (fun i => Work.Thom.bundleComap (M i) f)
          ((Work.Thom.CohMap f ℤ 0).hom δ) := by
  rw [lineSumCore_bundleComap (N := N) M f, Work.Thom.chernClass_comap, hδ, deltaCup_comap]

end

end Work.Whitney
