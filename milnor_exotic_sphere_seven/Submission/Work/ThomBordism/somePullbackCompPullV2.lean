import Mathlib
import Submission.Work.ThomBordism.chartModelClassDefs
import Submission.Work.Cohomology.capRelAux
import Submission.Work.Tubular.ThomComparison

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `compPull` is the pullback along `some`

A copy of `Work.ThomBordism.some_pullback_eq_compPull` (`cla_localisation.lean`) that does **not**
import `Submission.Work.ThomBordism.collapseLocalisation_ambientV2`, so that the target file can use
it without an import cycle.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Work.ThomBordism

noncomputable section

open CategoryTheory
open Work.Tubular

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- **`compPull` is the pullback along `some`.** -/
theorem some_pullback_eq_compPull (E : PontryaginThom.EmbeddingData V (8 + k)) (n : ℕ)
    (β : Work.Thom.RelCoh ℤ n (OnePoint (NormalTotal E)) (onePointNonzero E)) :
    (Work.Thom.relCohMap (⟨OnePoint.some, OnePoint.continuous_coe⟩) (normalNonzero E)
        (onePointNonzero E)
        (fun x hx => mem_onePointNonzero.mpr (Or.inr ⟨x, mem_normalNonzero.mp hx, rfl⟩)) ℤ n).hom β
      = (compPull E n) β := by
  have hid : (infComplIncl E).comp ⟨fun x => homeoV E x, (homeoV E).continuous_toFun⟩
      = ⟨OnePoint.some, OnePoint.continuous_coe⟩ := by
    ext x
    exact homeoV_apply E x
  have hcomp := Work.Thom.relCohMap_compA (X := NormalTotal E)
    (Y := ↥(infCompl E)) (Z := OnePoint (NormalTotal E))
    (A := normalNonzero E) (B := excSub E) (C := onePointNonzero E)
    (f := ⟨fun x => homeoV E x, (homeoV E).continuous_toFun⟩) (g := infComplIncl E)
    (hf := fun x hx => (homeoV_mem E x).mp hx)
    (hg := fun y hy => hy)
    (hgf := fun x hx => mem_onePointNonzero.mpr
      (Or.inr ⟨x, mem_normalNonzero.mp hx, rfl⟩)) ℤ n
  have hcongr := Work.Thom.relCohMap_congrA (A := normalNonzero E) (B := onePointNonzero E)
    hid (fun x hx => mem_onePointNonzero.mpr (Or.inr ⟨x, mem_normalNonzero.mp hx, rfl⟩))
    (fun x hx => mem_onePointNonzero.mpr (Or.inr ⟨x, mem_normalNonzero.mp hx, rfl⟩)) ℤ n
  have htotal : (Work.Thom.relCohMap (infComplIncl E) (excSub E) (onePointNonzero E)
        (fun y hy => hy) ℤ n
      ≫ Work.Thom.relCohMap (⟨fun x => homeoV E x, (homeoV E).continuous_toFun⟩)
          (normalNonzero E) (excSub E) (fun x hx => (homeoV_mem E x).mp hx) ℤ n)
      = Work.Thom.relCohMap (⟨OnePoint.some, OnePoint.continuous_coe⟩) (normalNonzero E)
          (onePointNonzero E)
          (fun x hx => mem_onePointNonzero.mpr (Or.inr ⟨x, mem_normalNonzero.mp hx, rfl⟩)) ℤ n :=
    hcomp.trans hcongr
  rw [show (compPull E n) β = (Work.Thom.relCohMap (infComplIncl E) (excSub E)
        (onePointNonzero E) (fun y hy => hy) ℤ n
      ≫ Work.Thom.relCohMap (⟨fun x => homeoV E x, (homeoV E).continuous_toFun⟩)
          (normalNonzero E) (excSub E) (fun x hx => (homeoV_mem E x).mp hx) ℤ n).hom β from rfl,
    htotal]



end

end Work.ThomBordism
