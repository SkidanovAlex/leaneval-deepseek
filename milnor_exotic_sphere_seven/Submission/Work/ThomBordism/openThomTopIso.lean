import Mathlib
import Submission.Work.Tubular.LocalStep
import Submission.Work.Tubular.thomClass_span_top
import Submission.Work.Cohomology.h0Evaluation
import Submission.Work.Cohomology.singularCohomology_zero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped Simplicial

namespace Work.ThomBordism

/-- **`H⁰` of a path-connected space is `ℤ`.**  For a path-connected space `B` the zeroth singular
cohomology with `ℤ`-coefficients is a free `ℤ`-module of rank one: the unit class `oneH` generates it
(`Work.Cohomology.exists_smul_oneH`) and evaluation at the base point is a left inverse of the map
`m ↦ m • oneH` (`Work.Cohomology.h0Ev`). -/
noncomputable def cohZeroEquivInt (B : Type) [TopologicalSpace B] [PathConnectedSpace B] :
    Work.Thom.Coh ℤ 0 B ≃ₗ[ℤ] ℤ := by
  have hf1 : Work.Cohomology.h0Ev (TopCat.toSSet.obj (TopCat.of B))
      (Work.Cohomology.baseSimplex (TopCat.of B))
      (Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of B))) = 1 := by
    rw [Work.Cohomology.oneH, Work.Cohomology.h0Ev_classOf]
    exact Work.Cohomology.genEval_unitCochain ℤ _ _
  have hsmul : ∀ m : ℤ, Work.Cohomology.h0Ev (TopCat.toSSet.obj (TopCat.of B))
      (Work.Cohomology.baseSimplex (TopCat.of B))
      (m • Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of B))) = m := by
    intro m
    rw [map_zsmul, hf1, smul_eq_mul, mul_one]
  refine LinearEquiv.ofBijective (Work.Cohomology.h0Ev (TopCat.toSSet.obj (TopCat.of B))
    (Work.Cohomology.baseSimplex (TopCat.of B))) ⟨?_, ?_⟩
  · intro x y hxy
    obtain ⟨m, rfl⟩ := Work.Cohomology.exists_smul_oneH (TopCat.of B) x
    obtain ⟨m', rfl⟩ := Work.Cohomology.exists_smul_oneH (TopCat.of B) y
    rw [hsmul, hsmul] at hxy
    rw [hxy]
  · intro m
    exact ⟨m • Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of B)), hsmul m⟩

theorem openThomTopIso {V : Work.ThomBordism.Man8} {k : ℕ} {ι : Type} {hk : 1 ≤ k}
    (Z : Work.TangentClasses.RealBundle V.pt (Fin k → ℝ) ι) [PathConnectedSpace V.pt]
    (hZ : Nonempty (Work.Thom.ThomClass Z k)) :
    Nonempty (Work.Thom.OpenThom Z k ≅ ModuleCat.of ℤ ℤ) := by
  obtain ⟨T⟩ := hZ
  have hdeg : (0 : ℕ) + k = k := Nat.zero_add k
  have e0 : Work.Thom.OpenThom Z (0 + k) ≅ ModuleCat.of ℤ ℤ :=
    (LinearEquiv.toModuleIso (T.thomEquiv 0)).symm.trans
      (LinearEquiv.toModuleIso (cohZeroEquivInt V.pt))
  have e2 : Work.Thom.OpenThom Z (0 + k) ≅ Work.Thom.OpenThom Z k :=
    eqToIso (congrArg (fun m => Work.Thom.OpenThom Z m) hdeg)
  exact ⟨e2.symm.trans e0⟩

end Work.ThomBordism
