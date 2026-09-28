import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Cohomology.isZero_dualComplex_empty
import Submission.Work.StemsB.collarSqEval

set_option autoImplicit false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits
open scoped Topology Simplicial

namespace Work.StemsB

noncomputable section

/-- There are no singular `n`-simplices in an empty space. -/
theorem isEmpty_singularSimplex_of_isEmpty (Y : Type) [TopologicalSpace Y] (hY : IsEmpty Y) (n : ℕ) :
    IsEmpty ((TopCat.toSSet.obj (TopCat.of Y)).obj (Opposite.op ⦋n⦌)) := by
  refine ⟨fun f => ?_⟩
  have hf := (TopCat.toSSetObjEquivT (TopCat.of Y) (Opposite.op ⦋n⦌)) f
  haveI : Nonempty (↑(stdSimplex ℝ (Fin ((Opposite.unop (Opposite.op ⦋n⦌)).len + 1)))) :=
    inferInstance
  exact hY.false (hf (Classical.arbitrary _))

/-- The `n`-th term of the singular cochain complex of an empty space is a zero object. -/
theorem isZero_singularCochainComplex_X_of_isEmpty (Y : Type) [TopologicalSpace Y]
    (hY : IsEmpty Y) (n : ℕ) :
    IsZero ((Work.Cohomology.singularCochainComplex ℤ (TopCat.of Y)).X n) := by
  refine Work.Cohomology.isZero_dualObj_of_isZero ℤ (Work.Cohomology.singularChains ℤ (TopCat.of Y)) ?_ n
  intro m
  haveI : IsEmpty ((TopCat.toSSet.obj (TopCat.of Y)).obj (Opposite.op ⦋m⦌)) :=
    isEmpty_singularSimplex_of_isEmpty Y hY m
  exact Work.Cohomology.isZero_coproduct_of_isEmpty
    (fun _ : (TopCat.toSSet.obj (TopCat.of Y)).obj (Opposite.op ⦋m⦌) => ModuleCat.of ℤ ℤ)

/-- A cochain complex whose `m`-th term is a zero object has vanishing `m`-th homology. -/
theorem isZero_homology_of_isZero_X_cochain {K : CochainComplex (ModuleCat ℤ) ℕ} (m : ℕ)
    (h : IsZero (K.X m)) : IsZero (K.homology m) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact ShortComplex.exact_of_isZero_X₂ _ h

/-- **The singular cohomology of an empty space vanishes in every degree.** -/
theorem subsingleton_Coh_of_isEmpty (Y : Type) [TopologicalSpace Y] (hY : IsEmpty Y) (n : ℕ) :
    Subsingleton (Work.Thom.Coh ℤ n Y) :=
  ModuleCat.subsingleton_of_isZero
    (isZero_homology_of_isZero_X_cochain n (isZero_singularCochainComplex_X_of_isEmpty Y hY n))

end

end Work.StemsB
