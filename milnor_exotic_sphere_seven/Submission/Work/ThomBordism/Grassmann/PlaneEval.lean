import Mathlib
import Submission.Work.ThomBordism.Grassmann.EvalBundle
import Submission.Work.ThomBordism.Grassmann.Rotation
import Submission.Work.Thom.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open scoped Topology

namespace Work.ThomBordism.Grassmann

noncomputable section

variable {k m : ℕ}

/-- `w` is a vector of the plane `P`. -/
def memPlane (P : OG k m) (w : Amb (k+m)) : Prop :=
  ∃ f : Stiefel k m, Quotient.mk'' f = P ∧
    w ∈ Submodule.span ℝ (Set.range (f.1 : Fin k → Amb (k+m)))

/-- **The fibre coordinate of an ambient vector of the plane**, read over the chart `S` and with the
orientation gauge applied. -/
noncomputable def toECoordAt (S : ChartIdx k m) (P : OG k m) (w : Amb (k+m)) : Amb k :=
  matLin (orientMat S P) (WithLp.toLp 2 (coordProj S (WithLp.ofLp w)))

/-- **`toECoordAt` is the inverse of the chart evaluation**: the vector of the plane with the fibre
coordinate `toECoordAt S P w` is `w` itself. -/
theorem evalChartO_toECoordAt (S : ChartIdx k m) (P : OG k m) (hPS : P ∈ baseSet S)
    (w : Amb (k+m)) (hw : memPlane P w) :
    evalChartO S ⟨P, hPS⟩ (toECoordAt S P w) = w := by
  obtain ⟨f, hf, hwspan⟩ := hw
  subst hf
  have hfc : f ∈ chartSet S :=
    (mem_baseSet_iff S f).mp (show Quotient.mk'' f ∈ baseSet S from hPS)
  show evalChartO S ⟨Quotient.mk'' f, (mem_baseSet_iff S f).mpr hfc⟩ (toECoordAt S _ w) = w
  rw [evalChartO_spec S f hfc (toECoordAt S (Quotient.mk'' f) w), toECoordAt]
  have hinv : matLin (orientMat S (Quotient.mk'' f)) (matLin (orientMat S (Quotient.mk'' f))
      (WithLp.toLp 2 (coordProj S (WithLp.ofLp w))))
      = WithLp.toLp 2 (coordProj S (WithLp.ofLp w)) := by
    rw [← ContinuousLinearMap.comp_apply, ← matLin_mul,
      orientMat_mul_self (S := S) (x := Quotient.mk'' f) hPS]
    simp
  rw [hinv]
  exact coordEval_coordProj S f hfc hwspan

/-- **The chart evaluation is additive in the fibre coordinate**, in particular it kills `0`. -/
theorem peEvalChartO_zero (S : ChartIdx k m) (x : ↥(baseSet S)) : evalChartO S x 0 = 0 := by
  obtain ⟨f, hf⟩ : ∃ f : Stiefel k m, Quotient.mk'' f = (x : OG k m) := Quotient.exists_rep _
  have hfc : f ∈ chartSet S := (mem_baseSet_iff S f).mp (hf ▸ x.2)
  rw [evalChartO, evalChart_spec S x f hfc hf.symm]
  simp [coordEval]

/-- The fibre coordinate of a nonzero vector of the plane is nonzero. -/
theorem toECoordAt_ne_zero (S : ChartIdx k m) (P : OG k m) (hPS : P ∈ baseSet S)
    (w : Amb (k+m)) (hw0 : w ≠ 0) (hw : memPlane P w) :
    toECoordAt S P w ≠ 0 := by
  intro h0
  exact hw0 (by rw [← evalChartO_toECoordAt S P hPS w hw, h0, peEvalChartO_zero])

/-- **The point of the zero complement of the tautological bundle with prescribed plane and vector
of the plane.** -/
noncomputable def toE (P : OG k m) (w : Amb (k+m)) (hw0 : w ≠ 0) (hw : memPlane P w) :
    ↥(Work.Thom.zeroComplement (tautologicalBundle k m)) :=
  ⟨⟨P, toECoordAt ((tautologicalBundle k m).indexAt P) P w⟩, by
    rw [Work.Thom.mem_zeroComplement]
    exact toECoordAt_ne_zero _ P ((tautologicalBundle k m).mem_baseSet_at P) w hw0 hw⟩


end

end Work.ThomBordism.Grassmann
