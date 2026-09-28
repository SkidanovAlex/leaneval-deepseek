import Mathlib
import Submission.Work.ThomBordism.Grassmann.ChartFrame
import Submission.Work.ThomBordism.Grassmann.Oriented

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-!
# The evaluation of the tautological bundle: the vector attached to a point of the total space

`tautologicalBundle k m` is the *oriented* tautological bundle: its trivialisation over the chart
`baseSet S` is the coordinate projection composed with the orientation gauge `orientMat S` (so that
the transition determinants are positive, see `Oriented.lean`).  Accordingly the vector of the
plane represented by a point of the total space is read as follows.

* `evalChartO S` — the continuous map `baseSet S × Amb k → Amb (k+m)`,
  `(x, v) ↦ coordEval S x (matLin (orientMat S x) v)`: the vector of the plane with
  *oriented chart coordinates* `v`.  Its compatibility on overlaps uses the oriented transition
  function: `evalChartO S (x, v) = evalChartO T (x, coordChangeO S T x v)` (`evalChartO_glue`) —
  this is the statement that the fibre coordinate of the *oriented* tautological bundle is well
  defined.
* `evalVec` — the resulting continuous map (`continuous_evalVec`) from the total space
  `(tautologicalBundle k m).TotalSpace` to `Amb (k+m)`: **the vector of the plane at that point**.
  It vanishes exactly on the zero section, and the complement of the zero section is thereby
  described by the classical incidence data (plane, non-zero vector in it).
-/

open scoped Topology
open Work.TangentClasses

namespace Work.ThomBordism.Grassmann

noncomputable section

variable {k m : ℕ}

/-! ## The orientation gauge is continuous on the chart -/

theorem continuous_orientMat_subtype (S : ChartIdx k m) :
    Continuous fun x : ↥(baseSet S) => orientMat S (x : OG k m) := by
  exact continuousOn_iff_continuous_domRestrict.mp (continuousOn_orientMat S)

/-- The inverse of the orientation gauge, on the chart: `orientMat S` is an involution. -/
theorem orientMat_involutive (S : ChartIdx k m) (x : OG k m) (hx : x ∈ baseSet S) (w : Amb k) :
    matLin (orientMat S x) (matLin (orientMat S x) w) = w := by
  rw [← ContinuousLinearMap.comp_apply, ← matLin_mul, orientMat_mul_self x hx, matLin_one,
    ContinuousLinearMap.one_apply]

/-! ## The oriented chart evaluation -/

/-- **The vector of the plane with oriented `S`-coordinates `v`.** -/
def evalChartO (S : ChartIdx k m) (x : ↥(baseSet S)) (v : Amb k) : Amb (k+m) :=
  evalChart S (x, matLin (orientMat S (x : OG k m)) v)

theorem continuous_evalChartO (S : ChartIdx k m) :
    Continuous fun p : ↥(baseSet S) × Amb k => evalChartO S p.1 p.2 := by
  have hmat : Continuous fun p : ↥(baseSet S) × Amb k => matLin (orientMat S (p.1 : OG k m)) :=
    continuous_matLin.comp ((continuous_orientMat_subtype S).comp continuous_fst)
  exact (evalChart S).continuous.comp
    (continuous_fst.prodMk (hmat.clm_apply continuous_snd))

theorem evalChartO_spec (S : ChartIdx k m) (f : Stiefel k m) (hf : f ∈ chartSet S) (v : Amb k) :
    evalChartO S ⟨Quotient.mk'' f, (mem_baseSet_iff S f).mpr hf⟩ v
      = coordEval S f (matLin (orientMat S (Quotient.mk'' f)) v) := by
  rw [evalChartO]
  exact evalChart_spec S
    (⟨Quotient.mk'' f, (mem_baseSet_iff S f).mpr hf⟩ : ↥(baseSet S)) f hf rfl
    (matLin (orientMat S (Quotient.mk'' f)) v)

/-- **The fibre coordinate of the oriented tautological bundle is well defined**: the vector is the
same when read in the two charts, the change of coordinates being `coordChangeO`. -/
theorem evalChartO_glue (S T : ChartIdx k m) (x : OG k m) (hx : x ∈ baseSet S ∩ baseSet T)
    (v : Amb k) :
    evalChartO S ⟨x, hx.1⟩ v = evalChartO T ⟨x, hx.2⟩ (coordChangeO S T x v) := by
  rw [evalChartO, evalChartO, coordChangeO_apply,
    orientMat_involutive T x hx.2 (coordChange S T x (matLin (orientMat S x) v))]
  exact evalChart_glue S T x hx (matLin (orientMat S x) v)

/-! ## The evaluation on the total space -/

/-- **The vector of the plane at a point of the total space of the tautological bundle**, read in
the chart of the base point. -/
noncomputable def evalVec (p : (tautologicalBundle k m).TotalSpace) : Amb (k+m) :=
  evalChartO ((tautologicalBundle k m).indexAt p.1) ⟨p.1, (tautologicalBundle k m).mem_baseSet_at p.1⟩
    ((tautologicalBundle k m).localTriv ((tautologicalBundle k m).indexAt p.1) p).2

theorem evalVec_apply_chart (p : (tautologicalBundle k m).TotalSpace) (S : ChartIdx k m)
    (hpS : p.1 ∈ (tautologicalBundle k m).baseSet S) :
    evalVec p = evalChartO S ⟨p.1, hpS⟩ ((tautologicalBundle k m).localTriv S p).2 := by
  rw [evalVec, VectorBundleCore.localTriv_apply,
    VectorBundleCore.coordChange_self _ _ _ ((tautologicalBundle k m).mem_baseSet_at p.1)]
  exact evalChartO_glue ((tautologicalBundle k m).indexAt p.1) S p.1
    ⟨(tautologicalBundle k m).mem_baseSet_at p.1, hpS⟩ p.2

/-! ## Continuity of the total evaluation -/

theorem continuous_evalVec : Continuous (evalVec (k := k) (m := m)) := by
  rw [continuous_iff_continuousAt]
  intro p
  set S := (tautologicalBundle k m).indexAt p.1 with hS
  have hpS : p.1 ∈ (tautologicalBundle k m).baseSet S := (tautologicalBundle k m).mem_baseSet_at p.1
  set W : Set (tautologicalBundle k m).TotalSpace :=
    (tautologicalBundle k m).proj ⁻¹' (tautologicalBundle k m).baseSet S with hW
  have hWopen : IsOpen W :=
    ((tautologicalBundle k m).isOpen_baseSet S).preimage (tautologicalBundle k m).continuous_proj
  have hpW : p ∈ W := hpS
  have hfst : Continuous fun q : ↥W =>
      (⟨(q : (tautologicalBundle k m).TotalSpace).1, q.2⟩ : ↥((tautologicalBundle k m).baseSet S)) :=
    ((tautologicalBundle k m).continuous_proj.restrictPreimage :
      Continuous (((tautologicalBundle k m).baseSet S).restrictPreimage
        (tautologicalBundle k m).proj))
  have hsnd : ContinuousOn (fun q : (tautologicalBundle k m).TotalSpace =>
      ((tautologicalBundle k m).localTriv S q).2) W := by
    refine ((continuous_snd.comp_continuousOn
      ((tautologicalBundle k m).localTriv S).continuousOn)).mono ?_
    intro q hq
    rw [VectorBundleCore.mem_localTriv_source]
    exact hq
  have hmodel : Continuous fun q : ↥W =>
      evalChartO S (⟨(q : (tautologicalBundle k m).TotalSpace).1, q.2⟩)
        ((show Amb k from ((tautologicalBundle k m).localTriv S
          (q : (tautologicalBundle k m).TotalSpace)).2)) :=
    (continuous_evalChartO S).comp (hfst.prodMk
      (continuousOn_iff_continuous_domRestrict.mp hsnd))
  have hcontOn : ContinuousOn evalVec W := by
    refine continuousOn_iff_continuous_domRestrict.mpr (hmodel.congr fun q => ?_)
    exact (evalVec_apply_chart (q : (tautologicalBundle k m).TotalSpace) S q.2).symm
  exact hcontOn.continuousAt (hWopen.mem_nhds hpW)


end

end Work.ThomBordism.Grassmann
