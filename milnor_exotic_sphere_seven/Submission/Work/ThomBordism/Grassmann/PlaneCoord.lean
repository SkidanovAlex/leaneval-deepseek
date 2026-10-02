import Mathlib
import Submission.Work.ThomBordism.Grassmann.PlaneAct

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-!
# Chart coordinates of the incidence data

The fibre coordinate `toECoordAt S P w` of an ambient vector of the plane `P` is *independent of the
chart* `S` containing `P` (both charts give a coordinate whose evaluation is `w`, and the chart
evaluation is injective).  Consequently the point `toE P w` of the zero complement is described by
the continuous formula `toECoordAt S P w` in any chart `S` of `P`, which is what makes the rotation
action `rotE` continuous.
-/

open scoped Topology

namespace Work.ThomBordism.Grassmann

noncomputable section

variable {k m : ℕ}

/-- The coordinate evaluation is additive in the coordinate. -/
theorem coordEval_add (S : ChartIdx k m) (f : Stiefel k m) (a b : Amb k) :
    coordEval S f (a + b) = coordEval S f a + coordEval S f b := by
  simp only [coordEval, WithLp.ofLp_add]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.add_apply, add_smul]

/-- The chart evaluation is additive in the fibre coordinate. -/
theorem evalChartO_add (S : ChartIdx k m) (x : ↥(baseSet S)) (a b : Amb k) :
    evalChartO S x (a + b) = evalChartO S x a + evalChartO S x b := by
  obtain ⟨f, hf⟩ : ∃ f : Stiefel k m, Quotient.mk'' f = (x : OG k m) := Quotient.exists_rep _
  have hfc : f ∈ chartSet S := (mem_baseSet_iff S f).mp (hf ▸ x.2)
  rw [show (x : ↥(baseSet S)) = ⟨Quotient.mk'' f, (mem_baseSet_iff S f).mpr hfc⟩ from
    Subtype.ext hf.symm]
  simp only [evalChartO_spec S f hfc, map_add, coordEval_add]

/-- **The chart evaluation is injective in the fibre coordinate.** -/
theorem peEvalChartO_injective (S : ChartIdx k m) (x : ↥(baseSet S)) :
    Function.Injective (evalChartO S x) := by
  obtain ⟨f, hf⟩ : ∃ f : Stiefel k m, Quotient.mk'' f = (x : OG k m) := Quotient.exists_rep _
  have hfc : f ∈ chartSet S := (mem_baseSet_iff S f).mp (hf ▸ x.2)
  rw [show (x : ↥(baseSet S)) = ⟨Quotient.mk'' f, (mem_baseSet_iff S f).mpr hfc⟩ from
    Subtype.ext hf.symm]
  intro a b h
  have h1 : matLin (orientMat S (Quotient.mk'' f)) a
      = matLin (orientMat S (Quotient.mk'' f)) b := by
    have h2 : coordEval S f (matLin (orientMat S (Quotient.mk'' f)) a)
        = coordEval S f (matLin (orientMat S (Quotient.mk'' f)) b) := by
      simpa only [evalChartO_spec S f hfc] using h
    have h3 : (matLin (orientMat S (Quotient.mk'' f)) a).ofLp
        = (matLin (orientMat S (Quotient.mk'' f)) b).ofLp := by
      have h4 := congrArg (fun z => coordProj S (WithLp.ofLp z)) h2
      simpa only [coordProj_coordEval S f (matLin (orientMat S (Quotient.mk'' f)) a) hfc,
        coordProj_coordEval S f (matLin (orientMat S (Quotient.mk'' f)) b) hfc] using h4
    exact WithLp.ofLp_injective 2 h3
  have hxS : Quotient.mk'' f ∈ baseSet S := (mem_baseSet_iff S f).mpr hfc
  have hinv : ∀ c : Amb k, matLin (orientMat S (Quotient.mk'' f))
      (matLin (orientMat S (Quotient.mk'' f)) c) = c := by
    intro c
    rw [← ContinuousLinearMap.comp_apply, ← matLin_mul,
      orientMat_mul_self (S := S) (x := Quotient.mk'' f) hxS]
    simp
  rw [← hinv a, ← hinv b, h1]


/-! ## The chart reading of `toE` -/

/-- **The `S`-reading of the fibre coordinate of `toE P w`** is `toECoordAt S P w`: the transition
function takes the coordinate in the chart of the plane to the coordinate in any chart `S`
containing `P`. -/
theorem coordChange_toECoordAt (S : ChartIdx k m) (P : OG k m) (hPS : P ∈ baseSet S)
    (w : Amb (k+m)) (hw : memPlane P w) :
    (tautologicalBundle k m).coordChange ((tautologicalBundle k m).indexAt P) S P
        (toECoordAt ((tautologicalBundle k m).indexAt P) P w) = toECoordAt S P w := by
  have hPS' : P ∈ (tautologicalBundle k m).baseSet ((tautologicalBundle k m).indexAt P) :=
    (tautologicalBundle k m).mem_baseSet_at P
  have hglue := evalChartO_glue ((tautologicalBundle k m).indexAt P) S P ⟨hPS', hPS⟩
    (toECoordAt ((tautologicalBundle k m).indexAt P) P w)
  refine peEvalChartO_injective S ⟨P, hPS⟩ ?_
  show evalChartO S ⟨P, hPS⟩ (coordChangeO ((tautologicalBundle k m).indexAt P) S P
      (toECoordAt ((tautologicalBundle k m).indexAt P) P w)) = evalChartO S ⟨P, hPS⟩ (toECoordAt S P w)
  rw [← hglue, evalChartO_toECoordAt ((tautologicalBundle k m).indexAt P) P hPS' w hw,
    evalChartO_toECoordAt S P hPS w hw]

/-- **The `S`-reading of `toE`**: over a chart `S` of the plane, the local trivialisation reads the
fibre coordinate of `toE P w` as `toECoordAt S P w`. -/
theorem localTriv_toE_snd (S : ChartIdx k m) (P : OG k m) (hPS : P ∈ baseSet S)
    (w : Amb (k+m)) (hw0 : w ≠ 0) (hw : memPlane P w) :
    (show Amb k from ((tautologicalBundle k m).localTriv S
        (toE P w hw0 hw : (tautologicalBundle k m).TotalSpace)).2) = toECoordAt S P w := by
  rw [show (toE P w hw0 hw : (tautologicalBundle k m).TotalSpace)
      = mkTotal P (toECoordAt ((tautologicalBundle k m).indexAt P) P w) from rfl]
  rw [VectorBundleCore.localTriv_apply]
  exact coordChange_toECoordAt S P hPS w hw


/-! ## The `S`-reading of `mkTotal` and its continuity -/

/-- **The `S`-reading of `mkTotal P (toECoordAt (indexAt P) P c)`** (the underlying point of
`toE P c`): over a chart `S` of `P` it is `(P, toECoordAt S P c)`. -/
theorem localTriv_mkTotal (S : ChartIdx k m) (P : OG k m) (hPS : P ∈ baseSet S) (c : Amb (k+m))
    (hw : memPlane P c) :
    (tautologicalBundle k m).localTriv S
      (mkTotal P (toECoordAt ((tautologicalBundle k m).indexAt P) P c))
      = (P, toECoordAt S P c) := by
  refine Prod.ext rfl ?_
  rw [VectorBundleCore.localTriv_apply]
  exact coordChange_toECoordAt S P hPS c hw

/-- The coordinate `toECoordAt S · ·` is continuous over a chart. -/
theorem continuousOn_toECoordAt (S : ChartIdx k m) :
    ContinuousOn (fun q : OG k m × Amb (k+m) => toECoordAt S q.1 q.2)
      {q | q.1 ∈ (tautologicalBundle k m).baseSet S} := by
  refine ContinuousOn.clm_apply ?_ ?_
  · exact continuous_matLin.comp_continuousOn
      ((continuousOn_orientMat S).comp continuousOn_fst (fun q hq => hq))
  · exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin k => ℝ)).comp_continuousOn
      (Continuous.continuousOn ((LinearMap.continuous_of_finiteDimensional (coordProj S)).comp
        ((PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin (k+m) => ℝ)).comp continuous_snd)))

/-- **The `S`-reading of `toE`, as a continuous function of `(P, c)`.** -/
theorem continuousOn_localTriv_toE (S : ChartIdx k m) :
    ContinuousOn (fun q : OG k m × Amb (k+m) =>
      (tautologicalBundle k m).localTriv S
        (mkTotal q.1 (toECoordAt ((tautologicalBundle k m).indexAt q.1) q.1 q.2)))
      {q | q.1 ∈ (tautologicalBundle k m).baseSet S ∧ memPlane q.1 q.2} := by
  refine (continuousOn_fst.prodMk ((continuousOn_toECoordAt S).mono
    (fun q hq => hq.1))).congr (fun q hq => ?_)
  exact localTriv_mkTotal S q.1 hq.1 q.2 hq.2


/-- **The point `toE P c` depends continuously on `(P, c)`** (on the incidence domain, where the
vector really is a vector of the plane). -/
theorem continuousOn_toE_underlying :
    ContinuousOn (fun q : OG k m × Amb (k+m) =>
      mkTotal q.1 (toECoordAt ((tautologicalBundle k m).indexAt q.1) q.1 q.2))
      {q : OG k m × Amb (k+m) | q.2 ≠ 0 ∧ memPlane q.1 q.2} := by
  intro x hx
  set S := (tautologicalBundle k m).indexAt x.1 with hS
  let e := (tautologicalBundle k m).localTriv S
  let U : Set (OG k m × Amb (k+m)) := {q | q.1 ∈ (tautologicalBundle k m).baseSet S}
  let s : Set (OG k m × Amb (k+m)) := {q | q.2 ≠ 0 ∧ memPlane q.1 q.2}
  have hxS : x.1 ∈ (tautologicalBundle k m).baseSet S := (tautologicalBundle k m).mem_baseSet_at x.1
  have hU : U ∈ 𝓝 x := ((isOpen_baseSet S).preimage continuous_fst).mem_nhds hxS
  have hsource : ∀ q : OG k m × Amb (k+m), q.1 ∈ (tautologicalBundle k m).baseSet S →
      mkTotal q.1 (toECoordAt ((tautologicalBundle k m).indexAt q.1) q.1 q.2) ∈ e.source := by
    intro q hq
    rw [VectorBundleCore.mem_localTriv_source]
    exact hq
  have htarget : ∀ q : OG k m × Amb (k+m), q.1 ∈ (tautologicalBundle k m).baseSet S →
      (q.1, toECoordAt S q.1 q.2) ∈ e.target := by
    intro q hq
    rw [VectorBundleCore.mem_localTriv_target]
    exact hq
  have hg : ContinuousOn (fun q : OG k m × Amb (k+m) =>
      e.toOpenPartialHomeomorph.symm (q.1, toECoordAt S q.1 q.2)) U :=
    (OpenPartialHomeomorph.continuousOn_symm e.toOpenPartialHomeomorph).comp
      (continuousOn_fst.prodMk (continuousOn_toECoordAt S)) htarget
  have hfilter : 𝓝[U ∩ s] x = 𝓝[s] x := nhdsWithin_inter_of_mem (nhdsWithin_le_nhds hU)
  have hmain : ContinuousWithinAt (fun q : OG k m × Amb (k+m) =>
      mkTotal q.1 (toECoordAt ((tautologicalBundle k m).indexAt q.1) q.1 q.2)) (U ∩ s) x := by
    refine ((hg.continuousWithinAt hxS).mono Set.inter_subset_left).congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with q hq
      rw [← localTriv_mkTotal S q.1 hq.1 q.2 hq.2.2]
      exact (e.left_inv' (hsource q hq.1)).symm
    · rw [← localTriv_mkTotal S x.1 hxS x.2 hx.2]
      exact (e.left_inv' (hsource x hxS)).symm
  show Filter.Tendsto (fun q : OG k m × Amb (k+m) =>
      mkTotal q.1 (toECoordAt ((tautologicalBundle k m).indexAt q.1) q.1 q.2)) (𝓝[s] x)
      (𝓝 (mkTotal x.1 (toECoordAt ((tautologicalBundle k m).indexAt x.1) x.1 x.2)))
  rw [← hfilter]
  exact hmain


/-- **`rotE` is continuous, in a continuous family of linear isometries acting on a continuous
family of points.** -/
theorem continuous_rotE_comp {ι : Type} [TopologicalSpace ι] [LocallyCompactSpace ι]
    (R : ι → Amb (k+m) →ₗᵢ[ℝ] Amb (k+m))
    (hR : Continuous fun q : ι × Amb (k+m) => R q.1 q.2)
    (x : ι → ↥(incZero k m)) (hx : Continuous x) :
    Continuous fun i => rotE (R i) (x i) := by
  have hproj : Continuous fun i : ι => (x i).1.1 :=
    (VectorBundleCore.continuous_proj (tautologicalBundle k m)).comp
      (continuous_subtype_val.comp hx)
  have hvec : Continuous fun i : ι => evalVec (x i).1 :=
    continuous_evalVec.comp (continuous_subtype_val.comp hx)
  have hP : Continuous fun i : ι => planeAct (R i) (x i).1.1 :=
    (continuous_planeAct_family (k := k) (m := m) R hR).comp (hproj.prodMk continuous_id)
  have hw : Continuous fun i : ι => R i (evalVec (x i).1) :=
    hR.comp (continuous_id.prodMk hvec)
  have hmem : ∀ i, R i (evalVec (x i).1) ≠ 0 ∧
      memPlane (planeAct (R i) (x i).1.1) (R i (evalVec (x i).1)) := by
    intro i
    refine ⟨?_, planeAct_memPlane (R i) (evalVec_memPlane (x i).1)⟩
    intro h0
    have h1 : evalVec (x i).1 = 0 := by
      have h2 : ‖R i (evalVec (x i).1)‖ = ‖evalVec (x i).1‖ := LinearIsometry.norm_map (R i) _
      rw [h0, norm_zero] at h2
      exact norm_eq_zero.mp h2.symm
    exact evalVec_ne_zero_of_mem_zeroComplement (x i).1 (x i).2 h1
  have hmain : Continuous fun i : ι => mkTotal (planeAct (R i) (x i).1.1)
      (toECoordAt ((tautologicalBundle k m).indexAt (planeAct (R i) (x i).1.1))
        (planeAct (R i) (x i).1.1) (R i (evalVec (x i).1))) :=
    continuousOn_toE_underlying.comp_continuous (hP.prodMk hw) hmem
  have hmem' : ∀ i, mkTotal (planeAct (R i) (x i).1.1)
      (toECoordAt ((tautologicalBundle k m).indexAt (planeAct (R i) (x i).1.1))
        (planeAct (R i) (x i).1.1) (R i (evalVec (x i).1))) ∈ incZero k m := by
    intro i
    rw [Work.Thom.mem_zeroComplement]
    show toECoordAt ((tautologicalBundle k m).indexAt (planeAct (R i) (x i).1.1))
        (planeAct (R i) (x i).1.1) (R i (evalVec (x i).1)) ≠ 0
    exact toECoordAt_ne_zero _ _ ((tautologicalBundle k m).mem_baseSet_at _) _
      (hmem i).1 (hmem i).2
  show Continuous fun i : ι => (⟨mkTotal (planeAct (R i) (x i).1.1)
      (toECoordAt ((tautologicalBundle k m).indexAt (planeAct (R i) (x i).1.1))
        (planeAct (R i) (x i).1.1) (R i (evalVec (x i).1))), hmem' i⟩ : ↥(incZero k m))
  exact Continuous.subtype_mk hmain hmem'

end

end Work.ThomBordism.Grassmann
