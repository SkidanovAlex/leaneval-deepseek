import Mathlib
import Submission.Work.ThomBordism.Grassmann.ChartFrame
import Submission.Work.ThomBordism.Grassmann.Smooth.gramSchmidtContinuous

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace Work.ThomBordism.Grassmann

open scoped Topology
open Work.TangentClasses

noncomputable section

variable {k m : ℕ}

/-- `chartFrame` depends only on the point of the Grassmannian: two frames of the same chart cell
that represent the same point give the same orthonormal frame. -/
theorem chartFrame_congr (S : ChartIdx k m) {f g : Stiefel k m}
    (h : (Quotient.mk'' f : OG k m) = Quotient.mk'' g) :
    chartFrame S f = chartFrame S g := by
  obtain ⟨A, hA⟩ := Quotient.exact h
  rw [hA, chartFrame_soActFun]

/-- The `S`-coordinate-vector family spans the plane of any frame of the chart. -/
theorem span_coordVec_eq (S : ChartIdx k m) (f : Stiefel k m) (hf : f ∈ chartSet S) :
    Submodule.span ℝ (Set.range (fun i => coordVec S f i))
      = Submodule.span ℝ (Set.range (f.1 : Fin k → Amb (k + m))) := by
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
  · rintro _ ⟨i, rfl⟩
    exact coordVec_mem_span S f i
  · rintro _ ⟨j, rfl⟩
    have hspan : f.1 j ∈ Submodule.span ℝ (Set.range (f.1 : Fin k → Amb (k + m))) :=
      Submodule.subset_span ⟨j, rfl⟩
    have hcj := coordEval_coordProj S f hf hspan
    rw [← hcj]
    show (∑ i, WithLp.ofLp (WithLp.toLp 2 (coordProj S (WithLp.ofLp (f.1 j)))) i
      • coordVec S f i) ∈ _
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- The span of the chart evaluation `v ↦ evalChart S (x, v)` is the span of the frame at `x`. -/
theorem span_evalChart_eq (S : ChartIdx k m) (x : ↥(baseSet S)) (f : Stiefel k m)
    (hf : f ∈ chartSet S) (hx : (x : OG k m) = Quotient.mk'' f) :
    Submodule.span ℝ (Set.range (fun v : Amb k => evalChart S (x, v)))
      = Submodule.span ℝ (Set.range (f.1 : Fin k → Amb (k + m))) := by
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
  · rintro _ ⟨v, rfl⟩
    change evalChart S (x, v) ∈ Submodule.span ℝ (Set.range (f.1 : Fin k → Amb (k + m)))
    rw [evalChart_spec S x f hf hx]
    show (∑ i, WithLp.ofLp v i • coordVec S f i) ∈ _
    rw [← span_coordVec_eq S f hf]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rintro _ ⟨j, rfl⟩
    have hspan : f.1 j ∈ Submodule.span ℝ (Set.range (f.1 : Fin k → Amb (k + m))) :=
      Submodule.subset_span ⟨j, rfl⟩
    have hcj := coordEval_coordProj S f hf hspan
    rw [← hcj, ← evalChart_spec S x f hf hx]
    exact Submodule.subset_span ⟨_, rfl⟩

/-- **A continuous orthonormal frame field on a chart of the oriented Grassmannian.**  The
witness is the descent of `chartFrame S` to the chart cell; continuity is proved in the curried
form (`Continuous F` for `F : ↥(baseSet S) → Fin k → ℝ^{k+m}`), which is what the quotient descent
supplies. -/
theorem exists_chartFrameAt (k m : ℕ) (S : ChartIdx k m) :
    ∃ F : ↥(baseSet S) → Fin k → Amb (k + m),
      (∀ x, Orthonormal ℝ (F x)) ∧
      (∀ x, Submodule.span ℝ (Set.range (F x))
              = Submodule.span ℝ (Set.range (fun v : Amb k => evalChart S (x, v)))) ∧
      Continuous F := by
  classical
  have hpre : (Quotient.mk'' ⁻¹' (baseSet S : Set (OG k m))) = chartSet S := by
    ext f
    rw [Set.mem_preimage, mem_baseSet_iff]
  have hvec : ∀ i : Fin k, Continuous fun x : ↥(chartSet S) =>
      coordVec S (x : Stiefel k m) i := fun i =>
    continuousOn_iff_continuous_domRestrict.mp (continuousOn_coordVec S i)
  have hli : ∀ x : ↥(chartSet S),
      LinearIndependent ℝ (fun j => coordVec S (x : Stiefel k m) j) :=
    fun x => coordVec_linearIndependent S x x.2
  have hgs : ∀ i : Fin k, Continuous fun x : ↥(chartSet S) =>
      chartFrame S (x : Stiefel k m) i := by
    intro i
    have h := Work.ThomBordism.Grassmann.Smooth.gramSchmidtContinuous
      (fun x : ↥(chartSet S) => fun j => coordVec S (x : Stiefel k m) j)
      (fun j => hvec j) hli i
    simpa only [chartFrame] using h
  have hout : ∀ x : ↥(baseSet S), (Quotient.out (x : OG k m) : Stiefel k m) ∈ chartSet S := by
    intro x
    have h1 : (Quotient.mk'' (Quotient.out (x : OG k m)) : OG k m) = (x : OG k m) :=
      Quotient.out_eq _
    rw [← mem_baseSet_iff S (Quotient.out (x : OG k m)), h1]
    exact x.2
  refine ⟨fun x i => chartFrame S (Quotient.out (x : OG k m)) i, ?_, ?_, ?_⟩
  · intro x
    exact chartFrame_orthonormal S _ (hout x)
  · intro x
    rw [span_evalChart_eq S x _ (hout x) (Quotient.out_eq _).symm, chartFrame_span S _ (hout x)]
  · have hcomp : Continuous fun x : ↥(Quotient.mk'' ⁻¹' (baseSet S : Set (OG k m))) =>
        chartFrame S (x : Stiefel k m) := by
      rw [hpre]
      exact continuous_pi fun i => hgs i
    refine ((Topology.IsQuotientMap.restrictPreimage_isOpen (s := (baseSet S : Set (OG k m)))
      isQuotientMap_quotient_mk' (isOpen_baseSet S)).continuous_iff).mpr ?_
    refine hcomp.congr fun x => ?_
    funext i
    show chartFrame S (x : Stiefel k m) i
      = chartFrame S (Quotient.out (Quotient.mk'' (x : Stiefel k m))) i
    rw [chartFrame_congr S (f := (x : Stiefel k m))
      (g := Quotient.out (Quotient.mk'' (x : Stiefel k m))) (Quotient.out_eq _).symm]

end

end Work.ThomBordism.Grassmann
