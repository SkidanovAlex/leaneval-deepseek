import Submission.Work.ThomBordism.Grassmann.TB.tbGaugeDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

/-!
# The geometry of the two-block plane, and the first properties of the gauge

Structural lemmas for `Submission/Work/ThomBordism/Grassmann/TB/tbGaugeDefs.lean`: the two-block
decomposition of `ℝ²⁰`, the identification of the plane of `tbMap x` with `L ⊕ L`, the chart
evaluations of the block frame and the coefficient change between two charts of `ℂP⁴`.
-/

namespace Work.ThomBordism.Grassmann.TBG

open Work.TangentClasses Work.Projective

noncomputable section

/-! ## 1. The two-block decomposition -/

/-- **The two-block decomposition of `ℝ²⁰`**: every vector is the sum of its two blocks. -/
theorem tbgBlk_decomp (w : Amb 20) : tbBlkL (tbUnL w) + tbBlkR (tbUnR w) = w := by
  refine PiLp.ext (fun k => ?_)
  rw [WithLp.ofLp_add, Pi.add_apply]
  refine Fin.addCases (m := 10) (n := 10) (fun i => ?_) (fun i => ?_) k
  · rw [tbBlkL_coord, tbBlkR_coordL, add_zero, tbUnL_coord]
  · rw [tbBlkL_coordR, tbBlkR_coordR, zero_add, tbUnR_coord]

theorem tbgUnR_tbBlkL (w : Amb 10) : tbUnR (tbBlkL w) = 0 := by
  refine PiLp.ext (fun i => ?_)
  rw [tbUnR_coord, tbBlkL_coordR]
  rfl

/-! ## 2. The span of the block frame of a line -/

theorem tbgRange_tbFrameB (v : Fin 5 → ℂ) :
    Set.range (tbFrameB v)
      = Set.range (fun a : Fin 2 => tbBlkL (tbRealF v a))
        ∪ Set.range (fun a : Fin 2 => tbBlkR (tbRealF v a)) := by
  ext w
  constructor
  · rintro ⟨i, rfl⟩
    rcases i with a | a
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr ⟨a, rfl⟩
  · rintro (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · exact ⟨Sum.inl a, rfl⟩
    · exact ⟨Sum.inr a, rfl⟩

theorem tbgRange_tbFrame (v : Fin 5 → ℂ) : Set.range (tbFrame v) = Set.range (tbFrameB v) := by
  ext w
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨tbS4.symm i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨tbS4 i, by rw [tbFrame, Equiv.symm_apply_apply]⟩

theorem tbgSpan_tbFrame (v : Fin 5 → ℂ) :
    Submodule.span ℝ (Set.range (tbFrame v))
      = Submodule.span ℝ (Set.range (fun a : Fin 2 => tbBlkL (tbRealF v a)))
        ⊔ Submodule.span ℝ (Set.range (fun a : Fin 2 => tbBlkR (tbRealF v a))) := by
  rw [tbgRange_tbFrame, tbgRange_tbFrameB, Submodule.span_union]

theorem tbgRealF_zero (v : Fin 5 → ℂ) : tbRealF v 0 = tbReal (cfUnit v) := by
  rw [tbRealF, tbLine_zero]

theorem tbgRealF_one (v : Fin 5 → ℂ) :
    tbRealF v 1 = -tbReal (Complex.I • cfUnit v) := by
  rw [tbRealF, tbLine_one, map_neg]

theorem tbgCfUnit_eq (v : Fin 5 → ℂ) : cfUnit v = (‖tbOfLpC v‖)⁻¹ • tbOfLpC v := by
  rw [cfUnit, tbOfLpC_apply]
  rfl

/-- A complex multiple of the line of `v` is in the real span of the frame of the line. -/
theorem tbgReal_smul_mem_span (v : Fin 5 → ℂ) (hv : v ≠ 0) (mu : ℂ) :
    tbReal (mu • tbOfLpC v) ∈ Submodule.span ℝ (Set.range (tbRealF v)) := by
  have hnorm : (‖tbOfLpC v‖) ≠ 0 := norm_ne_zero_iff.mpr (tbOfLpC_ne_zero hv)
  have hnf : tbOfLpC v = (‖tbOfLpC v‖) • cfUnit v := by
    rw [tbgCfUnit_eq, smul_smul, mul_inv_cancel₀ hnorm, one_smul]
  have h0 : tbReal (tbOfLpC v) = (‖tbOfLpC v‖) • tbRealF v 0 := by
    conv_lhs => rw [hnf]
    rw [tbgRealF_zero, ContinuousLinearMap.map_smul]
  have hI : tbRot10 Complex.I (tbRealF v 0) = -tbRealF v 1 := by
    rw [tbgRealF_zero, ← tbReal_smul (μ := Complex.I) (z := cfUnit v), tbgRealF_one, neg_neg]
  rw [tbReal_smul, tbRot10_decomp, h0]
  rw [ContinuousLinearMap.map_smul, hI]
  rw [smul_smul, smul_smul]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span
      (show tbRealF v 0 ∈ Set.range (tbRealF v) from ⟨0, rfl⟩)))
    (Submodule.smul_mem _ _ (Submodule.neg_mem _ (Submodule.subset_span
      (show tbRealF v 1 ∈ Set.range (tbRealF v) from ⟨1, rfl⟩))))

/-- Membership in the span of the frame of the line implies being a complex multiple of the line. -/
theorem tbgSpan_tbRealF_le (v : Fin 5 → ℂ) (hv : v ≠ 0) :
    Submodule.span ℝ (Set.range (tbRealF v))
      ≤ Submodule.map tbReal.toLinearMap
          ((Submodule.span ℂ {tbOfLpC v}).restrictScalars ℝ) := by
  have hcv : cfUnit v ∈ Submodule.span ℂ {tbOfLpC v} := by
    rw [Submodule.mem_span_singleton]
    exact ⟨((‖tbOfLpC v‖)⁻¹ : ℝ), by rw [Complex.coe_smul]; exact (tbgCfUnit_eq v).symm⟩
  rw [Submodule.span_le]
  intro w hw
  obtain ⟨a, rfl⟩ := hw
  fin_cases a
  · exact Submodule.mem_map.mpr ⟨cfUnit v, by
      rw [Submodule.restrictScalars_mem]; exact hcv, rfl⟩
  · refine Submodule.mem_map.mpr ⟨(-Complex.I) • cfUnit v, by
      rw [Submodule.restrictScalars_mem]
      exact Submodule.smul_mem _ _ hcv, ?_⟩
    show tbReal ((-Complex.I) • cfUnit v) = tbRealF v 1
    rw [tbgRealF_one, neg_smul, map_neg]

/-- **Membership in the span of the block frame of the line is membership in the line.** -/
theorem tbgUnL_mem_line (v : Fin 5 → ℂ) (hv : v ≠ 0) {W : Amb 20}
    (hW : W ∈ Submodule.span ℝ (Set.range (tbFrame v))) :
    ∃ lam : ℂ, tbUnL W = tbReal (lam • tbOfLpC v) := by
  rw [tbgSpan_tbFrame, Submodule.mem_sup] at hW
  obtain ⟨WL, hWL, WR, hWR, rfl⟩ := hW
  have h1 : tbUnL WL ∈ Submodule.span ℝ (Set.range (tbRealF v)) := by
    have hle : Submodule.span ℝ (Set.range (fun a : Fin 2 => tbBlkL (tbRealF v a)))
        ≤ Submodule.comap (tbUnL : Amb 20 →ₗ[ℝ] Amb 10)
            (Submodule.span ℝ (Set.range (tbRealF v))) := by
      rw [Submodule.span_le]
      rintro y ⟨a, rfl⟩
      show tbUnL (tbBlkL (tbRealF v a)) ∈ Submodule.span ℝ (Set.range (tbRealF v))
      rw [tbUnL_tbBlkL]
      exact Submodule.subset_span ⟨a, rfl⟩
    exact hle hWL
  have h2 : tbUnL WR = 0 := by
    have hle : Submodule.span ℝ (Set.range (fun a : Fin 2 => tbBlkR (tbRealF v a)))
        ≤ LinearMap.ker (tbUnL : Amb 20 →ₗ[ℝ] Amb 10) := by
      rw [Submodule.span_le]
      rintro y ⟨a, rfl⟩
      exact tbUnL_tbBlkR (tbRealF v a)
    exact hle hWR
  rw [map_add, h2, add_zero]
  have h3 := tbgSpan_tbRealF_le v hv h1
  obtain ⟨z, hz, hzW⟩ := Submodule.mem_map.mp h3
  rw [Submodule.restrictScalars_mem] at hz
  obtain ⟨lam, rfl⟩ := Submodule.mem_span_singleton.mp hz
  exact ⟨lam, hzW.symm⟩

/-- The same for the second block. -/
theorem tbgUnR_mem_line (v : Fin 5 → ℂ) (hv : v ≠ 0) {W : Amb 20}
    (hW : W ∈ Submodule.span ℝ (Set.range (tbFrame v))) :
    ∃ lam : ℂ, tbUnR W = tbReal (lam • tbOfLpC v) := by
  rw [tbgSpan_tbFrame, Submodule.mem_sup] at hW
  obtain ⟨WL, hWL, WR, hWR, rfl⟩ := hW
  have h1 : tbUnR WR ∈ Submodule.span ℝ (Set.range (tbRealF v)) := by
    have hle : Submodule.span ℝ (Set.range (fun a : Fin 2 => tbBlkR (tbRealF v a)))
        ≤ Submodule.comap (tbUnR : Amb 20 →ₗ[ℝ] Amb 10)
            (Submodule.span ℝ (Set.range (tbRealF v))) := by
      rw [Submodule.span_le]
      rintro y ⟨a, rfl⟩
      show tbUnR (tbBlkR (tbRealF v a)) ∈ Submodule.span ℝ (Set.range (tbRealF v))
      rw [tbUnR_tbBlkR]
      exact Submodule.subset_span ⟨a, rfl⟩
    exact hle hWR
  have h2 : tbUnR WL = 0 := by
    have hle : Submodule.span ℝ (Set.range (fun a : Fin 2 => tbBlkL (tbRealF v a)))
        ≤ LinearMap.ker (tbUnR : Amb 20 →ₗ[ℝ] Amb 10) := by
      rw [Submodule.span_le]
      rintro y ⟨a, rfl⟩
      exact tbgUnR_tbBlkL (tbRealF v a)
    exact hle hWL
  rw [map_add, h2, zero_add]
  have h3 := tbgSpan_tbRealF_le v hv h1
  obtain ⟨z, hz, hzW⟩ := Submodule.mem_map.mp h3
  rw [Submodule.restrictScalars_mem] at hz
  obtain ⟨lam, rfl⟩ := Submodule.mem_span_singleton.mp hz
  exact ⟨lam, hzW.symm⟩

/-! ## 3. The plane of `tbMap x`, and chart evaluations -/

theorem tbgCoordEval_mem_span (S : ChartIdx 4 16) (f : Stiefel 4 16) (v : Amb 4) :
    coordEval S f v ∈ Submodule.span ℝ (Set.range (f.1 : Fin 4 → Amb 20)) := by
  rw [coordEval]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (coordVec_mem_span S f i)

theorem tbgMemPlane_tbFrame {v : Fin 5 → ℂ} (hv : v ≠ 0) {w : Amb 20}
    (hw : w ∈ Submodule.span ℝ (Set.range (tbFrame v))) :
    memPlane (ogMk 4 16 (tbFrameW ⟨v, hv⟩)) w :=
  ⟨tbFrameW ⟨v, hv⟩, rfl, hw⟩

theorem tbgCoordEval_eq_of_mk_eq (S : ChartIdx 4 16) {f g : Stiefel 4 16}
    (h : (Quotient.mk'' f : OG 4 16) = Quotient.mk'' g) : coordEval S f = coordEval S g := by
  obtain ⟨A, hA⟩ := Quotient.exact h
  rw [hA]
  funext v
  exact (coordEval_soActFun S f v A).symm

/-- The frame `tbCF i x` is a frame of the plane `tbMap x`. -/
theorem tbgCF_mk (i : Fin 5) (x : CP 4) (hx : x ∈ Work.Projective.chartSet i) :
    (Quotient.mk'' (tbCF i x) : OG 4 16) = tbMap x := by
  show ogMk 4 16 (tbCF i x) = tbMap x
  rw [tbMap_apply_uVec i x hx]
  rfl

theorem tbgCF_mem_chartSet (S : ChartIdx 4 16) (i : Fin 5) (x : CP 4)
    (hS : tbMap x ∈ baseSet S) (hx : x ∈ Work.Projective.chartSet i) :
    tbCF i x ∈ chartSet S := by
  rw [← mem_baseSet_iff S (tbCF i x), tbgCF_mk i x hx]
  exact hS

/-- A chart evaluation read in a frame is the evaluation in the chart. -/
theorem tbgCoordEval_eq_evalChartO (S : ChartIdx 4 16) (x : ↥(baseSet S)) (f : Stiefel 4 16)
    (hf : f ∈ chartSet S) (hmk : (Quotient.mk'' f : OG 4 16) = (x : OG 4 16)) (c : Amb 4) :
    coordEval S f (matLin (orientMat S (x : OG 4 16)) c) = evalChartO S x c := by
  obtain rfl : x = ⟨Quotient.mk'' f, (mem_baseSet_iff S f).mpr hf⟩ := Subtype.ext hmk.symm
  rw [evalChartO_spec S f hf c]

/-- **The plane vector of the `S`-coordinates is the chart evaluation.** -/
theorem tbgEW_eq_evalChartO (S : ChartIdx 4 16) (i : Fin 5) (x : CP 4)
    (hS : tbMap x ∈ baseSet S) (hx : x ∈ Work.Projective.chartSet i) (c : Amb 4) :
    tbEW S i x c = evalChartO S ⟨tbMap x, hS⟩ c := by
  rw [tbEW_apply]
  exact tbgCoordEval_eq_evalChartO S ⟨tbMap x, hS⟩ (tbCF i x)
    (tbgCF_mem_chartSet S i x hS hx) (tbgCF_mk i x hx) c

/-- The plane vector with `S`-coordinates `c` is independent of the chart of `ℂP⁴` used to
describe the frame. -/
theorem tbgEW_frame_eq (S : ChartIdx 4 16) (i i' : Fin 5) (x : CP 4)
    (hS : tbMap x ∈ baseSet S) (hi : x ∈ Work.Projective.chartSet i)
    (hi' : x ∈ Work.Projective.chartSet i') (c : Amb 4) :
    tbEW S i' x c = tbEW S i x c := by
  rw [tbgEW_eq_evalChartO S i' x hS hi' c, tbgEW_eq_evalChartO S i x hS hi c]

/-- The plane vector of a chart evaluation lies in the plane. -/
theorem tbgMemPlane_tbEW (S : ChartIdx 4 16) (i : Fin 5) (x : CP 4)
    (hS : tbMap x ∈ baseSet S) (hx : x ∈ Work.Projective.chartSet i) (c : Amb 4) :
    memPlane (tbMap x) (tbEW S i x c) :=
  ⟨tbCF i x, tbgCF_mk i x hx, by rw [tbEW_apply]; exact tbgCoordEval_mem_span S (tbCF i x) _⟩

/-- The plane vector of a chart evaluation lies in the span of the block frame. -/
theorem tbgEW_mem_span (S : ChartIdx 4 16) (i : Fin 5) (x : CP 4)
    (hS : tbMap x ∈ baseSet S) (hx : x ∈ Work.Projective.chartSet i) (c : Amb 4) :
    tbEW S i x c ∈ Submodule.span ℝ (Set.range (tbFrame (Work.Gen.uVec i x))) := by
  rw [tbEW_apply]
  exact tbgCoordEval_mem_span S (tbCF i x) _

/-- **The `S`-coordinates of the plane vector `tbEW`**: reading back the chart evaluation. -/
theorem tbgEW_toECoordAt (S : ChartIdx 4 16) (i : Fin 5) (x : CP 4)
    (hS : tbMap x ∈ baseSet S) (hx : x ∈ Work.Projective.chartSet i) {w : Amb 20}
    (hw : memPlane (tbMap x) w) :
    tbEW S i x (toECoordAt S (tbMap x) w) = w := by
  rw [tbgEW_eq_evalChartO S i x hS hx]
  exact evalChartO_toECoordAt S (tbMap x) hS w hw

/-- **The chart evaluation of the coordinates of a plane vector is the vector.** -/
theorem tbgToECoordAt_evalChartO (S : ChartIdx 4 16) (P : OG 4 16) (hPS : P ∈ baseSet S)
    (c : Amb 4) : toECoordAt S P (evalChartO S ⟨P, hPS⟩ c) = c := by
  obtain ⟨f, hfmk⟩ : ∃ f : Stiefel 4 16, (Quotient.mk'' f : OG 4 16) = P := Quotient.exists_rep _
  subst hfmk
  have hfc : f ∈ chartSet S := (mem_baseSet_iff S f).mp hPS
  show matLin (orientMat S (Quotient.mk'' f))
      (WithLp.toLp 2 (coordProj S (WithLp.ofLp (evalChartO S ⟨Quotient.mk'' f, hPS⟩ c)))) = c
  rw [evalChartO_spec S f hfc c,
    show WithLp.toLp 2 (coordProj S (WithLp.ofLp (coordEval S f
        (matLin (orientMat S (Quotient.mk'' f)) c))))
       = WithLp.toLp 2 (WithLp.ofLp (matLin (orientMat S (Quotient.mk'' f)) c)) from by
      rw [coordProj_coordEval S f (matLin (orientMat S (Quotient.mk'' f)) c) hfc,
        WithLp.toLp_ofLp],
    orientMat_involutive S (Quotient.mk'' f) hPS c]

end

end Work.ThomBordism.Grassmann.TBG
