import Submission.Work.ThomBordism.Grassmann.TB.tbGaugeGeom

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
# The gauge identities for `tbZ ≅ tbW`

The heart of the construction: the coefficient change between two charts of `ℂP⁴`, the
reconstruction of a plane vector from the two extracted block coefficients, and the inverse
identities of the gauge family `tbPhi` / `tbPhiInv`.
-/

namespace Work.ThomBordism.Grassmann.TBG

open Work.TangentClasses Work.Projective

noncomputable section

/-! ## 1. The coefficient change between two charts -/

/-- The two normalisations of the line of `x` differ by the homogeneous ratio. -/
theorem tbgUvec_eq (i i' : Fin 5) (x : CP 4) (hi : x ∈ Work.Projective.chartSet i)
    (hi' : x ∈ Work.Projective.chartSet i') :
    Work.Gen.uVec i x = Work.Gen.homCoord 4 i i' x • Work.Gen.uVec i' x := by
  have hne : Work.Gen.homCoord 4 i i' x ≠ 0 := by
    have h := Work.Gen.homCoord_mul_inv_eq_one (n := 4) i i' hi hi'
    exact right_ne_zero_of_mul (by rw [h]; exact one_ne_zero)
  rw [Work.Gen.uVec_indep (n := 4) i i' ⟨hi, hi'⟩, smul_smul, mul_inv_cancel₀ hne, one_smul]

/-- **The extracted coefficient changes by the homogeneous ratio** between the charts `i` and
`i'` of `ℂP⁴`. -/
theorem tbgExtract_uVec_change (i i' : Fin 5) (x : CP 4)
    (hi : x ∈ Work.Projective.chartSet i) (hi' : x ∈ Work.Projective.chartSet i')
    {z : Fin 5 → ℂ} (hz : ∃ lam : ℂ, z = lam • Work.Gen.uVec i x) :
    tbExtract (Work.Gen.uVec i' x) z
      = Work.Gen.homCoord 4 i i' x * tbExtract (Work.Gen.uVec i x) z :=
  tbExtract_smul_left (Work.Gen.uVec_ne_zero i x) (Work.Gen.uVec_ne_zero i' x)
    (tbgUvec_eq i i' x hi hi') hz

/-- The extracted coefficient of the first block is that of the line, in any chart. -/
theorem tbgVecL_mem_line (S : ChartIdx 4 16) (i : Fin 5) (x : CP 4)
    (hS : tbMap x ∈ baseSet S) (hi : x ∈ Work.Projective.chartSet i) (c : Amb 4) :
    ∃ lam : ℂ, tbVecL S i x c = lam • Work.Gen.uVec i x := by
  obtain ⟨lam, hlam⟩ := tbgUnL_mem_line (Work.Gen.uVec i x) (Work.Gen.uVec_ne_zero i x)
    (tbgEW_mem_span S i x hS hi c)
  refine ⟨lam, ?_⟩
  rw [tbVecL_apply, hlam, tbcOfLpCLM_tbReal, WithLp.ofLp_smul, tbOfLpC_apply, WithLp.ofLp_toLp]

/-- The extracted coefficient of the second block is that of the line, in any chart. -/
theorem tbgVecR_mem_line (S : ChartIdx 4 16) (j : Fin 5) (x : CP 4)
    (hS : tbMap x ∈ baseSet S) (hj : x ∈ Work.Projective.chartSet j) (c : Amb 4) :
    ∃ lam : ℂ, tbVecR S j x c = lam • Work.Gen.uVec j x := by
  obtain ⟨lam, hlam⟩ := tbgUnR_mem_line (Work.Gen.uVec j x) (Work.Gen.uVec_ne_zero j x)
    (tbgEW_mem_span S j x hS hj c)
  refine ⟨lam, ?_⟩
  rw [tbVecR_apply, hlam, tbcOfLpCLM_tbReal, WithLp.ofLp_smul, tbOfLpC_apply, WithLp.ofLp_toLp]

theorem tbgVecL_frame_eq (S : ChartIdx 4 16) (i i' : Fin 5) (x : CP 4)
    (hS : tbMap x ∈ baseSet S) (hi : x ∈ Work.Projective.chartSet i)
    (hi' : x ∈ Work.Projective.chartSet i') (c : Amb 4) :
    tbVecL S i' x c = tbVecL S i x c := by
  rw [tbVecL_apply, tbVecL_apply, tbgEW_frame_eq S i i' x hS hi hi' c]

theorem tbgVecR_frame_eq (S : ChartIdx 4 16) (j j' : Fin 5) (x : CP 4)
    (hS : tbMap x ∈ baseSet S) (hj : x ∈ Work.Projective.chartSet j)
    (hj' : x ∈ Work.Projective.chartSet j') (c : Amb 4) :
    tbVecR S j' x c = tbVecR S j x c := by
  rw [tbVecR_apply, tbVecR_apply, tbgEW_frame_eq S j j' x hS hj hj' c]

/-- **The first block coefficient changes by `homCoord`** — this is what makes the transition
function of `tbW` (which is `expCMul (homCoord 4 i i')`) match. -/
theorem tbgCoefL_change (S : ChartIdx 4 16) (i i' : Fin 5) (x : CP 4)
    (hS : tbMap x ∈ baseSet S) (hi : x ∈ Work.Projective.chartSet i)
    (hi' : x ∈ Work.Projective.chartSet i') (c : Amb 4) :
    tbCoefL S i' x c = expCMul (Work.Gen.homCoord 4 i i' x) (tbCoefL S i x c) := by
  have hz := tbgVecL_mem_line S i x hS hi c
  rw [tbCoefL_apply, tbCoefL_apply, tbgVecL_frame_eq S i i' x hS hi hi' c, ← tbCof_smul]
  exact congrArg tbCof (tbgExtract_uVec_change i i' x hi hi' hz)

theorem tbgCoefR_change (S : ChartIdx 4 16) (j j' : Fin 5) (x : CP 4)
    (hS : tbMap x ∈ baseSet S) (hj : x ∈ Work.Projective.chartSet j)
    (hj' : x ∈ Work.Projective.chartSet j') (c : Amb 4) :
    tbCoefR S j' x c = expCMul (Work.Gen.homCoord 4 j j' x) (tbCoefR S j x c) := by
  have hz := tbgVecR_mem_line S j x hS hj c
  rw [tbCoefR_apply, tbCoefR_apply, tbgVecR_frame_eq S j j' x hS hj hj' c, ← tbCof_smul]
  exact congrArg tbCof (tbgExtract_uVec_change j j' x hj hj' hz)

/-! ## 2. The reconstruction of a plane vector from its coefficients -/

theorem tbgUnL_tbGeo (t : Fin 5 × Fin 5) (x : CP 4) (d : Amb 4) :
    tbUnL (tbGeo t x d)
      = tbReal (tbOfLpC ((tbZExp (((Work.Whitney.sumFibreR 2 2).symm d).1))
        • Work.Gen.uVec t.1 x)) := by
  rw [tbGeo_apply, map_add, tbUnL_tbBlkL, tbUnL_tbBlkR, add_zero]

theorem tbgUnR_tbGeo (t : Fin 5 × Fin 5) (x : CP 4) (d : Amb 4) :
    tbUnR (tbGeo t x d)
      = tbReal (tbOfLpC ((tbZExp (((Work.Whitney.sumFibreR 2 2).symm d).2))
        • Work.Gen.uVec t.2 x)) := by
  rw [tbGeo_apply, map_add, tbgUnR_tbBlkL, tbUnR_tbBlkR, zero_add]

/-- A vector of the realified line is a vector of the block frame span. -/
theorem tbgBlkL_mem_span {v : Fin 5 → ℂ} (hv : v ≠ 0) (mu : ℂ) :
    tbBlkL (tbReal (mu • tbOfLpC v))
      ∈ Submodule.span ℝ (Set.range (fun a : Fin 2 => tbBlkL (tbRealF v a))) := by
  have h1 : tbReal (mu • tbOfLpC v) ∈ Submodule.span ℝ (Set.range (tbRealF v)) :=
    tbgReal_smul_mem_span v hv mu
  have hle : Submodule.span ℝ (Set.range (tbRealF v))
      ≤ Submodule.comap (tbBlkL : Amb 10 →ₗ[ℝ] Amb 20)
          (Submodule.span ℝ (Set.range (fun a : Fin 2 => tbBlkL (tbRealF v a)))) := by
    rw [Submodule.span_le]
    rintro y ⟨a, rfl⟩
    exact Submodule.subset_span (s := Set.range (fun a : Fin 2 => tbBlkL (tbRealF v a)))
      ⟨a, rfl⟩
  exact hle h1

theorem tbgBlkR_mem_span {v : Fin 5 → ℂ} (hv : v ≠ 0) (mu : ℂ) :
    tbBlkR (tbReal (mu • tbOfLpC v))
      ∈ Submodule.span ℝ (Set.range (fun a : Fin 2 => tbBlkR (tbRealF v a))) := by
  have h1 : tbReal (mu • tbOfLpC v) ∈ Submodule.span ℝ (Set.range (tbRealF v)) :=
    tbgReal_smul_mem_span v hv mu
  have hle : Submodule.span ℝ (Set.range (tbRealF v))
      ≤ Submodule.comap (tbBlkR : Amb 10 →ₗ[ℝ] Amb 20)
          (Submodule.span ℝ (Set.range (fun a : Fin 2 => tbBlkR (tbRealF v a)))) := by
    rw [Submodule.span_le]
    rintro y ⟨a, rfl⟩
    exact Submodule.subset_span (s := Set.range (fun a : Fin 2 => tbBlkR (tbRealF v a)))
      ⟨a, rfl⟩
  exact hle h1

/-- **The reconstructed plane vector is a vector of the plane `tbMap x`.** -/
theorem tbgMemPlane_tbGeo (t : Fin 5 × Fin 5) (x : CP 4)
    (hx : x ∈ Work.Projective.chartSet t.1 ∩ Work.Projective.chartSet t.2) (d : Amb 4) :
    memPlane (tbMap x) (tbGeo t x d) := by
  have hmem : tbGeo t x d ∈ Submodule.span ℝ (Set.range (tbFrame (Work.Gen.uVec t.1 x))) := by
    rw [tbGeo_apply, tbgSpan_tbFrame]
    refine Submodule.add_mem _ ?_ ?_
    · rw [tbOfLpC_smul]
      exact Submodule.mem_sup_left (tbgBlkL_mem_span (Work.Gen.uVec_ne_zero t.1 x) _)
    · rw [tbgUvec_eq t.2 t.1 x hx.2 hx.1, smul_smul, tbOfLpC_smul]
      exact Submodule.mem_sup_right (tbgBlkR_mem_span (Work.Gen.uVec_ne_zero t.1 x) _)
  rw [tbMap_apply_uVec t.1 x hx.1]
  exact tbgMemPlane_tbFrame (Work.Gen.uVec_ne_zero t.1 x) hmem

/-- **The reconstruction identity**: rebuilding the plane vector from the two extracted block
coefficients returns the plane vector. -/
theorem tbgGeo_tbPhi (S : ChartIdx 4 16) (t : Fin 5 × Fin 5) (x : CP 4)
    (hS : tbMap x ∈ baseSet S)
    (hx : x ∈ Work.Projective.chartSet t.1 ∩ Work.Projective.chartSet t.2) (c : Amb 4) :
    tbGeo t x (tbPhi S t x c) = tbEW S t.1 x c := by
  have hsym : (Work.Whitney.sumFibreR 2 2).symm (tbPhi S t x c)
      = (tbCoefL S t.1 x c, tbCoefR S t.2 x c) := by
    rw [tbPhi_apply, ContinuousLinearEquiv.symm_apply_apply]
  obtain ⟨lamL, hlamL⟩ := tbgUnL_mem_line (Work.Gen.uVec t.1 x)
    (Work.Gen.uVec_ne_zero t.1 x) (tbgEW_mem_span S t.1 x hS hx.1 c)
  have hmemR : tbEW S t.1 x c ∈ Submodule.span ℝ (Set.range (tbFrame (Work.Gen.uVec t.2 x))) := by
    rw [← tbgEW_frame_eq S t.1 t.2 x hS hx.1 hx.2 c]
    exact tbgEW_mem_span S t.2 x hS hx.2 c
  obtain ⟨lamR, hlamR⟩ := tbgUnR_mem_line (Work.Gen.uVec t.2 x)
    (Work.Gen.uVec_ne_zero t.2 x) hmemR
  have hcoefL : tbZExp (tbCoefL S t.1 x c) = lamL := by
    rw [tbCoefL_apply, tbZExp_tbCof, tbVecL_apply, hlamL, tbcOfLpCLM_tbReal,
      WithLp.ofLp_smul, tbOfLpC_apply, WithLp.ofLp_toLp]
    exact tbExtract_smul (Work.Gen.uVec t.1 x) (Work.Gen.uVec_ne_zero t.1 x) lamL
  have hcoefR : tbZExp (tbCoefR S t.2 x c) = lamR := by
    rw [tbCoefR_apply, tbZExp_tbCof, tbVecR_apply, tbgEW_frame_eq S t.1 t.2 x hS hx.1 hx.2 c,
      hlamR, tbcOfLpCLM_tbReal,
      WithLp.ofLp_smul, tbOfLpC_apply, WithLp.ofLp_toLp]
    exact tbExtract_smul (Work.Gen.uVec t.2 x) (Work.Gen.uVec_ne_zero t.2 x) lamR
  rw [tbGeo_apply, hsym, hcoefL, hcoefR, tbOfLpC_smul, tbOfLpC_smul, ← hlamL, ← hlamR]
  exact tbgBlk_decomp (tbEW S t.1 x c)

/-! ## 3. The inverse identities -/

/-- **The left inverse identity of the gauge.** -/
theorem tbgPhiInv_tbPhi (S : ChartIdx 4 16) (t : Fin 5 × Fin 5) (x : CP 4)
    (hS : tbMap x ∈ baseSet S)
    (hx : x ∈ Work.Projective.chartSet t.1 ∩ Work.Projective.chartSet t.2) (c : Amb 4) :
    tbPhiInv S t x (tbPhi S t x c) = c := by
  rw [tbPhiInv_apply, tbgGeo_tbPhi S t x hS hx c, tbgEW_eq_evalChartO S t.1 x hS hx.1 c]
  exact tbgToECoordAt_evalChartO S (tbMap x) hS c

/-- **The right inverse identity of the gauge.** -/
theorem tbgPhi_tbPhiInv (S : ChartIdx 4 16) (t : Fin 5 × Fin 5) (x : CP 4)
    (hS : tbMap x ∈ baseSet S)
    (hx : x ∈ Work.Projective.chartSet t.1 ∩ Work.Projective.chartSet t.2) (d : Amb 4) :
    tbPhi S t x (tbPhiInv S t x d) = d := by
  have hmem : memPlane (tbMap x) (tbGeo t x d) := tbgMemPlane_tbGeo t x hx d
  have hEW : tbEW S t.1 x (tbPhiInv S t x d) = tbGeo t x d := by
    rw [tbPhiInv_apply, tbgEW_toECoordAt S t.1 x hS hx.1 hmem]
  have hsym : (Work.Whitney.sumFibreR 2 2).symm d
      = (((Work.Whitney.sumFibreR 2 2).symm d).1, ((Work.Whitney.sumFibreR 2 2).symm d).2) :=
    rfl
  have hL : tbCoefL S t.1 x (tbPhiInv S t x d)
      = tbCof (tbZExp (((Work.Whitney.sumFibreR 2 2).symm d).1)) := by
    rw [tbCoefL_apply, tbVecL_apply, hEW, tbgUnL_tbGeo, tbcOfLpCLM_tbReal, tbOfLpC_apply,
      WithLp.ofLp_toLp]
    exact congrArg tbCof (tbExtract_smul _ (Work.Gen.uVec_ne_zero t.1 x) _)
  have hR : tbCoefR S t.2 x (tbPhiInv S t x d)
      = tbCof (tbZExp (((Work.Whitney.sumFibreR 2 2).symm d).2)) := by
    rw [tbCoefR_apply, tbVecR_apply, tbgEW_frame_eq S t.1 t.2 x hS hx.1 hx.2 (tbPhiInv S t x d),
      hEW, tbgUnR_tbGeo, tbcOfLpCLM_tbReal, tbOfLpC_apply, WithLp.ofLp_toLp]
    exact congrArg tbCof (tbExtract_smul _ (Work.Gen.uVec_ne_zero t.2 x) _)
  rw [tbPhi_apply, hL, hR, tbCof_tbZExp, tbCof_tbZExp]
  rw [show (((Work.Whitney.sumFibreR 2 2).symm d).1, ((Work.Whitney.sumFibreR 2 2).symm d).2)
      = (Work.Whitney.sumFibreR 2 2).symm d from rfl]
  exact ContinuousLinearEquiv.apply_symm_apply (Work.Whitney.sumFibreR 2 2) d

end

end Work.ThomBordism.Grassmann.TBG
