import Submission.Work.BoxShrink.PinchOff.Rotation
import Submission.Work.BoxShrink.PinchOff.SpanSplit
import Submission.Work.BoxShrink.PinchOff.rotation_quarter_trace_curve
import Submission.Work.BoxShrink.PinchOff.meridian_one_rotation

/-!
# CORRECTION: the §26 "rotation refutation" does not stand

`README.md` §26 asserted that for `ψ` = the rotation of `ℝ³` about the `x`-axis by `α = 1/4`,
`c = 0`, `σ = (0 2 1)` (the cutting plane `{y = u}`) and `u = 0`, the trace of the cutting plane
is a *single contractible circle*, and concluded that the honest residual of the pinch
(`TracePerpSliceBox`, `TraceClosedSliceResidual`, the parent's `TraceClassBoundTame`) is **false**.

This module makes the correction of `README.md` §28 machine-checked:

* `rotation_trace_essential` — the trace at that configuration contains an **essential** closed
  curve: the explicit curve `rotTraceCurve` of `rotation_quarter_trace_curve.lean` (the graph
  `θ = arcsin (sin (1/4) · sin φ / (cos (1/4) · (2 + cos φ)))` in the parameter plane) has winding
  vector `(0, 1)`.  So the trace is *not* a union of contractible curves, and the step of §26.2
  ("the second alternative of the residual is unavailable") fails: the trace's class is nonzero;

* `rotation_witness_not_refutation` — sharper: at that configuration the residual's **conclusion
  actually holds**.  The meridian `{θ = 1}` of the rotated torus lies in the box region and in the
  upper half-region (`meridian_one_rotation`), so it realises the class `(0, 1)` in `W(Ω₊ ∪ Ω₋)`;
  the trace curve realises the same class in `W(F ∩ {plane})`; hence the second alternative of
  `TraceClassBound` is satisfied with `v = (0,1)`:

    `W(Ω) ⊓ ℚ(0,1) ≤ ℚ(0,1) ≤ W(Ω₊ ∪ Ω₋)`.

  So the configuration of §26.1 is an *instance* of the residual, not a counterexample to it.

Both names are recorded in `README.md` §28; the numeric diagnosis of the artefact is in
`_rot6.py` and `_wall3.py`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

/-! ## The trace is essential -/

/-- **The trace of the cutting plane at the §26 configuration carries an essential loop.**  The
witness is the explicit curve of `rotation_quarter_trace_curve.lean`, whose winding vector is
`(0, 1) ≠ 0`. -/
theorem rotation_trace_essential :
    (surface (rotDiffeo (1 / 4))).ContainsEssentialLoop
      (PlaneTrace (rotDiffeo (1 / 4)) 0 sigmaY 0) :=
  ⟨rotTraceCurve, ⟨rotTraceLift, by rw [rotTraceLift_winding]; decide⟩,
    rotTraceFun_mem_planeTrace⟩

/-- The class of the trace curve, as an element of `ℚ² = H₁`. -/
theorem zzClass_rotTraceCurve :
    zzClass (P := surface (rotDiffeo (1 / 4))) rotTraceCurve = ((0 : ℚ), (1 : ℚ)) := by
  simp only [zzClass, zzCast, windingOf_rotTraceCurve]
  norm_num

/-- **The class `(0,1)` lies in the span of the trace.** -/
theorem mem_planeSpan_rot :
    ((0 : ℚ), (1 : ℚ)) ∈ PlaneSpan (surface (rotDiffeo (1 / 4))) 0 sigmaY 0 := by
  refine Submodule.subset_span ⟨rotTraceCurve, rotTraceFun_mem_planeTrace, ?_⟩
  rw [windingOf_rotTraceCurve]
  norm_num

/-- **The class `(0,1)` lies in the span of the halves.**  The meridian `{θ = 1}` realises it, and
that meridian lies in the upper half-region, hence in the union of the two half-regions. -/
theorem mem_halvesSpan_rot :
    ((0 : ℚ), (1 : ℚ)) ∈ HalvesSpan (surface (rotDiffeo (1 / 4))) (9 / 5) 0 sigmaY 0 := by
  refine Work.SurgeryInvariance.WindingSpan_mono _ Set.subset_union_left ?_
  refine Submodule.subset_span
    ⟨Work.CoreTopology.meridianCurve (surface (rotDiffeo (1 / 4))) 1, meridian_one_rotation, ?_⟩
  rw [Work.SurgeryInvariance.windingOf_eq _ _
    (Work.CoreTopology.meridianLift (surface (rotDiffeo (1 / 4))) 1),
    Work.CoreTopology.meridianLift_winding]
  norm_num

/-! ## The residual holds at the §26 configuration -/

/-- **The §26 configuration does not refute the residual: it satisfies it.**  The honest residual
`TraceClassBound` of the parent chapter holds there, by its second alternative with the trace class
`v = (0, 1)`: the trace realises it (`mem_planeSpan_rot`) and so do the halves
(`mem_halvesSpan_rot`), whence `W(Ω) ⊓ ℚ(0,1) ≤ ℚ(0,1) ≤ W(Ω₊ ∪ Ω₋)`. -/
theorem rotation_witness_not_refutation :
    Work.BoxShrink.Pinch.TraceClassBound (surface (rotDiffeo (1 / 4))) (9 / 5) 0 sigmaY 0 := by
  refine Or.inr ⟨((0 : ℚ), (1 : ℚ)), by decide, mem_planeSpan_rot, ?_⟩
  exact (inf_span_singleton_le_iff (W := BoxSpan (surface (rotDiffeo (1 / 4))) (9 / 5) 0 sigmaY)
    (Wh := HalvesSpan (surface (rotDiffeo (1 / 4))) (9 / 5) 0 sigmaY 0)).mpr
      (Or.inr mem_halvesSpan_rot)

/-! ## The §26 configuration is an instance of *this chapter's* residual -/

/-- The trace parameter at `φ = π` is `0`, so the curve passes through the point `(1,0,0)`. -/
theorem rotTraceTheta_pi : rotTraceTheta Real.pi = 0 := by
  rw [rotTraceTheta, Real.sin_pi, mul_zero, zero_div, Real.arcsin_zero]

/-- **The trace curve meets the box region** at the §26 configuration: at `t = π` the curve is the
point `(1,0,0)` (`rotTraceTheta π = 0`), which lies in `PBox (9/5) 0 sigmaY` because its components
are `(1, 0, 0)` and the box half-lengths are `9/5`, `2^{1/3}·9/5`, `2^{2/3}·9/5` in the coordinates
`σ 1 = 0`, `σ 0 = 2`, `σ 2 = 1`. -/
theorem rotTraceCurve_mem_Omega :
    ∃ t : ℝ, rotTraceCurve t ∈ Omega (rotDiffeo (1 / 4)) (9 / 5) 0 sigmaY := by
  refine ⟨Real.pi, ?_⟩
  have hpt : rotTraceCurve Real.pi = WithLp.toLp 2 (![1, 0, 0] : Fin 3 → ℝ) := by
    rw [show rotTraceCurve Real.pi = rotTraceFun Real.pi from rfl, rotTraceFun_apply,
      rotTraceTheta_pi]
    ext i
    fin_cases i <;>
      simp only [show (⟨0, by omega⟩ : Fin 3) = 0 from rfl,
        show (⟨1, by omega⟩ : Fin 3) = 1 from rfl,
        show (⟨2, by omega⟩ : Fin 3) = 2 from rfl,
        rotDiffeo_apply, rotFun_coord_zero, rotFun_coord_one, rotFun_coord_two,
        Work.CoreTopology.torusMap_apply_zero, Work.CoreTopology.torusMap_apply_one,
        Work.CoreTopology.torusMap_apply_two, Real.cos_pi, Real.sin_pi, Real.cos_zero,
        Real.sin_zero, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      norm_num
  rw [Omega, Work.BoxShrink.Core.boxRegion, Set.mem_inter_iff]
  refine ⟨rotTraceCurve.mem Real.pi, ?_⟩
  rw [hpt, Submission.mem_PBox]
  intro i
  fin_cases i <;>
    simp only [show (⟨0, by omega⟩ : Fin 3) = 0 from rfl,
      show (⟨1, by omega⟩ : Fin 3) = 1 from rfl,
      show (⟨2, by omega⟩ : Fin 3) = 2 from rfl,
      PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, sigmaY_zero, sigmaY_one, sigmaY_two, PiLp.zero_apply,
      sub_zero, abs_zero, abs_one, Submission.boxSide_zero, Submission.boxSide_one,
      Submission.boxSide_two, mul_one] <;>
    (have hp1 : (0 : ℝ) < (2 : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos (by norm_num) (1 / 3)
     have hp2 : (0 : ℝ) < (2 : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos (by norm_num) (2 / 3)
     have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (1 / 3 : ℝ) := Submission.one_le_rpow_third
     try norm_num
     try exact hp2
     try nlinarith)

/-- **The §26 configuration satisfies the conclusion of this chapter's residual
`TracePerpSliceBox`.**  The trace curve `rotTraceCurve` meets the box region
(`rotTraceCurve_mem_Omega`) and has class `(0,1)` (`zzClass_rotTraceCurve`), and the class `(0,1)`
is realised in the half-regions (`mem_halvesSpan_rot`); hence the *second* alternative of the
residual holds with `v = (0,1)` and the family `{rotTraceCurve}`.  So the configuration of §26.1 is
an instance of the box-local residual, not a counterexample to it. -/
theorem rotation_witness_boxLocal :
    Work.SurgeryInvariance.WindingSpan (surface (rotDiffeo (1 / 4)))
        (Omega (rotDiffeo (1 / 4)) (9 / 5) 0 sigmaY) ≤
        Work.SurgeryInvariance.WindingSpan (surface (rotDiffeo (1 / 4)))
          (Halves (rotDiffeo (1 / 4)) (9 / 5) 0 sigmaY 0) ∨
      ∃ (v : ℚ × ℚ) (n : ℕ)
        (γ : Fin n → Work.CoreTopology.ClosedCurve (surface (rotDiffeo (1 / 4)))),
        v ≠ 0 ∧
        (∀ i, IsTraceCurve (rotDiffeo (1 / 4)) 0 sigmaY 0 (γ i)) ∧
        (∀ i, ∃ t : ℝ, γ i t ∈ Omega (rotDiffeo (1 / 4)) (9 / 5) 0 sigmaY) ∧
        (Pairwise fun i j => Disjoint (Set.range (γ i).γ) (Set.range (γ j).γ)) ∧
        v ∈ Submodule.span ℚ
          (Set.range fun i => zzClass (P := surface (rotDiffeo (1 / 4))) (γ i)) ∧
        Work.SurgeryInvariance.WindingSpan (surface (rotDiffeo (1 / 4)))
            (Omega (rotDiffeo (1 / 4)) (9 / 5) 0 sigmaY) ⊓
            LinearMap.ker (Work.BoxShrink.Pinch.crossLin v) ≤
          Work.SurgeryInvariance.WindingSpan (surface (rotDiffeo (1 / 4)))
            (Halves (rotDiffeo (1 / 4)) (9 / 5) 0 sigmaY 0) := by
  obtain ⟨t₀, ht₀⟩ := rotTraceCurve_mem_Omega
  refine Or.inr ⟨((0 : ℚ), (1 : ℚ)), 1, fun _ => rotTraceCurve, by decide,
    fun _ => rotTraceFun_mem_planeTrace, fun _ => ⟨t₀, ht₀⟩, ?_, ?_, ?_⟩
  · intro i j hij
    exact absurd (Subsingleton.elim i j) hij
  · refine Submodule.subset_span ⟨0, ?_⟩
    exact zzClass_rotTraceCurve
  · rw [ker_crossLin_eq_span (by decide : (((0 : ℚ), (1 : ℚ)) : ℚ × ℚ) ≠ 0)]
    exact (inf_span_singleton_le_iff (W := BoxSpan (surface (rotDiffeo (1 / 4))) (9 / 5) 0 sigmaY)
      (Wh := HalvesSpan (surface (rotDiffeo (1 / 4))) (9 / 5) 0 sigmaY 0)).mpr
        (Or.inr mem_halvesSpan_rot)

end

end Work.BoxShrink.PinchOff
