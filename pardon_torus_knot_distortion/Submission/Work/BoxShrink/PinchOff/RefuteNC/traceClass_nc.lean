import Mathlib
import Submission.Work.BoxShrink.PinchOff.RefuteNC.Config

/-!
# Every trace curve of the `nc` configuration has class along the meridian

At the configuration of `RefuteNC/Config.lean` (the standard torus, the box
`PBox ncRad ncCtr ncCyc3` and the cutting plane `{x = 1/2}`), a closed curve carried by the
trace of the cutting plane has winding class lying on the line `ℚ·(0,1)`: its longitude winding
vanishes.

The reason is the shape of the trace in the parameter plane: the plane `{x = 1/2}` is
`{ (2 + cos φ) cos θ = 1/2 }`, so `cos θ = 1/(2 (2 + cos φ)) ≥ 1/6 > 0` at every point of the
trace.  A lift `L` of a trace curve therefore satisfies `cos (L.Θ t) > 0` for all `t`, a one-sided
cosine bound which confines `L.Θ` to an interval of length `π < 2π` over a period
(`Work.BoxShrink.PinchOff.int_eq_zero_of_cos_gt`), forcing `(L.winding).1 = 0`.

This is the third of the three facts that make the configuration a counterexample to the
transport form of the residual (`RefuteNC/*`), namely that the trace periods of the cutting
plane all lie on the line `ℚ·(0,1)`.
-/

namespace Work.BoxShrink.PinchOff.RefuteNC

theorem traceClass_nc
    (γ : Work.CoreTopology.ClosedCurve (Work.BoxShrink.PinchOff.surface Work.BoxShrink.PinchOff.idDiffeo))
    (hγ : Work.BoxShrink.PinchOff.IsTraceCurve Work.BoxShrink.PinchOff.idDiffeo
      Work.BoxShrink.PinchOff.ncCtr Work.BoxShrink.PinchOff.ncCyc3
      Work.BoxShrink.PinchOff.ncU γ) :
    Work.BoxShrink.PinchOff.zzClass (P := Work.BoxShrink.PinchOff.surface Work.BoxShrink.PinchOff.idDiffeo) γ
      ∈ Submodule.span ℚ {((0 : ℚ), (1 : ℚ))} := by
  -- the plane coordinate of a point of the trace is `1/2`
  have hcoord : ∀ t : ℝ, γ t 0 = 1 / 2 := by
    intro t
    have h := ((Work.BoxShrink.PinchOff.mem_PlaneTrace_iff (ψ := Work.BoxShrink.PinchOff.idDiffeo)
      (c := Work.BoxShrink.PinchOff.ncCtr) (σ := Work.BoxShrink.PinchOff.ncCyc3)
      (u := Work.BoxShrink.PinchOff.ncU) (γ t)).mp (hγ t)).2
    simp only [Work.BoxShrink.PinchOff.ncCyc3_two, Work.BoxShrink.PinchOff.ncCtr_zero,
      Work.BoxShrink.PinchOff.ncU_eq] at h
    norm_num at h ⊢
    exact h
  -- a lift of `γ`
  obtain ⟨L⟩ := Work.TorusCover.ParamTorus_exists_liftOf
    (Work.BoxShrink.PinchOff.surface Work.BoxShrink.PinchOff.idDiffeo) γ
  have hlift : ∀ t : ℝ, Work.Core.torusMap (L.Θ t) (L.Φ t) = γ t := fun t => L.lifts t
  -- the plane equation `(2 + cos (L.Φ t)) cos (L.Θ t) = 1/2` gives `cos (L.Θ t) > 0`
  have hcos : ∀ t : ℝ, 0 < Real.cos (L.Θ t) := by
    intro t
    have h0 : (Work.Core.torusMap (L.Θ t) (L.Φ t)) 0 = γ t 0 := by rw [hlift t]
    rw [Work.CoreTopology.torusMap_apply_zero] at h0
    rw [hcoord t] at h0
    have hpos : (0 : ℝ) < 2 + Real.cos (L.Φ t) := by linarith [Real.neg_one_le_cos (L.Φ t)]
    nlinarith [h0, hpos]
  -- so the longitude winding vanishes
  have hw1 : (L.winding).1 = 0 := by
    refine Work.BoxShrink.PinchOff.int_eq_zero_of_cos_gt (f := L.Θ) L.contΘ (by norm_num)
      (by norm_num) hcos ?_
    linarith [L.winding_spec.1]
  have hwind : Work.SurgeryInvariance.windingOf
      (Work.BoxShrink.PinchOff.surface Work.BoxShrink.PinchOff.idDiffeo) γ = L.winding :=
    Work.SurgeryInvariance.windingOf_eq _ γ L
  have hwind2 : L.winding = ((0 : ℤ), (L.winding).2) := Prod.ext hw1 rfl
  rw [Work.BoxShrink.PinchOff.zzClass, hwind, hwind2]
  simp only [Work.BoxShrink.PinchOff.zzCast]
  refine Submodule.mem_span_singleton.mpr ⟨((L.winding).2 : ℚ), ?_⟩
  ext <;> simp

end Work.BoxShrink.PinchOff.RefuteNC
