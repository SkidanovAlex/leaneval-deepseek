import Mathlib
import Submission.Work.BoxShrink.PinchOff.RefuteNC.Config

/-!
# The trace of the cutting plane at the `nc` configuration realises the line `ℚ·(0,1)`

This module proves `Work.BoxShrink.PinchOff.RefuteNC.trace_nc`, the conjunction

* the trace of the cutting plane (at the configuration of `RefuteNC/Config.lean`: the standard
  torus, the box `PBox ncRad ncCtr ncCyc3` and the plane `{x = 1/2}`) has the period `(0, 1)`;
* the line `ℚ·(0,1)` is a **trace line**: every period of the trace lies in it.

Both are statements about the trace `Σ̃ = Φ⁻¹(F ∩ {x = 1/2})` in the parameter plane.  In the
parameter `(θ, φ)` of the standard torus the plane equation reads

  `(2 + cos φ) · cos θ = 1 / 2`,

so `cos θ = 1 / (2 (2 + cos φ)) ∈ [1/6, 1/2] ⊂ (0, 1)` everywhere on the trace: **the trace never
meets the locus `cos θ = 0`**, and its `θ`-coordinate is confined to an interval of length `π`.

* The period `(0, 1)` is realised explicitly: the path
  `t ↦ (arccos (1 / (2 (2 + cos (2πt)))), 2πt)`, which is continuous, moves by `(0, 2π)` over one
  unit of `t`, and lies on the trace because the arc-cosine inverts the plane equation
  (`tracePeriod_nc`).
* Every period `(k, l)` of the trace has `k = 0`: rescaling a witnessing path `q` by `2π` gives a
  continuous `f` with `cos (f s) > 0` everywhere and `f (2π) - f 0 = k · 2π`, so the winding
  increment `k` must vanish (`fst_eq_zero_of_tracePeriod`, via the toolkit lemma
  `Work.BoxShrink.PinchOff.int_eq_zero_of_cos_gt`).  Hence every trace period lies in the span of
  `(0, 1)`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff.RefuteNC

noncomputable section

/-! ## The explicit trace path realising the period `(0, 1)` -/

/-- **The trace path of the `nc` configuration.**  The point of the parameter plane with meridian
coordinate `2πt` and longitude the (unique positive) solution of the plane equation
`(2 + cos φ) cos θ = 1/2`. -/
def ncTracePath : ℝ → ℝ × ℝ :=
  fun t => (Real.arccos (1 / (2 * (2 + Real.cos (2 * Real.pi * t)))), 2 * Real.pi * t)

/-- **The trace in coordinates.**  A parameter `(θ, φ)` lies on the trace of the cutting plane
precisely when it satisfies the plane equation `(2 + cos φ) cos θ = 1/2` (the plane is
`{y 0 = 1 - 1/2} = {x = 1/2}`, and `torusMap θ φ 0 = (2 + cos φ) cos θ`). -/
theorem nc_mem_trace_iff {θ φ : ℝ} :
    ((θ, φ) : ℝ × ℝ) ∈
        Work.BoxShrink.Pinch.tracePreimage
          (Work.BoxShrink.PinchOff.surface Work.BoxShrink.PinchOff.idDiffeo)
          Work.BoxShrink.PinchOff.ncCtr Work.BoxShrink.PinchOff.ncCyc3
          Work.BoxShrink.PinchOff.ncU ↔
      (2 + Real.cos φ) * Real.cos θ = 1 / 2 := by
  rw [Work.BoxShrink.Pinch.tracePreimage, Work.BoxShrink.Pinch.mem_planePreimage,
    Work.BoxShrink.Core.mem_cutPlane]
  rw [Work.BoxShrink.PinchOff.surface_idDiffeo_eq_standard, Work.CoreTopology.standard_psi]
  simp only [Work.BoxShrink.PinchOff.ncCyc3_two, Work.BoxShrink.PinchOff.ncCtr_zero,
    Work.BoxShrink.PinchOff.ncU_eq]
  rw [Work.Core.torusMap_apply_zero]
  constructor <;> intro h <;> linarith

/-- The trace path is continuous. -/
theorem ncTracePath_cont : Continuous ncTracePath := by
  unfold ncTracePath
  refine Continuous.prodMk ?_ ?_
  · refine Real.continuous_arccos.comp ?_
    refine continuous_const.div ?_ ?_
    · fun_prop
    · intro t
      have h := Real.neg_one_le_cos (2 * Real.pi * t)
      nlinarith
  · fun_prop

/-- The trace path is a lift of the period `(0, 1)`: it moves by `(0, 2π)` over one unit of `t`. -/
theorem ncTracePath_period (t : ℝ) :
    ncTracePath (t + 1) = ncTracePath t + Work.TorusCover.periodShift ((0 : ℤ), (1 : ℤ)) := by
  have hcos : Real.cos (2 * Real.pi * (t + 1)) = Real.cos (2 * Real.pi * t) := by
    rw [show 2 * Real.pi * (t + 1) = 2 * Real.pi * t + (1 : ℤ) * (2 * Real.pi) by ring]
    rw [Real.cos_add_int_mul_two_pi]
  simp only [ncTracePath, Work.TorusCover.periodShift, hcos, Int.cast_zero, Int.cast_one,
    zero_mul, one_mul]
  ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring

/-- The trace path lies on the trace of the cutting plane. -/
theorem ncTracePath_mem (t : ℝ) :
    ncTracePath t ∈ Work.BoxShrink.Pinch.tracePreimage
      (Work.BoxShrink.PinchOff.surface Work.BoxShrink.PinchOff.idDiffeo)
      Work.BoxShrink.PinchOff.ncCtr Work.BoxShrink.PinchOff.ncCyc3
      Work.BoxShrink.PinchOff.ncU := by
  rw [nc_mem_trace_iff]
  simp only [ncTracePath]
  have hA1 : 1 ≤ 2 + Real.cos (2 * Real.pi * t) :=
    by linarith [Real.neg_one_le_cos (2 * Real.pi * t)]
  have hA3 : 2 + Real.cos (2 * Real.pi * t) ≤ 3 :=
    by linarith [Real.cos_le_one (2 * Real.pi * t)]
  have hden : 0 < 2 * (2 + Real.cos (2 * Real.pi * t)) := by linarith
  have hxle : 1 / (2 * (2 + Real.cos (2 * Real.pi * t))) ≤ 1 := by
    rw [div_le_one hden]; linarith
  have hxpos : 0 < 1 / (2 * (2 + Real.cos (2 * Real.pi * t))) := div_pos one_pos hden
  have hxge : -1 ≤ 1 / (2 * (2 + Real.cos (2 * Real.pi * t))) := by linarith
  rw [Real.cos_arccos hxge hxle]
  field_simp

/-- **The trace has the period `(0, 1)`**: the meridian circle `{x = 1/2}` of the torus. -/
theorem tracePeriod_nc :
    Work.BoxShrink.Pinch.TracePeriod
      (Work.BoxShrink.PinchOff.surface Work.BoxShrink.PinchOff.idDiffeo)
      Work.BoxShrink.PinchOff.ncCtr Work.BoxShrink.PinchOff.ncCyc3 Work.BoxShrink.PinchOff.ncU
      0 1 :=
  ⟨ncTracePath, ncTracePath_cont, fun t => by simpa using ncTracePath_period t, ncTracePath_mem⟩

/-! ## Every trace period has vanishing longitude winding -/

/-- **The trace keeps `cos θ` positive.**  A point of the trace satisfies
`(2 + cos φ) cos θ = 1/2` with `2 + cos φ ≥ 1 > 0`, whence `cos θ > 0`. -/
theorem cos_fst_pos_of_mem_trace {q : ℝ × ℝ}
    (hq : q ∈ Work.BoxShrink.Pinch.tracePreimage
      (Work.BoxShrink.PinchOff.surface Work.BoxShrink.PinchOff.idDiffeo)
      Work.BoxShrink.PinchOff.ncCtr Work.BoxShrink.PinchOff.ncCyc3
      Work.BoxShrink.PinchOff.ncU) :
    0 < Real.cos q.1 := by
  rw [Work.BoxShrink.Pinch.tracePreimage, Work.BoxShrink.Pinch.mem_planePreimage,
    Work.BoxShrink.Core.mem_cutPlane] at hq
  rw [Work.BoxShrink.PinchOff.surface_idDiffeo_eq_standard, Work.CoreTopology.standard_psi]
    at hq
  simp only [Work.BoxShrink.PinchOff.ncCyc3_two, Work.BoxShrink.PinchOff.ncCtr_zero,
    Work.BoxShrink.PinchOff.ncU_eq] at hq
  rw [Work.Core.torusMap_apply_zero] at hq
  have hA : 0 < 2 + Real.cos q.2 := by linarith [Real.neg_one_le_cos q.2]
  nlinarith [hq, hA]

/-- **The longitude winding of a trace period vanishes.**  A witness `q` of a trace period has
`cos (q t).1 > 0` for all `t`; rescaling it by `2π` gives a continuous function confined to an
interval of length `π` whose increment over one period is `k · 2π`, so `k = 0`. -/
theorem fst_eq_zero_of_tracePeriod {k l : ℤ}
    (h : Work.BoxShrink.Pinch.TracePeriod
      (Work.BoxShrink.PinchOff.surface Work.BoxShrink.PinchOff.idDiffeo)
      Work.BoxShrink.PinchOff.ncCtr Work.BoxShrink.PinchOff.ncCyc3
      Work.BoxShrink.PinchOff.ncU k l) : k = 0 := by
  obtain ⟨q, hqcont, hqper, hqmem⟩ := h
  have hθcont : Continuous (fun t : ℝ => (q t).1) := continuous_fst.comp hqcont
  have hcos : ∀ t : ℝ, 0 < Real.cos ((q t).1) := fun t => cos_fst_pos_of_mem_trace (hqmem t)
  let f : ℝ → ℝ := fun s => (q (s / (2 * Real.pi))).1
  have hfcont : Continuous f := hθcont.comp (continuous_id.div_const _)
  have hcosf : ∀ s : ℝ, 0 < Real.cos (f s) := fun s => hcos _
  have hdiff : f (2 * Real.pi) - f 0 = (k : ℝ) * (2 * Real.pi) := by
    have hp := hqper 0
    simp only [zero_add] at hp
    have h1 : f (2 * Real.pi) = (q 1).1 := by
      show (q ((2 * Real.pi) / (2 * Real.pi))).1 = (q 1).1
      rw [div_self (by positivity : (2 * Real.pi : ℝ) ≠ 0)]
    have h0 : f 0 = (q 0).1 := by
      show (q (0 / (2 * Real.pi))).1 = (q 0).1
      simp
    rw [h1, h0]
    have : (q 1).1 = (q 0).1 + (k : ℝ) * (2 * Real.pi) := by
      rw [hp]; simp [Work.TorusCover.periodShift]
    linarith
  exact Work.BoxShrink.PinchOff.int_eq_zero_of_cos_gt hfcont (by norm_num) (by norm_num) hcosf
    hdiff

/-- **The line `ℚ·(0,1)` is a trace line at the `nc` configuration.**  Its dimension is `1`, and
every trace period `(k, l)` has `k = 0`, hence lies in the span of `(0, 1)`. -/
theorem traceLine_nc :
    Work.BoxShrink.Pinch.TraceLine
      (Work.BoxShrink.PinchOff.surface Work.BoxShrink.PinchOff.idDiffeo)
      Work.BoxShrink.PinchOff.ncCtr Work.BoxShrink.PinchOff.ncCyc3 Work.BoxShrink.PinchOff.ncU
      (Submodule.span ℚ {((0 : ℚ), (1 : ℚ))}) := by
  refine ⟨?_, ?_⟩
  · exact le_of_eq (finrank_span_singleton (by norm_num : ((0 : ℚ), (1 : ℚ)) ≠ 0))
  · intro k l hper
    have hk : k = 0 := fst_eq_zero_of_tracePeriod hper
    rw [hk]
    have hmem : ((0 : ℚ), (1 : ℚ)) ∈ ({((0 : ℚ), (1 : ℚ))} : Set (ℚ × ℚ)) := by simp
    simpa using Submodule.smul_mem (Submodule.span ℚ {((0 : ℚ), (1 : ℚ))}) (l : ℚ)
      (Submodule.subset_span hmem)

end

theorem trace_nc :
    Work.BoxShrink.Pinch.TracePeriod (Work.BoxShrink.PinchOff.surface Work.BoxShrink.PinchOff.idDiffeo)
        Work.BoxShrink.PinchOff.ncCtr Work.BoxShrink.PinchOff.ncCyc3 Work.BoxShrink.PinchOff.ncU 0 1 ∧
      Work.BoxShrink.Pinch.TraceLine (Work.BoxShrink.PinchOff.surface Work.BoxShrink.PinchOff.idDiffeo)
        Work.BoxShrink.PinchOff.ncCtr Work.BoxShrink.PinchOff.ncCyc3 Work.BoxShrink.PinchOff.ncU
        (Submodule.span ℚ {((0 : ℚ), (1 : ℚ))}) := by
  exact ⟨tracePeriod_nc, traceLine_nc⟩

end Work.BoxShrink.PinchOff.RefuteNC
