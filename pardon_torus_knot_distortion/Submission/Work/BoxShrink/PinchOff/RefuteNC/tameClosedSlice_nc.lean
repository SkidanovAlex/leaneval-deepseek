import Mathlib
import Submission.Work.BoxShrink.PinchOff.RefuteNC.ArcSetup
import Submission.Work.BoxShrink.PinchOff.RefuteNC.ncArc_window_representative

/-!
# The slice of the `nc` configuration is closed-tame

The configuration `RefuteNC/Config.lean` is the standard torus of revolution, the box
`PBox ncRad ncCtr ncCyc3` (`ncRad = 1`, `ncCtr = (1, 19/10, 0)`, `ncCyc3 = (0 1 2)`) and the
cutting plane `{x = 1/2}` (`ncU = -1/2`).  Its slice

  `Σ = Sigma idDiffeo ncRad ncCtr ncCyc3 ncU = F ∩ PBox ∩ {x = 1/2}`

is the part of the trace of the plane `{x = 1/2}` on the torus cut out by the `y`-window
`9/10 < y < 29/10` of the box: two open arcs, whose closures are the two closed arcs

  `ncArc '' [ncPhiA, ncPhiB]`  and  `ncArc '' [2π - ncPhiB, 2π - ncPhiA]`,

where `ncArc φ = torusMap (ncTheta φ) φ` is the positive-branch trace
(`ArcSetup.lean`) and `ncPhiA = arccos (√(433/50) - 2)`, `ncPhiB = arccos (√(53/50) - 2)`
are the two parameters at which `ncY1 φ = 29/10` resp. `9/10`.

This module proves `TameClosedSlice` at the configuration: the two closed arcs are a finite family
of (continuous images of) arcs of the surface lying in — and covering — `closure Σ`.  It is the
witness that the configuration satisfies the honest tameness hypothesis of the corrected residual
`TraceClosedSliceResidual`, while its slice is *not* compact (the arcs end on the box sphere).

The two inputs are

* `trace_range_le` (proved here): `closure Σ ⊆ range ncArc`, i.e. every limit point of the slice
  lies on the positive-branch trace (`Σ` itself is on the positive branch because the `y`-window
  is positive; the range of `ncArc` is compact, hence closed);
* `ncArc_window_representative` (`ArcSetup`-sibling): the window inequality `9/10 ≤ ncY1 φ ≤ 29/10`
  puts `φ` on one of the two closed arcs modulo `2π`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff.RefuteNC

noncomputable section

/-! ## The two closed arcs as continuous maps on `ArcInterval = [0,1]` -/

/-- The first closed arc `ncArc '' [ncPhiA, ncPhiB]`, reparametrised over `[0,1]`. -/
def ncArc0 (t : Work.Smooth.Plane.ArcInterval) : R3 :=
  ncArc (ncPhiA + (t : ℝ) * (ncPhiB - ncPhiA))

/-- The second closed arc `ncArc '' [2π - ncPhiB, 2π - ncPhiA]`, reparametrised over `[0,1]`. -/
def ncArc1 (t : Work.Smooth.Plane.ArcInterval) : R3 :=
  ncArc ((2 * Real.pi - ncPhiB) +
    (t : ℝ) * ((2 * Real.pi - ncPhiA) - (2 * Real.pi - ncPhiB)))

theorem continuous_ncArc0 : Continuous ncArc0 :=
  continuous_ncArc.comp
    (continuous_const.add (continuous_subtype_val.mul continuous_const))

theorem continuous_ncArc1 : Continuous ncArc1 :=
  continuous_ncArc.comp
    (continuous_const.add (continuous_subtype_val.mul continuous_const))

/-- The first arc, as a continuous map on `ArcInterval`. -/
def arcLo : C(Work.Smooth.Plane.ArcInterval, R3) := ⟨ncArc0, continuous_ncArc0⟩

/-- The second arc, as a continuous map on `ArcInterval`. -/
def arcHi : C(Work.Smooth.Plane.ArcInterval, R3) := ⟨ncArc1, continuous_ncArc1⟩

theorem mem_Icc_phiA_phiB_of_param (t : Work.Smooth.Plane.ArcInterval) :
    ncPhiA + (t : ℝ) * (ncPhiB - ncPhiA) ∈ Set.Icc ncPhiA ncPhiB := by
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have hpos : (0 : ℝ) < ncPhiB - ncPhiA := by linarith [ncPhiA_lt_ncPhiB]
  refine ⟨?_, ?_⟩
  · have := mul_nonneg ht0 (le_of_lt hpos); linarith
  · have := mul_nonneg (sub_nonneg.mpr ht1) (le_of_lt hpos); linarith

theorem mem_Icc_second_of_param (t : Work.Smooth.Plane.ArcInterval) :
    (2 * Real.pi - ncPhiB) + (t : ℝ) * ((2 * Real.pi - ncPhiA) - (2 * Real.pi - ncPhiB))
      ∈ Set.Icc (2 * Real.pi - ncPhiB) (2 * Real.pi - ncPhiA) := by
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have hpos : (0 : ℝ) < (2 * Real.pi - ncPhiA) - (2 * Real.pi - ncPhiB) := by
    linarith [ncPhiA_lt_ncPhiB]
  refine ⟨?_, ?_⟩
  · have := mul_nonneg ht0 (le_of_lt hpos); linarith
  · have := mul_nonneg (sub_nonneg.mpr ht1) (le_of_lt hpos); linarith

/-! ## Every limit point of the slice lies on the positive-branch trace -/

/-- **The closure of the slice lies on the trace `ncArc`.**

A point `torusMap u v` of the slice satisfies `(2 + cos v) cos u = 1/2` (the plane `{x = 1/2}`)
and `9/10 < (2 + cos v) sin u < 29/10` (the `y`-window of the box), so `sin u > 0` and therefore
`(cos u, sin u) = (cos (ncTheta v), sin (ncTheta v))`: the point is `ncArc v`.  The range of
`ncArc` is compact (`ncArc` is `2π`-periodic), hence closed, so the whole closure is contained in
it. -/
theorem trace_range_le :
    closure (Work.BoxShrink.PinchOff.Sigma Work.BoxShrink.PinchOff.idDiffeo
        Work.BoxShrink.PinchOff.ncRad Work.BoxShrink.PinchOff.ncCtr
        Work.BoxShrink.PinchOff.ncCyc3 Work.BoxShrink.PinchOff.ncU) ⊆
      Set.range ncArc := by
  have hsub : Work.BoxShrink.PinchOff.Sigma Work.BoxShrink.PinchOff.idDiffeo
        Work.BoxShrink.PinchOff.ncRad Work.BoxShrink.PinchOff.ncCtr
        Work.BoxShrink.PinchOff.ncCyc3 Work.BoxShrink.PinchOff.ncU ⊆ Set.range ncArc := by
    intro y hy
    rw [Work.BoxShrink.PinchOff.Sigma, Work.BoxShrink.Core.mem_sliceRegion] at hy
    obtain ⟨hcar, hbox, hplane⟩ := hy
    obtain ⟨u, v, huv⟩ : ∃ u v : ℝ, Work.Core.torusMap u v = y := by
      rcases hcar with ⟨⟨u, v⟩, huv⟩
      exact ⟨u, v, huv⟩
    rw [← huv] at hbox hplane ⊢
    have hplane' : (2 + Real.cos v) * Real.cos u = 1 / 2 := by
      have h := hplane
      rw [Work.BoxShrink.PinchOff.ncCyc3_two, Work.Core.torusMap_apply_zero,
        Work.BoxShrink.PinchOff.ncCtr_zero, Work.BoxShrink.PinchOff.ncU_eq] at h
      linarith
    have hbox' : Submission.boxNorm Work.BoxShrink.PinchOff.ncCtr
        Work.BoxShrink.PinchOff.ncCyc3 (Work.Core.torusMap u v) < 1 := by
      have h := (Submission.mem_PBox_iff Work.BoxShrink.PinchOff.ncRad
        Work.BoxShrink.PinchOff.ncCtr Work.BoxShrink.PinchOff.ncCyc3
        (Work.Core.torusMap u v)).mp hbox
      rwa [Work.BoxShrink.PinchOff.ncRad_eq] at h
    have hy1 : 9 / 10 < (Work.Core.torusMap u v) 1 := by
      rw [Work.BoxShrink.PinchOff.boxNorm_nc] at hbox'
      have h1 : |(Work.Core.torusMap u v) 1 - 19 / 10| < 1 :=
        (max_lt_iff.mp (max_lt_iff.mp hbox').1).1
      rw [abs_lt] at h1
      linarith [h1.1]
    have hApos : 0 < 2 + Real.cos v := by linarith [Real.neg_one_le_cos v]
    have hy1' : 0 < (2 + Real.cos v) * Real.sin u := by
      rw [Work.Core.torusMap_apply_one] at hy1
      exact lt_trans (by norm_num) hy1
    have hsinu : 0 < Real.sin u := by nlinarith
    have hcosu : Real.cos u = Real.cos (ncTheta v) := by
      rw [ncTheta_cos]
      rw [eq_div_iff (ne_of_gt (by have := Real.neg_one_le_cos v; linarith :
        (0 : ℝ) < 2 * (2 + Real.cos v)))]
      linarith [hplane']
    have hsin_eq : Real.sin u = Real.sin (ncTheta v) := by
      have h1 : Real.sin u ^ 2 = Real.sin (ncTheta v) ^ 2 := by
        rw [Real.sin_sq, Real.sin_sq, hcosu]
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h | h
      · exact h
      · have := ncTheta_sin_pos v; linarith
    have hu : ∃ k : ℤ, u = ncTheta v + k * (2 * Real.pi) :=
      (Work.Core.cos_sin_eq_iff_exists_int u (ncTheta v)).mp ⟨hcosu, hsin_eq⟩
    refine ⟨v, ?_⟩
    rw [ncArc]
    exact ((Work.Core.torusMap_eq_iff u v (ncTheta v) v).mpr ⟨hu, ⟨0, by ring⟩⟩).symm
  have hclosed : IsClosed (Set.range ncArc) := by
    have hcomp : IsCompact (Set.range ncArc) := by
      have hrange : Set.range ncArc = ncArc '' Set.Icc (0 : ℝ) (2 * Real.pi) := by
        apply Subset.antisymm
        · rintro _ ⟨t, rfl⟩
          obtain ⟨s, hs, hsr⟩ :=
            Work.Smooth.Morse.Surface.exists_mem_Icc_periodic ncArc ncArc_periodic t
          exact ⟨s, hs, hsr⟩
        · rintro _ ⟨s, -, rfl⟩
          exact ⟨s, rfl⟩
      rw [hrange]
      exact isCompact_Icc.image continuous_ncArc
    exact hcomp.isClosed
  exact (hclosed.closure_subset_iff).mpr hsub

/-! ## The tameness witness -/

theorem tameClosedSlice_nc :
    Work.BoxShrink.PinchOff.TameClosedSlice Work.BoxShrink.PinchOff.idDiffeo
      Work.BoxShrink.PinchOff.ncRad Work.BoxShrink.PinchOff.ncCtr
      Work.BoxShrink.PinchOff.ncCyc3 Work.BoxShrink.PinchOff.ncU := by
  refine ⟨Fin 2, inferInstance, ![arcLo, arcHi], (0 : ℕ),
    (Fin.elim0 : Fin 0 → Work.CoreTopology.ClosedCurve (surface idDiffeo)),
    ?_, ?_, ?_⟩
  · intro j t
    fin_cases j
    · change ncArc (ncPhiA + (t : ℝ) * (ncPhiB - ncPhiA)) ∈
        closure (Sigma idDiffeo ncRad ncCtr ncCyc3 ncU)
      exact ncArc_image_Icc_phiA_phiB_subset_closure
        ⟨_, mem_Icc_phiA_phiB_of_param t, rfl⟩
    · change ncArc ((2 * Real.pi - ncPhiB) +
          (t : ℝ) * ((2 * Real.pi - ncPhiA) - (2 * Real.pi - ncPhiB))) ∈
        closure (Sigma idDiffeo ncRad ncCtr ncCyc3 ncU)
      exact ncArc_image_Icc_second_subset_closure
        ⟨_, mem_Icc_second_of_param t, rfl⟩
  · intro i
    exact Fin.elim0 i
  · intro x hx
    obtain ⟨φ, hφ⟩ := trace_range_le hx
    have hbox : Submission.boxNorm ncCtr ncCyc3 x ≤ 1 := by
      have hsub : Sigma idDiffeo ncRad ncCtr ncCyc3 ncU ⊆
          {y : R3 | Submission.boxNorm ncCtr ncCyc3 y ≤ ncRad} := by
        intro y hy
        have h := (Submission.mem_PBox_iff ncRad ncCtr ncCyc3 y).mp
          ((Work.BoxShrink.Core.mem_sliceRegion).mp hy).2.1
        exact le_of_lt h
      have hcl : IsClosed {y : R3 | Submission.boxNorm ncCtr ncCyc3 y ≤ ncRad} :=
        isClosed_le (Work.Topology.SphereSlicing.boxNorm_continuous ncCtr ncCyc3)
          continuous_const
      have := (hcl.closure_subset_iff).mpr hsub hx
      rwa [ncRad_eq] at this
    have hy1 : 9 / 10 ≤ ncY1 φ ∧ ncY1 φ ≤ 29 / 10 := by
      have h : |ncY1 φ - 19 / 10| ≤ 1 :=
        (boxNorm_ncArc_le_one_iff φ).mp (by rw [hφ]; exact hbox)
      rw [abs_le] at h
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    rcases ncArc_window_representative hy1 with ⟨ψ, hψ, heq⟩ | ⟨ψ, hψ, heq⟩
    · left
      refine ⟨0, ?_⟩
      show x ∈ Set.range arcLo
      refine ⟨⟨(ψ - ncPhiA) / (ncPhiB - ncPhiA), ?_, ?_⟩, ?_⟩
      · exact div_nonneg (by linarith [hψ.1]) (by linarith [ncPhiA_lt_ncPhiB])
      · rw [div_le_one (by linarith [ncPhiA_lt_ncPhiB])]; linarith [hψ.2]
      · show ncArc (ncPhiA + ((ψ - ncPhiA) / (ncPhiB - ncPhiA)) * (ncPhiB - ncPhiA)) = x
        rw [div_mul_cancel₀ _ (ne_of_gt (by linarith [ncPhiA_lt_ncPhiB]))]
        rw [show ncPhiA + (ψ - ncPhiA) = ψ by ring, heq, hφ]
    · left
      refine ⟨1, ?_⟩
      show x ∈ Set.range arcHi
      refine ⟨⟨(ψ - (2 * Real.pi - ncPhiB)) /
          ((2 * Real.pi - ncPhiA) - (2 * Real.pi - ncPhiB)), ?_, ?_⟩, ?_⟩
      · apply div_nonneg (by linarith [hψ.1])
        linarith [ncPhiA_lt_ncPhiB]
      · rw [div_le_one (by linarith [ncPhiA_lt_ncPhiB])]; linarith [hψ.2]
      · show ncArc ((2 * Real.pi - ncPhiB) +
            ((ψ - (2 * Real.pi - ncPhiB)) /
              ((2 * Real.pi - ncPhiA) - (2 * Real.pi - ncPhiB))) *
              ((2 * Real.pi - ncPhiA) - (2 * Real.pi - ncPhiB))) = x
        rw [div_mul_cancel₀ _ (ne_of_gt (by linarith [ncPhiA_lt_ncPhiB]))]
        rw [show (2 * Real.pi - ncPhiB) + (ψ - (2 * Real.pi - ncPhiB)) = ψ by ring, heq, hφ]

end

end Work.BoxShrink.PinchOff.RefuteNC
