import Mathlib
import Submission.Work.Drive.Mono.CutTransverse
import Submission.Work.Sweep.AeTransverseCoord.ae_transverse_coord

/-!
# Almost every cutting level is cut-transverse

The box norm is a continuous function of the point, so the closed box is the sublevel set of the
box norm; the closure of the open box is contained in it.  This gives the boundary half of
`Work.Drive.Mono.CutTransverse`: a meeting of the knot with the cutting plane that lies in the
closure of `PBox s c σ` but not in the open box has box norm exactly `s`, hence is one of the
(finitely many, by hypothesis) parameters counted by `hfin`.

The transversality half is one-dimensional Sard, exactly as in
`Work.Sweep.AeTransverseCoord.ae_transverse_coord`: the critical values of the `σ 2`-coordinate of
the curve form a null set, and the bad levels are a translate of it.
-/

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set
open scoped ENNReal Topology

namespace Work.Drive.Mono

noncomputable section

/-- The box norm is continuous in the point. -/
theorem continuous_boxNorm (c : R3) (σ : Equiv.Perm (Fin 3)) :
    Continuous (fun y : R3 => Submission.boxNorm c σ y) := by
  unfold Submission.boxNorm
  fun_prop

/-- The closure of the open box is contained in the sublevel set `{boxNorm ≤ s}` of the box norm. -/
theorem closure_PBox_subset_boxNorm (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    closure (Submission.PBox s c σ) ⊆ {y : R3 | Submission.boxNorm c σ y ≤ s} := by
  refine closure_minimal (fun y hy => ?_) ?_
  · show Submission.boxNorm c σ y ≤ s
    exact le_of_lt ((Submission.mem_PBox_iff s c σ y).mp hy)
  · exact isClosed_le (continuous_boxNorm c σ) continuous_const

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set in
open scoped ENNReal Topology in
theorem ae_cutTransverse (K : Knot) {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3))
    (hfin : {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s}.Finite) :
    ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), Work.Drive.Mono.CutTransverse K s c σ u := by
  have hclsub := closure_PBox_subset_boxNorm s c σ
  -- The `σ 2`-coordinate of the curve, and one-dimensional Sard for it.
  set g : ℝ → ℝ := fun r => (K.curve r) (σ 2) with hgdef
  have hgc : ContDiff ℝ (⊤ : ℕ∞) g := by
    have h : ContDiff ℝ (⊤ : ℕ∞)
        (fun u : ℝ => (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (σ 2)) (K.curve u)) :=
      ContDiff.continuousLinearMap_comp _ K.smooth
    simpa [g] using h
  have hgd : ∀ t, HasDerivAt g (deriv g t) t := fun t =>
    (hgc.differentiable (by simp)).differentiableAt.hasDerivAt
  have hSard : volume (g '' {t : ℝ | deriv g t = 0}) = 0 := by
    refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (μ := volume)
      (f' := fun t => ContinuousLinearMap.toSpanSingleton ℝ (deriv g t)) ?_ ?_
    · intro t _
      exact (hgd t).hasFDerivAt.hasFDerivWithinAt
    · intro t ht
      rw [ht, ContinuousLinearMap.det_toSpanSingleton]
  -- Levels at which the knot meets the plane non-transversally form a null set.
  have hnull1 : volume ((fun u : ℝ => c (σ 2) + u) ⁻¹' (g '' {t : ℝ | deriv g t = 0})) = 0 := by
    rw [measure_preimage_add]
    exact hSard
  -- Levels at which the knot meets the plane on the boundary of the box form a finite set.
  set f : ℝ → ℝ := fun t => (K.curve t) (σ 2) - c (σ 2) with hfdef
  have hnull2 : volume (f '' {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
      Submission.boxNorm c σ (K.curve t) = s}) = 0 :=
    (hfin.image f).measure_zero volume
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null (fun u hu => ?_) (measure_union_null hnull1 hnull2)
  change ¬ CutTransverse K s c σ u at hu
  rw [CutTransverse] at hu
  push Not at hu
  obtain ⟨t, htcl, htv, hbad⟩ := hu
  by_cases hin : K.curve t ∈ Submission.PBox s c σ
  · -- the meeting is non-transversal
    left
    exact ⟨t, by simpa [hgdef] using hbad hin, by simpa [hgdef] using htv⟩
  · -- the meeting lies on the boundary of the box: `t` reduces, modulo periodicity, to `hfin`
    right
    have hle : Submission.boxNorm c σ (K.curve t) ≤ s := hclsub htcl
    have hge : s ≤ Submission.boxNorm c σ (K.curve t) := by
      refine not_lt.mp (fun hlt => hin ?_)
      exact (Submission.mem_PBox_iff s c σ (K.curve t)).mpr hlt
    have hnorm : Submission.boxNorm c σ (K.curve t) = s := le_antisymm hle hge
    obtain ⟨t', ht'Ico, hcur⟩ :=
      Function.Periodic.exists_mem_Ico₀ K.periodic
        (by positivity : (0 : ℝ) < 2 * Real.pi) t
    refine ⟨t', ⟨ht'Ico, ?_⟩, ?_⟩
    · rw [← hcur]; exact hnorm
    · show (K.curve t') (σ 2) - c (σ 2) = u
      rw [← hcur, htv, add_sub_cancel_left]

end

end Work.Drive.Mono
