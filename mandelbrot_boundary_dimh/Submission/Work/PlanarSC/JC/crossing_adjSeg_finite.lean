import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.Defs
import Submission.Work.HornSC.CellBoundaryJordan.RayDefs
import Submission.Work.HornSC.CellBoundaryJordan.GridCycleAux

namespace Work.PlanarSC.JC

open Set
open Work.HornSC.CellBoundaryJordan

/-- On the ray `t ↦ rayPt a ε t` with `ε > 0` the imaginary part is strictly increasing, so the
parameter is determined by the imaginary part of the point of the ray. -/
lemma rayPt_eq_of_im_eq {a : ℂ} {ε : ℝ} (hε : 0 < ε) {t₁ t₂ : ℝ}
    (h : (rayPt a ε t₁).im = (rayPt a ε t₂).im) : t₁ = t₂ := by
  rw [rayPt_im, rayPt_im] at h
  exact mul_left_cancel₀ (ne_of_gt hε) (add_left_cancel h)

/-- On the ray `t ↦ rayPt a ε t` the real part is strictly increasing, so the parameter is
determined by the real part of the point of the ray. -/
lemma rayPt_eq_of_re_eq {a : ℂ} {ε : ℝ} {t₁ t₂ : ℝ}
    (h : (rayPt a ε t₁).re = (rayPt a ε t₂).re) : t₁ = t₂ := by
  rw [rayPt_re, rayPt_re] at h
  exact add_left_cancel h

/-- A unit grid segment is either horizontal or vertical; the ray `t ↦ rayPt a ε t` (`ε > 0`)
therefore meets it in at most one point, i.e. the set of parameters of the ray points lying on it
has at most one element. -/
lemma subsingleton_rayPt_preimage_adjSeg {u v : ℤ × ℤ} (h : IsUnitAdj u v)
    {a : ℂ} {ε : ℝ} (hε : 0 < ε) :
    {t : ℝ | rayPt a ε t ∈ adjSeg u v}.Subsingleton := by
  intro t₁ ht₁ t₂ ht₂
  simp only [Set.mem_ofPred_eq] at ht₁ ht₂
  rcases h with h | h | h | h
  · rw [h, adjSeg_east, mem_hSeg] at ht₁ ht₂
    exact rayPt_eq_of_im_eq hε (by rw [ht₁.1, ht₂.1])
  · rw [h, adjSeg_west, mem_hSeg] at ht₁ ht₂
    exact rayPt_eq_of_im_eq hε (by rw [ht₁.1, ht₂.1])
  · rw [h, adjSeg_north, mem_vSeg] at ht₁ ht₂
    exact rayPt_eq_of_re_eq (by rw [ht₁.1, ht₂.1])
  · rw [h, adjSeg_south, mem_vSeg] at ht₁ ht₂
    exact rayPt_eq_of_re_eq (by rw [ht₁.1, ht₂.1])

theorem crossing_adjSeg_finite {k : ℕ} (u : ℕ → ℤ × ℤ)
    (hstep : ∀ i, i < k → Work.HornSC.CellBoundaryJordan.IsUnitAdj (u i) (u (i + 1)))
    {a : ℂ} {ε : ℝ} (hε : 0 < ε) :
    {t : ℝ | 0 < t ∧ Work.HornSC.CellBoundaryJordan.rayPt a ε t ∈
      ⋃ i ∈ {i : ℕ | i < k}, Work.HornSC.CellBoundaryJordan.adjSeg (u i) (u (i + 1))}.Finite := by
  have hfin : (⋃ i ∈ {i : ℕ | i < k},
      {t : ℝ | rayPt a ε t ∈ adjSeg (u i) (u (i + 1))}).Finite :=
    Set.Finite.biUnion (Set.finite_Iio k)
      (fun i hi => (subsingleton_rayPt_preimage_adjSeg (hstep i hi) hε).finite)
  refine hfin.subset ?_
  intro t ht
  obtain ⟨-, ht⟩ := ht
  simpa only [Set.mem_ofPred_eq, Set.mem_iUnion] using ht

end Work.PlanarSC.JC
