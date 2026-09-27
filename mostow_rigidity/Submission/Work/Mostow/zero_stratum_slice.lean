import Mathlib
import Submission.Work.Mostow.tiDefs

namespace Work.Mostow

open Submission.Mostow MeasureTheory

/-- For `m = 0` the Fermi chart is the first projection: `fermi j 0 v w = v`
(since `E 0` is a subsingleton and `‖w‖ = 0`). -/
private lemma fermi_zero_snd (j : ℕ) (v : E j) (w : E 0) : fermi j 0 v w = v := by
  have hw : w = 0 := Subsingleton.elim w 0
  subst hw
  ext i
  simp only [fermi, WithLp.ofLp_toLp, norm_zero, Real.cosh_zero, one_mul]
  have hi : Fin.castAdd 0 i = i := Fin.ext rfl
  conv_lhs => rw [← hi]
  rw [Fin.append_left]

theorem zero_stratum_slice (j : ℕ) (DY : Set (Submission.Mostow.E j))
    (hDY : MeasureTheory.NullMeasurableSet DY (Submission.Mostow.volH j)) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    Work.Mostow.tiTubeSlice j 0 DY ρ =ᵐ[Submission.Mostow.volH (j + 0)] DY := by
  have hzero : (0 : E 0) ∈ Metric.closedBall 0 ρ := by
    simp [Metric.mem_closedBall, hρ]
  have hset : (fun p : E j × E 0 => fermi j 0 p.1 p.2) ''
        (toMeasurable (volH j) DY ×ˢ Metric.closedBall 0 ρ)
      = toMeasurable (volH j) DY := by
    ext u
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hfst : (fun p : E j × E 0 => fermi j 0 p.1 p.2) p = p.1 := by
        obtain ⟨v, w⟩ := p
        exact fermi_zero_snd j v w
      rw [hfst]
      exact hp.1
    · intro hu
      exact ⟨(u, 0), ⟨hu, hzero⟩, fermi_zero_snd j u 0⟩
  rw [Work.Mostow.tiTubeSlice, hset]
  refine (MeasureTheory.NullMeasurableSet.toMeasurable_ae_eq ?_).trans ?_
  · exact (measurableSet_toMeasurable _ _).nullMeasurableSet
  · exact hDY.toMeasurable_ae_eq

end Work.Mostow
