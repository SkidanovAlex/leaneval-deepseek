import Submission.Work.BoundaryChordSum
import Submission.Work.LemmaG4
import Submission.Work.TrapezoidLemma

open OptimalMoebius Topology ContDiff
open scoped BigOperators Matrix Topology Metric
set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Relation (4) and the Lemma-G witness from a far boundary point

Combining the sign-free chord-sum bound
(`BoundaryChordSum.boundary_chord_sum_le_abs`) with
`LemmaG4.relation4_of_points`: if some boundary point `f (1,s)` is at
perpendicular distance `> 1` from the line through the image endpoints of a
pre-bend chord `(0,α) → (1,β)` (any sign of the displacement), then

    √(5 + (β−α)²) < a + |β−α|          (relation (4), absolute-value form).

With the FREE relation (3) `√(1+Δ²) ≤ a − |Δ|`
(`BendArcFacts.chord_length_le_sub_abs_delta`) and
`TrapezoidLemma.lemmaG_of_aspect_inequalities` (applied at
`t := |β−α|`) this yields the `lemmaG_inequality` witness
`∃ t, 2a > max (aspectDelta t) (aspectNu t)`.  Note `Δ² = |Δ|²`, so relation
(3) at the leaf is exactly `√(1 + |Δ|²) ≤ a − |Δ|`.

Build: `lake build Submission.Work.Relation4Assembly` (rc=0 target).
-/

noncomputable section
namespace Submission

open Submission.PaperBand

/-- **Relation (4), absolute-value form.** -/
theorem relation4_of_boundary_far_abs {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {α β s : ℝ}
    (himg : ‖f !₂[1, β] - f !₂[0, α]‖ = ‖(!₂[1, β] : ℝ²) - !₂[0, α]‖)
    {c : ℝ} {n : ℝ³}
    (hdec : f !₂[1, s] - (1 / 2 : ℝ) • (f !₂[1, β] + f !₂[0, α])
        = c • (f !₂[1, β] - f !₂[0, α]) + n)
    (hperp : inner ℝ n (f !₂[1, β] - f !₂[0, α]) = 0) (hn : 1 < ‖n‖) :
    Real.sqrt (5 + (β - α) ^ 2) < a + |β - α| := by
  set u : ℝ := (β - α)
  have hbase : ‖f !₂[1, β] - f !₂[0, α]‖ = Real.sqrt (1 + |β - α| ^ 2) := by
    rw [himg, preimage_chord_length, sq_abs]
  have hsum := boundary_chord_sum_le_abs hf ha α β s
  have hdec' : f !₂[1, s] - (1 / 2 : ℝ) • (f !₂[0, α] + f !₂[1, β])
      = c • (f !₂[1, β] - f !₂[0, α]) + n := by
    rw [← hdec]; congr 2; rw [add_comm]
  have h := relation4_of_points (t := |β - α|) (h := ‖n‖)
    (p₁ := f !₂[0, α]) (p₂ := f !₂[1, β]) (w := f !₂[1, s])
    hbase hdec' hperp hn rfl hsum
  simpa only [sq_abs] using h

/-- **The Lemma-G witness from a pre-bend chord with a far boundary
point.** -/
theorem lemmaG_witness_of_boundary_far {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a)
    {α β s : ℝ}
    (himg : ‖f !₂[1, β] - f !₂[0, α]‖ = ‖(!₂[1, β] : ℝ²) - !₂[0, α]‖)
    {c : ℝ} {n : ℝ³}
    (hdec : f !₂[1, s] - (1 / 2 : ℝ) • (f !₂[1, β] + f !₂[0, α])
        = c • (f !₂[1, β] - f !₂[0, α]) + n)
    (hperp : inner ℝ n (f !₂[1, β] - f !₂[0, α]) = 0) (hn : 1 < ‖n‖) :
    ∃ t : ℝ, 2 * a > max (aspectDelta t) (aspectNu t) := by
  have h4 : Real.sqrt (5 + |β - α| ^ 2) < a + |β - α| := by
    have := relation4_of_boundary_far_abs hf ha himg hdec hperp hn
    simpa only [sq_abs] using this
  have h3 : Real.sqrt (1 + |β - α| ^ 2) ≤ a - |β - α| := by
    have h := chord_length_le_sub_abs_delta hf ha α β himg
    simpa only [sq_abs] using h
  have hta : |β - α| ≤ a := by
    have h1 : Real.sqrt (1 + |β - α| ^ 2) ≥ 1 := by
      have := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (|β - α|)] : (1 : ℝ) ≤ 1 + |β - α| ^ 2)
      rwa [Real.sqrt_one] at this
    linarith
  exact lemmaG_of_aspect_inequalities (abs_nonneg _) hta h3 h4

end Submission
