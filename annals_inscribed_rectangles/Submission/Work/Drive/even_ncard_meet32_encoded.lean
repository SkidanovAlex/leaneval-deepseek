import Mathlib
import Submission.Work.Drive.meet32_bordism_invariance

namespace Work.Drive

/-!
# Evenness of the endpoint triple count for the encoded `3 + 2 + 2` chains

`Submission/Work/Drive/meet32_bordism_invariance.lean` proves that for three chains `D 0`, `D 1`, `D 2`
in a `4`-manifold satisfying the packaged hypotheses `Meet3Hyp`, whose last two blocks `D 1`, `D 2` meet
their `x 2`-slices only on the seam, the two ends of the bordism `D 0` have the same triple intersection
number:
`Even ((topBdryMeet M D 0).ncard + (bottomBdryMeet M D 0).ncard)`.

Here we discharge the two remaining structural hypotheses for the concrete chains that come from the
*encoding* of a bordism of `2`-cycles: `Work.Drive.encodedChains W A B c` puts the bordism `W` in the
slice `M × {c}` at an interior time `c ∈ (0,1)`, and thickens the two `2`-cycles `A`, `B` in their third
parameter.  For those chains the second coordinate of `encodedChains W A B c 1 x` (resp. `2`) is `x 2`,
while the second coordinate of `encodedChains W A B c 0 x` is the constant `c`; a triple boundary point
of block `1` (resp. `2`) therefore has `x 1 2 = c` (resp. `x 2 2 = c`), which lies strictly between `0`
and `1`, so that its face coordinate cannot be the third one.  Hence it is a *seam* face, and the last
two blocks meet their slices only on the seam, which is exactly the hypothesis the bordism invariance
needs.
-/

/-- **A boundary face of the cube which is not the third one is a seam face.**  If a point of the unit
box lies on the boundary but neither `y 2 = 0` nor `y 2 = 1`, the boundary coordinate must be among the
first two, i.e. the point is on the seam. -/
lemma onSeam_of_mem_unitBoxBdry_of_third_ne {y : EuclideanSpace ℝ (Fin 3)}
    (hy : y ∈ Submission.Drive.unitBoxBdry 2) (h2a : y 2 ≠ 0) (h2b : y 2 ≠ 1) :
    onSeam y := by
  obtain ⟨-, i, hi⟩ := hy
  fin_cases i
  · rcases hi with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases hi with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · exact absurd hi (by rintro (h | h) <;> [exact h2a h; exact h2b h])

theorem even_ncard_meet32_encoded
    (M : Type*) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) (M × ℝ)]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (M × ℝ)]
    (W : EuclideanSpace ℝ (Fin 3) → M) (A B : EuclideanSpace ℝ (Fin 2) → M) (c : ℝ)
    (hc0 : 0 < c) (hc1 : c < 1)
    (h : Work.Drive.Meet3Hyp (M × ℝ) (Work.Drive.encodedChains W A B c)) :
    Even ((Work.Drive.topBdryMeet (M × ℝ) (Work.Drive.encodedChains W A B c) 0).ncard
      + (Work.Drive.bottomBdryMeet (M × ℝ) (Work.Drive.encodedChains W A B c) 0).ncard) := by
  classical
  -- Block `1` has second coordinate `x 2`, while block `0` has constant second coordinate `c`.
  have h1 : tripleBdryMeet (M × ℝ) (encodedChains W A B c) 1 ⊆
      seamBdryMeet (M × ℝ) (encodedChains W A B c) 1 := by
    rintro x ⟨hbox, h01, h02, hbdry⟩
    refine ⟨⟨hbox, h01, h02, hbdry⟩, ?_⟩
    have hsec : c = x 1 2 := by
      have := congrArg Prod.snd h01
      simpa using this
    exact onSeam_of_mem_unitBoxBdry_of_third_ne hbdry
      (fun h0 => absurd (hsec.trans h0) (ne_of_gt hc0))
      (fun h1 => absurd (hsec.trans h1) (ne_of_lt hc1))
  have h2 : tripleBdryMeet (M × ℝ) (encodedChains W A B c) 2 ⊆
      seamBdryMeet (M × ℝ) (encodedChains W A B c) 2 := by
    rintro x ⟨hbox, h01, h02, hbdry⟩
    refine ⟨⟨hbox, h01, h02, hbdry⟩, ?_⟩
    have hsec : c = x 2 2 := by
      have := congrArg Prod.snd h02
      simpa using this
    exact onSeam_of_mem_unitBoxBdry_of_third_ne hbdry
      (fun h0 => absurd (hsec.trans h0) (ne_of_gt hc0))
      (fun h1 => absurd (hsec.trans h1) (ne_of_lt hc1))
  exact even_ncard_topBdryMeet_add_bottomBdryMeet' (M × ℝ) (encodedChains W A B c) h h1 h2

end Work.Drive
