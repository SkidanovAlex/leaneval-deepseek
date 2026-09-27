import Mathlib
import Submission.Work.Drive.stripConfigInterface
import Submission.Work.Drive.strip_offset
import Submission.Work.Drive.stripOffset_param

namespace Work.Drive

/-- **The image of the configuration strip is the image of the offset parametrisation cut at the
diameters.**  The map `stripImage` realises the strip as the quotient image of the capping coordinates
`confOf (μ q)` over *all* chords `q : Circle × Circle`.  Using the parametrisation of the strip by the
"short" chords — second endpoint `x * exp (2π i s)` with `s ∈ [0, 1/2]`
(`Work.Drive.stripOffset_param`) — every chord has such a presentation, so the same image is obtained
from the offset family alone. -/
theorem stripImage_eq_offset_image (μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ)
    (hsym : ∀ x y : Circle, μ (y, x) = μ (x, y))
    (hinj : ∀ x y x' y' : Circle, μ (x, y) = μ (x', y') →
      (x = x' ∧ y = y') ∨ (x = y' ∧ y = x')) :
    Work.Drive.stripImage μ =
      Quotient.mk'' ''
        (Sum.inl '' {q : Work.Drive.ConfigPiece |
          ∃ x : Circle, ∃ s : ℝ, s ∈ Set.Icc (0 : ℝ) (1 / 2) ∧
            (q : ℝ × ℂ × UnitAddCircle) =
              Work.Drive.confOf (μ (x, x * Circle.exp (2 * Real.pi * s)))}) := by
  -- Every chord appears in the offset family with `s ∈ [0, 1/2]`.
  have hsurj := (Work.Drive.stripOffset_param μ hsym hinj).2.2
  ext p
  constructor
  · -- A point of `stripImage` comes from a chord `q`; rewrite `q` as an offset chord.
    intro hp
    rw [Work.Drive.mem_stripImage_iff] at hp
    obtain ⟨q, h1, h2, hp⟩ := hp
    obtain ⟨x', s, hs, hμ⟩ := hsurj q.1 q.2
    have hμ' : μ q = μ (x', x' * Circle.exp (2 * Real.pi * s)) := hμ
    have h1' : 0 < (Work.Drive.confOf (μ (x', x' * Circle.exp (2 * Real.pi * s)))).1 := by
      rw [← hμ']; exact h1
    have h2' : ‖(Work.Drive.confOf (μ (x', x' * Circle.exp (2 * Real.pi * s)))).2.1‖ ≤ 1 := by
      rw [← hμ']; exact h2
    let S : Work.Drive.ConfigPiece :=
      ⟨Work.Drive.confOf (μ (x', x' * Circle.exp (2 * Real.pi * s))), h1', h2'⟩
    refine ⟨Sum.inl S, ⟨S, ⟨x', s, hs, rfl⟩, rfl⟩, ?_⟩
    have hSq : S = Work.Drive.confPiece (μ q) h1 h2 := by
      apply Subtype.ext
      rw [Work.Drive.confPiece_val]
      exact (congrArg Work.Drive.confOf hμ').symm
    rw [hSq]
    exact hp.symm
  · -- A point of the offset image has an obvious preimage chord in the strip.
    intro hp
    rw [Set.mem_image] at hp
    obtain ⟨z, hz, hzp⟩ := hp
    rw [Set.mem_image] at hz
    obtain ⟨q0, hq0, rfl⟩ := hz
    rw [Work.Drive.mem_stripImage_iff]
    obtain ⟨x, s, hs, hqs⟩ := hq0
    have h1 : 0 < (Work.Drive.confOf (μ (x, x * Circle.exp (2 * Real.pi * s)))).1 := by
      rw [← hqs]; exact q0.2.1
    have h2 : ‖(Work.Drive.confOf (μ (x, x * Circle.exp (2 * Real.pi * s)))).2.1‖ ≤ 1 := by
      rw [← hqs]; exact q0.2.2
    refine ⟨(x, x * Circle.exp (2 * Real.pi * s)), h1, h2, ?_⟩
    have hq : q0 = Work.Drive.confPiece (μ (x, x * Circle.exp (2 * Real.pi * s))) h1 h2 := by
      apply Subtype.ext
      rw [Work.Drive.confPiece_val]
      exact hqs
    rw [← hzp, hq]

end Work.Drive
